use std::collections::HashMap;

use super::independent_variable_value_brancher::IndependentVariableValueBrancher;
use crate::DefaultBrancher;
use crate::basic_types::DeletablePredicateIdGenerator;
use crate::basic_types::PredicateId;
use crate::basic_types::SolutionReference;
use crate::branching::Brancher;
use crate::branching::BrancherEvent;
use crate::branching::SelectionContext;
use crate::branching::value_selection::InDomainMin;
use crate::branching::variable_selection::InputOrder;
use crate::conflict_resolving::LearnedNogood;
use crate::containers::KeyValueHeap;
use crate::containers::StorageKey;
use crate::create_statistics_struct;
use crate::engine::Assignments;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::predicates::predicate::PredicateType;
use crate::propagation::ReadDomains;
use crate::results::Solution;
use crate::statistics::Statistic;
use crate::statistics::StatisticLogger;
use crate::statistics::moving_averages::CumulativeMovingAverage;
use crate::statistics::moving_averages::MovingAverage;
use crate::variables::DomainId;

#[derive(Debug, Default, Clone)]
struct ValueActivity {
    ge: f64,
    le: f64,
    total: f64,
}

/// A custom [`Brancher`] implementation.
///
/// This is a placeholder for a user-defined branching strategy.
#[derive(Debug)]
pub struct CustomSearch<BackupBrancher> {
    // Backup brancher for when we can not make a decision
    backup_brancher: BackupBrancher,
    // How much the activity of a value is increased
    increment: f64,
    // variable -> value -> activity
    var_val_activity: HashMap<DomainId, HashMap<i32, ValueActivity>>,
    /// Stores the activity for a variable, using the max ValueActivity.total.
    heap: KeyValueHeap<DomainId, f64>,
}


const DEFAULT_INCREMENT: f64 = 1.0;
const DECAY_FACTOR: f64 = 0.95;

impl<BackupBrancher> CustomSearch<BackupBrancher> {
    /// Creates a new instance of `CustomSearch`.
    pub fn new(backup_brancher: BackupBrancher) -> Self {
        CustomSearch {
            // Initialize fields here.
            backup_brancher,
            increment: DEFAULT_INCREMENT,
            var_val_activity: HashMap::new(),
            heap: KeyValueHeap::default(),
        }
    }

    fn ensure_variable_entry(&mut self, var: DomainId) -> &mut HashMap<i32, ValueActivity> {
        self.var_val_activity.entry(var).or_default()
    }

    fn ensure_heap_entry(&mut self, var: DomainId) {
        while self.heap.len() <= var.index() {
            let next_key = DomainId::create_from_index(self.heap.len());
            self.heap.grow(next_key, 0.0);
        }
        self.heap.restore_key(var);
    }

    fn bump_value_activity(
        &mut self,
        variable: DomainId,
        value: i32,
        bump_ge: bool,
        bump_le: bool,
    ) {
        let increment = self.increment;
        let value_activity = self
            .ensure_variable_entry(variable)
            .entry(value)
            .or_default();

        if bump_ge {
            value_activity.ge += increment;
        }
        if bump_le {
            value_activity.le += increment;
        }

        let total_bumps = (bump_ge as u8 + bump_le as u8) as f64;
        value_activity.total += if total_bumps > 0.0 {
            total_bumps * increment
        } else {
            increment
        };

        self.ensure_heap_entry(variable);
        self.heap.increment(variable, increment);
    }
}

impl<BackupBrancher: Brancher> Brancher for CustomSearch<BackupBrancher> {
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        loop {
            let variable = match self.heap.peek_max() {
                Some((variable, _)) => *variable,
                None => {
                    break;
                },
            };

            if context.is_integer_fixed(variable) {
                let _ = self.heap.pop_max();
                continue;
            }

            let Some(value_activities) = self.var_val_activity.get(&variable) else {
                let _ = self.heap.pop_max();
                continue;
            };

            let mut best_value = None;
            let mut best_total = f64::NEG_INFINITY;

            for value in context.lower_bound(variable)..=context.upper_bound(variable) {
                if !context.contains(variable, value) {
                    continue;
                }

                let total = value_activities
                    .get(&value)
                    .map(|activity| activity.total)
                    .unwrap_or(0.0);
                if total > best_total {
                    best_total = total;
                    best_value = Some(value);
                }
            }

            let Some(value) = best_value else {
                let _ = self.heap.pop_max();
                continue;
            };

            let direction = value_activities.get(&value).cloned().unwrap_or_default();
            let predicate_type = if direction.ge >= direction.le {
                PredicateType::LowerBound
            } else {
                PredicateType::UpperBound
            };
            let predicate = Predicate::new(variable, predicate_type, value);
            // eprintln!("CustomSearch chose predicate: {predicate}");
            return Some(predicate);
        }

        return self.backup_brancher.next_decision(context);
    }

    fn log_statistics(&self, statistic_logger: StatisticLogger) {
        self.backup_brancher.log_statistics(statistic_logger);
    }

    fn on_backtrack(&mut self) {
        self.backup_brancher.on_backtrack();
    }

    fn synchronise(&mut self, context: &mut SelectionContext) {
        self.backup_brancher.synchronise(context);
    }

    fn on_conflict(&mut self) {
        self.backup_brancher.on_conflict();
    }

    fn on_solution(&mut self, solution: SolutionReference) {
        self.backup_brancher.on_solution(solution);
    }

    fn on_appearance_in_conflict_predicate(&mut self, predicate: Predicate) {
        let variable = predicate.get_domain();
        let value = predicate.get_right_hand_side();

        if predicate.is_lower_bound_predicate() {
            self.bump_value_activity(variable, value, true, false);
        } else if predicate.is_upper_bound_predicate() {
            self.bump_value_activity(variable, value, false, true);
        } else if predicate.is_equality_predicate() {
            self.bump_value_activity(variable, value, true, true);
        } else if predicate.is_not_equal_predicate() {
            self.bump_value_activity(variable, value.saturating_sub(1), false, true);
            self.bump_value_activity(variable, value.saturating_add(1), true, false);
        }

        self.backup_brancher.on_appearance_in_conflict_predicate(predicate);
    }
    
    fn on_restart(&mut self) {
        self.backup_brancher.on_restart();
    }

    // TODO: add back variable to the heap?
    fn on_unassign_integer(&mut self, variable: DomainId, value: i32) {
        self.backup_brancher.on_unassign_integer(variable, value);
    }

    fn is_restart_pointless(&mut self) -> bool {
        false
    }

    fn subscribe_to_events(&self) -> Vec<BrancherEvent> {
        [
            BrancherEvent::Solution,
            BrancherEvent::Conflict,
            BrancherEvent::Backtrack,
            BrancherEvent::Synchronise,
            BrancherEvent::AppearanceInConflictPredicate,
            BrancherEvent::LearnedNogood
        ]
        .into_iter()
        .chain(self.backup_brancher.subscribe_to_events())
        .collect()
    }

    fn on_learned_nogood(
        &mut self,
        learned_nogood: &LearnedNogood,
        context: &SelectionContext,
    ) {
        self.backup_brancher.on_learned_nogood(learned_nogood, context);
    }
}

#[cfg(test)]
mod tests {
    use super::CustomSearch;
    use crate::branching::Brancher;
    use crate::branching::SelectionContext;
    use crate::engine::Assignments;

    #[test]
    fn test_custom_search() {
        
    }
}