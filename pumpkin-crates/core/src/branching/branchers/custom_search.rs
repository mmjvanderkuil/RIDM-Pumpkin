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
    /// Stores the activity for a variable, using max(ge, le) across values.
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

    fn set_heap_value(&mut self, variable: DomainId, new_value: f64) {
        self.ensure_heap_entry(variable);
        self.heap.delete_key(variable);
        let current = *self.heap.get_value(variable);
        self.heap.increment(variable, new_value - current);
        self.heap.restore_key(variable);
    }

    fn value_score(activity: &ValueActivity) -> f64 {
        activity.ge.max(activity.le)
    }

    fn preferred_predicate_type(activity: &ValueActivity) -> PredicateType {
        if activity.ge >= activity.le {
            PredicateType::LowerBound
        } else {
            PredicateType::UpperBound
        }
    }

    fn refresh_heap_value_from_activity(&mut self, variable: DomainId) {
        let Some(value_activities) = self.var_val_activity.get(&variable) else {
            self.ensure_heap_entry(variable);
            return;
        };

        let best_score = value_activities
            .values()
            .map(Self::value_score)
            .max_by(|a, b| a.total_cmp(b))
            .unwrap_or(0.0);

        self.set_heap_value(variable, best_score);
    }

    fn refresh_heap_value_from_context(&mut self, variable: DomainId, context: &SelectionContext) {
        let Some(value_activities) = self.var_val_activity.get(&variable) else {
            self.heap.delete_key(variable);
            return;
        };

        let mut best_score = f64::NEG_INFINITY;
        let mut found = false;

        for value in context.lower_bound(variable)..=context.upper_bound(variable) {
            if !context.contains(variable, value) {
                continue;
            }

            let direction = value_activities.get(&value).cloned().unwrap_or_default();
            let predicate_type = if direction.ge >= direction.le {
                PredicateType::LowerBound
            } else {
                PredicateType::UpperBound
            };
            let predicate = Predicate::new(variable, predicate_type, value);
            if context.is_predicate_assigned(predicate) {
                continue;
            }

            let score = value_activities
                .get(&value)
                .map(Self::value_score)
                .unwrap_or(0.0);
            if score > best_score {
                best_score = score;
                found = true;
            }
        }

        if found {
            self.set_heap_value(variable, best_score);
        } else {
            self.heap.delete_key(variable);
        }
    }

    fn bump_value_activity(
        &mut self,
        variable: DomainId,
        value: i32,
        bump_ge: bool,
        bump_le: bool,
    ) {
        let increment = self.increment;
        let new_score = {
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

            Self::value_score(value_activity)
        };

        self.ensure_heap_entry(variable);
        if new_score > *self.heap.get_value(variable) {
            self.set_heap_value(variable, new_score);
        }
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
            let mut best_score = f64::NEG_INFINITY;

            for value in context.lower_bound(variable)..=context.upper_bound(variable) {
                if !context.contains(variable, value) {
                    continue;
                }

                let score = value_activities
                    .get(&value)
                    .map(Self::value_score)
                    .unwrap_or(0.0);
                let direction = value_activities.get(&value).cloned().unwrap_or_default();

                if score > best_score {
                    best_score = score;
                    best_value = Some(value);
                } else if score.total_cmp(&best_score).is_eq() {
                    let should_replace = match Self::preferred_predicate_type(&direction) {
                        PredicateType::LowerBound => {
                            best_value.map(|current| value < current).unwrap_or(true)
                        }
                        PredicateType::UpperBound => {
                            best_value.map(|current| value > current).unwrap_or(true)
                        }
                        _ => false,
                    };

                    if should_replace {
                        best_value = Some(value);
                    }
                }
            }

            let Some(value) = best_value else {
                let _ = self.heap.pop_max();
                continue;
            };

            let direction = value_activities.get(&value).cloned().unwrap_or_default();
            let predicate_type = Self::preferred_predicate_type(&direction);
            let predicate = Predicate::new(variable, predicate_type, value);

            if context.is_predicate_assigned(predicate) {
                self.refresh_heap_value_from_context(variable, context);
                continue;
            }

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
        self.backup_brancher.on_appearance_in_conflict_predicate(predicate);
    }
    
    fn on_restart(&mut self) {
        self.backup_brancher.on_restart();
    }

    fn on_unassign_integer(&mut self, variable: DomainId, value: i32) {
        self.refresh_heap_value_from_activity(variable);
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
        for predicate in &learned_nogood.predicates {
            let variable = predicate.get_domain();
            let value = predicate.get_right_hand_side();

            if predicate.is_lower_bound_predicate() {
                let start = value.max(context.lower_bound(variable));
                let end = context.upper_bound(variable);
                for implied_value in start..=end {
                    if context.contains(variable, implied_value) {
                        self.bump_value_activity(variable, implied_value, true, false);
                    }
                }
            } else if predicate.is_upper_bound_predicate() {
                let start = context.lower_bound(variable);
                let end = value.min(context.upper_bound(variable));
                for implied_value in start..=end {
                    if context.contains(variable, implied_value) {
                        self.bump_value_activity(variable, implied_value, false, true);
                    }
                }
            } else if predicate.is_equality_predicate() {
                self.bump_value_activity(variable, value, true, true);
            } else if predicate.is_not_equal_predicate() {
                let lower = context.lower_bound(variable);
                let upper = context.upper_bound(variable);

                let le_end = value.saturating_sub(1).min(upper);
                for implied_value in lower..=le_end {
                    if context.contains(variable, implied_value) {
                        self.bump_value_activity(variable, implied_value, false, true);
                    }
                }

                let ge_start = value.saturating_add(1).max(lower);
                for implied_value in ge_start..=upper {
                    if context.contains(variable, implied_value) {
                        self.bump_value_activity(variable, implied_value, true, false);
                    }
                }
            }
        }
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