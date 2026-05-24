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
            var_val_activity: HashMap::new()
        }
    }
}

impl<BackupBrancher: Brancher> Brancher for CustomSearch<BackupBrancher> {
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        eprintln!("Current variable bounds:");

        for variable in context.get_domains() {
            eprintln!(
                "var {:?}: [{}, {}]",
                variable,
                context.lower_bound(variable),
                context.upper_bound(variable)
            );
        }
        
        self.backup_brancher.next_decision(context)
    }

    fn log_statistics(&self, _statistic_logger: StatisticLogger) {
        // Implement logging of statistics if needed.
    }

    fn on_backtrack(&mut self) {
        // Implement behavior on backtracking.
    }

    fn synchronise(&mut self, context: &mut SelectionContext) {
        // Implement synchronization logic if needed.
    }

    fn on_conflict(&mut self) {
        // Implement behavior on conflict.
    }

    fn on_solution(&mut self, _solution: SolutionReference) {
        // Implement behavior on finding a solution.
    }

    fn on_appearance_in_conflict_predicate(&mut self, predicate: Predicate) {
        // Implement behavior when a predicate appears in a conflict.
        let variable = predicate.get_domain();

        if predicate.is_lower_bound_predicate() {

		} else if predicate.is_upper_bound_predicate() {
		} else if predicate.is_not_equal_predicate() {
		} else if predicate.is_equality_predicate() {
		}
    }
    
    fn on_restart(&mut self) {
        // Implement behavior on restart.
    }

    fn on_unassign_integer(&mut self, _variable: DomainId, _value: i32) {
        // Implement behavior on unassigning an integer.
    }

    fn is_restart_pointless(&mut self) -> bool {
        // Implement logic to determine if a restart is pointless.
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
    ) {
        eprintln!("Learned nogood with {} predicates:", learned_nogood.predicates.len());
        for (i, predicate) in learned_nogood.predicates.iter().enumerate() {
            eprintln!("  [{}] {:?}", i, predicate);
        }
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