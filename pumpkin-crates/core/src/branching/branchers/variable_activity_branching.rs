use crate::DefaultBrancher;
use crate::basic_types::SolutionReference;
use crate::branching::Brancher;
use crate::branching::BrancherEvent;
use crate::branching::SelectionContext;
use crate::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use crate::branching::value_selection::InDomainMin;
use crate::branching::variable_selection::InputOrder;
use crate::engine::Assignments;
use crate::predicates::Predicate;
use crate::statistics::StatisticLogger;
use crate::variables::DomainId;

/// A custom [`Brancher`] implementation.
///
/// This is a placeholder for a user-defined branching strategy.
#[derive(Debug)]
pub struct VariableActivitySearch<BackupBrancher> {
    // Backup brancher for when we can not make a decision
    backup_brancher: BackupBrancher,
    // How much the activity of a value is increased
    increment: f64,
}

const DEFAULT_INCREMENT: f64 = 1.0;

impl DefaultBrancher {
    /// Creates a new instance with default values for
    /// the parameters (`1.0` for the increment, `1e100` for the max threshold,
    /// `0.95` for the decay factor and `0.0` for the initial VSIDS value).
    ///
    /// If there are no more predicates left to select, this [`Brancher`] switches to
    /// [`InputOrder`] with [`InDomainMin`].
    pub fn default_over_all_variables(assignments: &Assignments) -> DefaultBrancher {
        VariableActivitySearch {
            increment: DEFAULT_INCREMENT,
            backup_brancher: IndependentVariableValueBrancher::new(
                InputOrder::new(&assignments.get_domains().collect::<Vec<_>>()),
                InDomainMin,
            ),
        }
    }

    pub fn add_domain(&mut self, domain: DomainId) {
        self.backup_brancher.variable_selector.add_domain(domain);
    }
}


// impl DefaultBrancher {
//     /// Creates a new instance with default values for
//     /// the parameters (`1.0` for the increment, `1e100` for the max threshold,
//     /// `0.95` for the decay factor and `0.0` for the initial VSIDS value).
//     ///
//     /// If there are no more predicates left to select, this [`Brancher`] switches to
//     /// [`InputOrder`] with [`InDomainMin`].
//     pub fn default_over_all_variables(assignments: &Assignments) -> DefaultBrancher {
//         AutonomousSearch {
//             predicate_id_info: DeletablePredicateIdGenerator::default(),
//             heap: KeyValueHeap::default(),
//             dormant_predicates: vec![],
//             increment: DEFAULT_VSIDS_INCREMENT,
//             max_threshold: DEFAULT_VSIDS_MAX_THRESHOLD,
//             decay_factor: DEFAULT_VSIDS_DECAY_FACTOR,
//             best_known_solution: None,
//             should_synchronise: false,
//             backup_brancher: IndependentVariableValueBrancher::new(
//                 InputOrder::new(&assignments.get_domains().collect::<Vec<_>>()),
//                 InDomainMin,
//             ),
//             statistics: Default::default(),
//         }
//     }

//     pub fn add_domain(&mut self, domain: DomainId) {
//         self.backup_brancher.variable_selector.add_domain(domain);
//     }
// }

impl<BackupBrancher> VariableActivitySearch<BackupBrancher> {
    /// Creates a new instance of `VariableActivitySearch`.
    pub fn new(backup_brancher: BackupBrancher) -> Self {
        println!("Here\n");
        VariableActivitySearch {
            // Initialize fields here.
            backup_brancher,
            increment: DEFAULT_INCREMENT
        }
    }
}

impl<BackupBrancher: Brancher> Brancher for VariableActivitySearch<BackupBrancher> {
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        println!("Current variable bounds:");

        for variable in context.get_domains() {
            println!(
                "var {:?}: [{}, {}]",
                variable,
                context.lower_bound(variable),
                context.upper_bound(variable)
            );
        }
        
        None
        // self.backup_brancher.next_decision(context)
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
        // Subscribe to relevant events.
        vec![]
    }
}

#[cfg(test)]
mod tests {
    use super::VariableActivitySearch;
    use crate::branching::Brancher;
    use crate::branching::SelectionContext;
    use crate::engine::Assignments;

    #[test]
    fn test_custom_search() {
        
    }
}