use crate::DefaultBrancher;
use crate::basic_types::SolutionReference;
use crate::branching::Brancher;
use crate::branching::BrancherEvent;
use crate::branching::branchers::autonomous_search::AutonomousSearchStatistics;
use crate::branching::SelectionContext;
use crate::branching::value_selection::InDomainMiddle;
use crate::branching::value_selection::InDomainSplit;
use crate::branching::value_selection::ValueSelector;
use crate::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use crate::branching::value_selection::InDomainMin;
use crate::branching::variable_selection::InputOrder;
use crate::containers::KeyValueHeap;
use crate::containers::StorageKey;
use crate::engine::Assignments;
use crate::predicates::Predicate;
use crate::statistics::moving_averages::MovingAverage;
use crate::statistics::{Statistic, StatisticLogger};
use crate::variables::DomainId;

/// A custom [`Brancher`] implementation.
///
/// This is a placeholder for a user-defined branching strategy.
#[derive(Debug)]
pub struct VariableActivitySearch<BackupBrancher> {
    /// Stores the activities for a variable, represented with its id.
    heap: KeyValueHeap<DomainId, f64>,
    /// Assigned variables removed from the heap and restored after synchronisation.
    dormant_variables: Vec<DomainId>,
    // Backup brancher for when we can not make a decision
    backup_brancher: BackupBrancher,
    /// Selects the branch value once the variable has been chosen.
    value_selector: InDomainSplit,
    /// How much the activity of a variable is increased when it appears in a conflict.
    /// This value changes during search.
    increment: f64,
    /// The maximum allowed activity value, if this value is reached then all of the values are
    /// divided by this value. The increment is constant.
    max_threshold: f64,
    /// Whenever a conflict is found, the [`Vsids::increment`] is multiplied by
    /// 1 / [`Vsids::decay_factor`] (this is synonymous with increasing the
    /// [`Vsids::increment`] since 0 <= [`Vsids::decay_factor`] <= 1).
    /// The decay factor is constant.
    decay_factor: f64,
    /// Tracks whether dormant variables should be restored before selecting next decision.
    should_synchronise: bool,
    statistics: AutonomousSearchStatistics,
}

const DEFAULT_INCREMENT: f64 = 1.0;
const DEFAULT_MAX_THRESHOLD: f64 = 1e100;
const DEFAULT_DECAY_FACTOR: f64 = 0.95;
const DEFAULT_ACT_VALUE: f64 = 0.0;

impl DefaultBrancher {
    /// Creates a new instance with default values for
    /// the parameters (`1.0` for the increment, `1e100` for the max threshold,
    /// `0.95` for the decay factor and `0.0` for the initial VSIDS value).
    ///
    /// If there are no more predicates left to select, this [`Brancher`] switches to
    /// [`InputOrder`] with [`InDomainMin`].
    pub fn default_over_all_variables(assignments: &Assignments) -> DefaultBrancher {
        VariableActivitySearch {
            backup_brancher: IndependentVariableValueBrancher::new(
                InputOrder::new(&assignments.get_domains().collect::<Vec<_>>()),
                InDomainMin,
            ),
            dormant_variables: vec![],
            value_selector: InDomainSplit,
            increment: DEFAULT_INCREMENT,
            decay_factor: DEFAULT_DECAY_FACTOR,
            max_threshold: DEFAULT_MAX_THRESHOLD,
            should_synchronise: false,
            heap: KeyValueHeap::default(),
            statistics: AutonomousSearchStatistics::default()
        }
    }

    pub fn add_domain(&mut self, domain: DomainId) {
        self.backup_brancher.variable_selector.add_domain(domain);
    }
}

impl<BackupBrancher> VariableActivitySearch<BackupBrancher> {
    pub fn new(backup_brancher: BackupBrancher) -> Self {
        VariableActivitySearch {
            backup_brancher,
            dormant_variables: vec![],
            value_selector: InDomainSplit,
            increment: DEFAULT_INCREMENT,
            decay_factor: DEFAULT_DECAY_FACTOR,
            max_threshold: DEFAULT_MAX_THRESHOLD,
            should_synchronise: false,
            heap: KeyValueHeap::default(),
            statistics: AutonomousSearchStatistics::default()
        }
    }

    fn ensure_heap_entry(&mut self, variable: DomainId) {
        while self.heap.len() <= variable.index() {
            let next_id = DomainId::create_from_index(self.heap.len());
            self.heap.grow(next_id, DEFAULT_ACT_VALUE);
        }
    }

    fn bump_activity(&mut self, variable: DomainId) {
        self.statistics.num_predicates_added += 1;
        self.ensure_heap_entry(variable);
        self.heap.restore_key(variable);

        let activity = self.heap.get_value(variable);
        if activity + self.increment >= self.max_threshold {
            self.heap.divide_values(self.max_threshold);
            self.increment /= self.max_threshold;
        }

        self.heap.increment(variable, self.increment);
    }

    fn restore_dormant_variables(&mut self) {
        let dormant = self.dormant_variables.drain(..).collect::<Vec<_>>();
        dormant.into_iter().for_each(|variable| {
            self.ensure_heap_entry(variable);
            self.heap.restore_key(variable);
        });
    }

    fn next_candidate_variable(&mut self, context: &mut SelectionContext) -> Option<DomainId> {
        loop {
            let variable = match self.heap.peek_max() {
                Some((variable, _)) => *variable,
                None => return None,
            };

            if context.is_integer_fixed(variable) {
                self.statistics.num_assigned_predicates_encountered += 1;
                let _ = self.heap.pop_max();
                self.heap.delete_key(variable);
                self.dormant_variables.push(variable);
                continue;
            }

            return Some(variable);
        }
    }

    /// Decays the activities (i.e. increases the [`Vsids::increment`] by multiplying it
    /// with 1 / [`Vsids::decay_factor`]) such that future bumps (see
    /// [`Vsids::bump_activity`]) is more impactful.
    ///
    /// Doing it in this manner is cheaper than dividing each activity value eagerly.
    fn decay_activities(&mut self) {
        self.increment *= 1.0 / self.decay_factor;
    }
}

impl<BackupBrancher: Brancher> Brancher for VariableActivitySearch<BackupBrancher> {
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        self.statistics.num_calls += 1;
        self.statistics.average_size_of_heap.add_term(self.heap.num_nonremoved_elements());

        if self.should_synchronise {
            self.restore_dormant_variables();
            self.should_synchronise = false;
        }

        if let Some(variable) = self.next_candidate_variable(context) {
            return Some(self.value_selector.select_value(context, variable));
        }

        if context.are_all_variables_assigned() {
            None
        } else {
            self.statistics.num_backup_called;
            self.backup_brancher.next_decision(context)
        }
    }

    fn log_statistics(&self, statistic_logger: StatisticLogger) {
        self.statistics.log(statistic_logger)
    }

    fn on_backtrack(&mut self) {
        self.backup_brancher.on_backtrack();
    }

    fn synchronise(&mut self, context: &mut SelectionContext) {
        self.should_synchronise = true;
        self.backup_brancher.synchronise(context);
    }

    fn on_conflict(&mut self) {
        self.decay_activities();
        self.backup_brancher.on_conflict();
    }

    fn on_solution(&mut self, solution: SolutionReference) {
        self.backup_brancher.on_solution(solution);
    }

    fn on_appearance_in_conflict_predicate(&mut self, predicate: Predicate) {
        self.bump_activity(predicate.get_domain());
        self.backup_brancher
            .on_appearance_in_conflict_predicate(predicate);
    }
    
    fn on_restart(&mut self) {
        self.backup_brancher.on_restart();
    }

    fn on_unassign_integer(&mut self, variable: DomainId, value: i32) {
        self.backup_brancher.on_unassign_integer(variable, value)
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
        ]
        .into_iter()
        .chain(self.backup_brancher.subscribe_to_events())
        .collect()
    }
}
