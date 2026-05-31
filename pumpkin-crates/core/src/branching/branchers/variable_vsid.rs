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
/// A [`Brancher`] that combines [VSIDS \[1\]](https://dl.acm.org/doi/pdf/10.1145/378239.379017)
/// and [Solution-based phase saving \[2\]](https://people.eng.unimelb.edu.au/pstuckey/papers/lns-restarts.pdf).
///
/// There are three components:
/// 1. Predicate selection
/// 2. Truth value assignment
/// 3. Backup Selection
///
/// # Predicate selection
/// The VSIDS algorithm is an adaptation for the CP case. It determines which
/// [`Predicate`] should be branched on based on how often it appears in conflicts.
///
/// Intuitively, the more often a [`Predicate`] appears in *recent* conflicts, the more "important"
/// it is during the search process. VSIDS is originally from the SAT field (see \[1\]) but we
/// adapted it for constraint programming by considering [`Predicate`]s from recent conflicts
/// directly rather than Boolean variables.
///
/// # Truth value assignment
/// The truth value for the [`Predicate`] is selected to be consistent with the
/// best solution known so far. In this way, the search is directed around this existing solution.
///
/// In case where there is no known solution, then the predicate is assigned to true. This resembles
/// a fail-first strategy with the idea that the given predicate was encountered in conflicts, so
/// assigning it to true may cause another conflict soon.
///
/// # Backup selection
/// VSIDS relies on [`Predicate`]s appearing in conflicts to discover which [`Predicate`]s are
/// "important". However, it could be the case that all [`Predicate`]s which VSIDS has discovered
/// are already assigned.
///
/// In this case, [`VariableVsidBrancher`] defaults either to the backup described in
/// [`DefaultBrancher`] (when created using [`VariableVsidBrancher::default_over_all_variables`]) or it
/// defaults to the [`Brancher`] provided to [`VariableVsidBrancher::new`].
///
/// # Bibliography
/// \[1\] M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, and S. Malik, ‘Chaff: Engineering an
/// efficient SAT solver’, in Proceedings of the 38th annual Design Automation Conference, 2001.
///
/// \[2\] E. Demirović, G. Chu, and P. J. Stuckey, ‘Solution-based phase saving for CP: A
/// value-selection heuristic to simulate local search behavior in complete solvers’, in the
/// proceedings of the Principles and Practice of Constraint Programming (CP 2018).
#[derive(Debug)]
pub struct VariableVsidBrancher<BackupBrancher> {
    /// Predicates are mapped to ids. This is used internally in the heap.
    predicate_id_info: DeletablePredicateIdGenerator,
    /// Stores the activities for variable
    variable_heap: KeyValueHeap<DomainId, f64>,
    /// After popping variables off the heap that are assigned, the variables are
    /// labelled as dormant because they do not contribute to VSIDS at the moment. When
    /// backtracking, dormant variables are examined and readded to the heap.
    dormant_variables: Vec<DomainId>,
    /// Stores the activities for predicates for a variable
    predicate_heap: HashMap<DomainId, KeyValueHeap<PredicateId, f64>>,
    /// How much the activity of a predicate/variable is increased when it appears in a conflict.
    /// This value changes during search (see [`Vsids::decay_activities`]).
    increment: f64,
    /// The maximum allowed [`Vsids`] value, if this value is reached then all of the values are
    /// divided by this value. The increment is constant.
    max_threshold: f64,
    /// Whenever a conflict is found, the [`Vsids::increment`] is multiplied by
    /// 1 / [`Vsids::decay_factor`] (this is synonymous with increasing the
    /// [`Vsids::increment`] since 0 <= [`Vsids::decay_factor`] <= 1).
    /// The decay factor is constant.
    decay_factor: f64,
    /// Contains the best-known solution or [`None`] if no solution has been found.
    best_known_solution: Option<Solution>,
    /// If the heap does not contain any more unfixed predicates then this backup_brancher will be
    /// used instead.
    backup_brancher: BackupBrancher,
    /// The statistics gathered by the autonomous search
    statistics: VariableVsidBrancherStatistics,
    /// Whether synchronisation should take place in the next call to
    /// [`VariableVsidBrancher::next_decision`].
    ///
    /// This is used to prevent unnecessary work when [`VariableVsidBrancher::synchronise`] is called
    /// multiple times in a row without a call to [`VariableVsidBrancher::next_decision`].
    should_synchronise: bool,
}

create_statistics_struct!(VariableVsidBrancherStatistics {
    num_backup_called: usize,
    num_predicates_removed: usize,
    num_calls: usize,
    num_predicates_added: usize,
    average_size_of_heap: CumulativeMovingAverage<usize>,
    num_assigned_predicates_encountered: usize,
});

const DEFAULT_VSIDS_INCREMENT: f64 = 1.0;
const DEFAULT_VSIDS_MAX_THRESHOLD: f64 = 1e100;
const DEFAULT_VSIDS_DECAY_FACTOR: f64 = 0.95;
const DEFAULT_VSIDS_VALUE: f64 = 0.0;

impl DefaultBrancher {
    /// Creates a new instance with default values for
    /// the parameters (`1.0` for the increment, `1e100` for the max threshold,
    /// `0.95` for the decay factor and `0.0` for the initial VSIDS value).
    ///
    /// If there are no more predicates left to select, this [`Brancher`] switches to
    /// [`InputOrder`] with [`InDomainMin`].
    pub fn default_over_all_variables(assignments: &Assignments) -> DefaultBrancher {
        VariableVsidBrancher {
            predicate_id_info: DeletablePredicateIdGenerator::default(),
            variable_heap: KeyValueHeap::default(),
            predicate_heap: HashMap::default(),
            dormant_variables: vec![],
            increment: DEFAULT_VSIDS_INCREMENT,
            max_threshold: DEFAULT_VSIDS_MAX_THRESHOLD,
            decay_factor: DEFAULT_VSIDS_DECAY_FACTOR,
            best_known_solution: None,
            should_synchronise: false,
            backup_brancher: IndependentVariableValueBrancher::new(
                InputOrder::new(&assignments.get_domains().collect::<Vec<_>>()),
                InDomainMin,
            ),
            statistics: Default::default(),
        }
    }

    pub fn add_domain(&mut self, domain: DomainId) {
        self.backup_brancher.variable_selector.add_domain(domain);
    }
}

impl<BackupBrancher> VariableVsidBrancher<BackupBrancher> {
    fn resize_variable_heap(&mut self, variable_id: DomainId) {
        while self.variable_heap.len() <= variable_id.index() {
            let next_id = DomainId::create_from_index(self.variable_heap.len());
            self.variable_heap.grow(next_id, DEFAULT_VSIDS_VALUE);
        }
    }

    fn resize_heap(&mut self, variable_id: DomainId, id: PredicateId) {
        let heap = self
            .predicate_heap
            .entry(variable_id)
            .or_insert_with(KeyValueHeap::default);

        while heap.len() <= id.index() {
            let next_id = PredicateId::create_from_index(heap.len());
            heap.grow(next_id, DEFAULT_VSIDS_VALUE);
        }
    }

    fn rescale_activities(&mut self) {
        self.variable_heap.divide_values(self.max_threshold);
        self.predicate_heap
            .values_mut()
            .for_each(|heap| heap.divide_values(self.max_threshold));
        self.increment /= self.max_threshold;
    }

    /// Bumps the activity of a variable and its predicate by [`Vsids::increment`].
    /// Used when a predicate is encountered during a conflict.
    fn bump_activity(&mut self, predicate: Predicate) {
        let variable_id = predicate.get_domain();
        self.statistics.num_predicates_added +=
            (!self.predicate_id_info.has_id_for_predicate(predicate)) as usize;
        let id = self.predicate_id_info.get_id(predicate);
        self.resize_variable_heap(variable_id);
        self.resize_heap(variable_id, id);

        self.variable_heap.restore_key(variable_id);

        let variable_activity = self.variable_heap.get_value(variable_id);
        let predicate_activity = self
            .predicate_heap
            .get(&variable_id)
            .expect("Expected predicate heap for domain to exist")
            .get_value(id);

        // Scale the activities if the values are too large.
        // Also remove predicates that have activities close to zero.
        if variable_activity + self.increment >= self.max_threshold
            || predicate_activity + self.increment >= self.max_threshold
        {
            self.rescale_activities();
        }

        // Now perform the standard bumping
        self.variable_heap.increment(variable_id, self.increment);
        self.predicate_heap
            .get_mut(&variable_id)
            .expect("Expected predicate heap for domain to exist")
            .restore_key(id);
        self.predicate_heap
            .get_mut(&variable_id)
            .expect("Expected predicate heap for domain to exist")
            .increment(id, self.increment);
    }

    /// Decays the activities (i.e. increases the [`Vsids::increment`] by multiplying it
    /// with 1 / [`Vsids::decay_factor`]) such that future bumps (see
    /// [`Vsids::bump_activity`]) is more impactful.
    ///
    /// Doing it in this manner is cheaper than dividing each activity value eagerly.
    fn decay_activities(&mut self) {
        self.increment *= 1.0 / self.decay_factor;
    }

    fn next_candidate_predicate(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        loop {
            let variable_id = match self.variable_heap.peek_max() {
                Some((candidate, _)) => *candidate,
                None => return None,
            };

            if context.is_integer_fixed(variable_id) {
                let _ = self.variable_heap.pop_max();
                self.variable_heap.delete_key(variable_id);
                self.dormant_variables.push(variable_id);
                continue;
            }

            loop {
                let predicate_id = match self
                    .predicate_heap
                    .get(&variable_id)
                    .and_then(|heap| heap.peek_max().map(|(candidate, _)| *candidate))
                {
                    Some(predicate_id) => predicate_id,
                    None => {
                        let _ = self.variable_heap.pop_max();
                        self.variable_heap.delete_key(variable_id);
                        self.dormant_variables.push(variable_id);
                        break;
                    }
                };

                let predicate = self
                    .predicate_id_info
                    .get_predicate(predicate_id);

                let Some(predicate) = predicate else {
                    if let Some(heap) = self.predicate_heap.get_mut(&variable_id) {
                        let _ = heap.pop_max();
                    }
                    continue;
                };

                if predicate.get_domain() != variable_id {
                    if let Some(heap) = self.predicate_heap.get_mut(&variable_id) {
                        let _ = heap.pop_max();
                    }
                    continue;
                }

                if context.is_predicate_assigned(predicate) {
                    self.statistics.num_assigned_predicates_encountered += 1;
                    if let Some(heap) = self.predicate_heap.get_mut(&variable_id) {
                        let _ = heap.pop_max();
                    }
                    continue;
                }

                return Some(predicate);
            }
        }
    }

    /// Determines whether the provided [`Predicate`] should be returned as is or whether its
    /// negation should be returned. This is determined based on its assignment in the best-known
    /// solution.
    ///
    /// For example, if we have found the solution `x = 5` then the call `determine_polarity([x >=
    /// 3])` would return `true`.
    fn determine_polarity(&self, predicate: Predicate) -> Predicate {
        if let Some(solution) = &self.best_known_solution {
            // We have a solution
            if !solution.contains_domain_id(predicate.get_domain()) {
                // This can occur if an encoding is used
                return predicate;
            }
            // Match the truth value according to the best solution.
            if solution.evaluate_predicate(predicate) == Some(true) {
                predicate
            } else {
                !predicate
            }
        } else {
            // We do not have a solution to match against, we simply return the predicate with
            // positive polarity
            predicate
        }
    }
    
    fn synchronise_internal(&mut self) {
        // We drain the dormant variables and add them back to the variable heap. For each such
        // variable, we also restore all predicate entries already known in that variable's local
        // predicate heap.
        let dormant_variables = self.dormant_variables.drain(..).collect::<Vec<_>>();

        dormant_variables.into_iter().for_each(|variable_id| {
            self.resize_variable_heap(variable_id);
            self.variable_heap.restore_key(variable_id);

            if let Some(heap) = self.predicate_heap.get_mut(&variable_id) {
                for index in 0..heap.len() {
                    heap.restore_key(PredicateId::create_from_index(index));
                }
            }
        });
    }
}

impl<BackupBrancher: Brancher> Brancher for VariableVsidBrancher<BackupBrancher>{
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        if self.should_synchronise {
            self.synchronise_internal();
            self.should_synchronise = false;
        }
        self.statistics.num_calls += 1;
        self.statistics
            .average_size_of_heap
            .add_term(self.variable_heap.num_nonremoved_elements());
        let result = self
            .next_candidate_predicate(context)
            .map(|predicate| self.determine_polarity(predicate));
        if result.is_none() && !context.are_all_variables_assigned() {
            // There are variables for which we do not have a predicate, rely on the backup
            self.statistics.num_backup_called += 1;
            self.backup_brancher.next_decision(context)
        } else {
            result
        }
    }

    fn log_statistics(&self, statistic_logger: StatisticLogger) {
        let statistic_logger = statistic_logger.attach_to_prefix("AutonomousSearch");
        self.statistics.log(statistic_logger);
    }

    fn on_backtrack(&mut self) {
        self.backup_brancher.on_backtrack()
    }

    /// Restores dormant varaiables after backtracking.
    fn synchronise(&mut self, context: &mut SelectionContext) {
        self.should_synchronise = true;
        self.backup_brancher.synchronise(context);
    }

    fn on_conflict(&mut self) {
        self.decay_activities();
        self.backup_brancher.on_conflict();
    }

    fn on_solution(&mut self, solution: SolutionReference) {
        // We store the best known solution
        self.best_known_solution = Some(solution.into());
        self.backup_brancher.on_solution(solution);
    }

    fn on_appearance_in_conflict_predicate(&mut self, predicate: Predicate) {
        self.bump_activity(predicate);
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

#[cfg(test)]
mod tests {
    use super::VariableVsidBrancher;
    use crate::basic_types::tests::TestRandom;
    use crate::branching::{Brancher, SelectionContext};
    use crate::engine::Assignments;
    use crate::engine::notifications::NotificationEngine;
    use crate::predicate;
    use crate::results::SolutionReference;

    #[test]
    fn brancher_picks_most_active_predicate_for_variable() {
        let mut assignments = Assignments::default();
        let x = assignments.grow(0, 10);
        let y = assignments.grow(0, 10);

        let mut brancher = VariableVsidBrancher::default_over_all_variables(&assignments);
        brancher.on_appearance_in_conflict_predicate(predicate!( y >= 5));
        brancher.on_appearance_in_conflict_predicate(predicate!( y >= 5));
        brancher.on_appearance_in_conflict_predicate(predicate!( y >= 5));
        brancher.on_appearance_in_conflict_predicate(predicate!(x >= 5));
        brancher.on_appearance_in_conflict_predicate(predicate!(x >= 4));
        brancher.on_appearance_in_conflict_predicate(predicate!(x >= 7));
        brancher.on_appearance_in_conflict_predicate(predicate!(x >= 7));

        let result = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));

        assert_eq!(result, Some(predicate!(x >= 7)));
    }

    #[test]
    fn dormant_variables_are_restored_after_synchronise() {
        let mut notification_engine = NotificationEngine::default();
        let mut assignments = Assignments::default();
        let x = assignments.grow(0, 10);
        notification_engine.grow();

        let mut brancher = VariableVsidBrancher::default_over_all_variables(&assignments);

        let predicate = predicate!(x >= 5);
        brancher.on_appearance_in_conflict_predicate(predicate);
        let decision = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));
        assert_eq!(decision, Some(predicate));

        assignments.new_checkpoint();
        let _ = assignments.post_predicate(predicate!(x >= 5), None, &mut notification_engine);

        assignments.new_checkpoint();
        let _ = assignments.post_predicate(predicate!(x >= 7), None, &mut notification_engine);

        assignments.new_checkpoint();
        let _ = assignments.post_predicate(predicate!(x >= 10), None, &mut notification_engine);

        assignments.new_checkpoint();

        let decision = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));
        assert!(decision.is_none());
        assert!(brancher.dormant_variables.contains(&x));

        let _ = assignments.synchronise(3, &mut notification_engine);

        let decision = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));
        assert!(decision.is_none());
        assert!(brancher.dormant_variables.contains(&x));

        let _ = assignments.synchronise(0, &mut notification_engine);
        brancher.synchronise(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));

        let decision = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));
        assert_eq!(decision, Some(predicate));
        assert!(!brancher.dormant_variables.contains(&x));
    }

    #[test]
    fn uses_stored_solution() {
        let mut notification_engine = NotificationEngine::default();
        let mut assignments = Assignments::default();
        let x = assignments.grow(0, 10);
        notification_engine.grow();

        assignments.new_checkpoint();
        let _ = assignments.post_predicate(predicate!(x == 7), None, &mut notification_engine);

        let mut brancher = VariableVsidBrancher::default_over_all_variables(&assignments);

        brancher.on_solution(SolutionReference::new(&assignments));

        let _ = assignments.synchronise(0, &mut notification_engine);

        assert_eq!(
            predicate!(x >= 5),
            brancher.determine_polarity(predicate!(x >= 5))
        );
        assert_eq!(
            !predicate!(x >= 10),
            brancher.determine_polarity(predicate!(x >= 10))
        );
        assert_eq!(
            predicate!(x <= 8),
            brancher.determine_polarity(predicate!(x <= 8))
        );
        assert_eq!(
            !predicate!(x <= 5),
            brancher.determine_polarity(predicate!(x <= 5))
        );

        brancher.on_appearance_in_conflict_predicate(predicate!(x >= 5));

        let result = brancher.next_decision(&mut SelectionContext::new(
            &assignments,
            &mut TestRandom::default(),
        ));
        assert_eq!(result, Some(predicate!(x >= 5)));
    }

}
