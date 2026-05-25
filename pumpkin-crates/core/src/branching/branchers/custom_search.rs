use itertools::Itertools;
use num::abs;
use num::integer::div_floor;
use pumpkin_checking::CheckerVariable;
use crate::basic_types::SolutionReference;
use crate::branching::Brancher;
use crate::branching::BrancherEvent;
use crate::branching::SelectionContext;
use crate::conflict_resolving::LearnedNogood;
use crate::containers::{HashMap, KeyValueHeap};
use crate::containers::StorageKey;
use crate::create_statistics_struct;
use crate::engine::predicates::predicate::Predicate;
use crate::predicates::PredicateType;
use crate::propagation::ReadDomains;
use crate::results::Solution;
use crate::state::State;
use crate::statistics::Statistic;
use crate::statistics::StatisticLogger;
use crate::statistics::moving_averages::CumulativeMovingAverage;
use crate::statistics::moving_averages::MovingAverage;
use crate::variables::DomainId;

const DOMAIN_SIZE: usize = 1000;

#[derive(Debug, Clone, Copy)]
struct DomainValueId  {
    id: DomainId,
    value: i32,
}

impl StorageKey for DomainValueId {
    fn index(&self) -> usize {
        // DomainId = D
        // DDDDDDDxx
        let dom_loc = self.id.index() * DOMAIN_SIZE;
        if self.value <= 0 {
            dom_loc + 2 * abs(self.value) as usize
        } else {
            dom_loc + (2 * self.value as usize) - 1
        }
    }

    fn create_from_index(index: usize) -> Self {
        let dom_id = DomainId::create_from_index(div_floor(index, DOMAIN_SIZE));
        let remainder = index % DOMAIN_SIZE;

        // Consider the mapping 0, 1, -1, 2, -2 -> 0, 1, 2, 3, 4, 5
        // where:
        // i > 0:     i => 2i-1,
        // i <= 0:    i => 2|i|
        if remainder == 0 {
            DomainValueId { id: dom_id, value: 0 }
        } else if remainder == 1 {
            DomainValueId { id: dom_id, value: 1 }
        } else if remainder % 2 == 1 {
            let i = (remainder / 2).saturating_sub(1);
            DomainValueId { id: dom_id, value: i as i32 }
        } else {
            let i: i32 = (remainder / 2) as i32;
            return DomainValueId { id: dom_id, value: -i }
        }
    }
}

/// A custom [`Brancher`] implementation.
///
/// This is a placeholder for a user-defined branching strategy.
#[derive(Debug)]
pub struct CustomSearch<BackupBrancher> {
    // Backup brancher for when we can not make a decision
    backup_brancher: BackupBrancher,
    // Heaps
    heap_eq: KeyValueHeap<DomainValueId, f64>,
    heap_lt: KeyValueHeap<DomainValueId, f64>,
    heap_gt: KeyValueHeap<DomainValueId, f64>,
    heap_ne: KeyValueHeap<DomainValueId, f64>,
    // How much the activity of a value is increased
    increment: f64,
    statistics: CustomSearchStatistics,
    pub max_threshold: f64,
    pub decay_factor: f64,
    pub best_known_solution: Option<Solution>,
    dormant_predicates: HashMap<(DomainId, PredicateType), i32>
}

create_statistics_struct!(CustomSearchStatistics {
    num_predicates_removed: usize,
    num_backup_called: usize,
    num_calls: usize,
    num_vars_added: usize,
    average_value_per_variable: CumulativeMovingAverage<usize>,
    average_size_of_heap: CumulativeMovingAverage<usize>,
    num_assigned_predicates_encountered: usize,num_equality_decisions: usize,
    num_not_equal_decisions: usize,
    num_less_than_decisions: usize,
    num_greater_than_decisions: usize,
});

const DEFAULT_INCREMENT: f64 = 1.0;
const DEFAULT_VALUE: f64 = 0.0;
const DEFAULT_GAMMA: f64 = 0.9;
const DEFAULT_MAX_THRESHOLD: f64 = 1e100;

impl<BackupSelector> CustomSearch<BackupSelector> {
    /// Creates a new instance with default values for
    /// the parameters (`1.0` for the increment, `1e100` for the max threshold,
    /// `0.95` for the decay factor and `0.0` for the initial VSIDS value).
    ///
    /// Uses the `backup_brancher` in case there are no more predicates to be selected by the counter.
    pub fn new(backup_brancher: BackupSelector) -> Self {
        CustomSearch {
            heap_lt: KeyValueHeap::default(),
            heap_gt: KeyValueHeap::default(),
            heap_eq: KeyValueHeap::default(),
            heap_ne: KeyValueHeap::default(),
            increment: DEFAULT_INCREMENT,
            max_threshold: DEFAULT_MAX_THRESHOLD,
            decay_factor: DEFAULT_GAMMA,
            best_known_solution: None,
            backup_brancher,
            statistics: Default::default(),
            dormant_predicates: Default::default(),
        }
    }

    /// Resizes the heap to accommodate for the id.
    /// Recall that the underlying heap uses direct hashing.
    fn resize_heap(&mut self, id: DomainValueId, p_type: PredicateType) {
        match p_type {
            PredicateType::Equal => {
                // while self.heap_eq.len() <= id.index() {
                //     self.heap_eq.grow(id, DEFAULT_VALUE);
                // }
                while self.heap_eq.len() <= id.index() {
                    let next_key = DomainValueId::create_from_index(self.heap_eq.len());
                    self.heap_eq.grow(next_key, 0.0);
                }
                self.heap_eq.restore_key(id);

            },
            PredicateType::NotEqual => {
                while self.heap_ne.len() <= id.index() {
                    let next_key = DomainValueId::create_from_index(self.heap_ne.len());
                    self.heap_ne.grow(next_key, 0.0);
                }
                self.heap_ne.restore_key(id);
            },
            PredicateType::UpperBound => {
                while self.heap_lt.len() <= id.index() {
                    let next_key = DomainValueId::create_from_index(self.heap_lt.len());
                    self.heap_lt.grow(next_key, 0.0);
                }
                self.heap_lt.restore_key(id);
            },
            PredicateType::LowerBound => {
                while self.heap_gt.len() <= id.index() {
                    let next_key = DomainValueId::create_from_index(self.heap_gt.len());
                    self.heap_gt.grow(next_key, 0.0);
                }
                self.heap_gt.restore_key(id);
            }
        }
    }

    // Makes sure all counters are divided such that they are on equal level
    fn divide_heaps(&mut self) {
        // Adjust heap values.
        self.heap_eq.divide_values(self.max_threshold);
        self.heap_ne.divide_values(self.max_threshold);
        self.heap_lt.divide_values(self.max_threshold);
        self.heap_gt.divide_values(self.max_threshold);

        // Adjust increment. It is important to adjust the increment after the above code.
        self.increment /= self.max_threshold;
    }

    fn domain_values_to_increment(&mut self, id: DomainId, predicate: PredicateType, value:i32, state: &mut State) -> Vec<DomainValueId> {
        let mut dv_idx: Vec<DomainValueId> = vec![];
        match predicate {
            PredicateType::UpperBound => {
                // Less than == upper bound
                // if [x <= v] => also increase [x <= v+i] for i = -1, -2, ...
                // As those also validate this predicate
                let lb = state.lower_bound(id);
                for val in lb..=value {
                    dv_idx.push(DomainValueId { id, value: val });
                }
            },
            PredicateType::LowerBound => {
                // Greater than == lower bound
                // if [x >= v] => also increase [x >= v+i] for i = 1,2,...
                // As those also validate this predicate
                let ub = state.upper_bound(id);
                for val in value..=ub {
                    dv_idx.push(DomainValueId { id, value: val });
                }
            },
            PredicateType::NotEqual => {
                let lb = state.lower_bound(id);
                let ub = state.upper_bound(id);
                for val in lb..=ub {
                    if val != value {
                        dv_idx.push(DomainValueId { id, value: val });
                    }
                }
            }
            _ => ()
        };
        dv_idx
    }

    /// Bumps the activity of a predicate by [`Vsids::increment`].
    /// Used when a predicate is encountered during a conflict.
    fn bump_activity(&mut self, predicate: Predicate, state: &mut State) {
        let id = predicate.get_domain();
        let value = predicate.get_right_hand_side();
        let dv_id = DomainValueId{id, value };
        let pred_type = predicate.get_predicate_type();
        self.resize_heap(dv_id, pred_type);

        match pred_type {
            PredicateType::Equal => {
                let activity = self.heap_eq.get_value(dv_id);
                if activity + self.increment > self.max_threshold {
                    self.divide_heaps();
                }
                self.heap_eq.increment(dv_id, self.increment);
            },
            PredicateType::NotEqual => {
                let activity = self.heap_ne.get_value(dv_id);
                if activity + self.increment > self.max_threshold {
                    self.divide_heaps();
                }
                self.heap_ne.increment(dv_id, self.increment);
                let dv_idx = self.domain_values_to_increment(id,pred_type, value, state);

                for other_dv_id in dv_idx {
                    self.resize_heap(other_dv_id, PredicateType::Equal);
                    let activity = self.heap_eq.get_value(other_dv_id);
                    if activity + self.increment > self.max_threshold {
                        self.divide_heaps();
                    }
                    self.heap_eq.increment(other_dv_id, self.increment);
                }


            },
            PredicateType::UpperBound => {
                // Also bumps the counter for each value in the domain less than v
                let dv_idx = self.domain_values_to_increment(id, pred_type, value, state);

                for (i,other_dv_id) in dv_idx.iter().enumerate() {
                    self.resize_heap(*other_dv_id, PredicateType::UpperBound);
                    self.resize_heap(*other_dv_id, PredicateType::Equal);
                    if i == 0 {
                        // As we know that the counters over this domain will be strictly decreasing
                        // we only have to check if the lowest value counter will be exceeding the
                        // threshold
                        let activity = self.heap_lt.get_value(*other_dv_id).max(*self.heap_eq.get_value(*other_dv_id));
                        if activity + self.increment > self.max_threshold {
                            self.divide_heaps();
                        }
                    }
                    self.heap_eq.increment(*other_dv_id, self.increment);
                    self.heap_lt.increment(*other_dv_id, self.increment);
                }

            },
            PredicateType::LowerBound => {
                // Also bumps the counter for each value in the domain greater than v
                let dv_idx = self.domain_values_to_increment(id, pred_type, value, state);

                for (i,other_dv_id) in dv_idx.iter().rev().enumerate() {
                    self.resize_heap(*other_dv_id, PredicateType::Equal);
                    self.resize_heap(*other_dv_id, PredicateType::LowerBound);
                    if i == 0 {
                        // As we know that the counters over this domain will be strictly increasing
                        // we only have to check if the highest value counter will be exceeding the
                        // threshold
                        let activity = self.heap_gt.get_value(*other_dv_id).max(*self.heap_eq.get_value(*other_dv_id));
                        if activity + self.increment > self.max_threshold {
                            self.divide_heaps();
                        }
                    }
                    self.heap_gt.increment(*other_dv_id, self.increment);
                    // Also increment the equality, as those also set the predicate to true
                    self.heap_eq.increment(*other_dv_id, self.increment);
                }

            }
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

    fn next_candidate_predicate(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        // Loop until we find an allowed predicate
        //
        // todo(The idea is that we store for the domain and predicate, which value it was decided on.)
        // todo(It is undesirable to first branch on [x >= 2] and then on [x >= 1].);
        loop {
            // For each heap we check the highest count, and take the max of those maxes
            let choices = [
                self.heap_lt.peek_max().map(|(id, &v)| (id.clone(), v)),
                self.heap_gt.peek_max().map(|(id, &v)| (id.clone(), v)),
                self.heap_eq.peek_max().map(|(id, &v)| (id.clone(), v)),
                self.heap_ne.peek_max().map(|(id, &v)| (id.clone(), v)),
            ];

            // Necessary as position_max needs f64 to implement Ord, which it doesnt
            let max_index = choices
                .iter()
                .map(|opt| opt.map(|(_, val)| val).unwrap_or(-1.0))
                .enumerate()
                .max_by(|(_, a), (_, b)| a.total_cmp(b))
                .map(|(idx, _)| idx);

            if let Some(idx) = max_index {
                if let Some(candidate) = choices[idx] {
                    let (dv_id, _) = candidate;
                    let domain_id = dv_id.id;
                    let value = dv_id.value;

                    //
                    match idx {
                        0 => {
                            // Less than constraint
                            let predicate = domain_id.atomic_less_than(value);
                            if context.is_predicate_assigned(predicate) {
                                self.statistics.num_assigned_predicates_encountered += 1;
                                self.heap_lt.pop_max();

                                self.heap_lt.delete_key(dv_id);
                                self.dormant_predicates.insert((domain_id, PredicateType::UpperBound), value);
                            } else {
                                return Some(predicate);
                            }
                        },
                        1 => {
                            // Greater than constraint
                            let predicate = domain_id.atomic_greater_than(value);
                            if context.is_predicate_assigned(predicate) {
                                self.statistics.num_assigned_predicates_encountered += 1;
                                self.heap_gt.pop_max();

                                self.heap_gt.delete_key(dv_id);
                                self.dormant_predicates.insert((domain_id, PredicateType::LowerBound), value);
                            } else {
                                return Some(predicate);
                            }

                        },
                        2 => {
                            // Equals constraint
                            // Less than constraint
                            let predicate = domain_id.atomic_equal(value);
                            if context.is_predicate_assigned(predicate) {
                                self.statistics.num_assigned_predicates_encountered += 1;
                                self.heap_eq.pop_max();

                                self.heap_eq.delete_key(dv_id);
                                self.dormant_predicates.insert((domain_id, PredicateType::Equal), value);
                            } else {
                                return Some(predicate);
                            }
                        },
                        3 => {
                            // Not-equals constraint
                            // Less than constraint
                            let predicate = domain_id.atomic_not_equal(value);
                            if context.is_predicate_assigned(predicate) {
                                self.statistics.num_assigned_predicates_encountered += 1;
                                self.heap_ne.pop_max();

                                self.heap_ne.delete_key(dv_id);
                                self.dormant_predicates.insert((domain_id, PredicateType::NotEqual), value);
                            } else {
                                return Some(predicate);
                            }
                        }
                        _ => return None
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }
}



impl<BackupBrancher: Brancher> Brancher for CustomSearch<BackupBrancher> {
    fn next_decision(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
        self.statistics.num_calls += 1;
        let avg = (self.heap_lt.num_nonremoved_elements() + self.heap_gt.num_nonremoved_elements()
            + self.heap_eq.num_nonremoved_elements() + self.heap_ne.num_nonremoved_elements())/4;
        self.statistics
            .average_size_of_heap
            .add_term(avg);

        let result = self
            .next_candidate_predicate(context);
        if result.is_none() && !context.are_all_variables_assigned() {
            // There are variables for which we do not have a predicate, rely on the backup
            self.statistics.num_backup_called += 1;
            self.backup_brancher.next_decision(context)
        } else {
            if let Some(pred) = result {
                self.statistics.num_equality_decisions += pred.is_equality_predicate() as usize;
                self.statistics.num_greater_than_decisions += pred.is_lower_bound_predicate() as usize;
                self.statistics.num_less_than_decisions += pred.is_upper_bound_predicate() as usize;
                self.statistics.num_not_equal_decisions += pred.is_not_equal_predicate() as usize;
            } else {

                self.backup_brancher.next_decision(context);
            }
            result
        }
    }

    fn log_statistics(&self, statistic_logger: StatisticLogger) {
        // Implement logging of statistics if needed.
        let statistic_logger = statistic_logger.attach_to_prefix("CustomBrancher");
        self.statistics.log(statistic_logger);
        // self.backup_brancher.log(statistic_logger);
    }

    fn on_backtrack(&mut self) {
        // Implement behavior on backtracking.
        self.backup_brancher.on_backtrack();
    }

    fn synchronise(&mut self, _context: &mut SelectionContext) {
        // Implement synchronization logic if needed.
        self.backup_brancher.synchronise(_context)
    }

    fn on_conflict(&mut self) {
        // Implement behavior on conflict.
        self.backup_brancher.on_conflict();
    }

    fn on_solution(&mut self, _solution: SolutionReference) {
        // Implement behavior on finding a solution.
        self.backup_brancher.on_solution(_solution);
    }

    fn on_appearance_in_conflict_predicate(&mut self, predicate: Predicate) {
        // Implement behavior when a predicate appears in a conflict.
        self.backup_brancher.on_appearance_in_conflict_predicate(predicate);
        // let _variable = predicate.get_domain();
        //
        // if predicate.is_lower_bound_predicate() {
        //
		// } else if predicate.is_upper_bound_predicate() {
		// } else if predicate.is_not_equal_predicate() {
		// } else if predicate.is_equality_predicate() {
		// }
    }
    
    fn on_restart(&mut self) {
        // Implement behavior on restart.
        self.backup_brancher.on_restart();
    }

    fn on_unassign_integer(&mut self, _variable: DomainId, _value: i32) {
        // Implement behavior on unassigning an integer.
        self.on_unassign_integer(_variable, _value);
    }

    fn is_restart_pointless(&mut self) -> bool {
        // Implement logic to determine if a restart is pointless.
        self.backup_brancher.is_restart_pointless()
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

    fn on_learned_nogood(&mut self, learned_nogood: &LearnedNogood, state: &mut State) {
        eprintln!("Learned nogood with {} predicates:", learned_nogood.predicates.len());
        for (i, predicate) in learned_nogood.predicates.iter().enumerate() {
            eprintln!("  [{}] {:?}", i, predicate);
            self.bump_activity(*predicate, state);
        }
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_custom_search() {
        
    }
}