use num::integer::{div_floor, mod_floor};
use crate::basic_types::SolutionReference;
use crate::branching::Brancher;
use crate::branching::BrancherEvent;
use crate::branching::SelectionContext;
use crate::conflict_resolving::LearnedNogood;
use crate::containers::KeyValueHeap;
use crate::containers::StorageKey;
use crate::create_statistics_struct;
use crate::engine::predicates::predicate::Predicate;
use crate::predicates::PredicateType;
use crate::propagation::ReadDomains;
use crate::results::Solution;
use crate::statistics::Statistic;
use crate::statistics::StatisticLogger;
use crate::statistics::moving_averages::CumulativeMovingAverage;
use crate::statistics::moving_averages::MovingAverage;
use crate::variables::DomainId;

#[derive(Debug, Clone, Copy)]
struct DomainValueId  {
    id: DomainId,
    value: i32,
}

impl StorageKey for DomainValueId {
    fn index(&self) -> usize {
        if self.value >= 0{
            (self.id.index() * 1000 + self.value as usize)
        } else {
            ((self.id.index() + 1 ) as i32 * 1000 + self.value) as usize
        }
    }

    fn create_from_index(index: usize) -> Self {
        let pos_id = div_floor(index,1000);
        let dom_id: DomainId;
        let mut value:i32 = mod_floor(index as i32, 1000);
        if value > 500 {
            dom_id = DomainId::create_from_index(pos_id-1);
            value = value - 1000
        } else {
            dom_id = DomainId::create_from_index(pos_id)
        }
        DomainValueId {
            id: dom_id,
            value: value,
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
    dormant_predicates: Vec<(DomainId, PredicateType)>
}

create_statistics_struct!(CustomSearchStatistics {
    num_backup_called: usize,
    num_predicates_removed: usize,
    num_calls: usize,
    num_vars_added: usize,
    average_value_per_variable: CumulativeMovingAverage<usize>,
    average_size_of_heap: CumulativeMovingAverage<usize>,
    num_assigned_predicates_encountered: usize,
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
            dormant_predicates: vec![],
        }
    }

    /// Resizes the heap to accommodate for the id.
    /// Recall that the underlying heap uses direct hashing.
    fn resize_heap(&mut self, id: DomainValueId, p_type: PredicateType) {
        match p_type {
            PredicateType::Equal => {
                while self.heap_eq.len() <= id.index() {
                    self.heap_eq.grow(id, DEFAULT_VALUE);
                }
            },
            PredicateType::NotEqual => {
                while self.heap_ne.len() <= id.index() {
                    self.heap_eq.grow(id, DEFAULT_VALUE);
                }
            },
            PredicateType::UpperBound => {
                while self.heap_lt.len() <= id.index() {
                    self.heap_lt.grow(id, DEFAULT_VALUE);
                }
            },
            PredicateType::LowerBound => {
                while self.heap_gt.len() <= id.index() {
                    self.heap_eq.grow(id, DEFAULT_VALUE);
                }
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

    /// Bumps the activity of a predicate by [`Vsids::increment`].
    /// Used when a predicate is encountered during a conflict.
    fn bump_activity(&mut self, predicate: Predicate) {
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
            },
            PredicateType::UpperBound => {
                let activity = self.heap_lt.get_value(dv_id);
                if activity + self.increment > self.max_threshold {
                    self.divide_heaps();
                }
                self.heap_lt.increment(dv_id, self.increment);
            },
            PredicateType::LowerBound => {
                let activity = self.heap_gt.get_value(dv_id);
                if activity + self.increment > self.max_threshold {
                    self.divide_heaps();
                }
                self.heap_gt.increment(dv_id, self.increment);
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

    // fn next_candidate_predicate(&mut self, context: &mut SelectionContext) -> Option<Predicate> {
    //     loop {
    //         // We peek the next variable, since we do not pop since we do not (yet) want to
    //         // remove the value from the heap.
    //         if let Some((candidate, _)) = self.heap.peek_max() {
    //             let predicate = self
    //                 .predicate_id_info
    //                 .get_predicate(*candidate)
    //                 .expect("Expected predicate id to exist");
    //             if context.is_predicate_assigned(predicate) {
    //                 self.statistics.num_assigned_predicates_encountered += 1;
    //                 let _ = self.heap.pop_max();
    //
    //                 // We know that this predicate is now dormant
    //                 let predicate_id = self.predicate_id_info.get_id(predicate);
    //                 self.heap.delete_key(predicate_id);
    //                 self.predicate_id_info.delete_id(predicate_id);
    //                 self.dormant_predicates.push(predicate);
    //             } else {
    //                 return Some(predicate);
    //             }
    //         } else {
    //             return None;
    //         }
    //     }
    // }

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

    // fn synchronise_internal(&mut self) {
    //     // We drain the dormant predicates and add them back to the heap; we could check here
    //     // whether the predicates are already satisfied but this appeared to introduce too much
    //     // overhead in some cases.
    //     self.dormant_predicates.drain(..).for_each(|predicate| {
    //         let id = self.predicate_id_info.get_id(predicate);
    //
    //         while self.heap.len() <= id.index() {
    //             self.heap.grow(id, DEFAULT_VALUE);
    //         }
    //
    //         self.heap.restore_key(id);
    //     });
    // }


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

    fn synchronise(&mut self, _context: &mut SelectionContext) {
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
        let _variable = predicate.get_domain();

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

    #[test]
    fn test_custom_search() {
        
    }
}