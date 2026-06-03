use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::time::Duration;

use crate::containers::KeyedVec;
use crate::propagation::Priority;
use crate::propagation::PropagatorId;
use crate::pumpkin_assert_moderate;
use crate::statistics::log_statistic;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "clap", derive(clap::ValueEnum))]
pub enum PropagatorUtilityFormula {
    #[default]
    Default,
    ConflictRate,
    PruningRate,
    Conflicts,
    Prunings,
}

impl PropagatorUtilityFormula {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().replace('_', "-").as_str() {
            "default" => Some(PropagatorUtilityFormula::Default),
            "conflict-rate" | "conflict_rate" => Some(PropagatorUtilityFormula::ConflictRate),
            "pruning-rate" | "pruning_rate" => Some(PropagatorUtilityFormula::PruningRate),
            "conflicts" => Some(PropagatorUtilityFormula::Conflicts),
            "prunings" => Some(PropagatorUtilityFormula::Prunings),
            _ => None,
        }
    }

    pub fn from_env() -> Option<Self> {
        std::env::var("PUMPKIN_UTILITY_FORMULA")
            .ok()
            .and_then(|val| Self::from_str(&val))
    }

    pub fn get_decay() -> f32 {
        std::env::var("PUMPKIN_UTILITY_DECAY")
            .ok()
            .and_then(|val| val.parse().ok())
            .unwrap_or(0.8)
    }

    pub fn get_conflict_weight() -> f32 {
        std::env::var("PUMPKIN_UTILITY_CONFLICT_WEIGHT")
            .ok()
            .and_then(|val| val.parse().ok())
            .unwrap_or(1000.0)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct PropagatorQueue {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    propagator_utility: KeyedVec<PropagatorId, f32>,
    base_priorities: KeyedVec<PropagatorId, Option<Priority>>,
    bin_sums: [f32; 4],
    bin_counts: [usize; 4],
    bin_averages: [f32; 4],
    sorted_bins: [(usize, f32); 4],
    present_priorities: BinaryHeap<Reverse<u32>>,
    pub(crate) num_priority_changes: usize,
    last_priorities: KeyedVec<PropagatorId, Option<Priority>>,
    pub(crate) dynamic_priority_adaptation: bool,
    pub(crate) propagator_utility_formula: PropagatorUtilityFormula,
    pub(crate) propagator_utility_decay: f32,
    pub(crate) propagator_utility_conflict_weight: f32,

    pub(crate) previous_static_priority: KeyedVec<PropagatorId, (f32, Priority)>,
    pub(crate) has_previous_static_priority: bool,
}

pub(crate) struct PropagationOutcome {
    // Time spent in the propagator
    pub(crate) time: Duration,
    pub(crate) found_conflict: bool,
    pub(crate) total_removed_values: u32
}

impl Default for PropagatorQueue {
    fn default() -> Self {
        Self::new(5)
    }
}

impl PropagatorQueue {
    pub(crate) fn new(num_priority_levels: u32) -> PropagatorQueue {
        PropagatorQueue {
            queues: vec![VecDeque::new(); num_priority_levels as usize],
            is_enqueued: KeyedVec::default(),
            num_enqueued: 0,
            propagator_utility: KeyedVec::default(),
            base_priorities: KeyedVec::default(),
            bin_sums: [0.0; 4],
            bin_counts: [0; 4],
            bin_averages: [10.0, 1.0, 0.1, 0.0],
            sorted_bins: [
                (0, 10.0),
                (1, 1.0),
                (2, 0.1),
                (3, 0.0),
            ],
            present_priorities: BinaryHeap::new(),
            num_priority_changes: 0,
            last_priorities: KeyedVec::default(),
            dynamic_priority_adaptation: false,
            propagator_utility_formula: PropagatorUtilityFormula::default(),
            propagator_utility_decay: 0.8,
            propagator_utility_conflict_weight: 1000.0,
            has_previous_static_priority: false,
            previous_static_priority: KeyedVec::default(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    pub(crate) fn enqueue_propagator(&mut self, propagator_id: PropagatorId, priority: Priority) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());

        if self.dynamic_priority_adaptation {
            self.last_priorities.accomodate(propagator_id, None);
            if let Some(last) = self.last_priorities[propagator_id] {
                if last != priority {
                    self.num_priority_changes += 1;
                }
            }
            self.last_priorities[propagator_id] = Some(priority);
        }

        if self.has_previous_static_priority {
            self.is_enqueued.accomodate(propagator_id, false);
            self.is_enqueued[propagator_id] = true;
            self.num_enqueued += 1;

            let (_, static_priority) = self.previous_static_priority[propagator_id];
            if self.queues[static_priority as usize].is_empty() {
                self.present_priorities.push(Reverse(static_priority as u32));
            }
            self.queues[static_priority as usize].push_back(propagator_id);
            return
        }

        if !self.is_propagator_enqueued(propagator_id) {
            self.is_enqueued.accomodate(propagator_id, false);
            self.is_enqueued[propagator_id] = true;
            self.num_enqueued += 1;

            if self.queues[priority as usize].is_empty() {
                self.present_priorities.push(Reverse(priority as u32));
            }
            self.queues[priority as usize].push_back(propagator_id);
        }
    }

    fn update_bin_average(&mut self, bin_idx: usize) {
        if bin_idx >= 4 {
            return;
        }
        let count = self.bin_counts[bin_idx];
        if count > 0 {
            self.bin_averages[bin_idx] = self.bin_sums[bin_idx] / count as f32;
        } else {
            let defaults = [10.0, 1.0, 0.1, 0.0];
            self.bin_averages[bin_idx] = defaults[bin_idx];
        }

        // Rebuild sorted_bins
        self.sorted_bins = [
            (0, self.bin_averages[0]),
            (1, self.bin_averages[1]),
            (2, self.bin_averages[2]),
            (3, self.bin_averages[3]),
        ];
        // Sort using a simple bubble/insertion sort (4 elements only)
        for i in 1..4 {
            let mut j = i;
            while j > 0 && self.sorted_bins[j - 1].1 < self.sorted_bins[j].1 {
                self.sorted_bins.swap(j - 1, j);
                j -= 1;
            }
        }
    }

    /// Alters the parameters used for calculating the dynamic priority of the propagator
    pub(crate) fn record_propagation_outcome(&mut self, propagator_id: PropagatorId, outcome: PropagationOutcome) {
        if self.has_previous_static_priority {
            return;
        }
        self.propagator_utility.accomodate(propagator_id, 0.0);
        self.base_priorities.accomodate(propagator_id, None);

        let old_util = self.propagator_utility[propagator_id];
        let run_util = match self.propagator_utility_formula {
            PropagatorUtilityFormula::Default => {
                (outcome.total_removed_values as f32 + if outcome.found_conflict { self.propagator_utility_conflict_weight } else { 0.0 }) / (outcome.time.as_micros() as f32 + 1.0)
            }
            PropagatorUtilityFormula::ConflictRate => {
                (if outcome.found_conflict { 1.0 } else { 0.0 }) / (outcome.time.as_micros() as f32 + 1.0)
            }
            PropagatorUtilityFormula::PruningRate => {
                outcome.total_removed_values as f32 / (outcome.time.as_micros() as f32 + 1.0)
            }
            PropagatorUtilityFormula::Conflicts => {
                if outcome.found_conflict { 1.0 } else { 0.0 }
            }
            PropagatorUtilityFormula::Prunings => {
                outcome.total_removed_values as f32
            }
        };
        let decay = self.propagator_utility_decay;
        let new_util = decay * old_util + (1.0 - decay) * run_util;
        self.propagator_utility[propagator_id] = new_util;

        // If we know the base priority, update sums/averages in O(1)
        if let Some(Some(base_priority)) = self.base_priorities.get(propagator_id) {
            let bin_idx = *base_priority as usize;
            if bin_idx < 4 {
                self.bin_sums[bin_idx] = self.bin_sums[bin_idx] - old_util + new_util;
                self.update_bin_average(bin_idx);
            }
        }
    }

    pub(crate) fn calculate_dynamic_priority(&mut self, propagator_id: PropagatorId, priority: Priority) -> Priority {
        if self.has_previous_static_priority {
            return self.previous_static_priority[propagator_id].1;
        }
        self.propagator_utility.accomodate(propagator_id, 0.0);
        self.base_priorities.accomodate(propagator_id, None);

        if self.base_priorities[propagator_id].is_none() {
            self.base_priorities[propagator_id] = Some(priority);
            let bin_idx = priority as usize;
            if bin_idx < 4 {
                self.bin_counts[bin_idx] += 1;
                let util = self.propagator_utility[propagator_id];
                self.bin_sums[bin_idx] += util;
                self.update_bin_average(bin_idx);
            }
        }

        let util = self.propagator_utility[propagator_id];

        // Find which sorted bin is closest to the current utility in O(1)
        let mut best_idx = 0;
        let mut min_dist = f32::MAX;
        for i in 0..4 {
            let dist = (util - self.sorted_bins[i].1).abs();
            if dist < min_dist {
                min_dist = dist;
                best_idx = i;
            }
        }

        match best_idx {
            0 => Priority::High,
            1 => Priority::Medium,
            2 => Priority::Low,
            _ => Priority::VeryLow,
        }
    }

    pub(crate) fn pop(&mut self) -> Option<PropagatorId> {
        if self.present_priorities.is_empty() {
            return None;
        }

        let top_priority = self.present_priorities.peek().unwrap().0 as usize;
        pumpkin_assert_moderate!(!self.queues[top_priority].is_empty());

        let next_propagator_id = self.queues[top_priority].pop_front();

        if let Some(propagator_id) = next_propagator_id {
            self.is_enqueued[propagator_id] = false;

            if self.queues[top_priority].is_empty() {
                let _ = self.present_priorities.pop();
            }
        }

        self.num_enqueued -= 1;

        next_propagator_id
    }

    pub(crate) fn clear(&mut self) {
        while !self.present_priorities.is_empty() {
            let priority = self.present_priorities.pop().unwrap().0 as usize;
            pumpkin_assert_moderate!(!self.queues[priority].is_empty());
            self.queues[priority].clear();
        }

        for is_propagator_enqueued in self.is_enqueued.iter_mut() {
            *is_propagator_enqueued = false;
        }

        self.present_priorities.clear();
        self.num_enqueued = 0;
    }

    pub(crate) fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool {
        self.is_enqueued
            .get(propagator_id)
            .copied()
            .unwrap_or_default()
    }

    pub(crate) fn log_statistics(&self) {
        log_statistic("numberOfPropagators", self.propagator_utility.len());

        for (p_id, value) in self.propagator_utility.iter().enumerate() {
            let p_id = PropagatorId(p_id as u32);
            log_statistic(p_id, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::engine::PropagatorQueue;
    use crate::engine::cp::propagator_queue::PropagationOutcome;
    use crate::propagation::Priority;
    use crate::state::PropagatorId;

    #[test]
    fn test_ordering() {
        let mut queue = PropagatorQueue::default();

        queue.enqueue_propagator(PropagatorId(1), Priority::High);
        queue.enqueue_propagator(PropagatorId(0), Priority::Medium);
        queue.enqueue_propagator(PropagatorId(3), Priority::VeryLow);
        queue.enqueue_propagator(PropagatorId(4), Priority::Low);

        assert_eq!(PropagatorId(1), queue.pop().unwrap());
        assert_eq!(PropagatorId(0), queue.pop().unwrap());
        assert_eq!(PropagatorId(4), queue.pop().unwrap());
        assert_eq!(PropagatorId(3), queue.pop().unwrap());
        assert_eq!(None, queue.pop());
    }

    #[test]
    fn test_dynamic_priority() {
        let mut queue = PropagatorQueue::default();

        queue.enqueue_propagator(PropagatorId(1), Priority::Medium);
        queue.enqueue_propagator(PropagatorId(0), Priority::High);

        assert_eq!(PropagatorId(0), queue.pop().unwrap());
        assert_eq!(PropagatorId(1), queue.pop().unwrap());
        assert_eq!(None, queue.pop());

        // Propagator `0` is really bad and `1` is really good
        queue.record_propagation_outcome(PropagatorId(0), PropagationOutcome {
            time: Duration::from_secs(1),
            found_conflict: false,
            total_removed_values: 0
        });
        queue.record_propagation_outcome(PropagatorId(1), PropagationOutcome {
            time: Duration::from_secs(2),
            found_conflict: true,
            total_removed_values: 5
        });

        let priority = queue.calculate_dynamic_priority(PropagatorId(1), Priority::Medium);
        queue.enqueue_propagator(PropagatorId(1), priority);
        let priority = queue.calculate_dynamic_priority(PropagatorId(0), Priority::High);
        queue.enqueue_propagator(PropagatorId(0), priority);
        assert_eq!(PropagatorId(1), queue.pop().unwrap());
        assert_eq!(PropagatorId(0), queue.pop().unwrap());

        assert_eq!(None, queue.pop());
    }

    #[test]
    fn test_custom_utility_formulas() {
        use crate::engine::cp::propagator_queue::PropagatorUtilityFormula;

        // 1. ConflictRate Formula
        let mut queue = PropagatorQueue::default();
        queue.propagator_utility_formula = PropagatorUtilityFormula::ConflictRate;
        queue.record_propagation_outcome(PropagatorId(0), PropagationOutcome {
            time: Duration::from_micros(999),
            found_conflict: true,
            total_removed_values: 5,
        });
        // old_util = 0.0, run_util = 1.0 / (999.0 + 1.0) = 0.001
        // new_util = 0.8 * 0.0 + 0.2 * 0.001 = 0.0002
        assert_eq!(queue.propagator_utility[PropagatorId(0)], 0.0002);

        // 2. Prunings Formula with custom decay
        let mut queue = PropagatorQueue::default();
        queue.propagator_utility_formula = PropagatorUtilityFormula::Prunings;
        queue.propagator_utility_decay = 0.5;
        queue.record_propagation_outcome(PropagatorId(0), PropagationOutcome {
            time: Duration::from_secs(10),
            found_conflict: false,
            total_removed_values: 10,
        });
        // old_util = 0.0, run_util = 10.0
        // new_util = 0.5 * 0.0 + 0.5 * 10.0 = 5.0
        assert_eq!(queue.propagator_utility[PropagatorId(0)], 5.0);
    }
}
