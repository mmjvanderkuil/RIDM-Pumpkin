use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::time::Duration;

use crate::containers::KeyedVec;
use crate::create_statistics_struct;
use crate::propagation::Priority;
use crate::propagation::PropagatorId;
use crate::pumpkin_assert_moderate;

#[derive(Debug, Clone)]
pub(crate) struct PropagatorQueue {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    present_priorities: BinaryHeap<Reverse<u32>>,
    pub(crate) statistics: PropagatorPrioritiesStatistics,
    #[cfg(feature = "utility-bins")]
    utility_bins: UtilityBins,
    #[cfg(feature = "normal-estimator")]
    normal_est: NormalEstimator,
}

#[cfg(feature = "utility-bins")]
#[derive(Debug, Clone)]
struct UtilityBins {
    propagator_utility: KeyedVec<PropagatorId, f32>,
    base_priorities: KeyedVec<PropagatorId, Option<Priority>>,
    bin_sums: [f32; 4],
    bin_counts: [usize; 4],
    bin_averages: [f32; 4],
    sorted_bins: [(usize, f32); 4],
}

#[cfg(feature = "utility-bins")]
impl Default for UtilityBins {
    fn default() -> Self {
        Self {
            propagator_utility: KeyedVec::default(),
            base_priorities: KeyedVec::default(),
            bin_sums: [0.0; 4],
            bin_counts: [0; 4],
            bin_averages: [10.0, 1.0, 0.1, 0.0],
            sorted_bins: [(0, 10.0), (1, 1.0), (2, 0.1), (3, 0.0)],
        }
    }
}

#[cfg(feature = "utility-bins")]
impl UtilityBins {
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

    pub(crate) fn record_propagation_outcome(
        &mut self,
        propagator_id: PropagatorId,
        outcome: PropagationOutcome,
    ) {
        self.propagator_utility.accomodate(propagator_id, 0.0);
        self.base_priorities.accomodate(propagator_id, None);

        let old_util = self.propagator_utility[propagator_id];
        let run_util = (outcome.total_removed_values as f32
            + if outcome.found_conflict { 1000.0 } else { 0.0 })
            / (outcome.time.as_micros() as f32 + 1.0);
        let new_util = 0.8 * old_util + 0.2 * run_util;
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

    pub(crate) fn calculate_dynamic_priority(
        &mut self,
        propagator_id: PropagatorId,
        priority: Priority,
    ) -> Priority {
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
}

#[cfg(feature = "normal-estimator")]
#[derive(Clone, Debug)]
struct NormalEstimator {
    /// Cumulative sum of x^0, x^1, x^2
    t: [f32; 3],
    /// Mean
    total_mean: f32,
    /// Standard Deviation
    sd: f32,

    alpha: f32,
    propagator_means: KeyedVec<PropagatorId, f32>,
    is_measured: KeyedVec<PropagatorId, bool>,
}

#[cfg( feature = "normal-estimator")]
impl Default for NormalEstimator {
    fn default() -> Self {

        Self {
            t: Default::default(),
            total_mean: 0.0,
            sd: 0.0,
            alpha: 0.8,
            propagator_means: Default::default(),
            is_measured: Default::default(),
        }
    }
}

#[cfg(feature = "normal-estimator")]
impl NormalEstimator {
    const QUARTILE: f32 = 0.67448;

    fn record_propagation_outcome(
        &mut self,
        propagator_id: PropagatorId,
        outcome: PropagationOutcome,
    ) {
        // Calculate the new value
        let value = outcome.total_removed_values as f32 / (outcome.time.as_millis() as f32 + 0.00001);
        self.is_measured.accomodate(propagator_id, false);
        if self.is_measured[propagator_id] {
            let p_mean = self.propagator_means[propagator_id];
            let new_mean = self.alpha * value + (1.0 - self.alpha) * p_mean;
            self.propagator_means[propagator_id] = new_mean;

            // Update the t-parameters
            self.t[1] += new_mean - p_mean;
            self.t[2] += new_mean * new_mean - p_mean * p_mean;
        } else {
            self.propagator_means.accomodate(propagator_id, 0.0);
            self.propagator_means[propagator_id] = value;
            self.is_measured[propagator_id] = true;
            self.t[0] += 1.0;
            self.t[1] += value;
            self.t[2] += value * value;
        }

        if self.t[0] > 1.5 {
            self.total_mean = self.t[1] / self.t[0];
            self.sd = 1.0 / self.t[0]
                * (self.t[0] / (self.t[0] - 1.0)).sqrt()
                * (self.t[0] * self.t[2] - self.t[1] * self.t[1]).sqrt()

        }
    }

    fn calculate_dynamic_priority(
        &mut self,
        propagator_id: PropagatorId,
        priority: Priority,
    ) -> Priority {
        match self.propagator_means.get(propagator_id) {
            None if self.t[0] < 1.5 => priority, // Base priority if we do not yet have enough values
            Some(&x) if x < self.total_mean - Self::QUARTILE * self.sd => Priority::VeryLow,
            Some(&x) if x < self.total_mean => Priority::Low,
            Some(&x) if x < self.total_mean + Self::QUARTILE * self.sd => Priority::Medium,
            _ => Priority::High
        }
    }
}

create_statistics_struct! {
    PropagatorPrioritiesStatistics {
        num_priority_changes: usize,
    }
}

pub(crate) struct PropagationOutcome {
    // Time spent in the propagator
    pub(crate) time: Duration,
    pub(crate) found_conflict: bool,
    pub(crate) total_removed_values: u32,
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
            present_priorities: BinaryHeap::new(),
            statistics: PropagatorPrioritiesStatistics::default(),
            #[cfg(feature = "utility-bins")]
            utility_bins: UtilityBins::default(),
            #[cfg(feature = "normal-estimator")]
            normal_est: NormalEstimator::default(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    pub(crate) fn enqueue_propagator(
        &mut self,
        propagator_id: PropagatorId,
        mut priority: Priority,
    ) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());

        #[cfg(feature = "dynamic-priorities")]
        {
            priority = self.calculate_priority(propagator_id, priority);
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

    /// Alters the parameters used for calculating the dynamic priority of the propagator
    #[cfg(feature = "dynamic-priorities")]
    pub(crate) fn record_propagation_outcome(
        &mut self,
        propagator_id: PropagatorId,
        outcome: PropagationOutcome,
    ) {
        #[cfg(feature = "utility-bins")]
        self.utility_bins
            .record_propagation_outcome(propagator_id, outcome);

        #[cfg(feature = "normal-estimator")]
        self.normal_est
            .record_propagation_outcome(propagator_id, outcome);
    }

    #[cfg(feature = "dynamic-priorities")]
    fn calculate_priority(&mut self, propagator_id: PropagatorId, priority: Priority) -> Priority {
        #[cfg(feature = "utility-bins")]
        {
            let dynamic_priority = self
                .utility_bins
                .calculate_dynamic_priority(propagator_id, priority);
            if dynamic_priority != priority {
                self.statistics.num_priority_changes += 1;
            }
            return dynamic_priority;
        }
        #[cfg(feature = "normal-estimator")]
        {
            let dynamic_priority = self
                .normal_est
                .calculate_dynamic_priority(propagator_id, priority);
            if dynamic_priority != priority {
                self.statistics.num_priority_changes += 1;
            }
            return dynamic_priority;
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
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::engine::cp::propagator_queue::PropagationOutcome;
    use crate::engine::PropagatorQueue;
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

    #[cfg(feature = "dynamic-priorities")]
    #[test]
    fn test_dynamic_priority() {
        let mut queue = PropagatorQueue::default();

        queue.enqueue_propagator(PropagatorId(1), Priority::Medium);
        queue.enqueue_propagator(PropagatorId(0), Priority::High);

        assert_eq!(PropagatorId(0), queue.pop().unwrap());
        assert_eq!(PropagatorId(1), queue.pop().unwrap());
        assert_eq!(None, queue.pop());

        // Propagator `0` is really bad and `1` is really good
        queue.record_propagation_outcome(
            PropagatorId(0),
            PropagationOutcome {
                time: Duration::from_secs(1),
                found_conflict: false,
                total_removed_values: 0,
            },
        );
        queue.record_propagation_outcome(
            PropagatorId(1),
            PropagationOutcome {
                time: Duration::from_secs(2),
                found_conflict: true,
                total_removed_values: 5,
            },
        );

        queue.enqueue_propagator(PropagatorId(1), Priority::Medium);
        queue.enqueue_propagator(PropagatorId(0), Priority::High);
        assert_eq!(PropagatorId(1), queue.pop().unwrap());
        assert_eq!(PropagatorId(0), queue.pop().unwrap());

        assert_eq!(None, queue.pop());
    }
}
