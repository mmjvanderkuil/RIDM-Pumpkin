use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::time::Duration;

use dyn_clone::DynClone;
use dyn_clone::clone_trait_object;

use crate::containers::KeyedVec;
use crate::create_statistics_struct;
use crate::propagation::Priority;
use crate::propagation::PropagatorId;
use crate::pumpkin_assert_moderate;
use crate::statistics::log_statistic;

pub(crate) trait PropagatorQueue: Debug + DynClone {
    fn is_empty(&self) -> bool;

    fn enqueue_propagator(
        &mut self,
        propagator_id: PropagatorId,
        priority: Priority,
    );

    fn pop(&mut self) -> Option<PropagatorId>;

    fn clear(&mut self);

    fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool;

    /// Alters the parameters used for calculating the dynamic priority of the propagator
    fn record_propagation_outcome(
        &mut self,
        _propagator_id: PropagatorId,
        _outcome: PropagationOutcome,
    ) {}

    fn log_statistics(&self) {}
}

clone_trait_object!(PropagatorQueue);

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[cfg_attr(feature = "clap", derive(clap::ValueEnum))]
pub enum PropagationQueueType {
    #[default]
    Static,
    UtilityBins,
    NormalEstimator,
}

impl PropagationQueueType {
    pub(crate) fn create_queue(self) -> Box<dyn PropagatorQueue> {
        match self {
            PropagationQueueType::Static => Box::new(StaticPropagatorQueue::default()),
            PropagationQueueType::UtilityBins => Box::new(UtilityBins::default()),
            PropagationQueueType::NormalEstimator => {
                Box::new(NormalEstimatorBins::default())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StaticPropagatorQueue {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    present_priorities: BinaryHeap<Reverse<u32>>,
    pub(crate) statistics: PropagatorPrioritiesStatistics,
}

impl Default for StaticPropagatorQueue {
    fn default() -> Self {
        Self::new(5)
    }
}

impl PropagatorQueue for StaticPropagatorQueue {
    fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    fn enqueue_propagator(
        &mut self,
        propagator_id: PropagatorId,
        priority: Priority,
    ) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());

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

    fn pop(&mut self) -> Option<PropagatorId> {
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

    fn clear(&mut self) {
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

    fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool {
        self.is_enqueued
            .get(propagator_id)
            .copied()
            .unwrap_or_default()
    }

    fn log_statistics(&self) {
        log_statistic("numberOfPrioritiesChanged", self.statistics.num_priority_changes);
    }
}

impl StaticPropagatorQueue {
    pub(crate) fn new(num_priority_levels: u32) -> StaticPropagatorQueue {
        StaticPropagatorQueue {
            queues: vec![VecDeque::new(); num_priority_levels as usize],
            is_enqueued: KeyedVec::default(),
            num_enqueued: 0,
            present_priorities: BinaryHeap::new(),
            statistics: PropagatorPrioritiesStatistics::default(),
        }
    }

}

#[derive(Debug, Clone)]
pub(crate) struct UtilityBins {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    present_priorities: BinaryHeap<Reverse<u32>>,
    propagator_utility: KeyedVec<PropagatorId, f32>,
    base_priorities: KeyedVec<PropagatorId, Option<Priority>>,
    bin_sums: [f32; 4],
    bin_counts: [usize; 4],
    bin_averages: [f32; 4],
    sorted_bins: [(usize, f32); 4],
    statistics: PropagatorPrioritiesStatistics,
}

impl Default for UtilityBins {
    fn default() -> Self {
        Self {
            queues: vec![VecDeque::default(); 4],
            is_enqueued: KeyedVec::default(),
            num_enqueued: 0,
            present_priorities: BinaryHeap::new(),
            propagator_utility: KeyedVec::default(),
            base_priorities: KeyedVec::default(),
            bin_sums: [0.0; 4],
            bin_counts: [0; 4],
            bin_averages: [10.0, 1.0, 0.1, 0.0],
            sorted_bins: [(0, 10.0), (1, 1.0), (2, 0.1), (3, 0.0)],
            statistics: PropagatorPrioritiesStatistics::default(),
        }
    }
}

impl PropagatorQueue for UtilityBins {
    fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    fn enqueue_propagator(&mut self, propagator_id: PropagatorId, mut priority: Priority) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());
        let base_priority = priority;
        priority = self.calculate_dynamic_priority(propagator_id, priority);
        if priority != base_priority {
            self.statistics.num_priority_changes += 1;
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

    fn pop(&mut self) -> Option<PropagatorId> {
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

    fn clear(&mut self) {
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

    fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool {
        self.is_enqueued
            .get(propagator_id)
            .copied()
            .unwrap_or_default()
    }

    fn record_propagation_outcome(
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

    fn log_statistics(&self) {
        log_statistic("numberOfPrioritiesChanged", self.statistics.num_priority_changes);
    }

}

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

#[derive(Debug, Clone)]
pub(crate) struct NormalEstimatorBins {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    present_priorities: BinaryHeap<Reverse<u32>>,
    /// Cumulative sum of x^0, x^1, x^2
    t: [f32; 3],
    total_mean: f32,
    sd: f32,
    /// Alpha used for EWMA
    alpha: f32,
    propagator_means: KeyedVec<PropagatorId, f32>,
    is_measured: KeyedVec<PropagatorId, bool>,
    statistics: PropagatorPrioritiesStatistics,
}

impl Default for NormalEstimatorBins {
    fn default() -> Self {
        Self {
            queues: vec![VecDeque::default(); 4],
            is_enqueued: KeyedVec::default(),
            num_enqueued: 0,
            present_priorities: BinaryHeap::new(),
            t: Default::default(),
            total_mean: 0.0,
            sd: 0.0,
            alpha: 0.8,
            propagator_means: Default::default(),
            is_measured: Default::default(),
            statistics: PropagatorPrioritiesStatistics::default(),
        }
    }
}

impl PropagatorQueue for NormalEstimatorBins {
    fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    fn enqueue_propagator(&mut self, propagator_id: PropagatorId, mut priority: Priority) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());
        priority = self.calculate_dynamic_priority(propagator_id, priority);

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

    fn pop(&mut self) -> Option<PropagatorId> {
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

    fn clear(&mut self) {
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

    fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool {
        self.is_enqueued
            .get(propagator_id)
            .copied()
            .unwrap_or_default()
    }

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

    fn log_statistics(&self) {
        log_statistic("numberOfPrioritiesChanged", self.statistics.num_priority_changes);
    }
}

impl NormalEstimatorBins {
    const QUARTILE: f32 = 0.67448;

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

#[derive(Debug, Clone)]
pub(crate) struct AverageHeap {
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    queue: BinaryHeap<(Reverse<f32>, Reverse<u32>, PropagatorId)>,
}

impl Default for AverageHeap {
    fn default() -> Self {
        todo!()
    }
}

impl PropagatorQueue for AverageHeap {
    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn enqueue_propagator(
        &mut self,
        propagator_id: PropagatorId,
        priority: Priority,
    ) {
        pumpkin_assert_moderate!((priority as usize) < self.queues.len());
        if !self.is_propagator_enqueued(propagator_id) {
            self.is_enqueued.accomodate(propagator_id, false);
            self.is_enqueued[propagator_id] = true;
            self.num_enqueued += 1;

            self.queue.push();
        }
    }

    fn pop(&mut self) -> Option<PropagatorId>;

    fn clear(&mut self);

    fn is_propagator_enqueued(&self, propagator_id: PropagatorId) -> bool;

    /// Alters the parameters used for calculating the dynamic priority of the propagator
    fn record_propagation_outcome(
        &mut self,
        _propagator_id: PropagatorId,
        _outcome: PropagationOutcome,
    ) {}

    fn log_statistics(&self) {}
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

#[cfg(test)]
mod tests {
    use std::time::Duration;
    use crate::engine::cp::propagator_queue::PropagationOutcome;
    use crate::engine::PropagatorQueue;
    use crate::engine::StaticPropagatorQueue;
    use crate::engine::UtilityBins;
    use crate::propagation::Priority;
    use crate::state::PropagatorId;

    #[test]
    fn test_ordering() {
        let mut queue = StaticPropagatorQueue::default();

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
        let mut queue = UtilityBins::default();

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
