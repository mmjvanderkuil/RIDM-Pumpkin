use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::time::Duration;

use crate::containers::KeyedVec;
use crate::propagation::Priority;
use crate::propagation::PropagatorId;
use crate::pumpkin_assert_moderate;

#[derive(Debug, Clone)]
pub(crate) struct PropagatorQueue {
    queues: Vec<VecDeque<PropagatorId>>,
    is_enqueued: KeyedVec<PropagatorId, bool>,
    num_enqueued: usize,
    bump_value: KeyedVec<PropagatorId, f32>,
    total_bump: f32,
    present_priorities: BinaryHeap<Reverse<u32>>,
}

struct PropagationOutcome {
    // Time spent in the propagator
    time: Duration,
    found_conflict: bool,
    total_removed_values: u32
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
            bump_value: KeyedVec::default(),
            total_bump: 0.0,
            num_enqueued: 0,
            present_priorities: BinaryHeap::new(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.num_enqueued == 0
    }

    pub(crate) fn enqueue_propagator(&mut self, propagator_id: PropagatorId, priority: Priority) {
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

    /// Alters the parameters used for calculating the dynamic priority of the propagator
    pub(crate) fn record_propagation_outcome(&mut self, propagator_id: PropagatorId, outcome: PropagationOutcome) {
        self.bump_value.accomodate(propagator_id, 0.0);
        // Did the propagator prune any domains?
        if outcome.total_removed_values == 0 {
            self.bump_value[propagator_id] -= 1.0;
        } 
        // Did the propagator find a conflict?
        else if outcome.found_conflict {
            self.bump_value[propagator_id] += 1.0;
        } 
        // The propagator must have pruned but did not find a conflict
        else {
            self.bump_value[propagator_id] = 0.0;
        }
    }

    pub(crate) fn calculate_dynamic_priority(&mut self, propagator_id: PropagatorId, priority: Priority) -> Priority {
        self.bump_value.accomodate(propagator_id, 0.0);
        let bump_value = self.bump_value[propagator_id];
        // TODO: What is a good way to calculate a new dynamic priority
        let new_priority = (priority as usize as f32) - bump_value;

        return Priority::from(new_priority)
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
}
