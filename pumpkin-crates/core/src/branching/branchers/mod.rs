//! Provides several implementations of [`Brancher`]s.

pub mod alternating;
pub mod autonomous_search;
pub mod dynamic_brancher;
pub mod independent_variable_value_brancher;
pub mod warm_start;
pub mod custom_search;
pub(crate) mod cumulative_conflict_activity_brancher;

#[cfg(doc)]
use super::Brancher;
