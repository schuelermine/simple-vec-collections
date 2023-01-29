//! This crate provides simple unoptimized [`Vec`]-based [sets] and [maps].
//!
//! [sets]: crate::vec_set::VecSet
//! [maps]: crate::vec_map::VecMap

pub mod vec_map;
pub mod vec_set;

pub use crate::vec_map::VecMap;
pub use crate::vec_set::VecSet;
