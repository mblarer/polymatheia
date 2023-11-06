//! Mathematical functions, types, traits, and algorithms in pure and safe Rust.
//!
//! The crate's name, polymatheia, means "much knowledge" in ancient greek.
//!
//! The goals of this crate are, with decreasing priority:
//! 1. **Having fun.** This is a recreational project.
//! 1. **Correctness.** This implies that all items should be tested.
//! 1. **Cleanliness.** The code should be simple and elegant.
//! 1. **Independence.** The crate should only depend on the `std` library.
//!
//! The crate currently implements:
//! - Euclidean GCD algorithm
//! - Fibonacci sequence generation
//! - Rational numbers
pub mod euclid;
pub mod fibonacci;
pub mod rational;
pub mod traits;
