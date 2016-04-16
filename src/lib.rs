//! This crate provides some extra simple types.
//!
//! u128 and i128
//! =============
//!
//! Support signed and unsigned 128-bit integers. These implement the `Int`
//! trait, so most operations associated with integers are allowed.
//!
//! These are mainly needed where explicit 128-bit integer types are required.
//! If the purpose is to operate on "very large integers", the bigint library
//! may be more suitable.
//!
//! Literal macros
//! ==============
//!
//! To construct u128 or i128 at compile time (for `const` items for instance),
//! one should use the `u128!` and `i128!` macros.
//!
//! ```ignored
//! extern crate extprim;
//! use extprim::i128::i128;
//!
//! fn main() {
//!     let some_big_value = i128::from_str("-123_456_789_987_654_321_000");
//!     assert_eq!("-123456789987654321000", format!("{}", some_big_value));
//! }
//! ```
//!

#![cfg_attr(extprim_channel="unstable", feature(asm, test, specialization))]

#[cfg(extprim_channel="unstable")]
extern crate test;

extern crate core;
extern crate rand;
#[macro_use]
extern crate lazy_static;
extern crate num_traits;

mod error;
#[macro_use]
mod forward;
pub mod traits;
pub mod u128;
pub mod i128;
pub mod cast;
mod compiler_rt;

