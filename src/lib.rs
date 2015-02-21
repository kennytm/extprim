#![feature(asm)]
#![feature(rustc_private, plugin_registrar, quote)]
#![feature(test, core, unicode, collections)]

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
//! ```
//! #![feature(plugin)]
//!
//! #![plugin(extprim)]
//!
//! #[allow(plugin_as_library)]
//! extern crate extprim;
//! use extprim::i128::i128;
//!
//! const SOME_BIG_VALUE: i128 = i128!(-123_456_789_987_654_321_000);
//! fn main() {
//!     assert_eq!("-123456789987654321000", format!("{}", SOME_BIG_VALUE));
//! }
//! ```
//!

extern crate core;
extern crate test;
extern crate syntax;
extern crate rustc;
#[macro_use]
extern crate lazy_static;

mod error;
pub mod u128;
pub mod i128;
mod compiler_rt;
pub mod literals;

