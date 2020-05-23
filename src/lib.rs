//! This crate provides some extra simple types.
//!
//! u128 and i128
//! =============
//!
//! Support signed and unsigned 128-bit integers. Also standard primitive operations are supported.
//!
//! These are mainly needed where explicit 128-bit integer types are required. If the purpose is to
//! operate on "very large integers", the [bigint](https://crates.io/crates/num-bigint) library may
//! be more suitable.
//!
//! ```rust
//! #[macro_use] extern crate extprim_literals;
//! extern crate extprim;
//!
//! use std::str::FromStr;
//! use extprim::i128::i128;
//!
//! fn main() {
//!     let a = i128::from_str("100000000000000000000000000000000000000").unwrap();
//!             // convert string to u128 or i128
//!     let b = i128::new(10).pow(38);
//!             // 64-bit integers can be directly new'ed
//!     assert_eq!(a, b);
//!
//!     let c = i128::from_parts(5421010862427522170, 687399551400673280);
//!             // represent using the higher- and lower-64-bit parts
//!     let d = c - a;
//!             // standard operators like +, -, *, /, %, etc. work as expected.
//!     assert_eq!(d, i128::zero());
//!
//!     const e: i128 = i128!(100000000000000000000000000000000000000);
//!             // use the literal macros
//!     assert_eq!(a, e);
//! }
//! ```
//!
//! Literal macros
//! ==============
//!
//! The extra primitive types can be created via the literal macros using the `extprim_literals` procedural macro.
//! Please check the [documentation of `extprim_literals`](../../extprim_literals/index.html) for details.
//!
//! ```ignore
//! #![macro_use]
//! extern crate extprim_literals;
//! extern crate extprim;
//!
//! fn main() {
//!     let a = u128!(0xffeeddcc_bbaa9988_77665544_33221100);
//!     let b = u128!(73);
//!     let result = a / b;
//!     let expected = u128!(4_660_183_619_323_730_626_856_278_982_251_165_334);
//!     assert_eq!(a / b, expected);
//! }
//! ```

#![cfg_attr(extprim_channel="unstable", feature(llvm_asm, test, specialization, const_fn))]
// feature requirement:
//  - llvm_asm: to provide a fast implementation of u64_long_mul in x86_64
//  - test: benchmarking
//  - specialization: to allow ToExtraPrimitive inherit from ToPrimitive, while ensuring conversion
//                    between the 128-bit types remain correct
//  - const_fn: Create 128-bit constants

#![cfg_attr(not(feature="use-std"), no_std)]

#[cfg(extprim_channel="unstable")] extern crate test;

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

#[cfg(feature="use-std")] extern crate core;
#[cfg(not(feature="use-std"))] extern crate core as std;
#[cfg(feature="rand")] extern crate rand;
extern crate num_traits;

#[macro_use] mod forward;
#[cfg_attr(test, macro_use)] mod format_buffer;
mod error;
pub mod traits;
pub mod u128;
pub mod i128;
mod compiler_rt;

