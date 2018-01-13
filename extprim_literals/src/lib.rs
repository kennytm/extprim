//! Literal macros for `extprim`.
//!
//! This crate provides a syntex extension (on stable) so that the `extprim` types can be
//! constructed at compile-time using the `i128!()` and `u128!()` macros.
//!
//! Setup
//! =====
//!
//! Simply add `extprim_literals` to dependencies in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! extprim_literals = "2"
//! ```
//!
//! Use the macros in `src/consts.rs`:
//!
//! ```
//! #[macro_use]
//! extern crate extprim_literals;
//! extern crate extprim;
//! use extprim::u128::u128;
//!
//! const TEN: u128 = u128!(10);
//! # fn main() {}
//! ```

#[allow(unused_imports)] // <- why do we need this at all?
#[macro_use] extern crate extprim_literals_macros;
#[macro_use] extern crate procedural_masquerade;

pub use extprim_literals_macros::*;

define_invoke_proc_macro!(internal_extprim_literals_macros_invoke);

/// Creates an unsigned 128-bit integer at compile time. The content can be any integer literals
/// supported by Rust, e.g.
///
/// ```
/// #[macro_use] extern crate extprim_literals;
/// extern crate extprim;
/// use extprim::u128::u128;
///
/// # fn main() {
/// u128!(190645052318211650775886739373212217031);
/// u128!(290_016_114_491_568_400_953_264_683_755_668_101_244);
/// u128!(0x1755_7146_02da_b606_e059_515e_7938_5189);
/// u128!(0o3653247246101356646675471111622746760005231);
/// u128!(0b11001001000000101100010000101110100001100110100100110110000100011110110110010111);
/// # }
/// ```
#[macro_export]
macro_rules! u128 {
    ($e:tt) => {
        {
            internal_extprim_literals_macros_invoke! {
                internal_extprim_literals_macros_u128!($e)
            }
            VALUE
        }
    }
}

/// Creates a signed 128-bit integer at compile time. The content can be any integer literals
/// supported by Rust, e.g.
///
/// ```
/// #[macro_use] extern crate extprim_literals;
/// extern crate extprim;
/// use extprim::i128::i128;
///
/// # fn main() {
/// i128!(123623219786789911069641050508607316353);
/// i128!(+1241909465635371210237387091769850650);
/// i128!(-42128403654828209595896121373164578595);
/// i128!(-0x34c1b7a2_2955e5bb_03cc1a88_342b9e8d);
/// i128!(0o1_151760_574675_745253_103376_166404_235110_762614);
/// i128!(-0b11000111001101001100001010010111110101000101011011011111101111111111110101110110);
/// # }
/// ```
#[macro_export]
macro_rules! i128 {
    (+ $e:tt) => {
        {
            internal_extprim_literals_macros_invoke! {
                internal_extprim_literals_macros_i128!($e)
            }
            VALUE
        }
    };
    (- $e:tt) => {
        {
            internal_extprim_literals_macros_invoke! {
                internal_extprim_literals_macros_i128!(-$e)
            }
            VALUE
        }
    };
    ($e:tt) => {
        {
            internal_extprim_literals_macros_invoke! {
                internal_extprim_literals_macros_i128!($e)
            }
            VALUE
        }
    };
}

/// Provided for backward-compatibility only. This method does nothing.
#[deprecated(since="2.0.0", note="plugin registration is no longer required, and this method is no-op now")]
pub fn register<T>(_: T) {}
