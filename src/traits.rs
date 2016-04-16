use num_traits::ToPrimitive;
use u128::u128;
use i128::i128;

/// Trait for converting itself into the extra primitive types.
pub trait ToExtraPrimitive: ToPrimitive {
    /// Tries to convert itself into an unsigned 128-bit integer.
    fn to_u128(&self) -> Option<u128>;

    /// Tries to convert itself into a signed 128-bit integer.
    fn to_i128(&self) -> Option<i128>;
}

/// Wrapper for `u128` and `i128` to turn arithmetic operators to wrapping ones.
///
/// Equivalent to `std::num::Wrapping`, but due to E0117 (orphan rule) we need
/// to define it here to implement operators on it.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Default)]
pub struct Wrapping<T>(pub T);

