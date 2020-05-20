//! Unsigned 128-bit integer.

use std::cmp::Ordering;
use std::fmt::{self, Write};
use std::iter::{Product, Sum};
use std::num::ParseIntError;
use std::ops::*;
use std::str::FromStr;
use std::u64;

#[cfg(feature="rand")] use rand::Rng;
#[cfg(feature="rand")] use rand::distributions::{Standard, Distribution};
use num_traits::*;

use compiler_rt::{udiv128, umod128, udivmod128};
use error;
use format_buffer::FormatBuffer;
use i128::i128;
use traits::{ToExtraPrimitive, Wrapping};
#[cfg(extprim_has_stable_i128)] use compiler_rt::builtins::{I128, U128};

//{{{ Structure

/// Number of bits an unsigned 128-bit number occupies.
pub const BITS: usize = 128;

/// Number of bytes an unsigned 128-bit number occupies.
pub const BYTES: usize = 16;

/// The smallest unsigned 128-bit integer (0).
pub const MIN: u128 = u128 { lo: 0, hi: 0 };

/// The largest unsigned 128-bit integer (`340_282_366_920_938_463_463_374_607_431_768_211_455`).
pub const MAX: u128 = u128 { lo: u64::MAX, hi: u64::MAX };

/// The constant 0.
pub const ZERO: u128 = MIN;

/// The constant 1.
pub const ONE: u128 = u128 { lo: 1, hi: 0 };

/// An unsigned 128-bit number.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Default, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
#[allow(non_camel_case_types)]
pub struct u128 {
    // TODO these two fields are public because `const fn` are not yet stable.

    /// The lower 64-bit of the number.
    #[doc(hidden)]
    #[cfg(target_endian="little")]
    pub lo: u64,

    /// The higher 64-bit of the number.
    #[doc(hidden)]
    pub hi: u64,

    /// The lower 64-bit of the number.
    #[doc(hidden)]
    #[cfg(target_endian="big")]
    pub lo: u64,
}

impl u128 {
    /// Constructs a new 128-bit integer from a 64-bit integer.
    #[cfg(extprim_channel="stable")]
    pub fn new(lo: u64) -> u128 {
        u128 { lo: lo, hi: 0 }
    }

    /// Constructs a new 128-bit integer from a 64-bit integer.
    #[cfg(extprim_channel="unstable")]
    pub const fn new(lo: u64) -> u128 {
        u128 { lo: lo, hi: 0 }
    }

    /// Constructs a new 128-bit integer from the built-in 128-bit integer.
    #[cfg(extprim_has_stable_i128)]
    #[cfg(extprim_channel="stable")]
    pub fn from_built_in(value: U128) -> u128 {
        u128 {
            lo: (value & 0xffff_ffff_ffff_ffff) as u64,
            hi: (value >> 64) as u64,
        }
    }

    /// Constructs a new 128-bit integer from the built-in 128-bit integer.
    #[cfg(extprim_has_stable_i128)]
    #[cfg(extprim_channel="unstable")]
    pub const fn from_built_in(value: U128) -> u128 {
        u128 {
            lo: (value & 0xffff_ffff_ffff_ffff) as u64,
            hi: (value >> 64) as u64,
        }
    }

    /// Constructs a new 128-bit integer from the high-64-bit and low-64-bit parts.
    ///
    /// The new integer can be considered as `hi * 2**64 + lo`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let number = u128::from_parts(6692605942, 14083847773837265618);
    /// assert_eq!(format!("{}", number), "123456789012345678901234567890");
    /// ```
    #[cfg(extprim_channel="stable")]
    pub fn from_parts(hi: u64, lo: u64) -> u128 {
        u128 { lo: lo, hi: hi }
    }

    /// Constructs a new 128-bit integer from the high-64-bit and low-64-bit parts.
    ///
    /// The new integer can be considered as `hi * 2**64 + lo`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let number = u128::from_parts(6692605942, 14083847773837265618);
    /// assert_eq!(format!("{}", number), "123456789012345678901234567890");
    /// ```
    #[cfg(extprim_channel="unstable")]
    pub const fn from_parts(hi: u64, lo: u64) -> u128 {
        u128 { lo: lo, hi: hi }
    }

    /// Fetches the lower-64-bit of the number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let number = u128::from_str_radix("ffd1390a0adc2fb8dabbb8174d95c99b", 16).unwrap();
    /// assert_eq!(number.low64(), 0xdabbb8174d95c99b);
    /// ```
    pub fn low64(self) -> u64 {
        self.lo
    }

    /// Fetch the higher-64-bit of the number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let number = u128::from_str_radix("ffd1390a0adc2fb8dabbb8174d95c99b", 16).unwrap();
    /// assert_eq!(number.high64(), 0xffd1390a0adc2fb8);
    /// ```
    pub fn high64(self) -> u64 {
        self.hi
    }

    /// Converts this number to signed with wrapping.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    /// use extprim::i128::i128;
    ///
    /// let a = u128::from_str_radix( "ffd1390a0adc2fb8dabbb8174d95c99b", 16).unwrap();
    /// let b = i128::from_str_radix("-002ec6f5f523d047254447e8b26a3665", 16).unwrap();
    /// assert_eq!(a.as_i128(), b);
    /// assert_eq!(b.as_u128(), a);
    /// ```
    pub fn as_i128(self) -> i128 {
        i128::from_parts(self.hi as i64, self.lo)
    }

    /// Converts this number to the built-in 128-bit integer type.
    #[cfg(extprim_has_stable_i128)]
    pub fn as_built_in(self) -> U128 {
        (self.hi as U128) << 64 | self.lo as U128
    }
}

//}}}

//{{{ Rand

#[cfg(feature="rand")]
impl Distribution<u128> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u128 {
        let (lo, hi) = rng.gen();
        u128::from_parts(lo, hi)
    }
}

//}}}

//{{{ Add, Sub

impl u128 {
    /// Wrapping (modular) addition. Computes `self + other`, wrapping around at the boundary of
    /// the type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(5).wrapping_add(u128::new(6)), u128::new(11));
    /// assert_eq!(u128::max_value().wrapping_add(u128::one()), u128::zero());
    /// ```
    pub fn wrapping_add(self, other: u128) -> u128 {
        let (lo, carry) = self.lo.overflowing_add(other.lo);
        let hi = self.hi.wrapping_add(other.hi);
        let hi = hi.wrapping_add(if carry { 1 } else { 0 });
        u128::from_parts(hi, lo)
    }

    /// Wrapping (modular) subtraction. Computes `self - other`, wrapping around at the boundary of
    /// the type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).wrapping_sub(u128::new(5)), u128::one());
    /// assert_eq!(u128::new(5).wrapping_sub(u128::new(6)), u128::max_value());
    /// ```
    pub fn wrapping_sub(self, other: u128) -> u128 {
        let (lo, borrow) = self.lo.overflowing_sub(other.lo);
        let hi = self.hi.wrapping_sub(other.hi);
        let hi = hi.wrapping_sub(if borrow { 1 } else { 0 });
        u128::from_parts(hi, lo)
    }

    /// Calculates `self + other`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).overflowing_add(u128::new(13)), (u128::new(19), false));
    /// assert_eq!(u128::max_value().overflowing_add(u128::one()), (u128::zero(), true));
    /// ```
    pub fn overflowing_add(self, other: u128) -> (u128, bool) {
        let (lo, lo_carry) = self.lo.overflowing_add(other.lo);
        let (hi, hi_carry_1) = self.hi.overflowing_add(if lo_carry { 1 } else { 0 });
        let (hi, hi_carry_2) = hi.overflowing_add(other.hi);
        (u128::from_parts(hi, lo), hi_carry_1 || hi_carry_2)
    }

    /// Calculates `self - other`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).overflowing_sub(u128::new(5)), (u128::one(), false));
    /// assert_eq!(u128::new(5).overflowing_sub(u128::new(6)), (u128::max_value(), true));
    /// ```
    pub fn overflowing_sub(self, other: u128) -> (u128, bool) {
        let (lo, lo_borrow) = self.lo.overflowing_sub(other.lo);
        let (hi, hi_borrow_1) = self.hi.overflowing_sub(if lo_borrow { 1 } else { 0 });
        let (hi, hi_borrow_2) = hi.overflowing_sub(other.hi);
        (u128::from_parts(hi, lo), hi_borrow_1 || hi_borrow_2)
    }

    /// Saturating integer addition. Computes `self + other`, saturating at the numeric bounds
    /// instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(13).saturating_add(u128::new(7)), u128::new(20));
    ///
    /// let huge_num = u128::from_str_radix("ccccccccbbbbbbbbaaaaaaaa99999999", 16).unwrap();
    /// let also_big = u128::from_str_radix("5566778899aabbccddeeff0011223344", 16).unwrap();
    /// assert_eq!(huge_num.saturating_add(also_big), u128::max_value());
    /// ```
    pub fn saturating_add(self, other: u128) -> u128 {
        self.checked_add(other).unwrap_or(MAX)
    }

    /// Saturating integer subtraction. Computes `self - other`, saturating at the numeric bounds
    /// instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(91).saturating_sub(u128::new(13)), u128::new(78));
    /// assert_eq!(u128::new(13).saturating_sub(u128::new(91)), u128::zero());
    /// ```
    pub fn saturating_sub(self, other: u128) -> u128 {
        if self <= other {
            ZERO
        } else {
            self.wrapping_sub(other)
        }
    }

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents all applications of this function
    /// will wrap (except for `-0`). For values smaller than the corresponding signed type's
    /// maximum the result is the same as casting the corresponding signed value. Any larger values
    /// are equivalent to `MAX + 1 - (val - MAX - 1)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::zero().wrapping_neg(), u128::zero());
    /// assert_eq!(u128::one().wrapping_neg(), u128::max_value());
    /// assert_eq!(u128::max_value().wrapping_neg(), u128::one());
    /// ```
    pub fn wrapping_neg(self) -> u128 {
        ONE.wrapping_add(!self)
    }
}

forward_symmetric! {
    /// Checked integer addition. Computes `self + other`, returning `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(5).checked_add(u128::new(8)), Some(u128::new(13)));
    /// assert_eq!(u128::max_value().checked_add(u128::max_value()), None);
    /// ```
    impl Add(add, checked_add, wrapping_add, overflowing_add) for u128
}
forward_symmetric! {
    /// Checked integer subtraction. Computes `self - other`, returning `None` if underflow
    /// occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(8).checked_sub(u128::new(5)), Some(u128::new(3)));
    /// assert_eq!(u128::new(5).checked_sub(u128::new(8)), None);
    /// ```
    impl Sub(sub, checked_sub, wrapping_sub, overflowing_sub) for u128
}
forward_assign!(AddAssign(add_assign, add) for u128);
forward_assign!(SubAssign(sub_assign, sub) for u128);

impl Neg for Wrapping<u128> {
    type Output = Self;
    fn neg(self) -> Self {
        Wrapping(self.0.wrapping_neg())
    }
}

impl CheckedAdd for u128 {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        Self::checked_add(*self, *other)
    }
}

impl CheckedSub for u128 {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        Self::checked_sub(*self, *other)
    }
}

impl Saturating for u128 {
    fn saturating_add(self, other: Self) -> Self {
        Self::saturating_add(self, other)
    }

    fn saturating_sub(self, other: Self) -> Self {
        Self::saturating_add(self, other)
    }
}

#[cfg(test)]
mod add_sub_tests {
    use u128::{u128, ZERO, ONE, MAX};

    #[test]
    fn test_add() {
        assert_eq!(u128::from_parts(23, 12) + u128::from_parts(78, 45),
                    u128::from_parts(101, 57));
        assert_eq!(u128::from_parts(0x4968eca20d32da8d, 0xaf40c0e1a806fa23) +
                    u128::from_parts(0x71b6119ef76e4fe3, 0x0f58496c74669747),
                    u128::from_parts(0xbb1efe4104a12a70, 0xbe990a4e1c6d916a));
        assert_eq!(u128::from_parts(1, 0xffffffff_ffffffff) + u128::from_parts(0, 1),
                    u128::from_parts(2, 0));
    }

    #[test]
    fn test_wrapping_overflowing_add() {
        let a = u128::from_parts(0xfeae4b298df991ae, 0x21b6c7c3766908a7);
        let b = u128::from_parts(0x08a45eef16781327, 0xff1049ddf49ff8a8);
        let c = u128::from_parts(0x0752aa18a471a4d6, 0x20c711a16b09014f);
        assert_eq!(a.wrapping_add(b), c);
        assert_eq!(a.overflowing_add(b), (c, true));
        assert_eq!(a.checked_add(b), None);
        assert_eq!(a.saturating_add(b), MAX);

        assert_eq!(ONE.wrapping_add(ONE), u128::new(2));
        assert_eq!(ONE.overflowing_add(ONE), (u128::new(2), false));
        assert_eq!(ONE.checked_add(ONE), Some(u128::new(2)));
        assert_eq!(ONE.saturating_add(ONE), u128::new(2));

        assert_eq!(MAX.wrapping_add(ONE), ZERO);
        assert_eq!(MAX.overflowing_add(ONE), (ZERO, true));
        assert_eq!(MAX.checked_add(ONE), None);
        assert_eq!(MAX.saturating_add(ONE), MAX);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_add_overflow_without_carry() {
        let _ = u128::from_parts(0x80000000_00000000, 0) + u128::from_parts(0x80000000_00000000, 0);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_add_overflow_with_carry() {
        let _ = MAX + ONE;
    }

    #[test]
    fn test_sub() {
        assert_eq!(u128::from_parts(78, 45) - u128::from_parts(23, 12),
                    u128::from_parts(55, 33));
        assert_eq!(u128::from_parts(0xfeae4b298df991ae, 0x21b6c7c3766908a7) -
                    u128::from_parts(0x08a45eef16781327, 0xff1049ddf49ff8a8),
                    u128::from_parts(0xf609ec3a77817e86, 0x22a67de581c90fff));
    }

    #[test]
    fn test_wrapping_overflowing_sub() {
        let a = u128::from_parts(3565142335064920496, 15687467940602204387);
        let b = u128::from_parts(4442421226426414073, 17275749316209243331);
        let c = u128::from_parts(17569465182348058038, 16858462698102512672);
        let neg_c = c.wrapping_neg();

        assert_eq!(a.wrapping_sub(b), c);
        assert_eq!(a.overflowing_sub(b), (c, true));
        assert_eq!(a.checked_sub(b), None);
        assert_eq!(a.saturating_sub(b), ZERO);

        assert_eq!(b.wrapping_sub(a), neg_c);
        assert_eq!(b.overflowing_sub(a), (neg_c, false));
        assert_eq!(b.checked_sub(a), Some(neg_c));
        assert_eq!(b.saturating_sub(a), neg_c);

        assert_eq!(ONE.wrapping_sub(ONE), ZERO);
        assert_eq!(ONE.overflowing_sub(ONE), (ZERO, false));
        assert_eq!(ONE.checked_sub(ONE), Some(ZERO));
        assert_eq!(ONE.saturating_sub(ONE), ZERO);

        assert_eq!(ZERO.wrapping_sub(ONE), MAX);
        assert_eq!(ZERO.overflowing_sub(ONE), (MAX, true));
        assert_eq!(ZERO.checked_sub(ONE), None);
        assert_eq!(ZERO.saturating_sub(ONE), ZERO);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_sub_overflow() {
        let _ = ZERO - ONE;
    }
}

//}}}

//{{{ PartialOrd, Ord

impl PartialOrd for u128 {
    fn partial_cmp(&self, other: &u128) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for u128 {
    fn cmp(&self, other: &u128) -> Ordering {
        (self.hi, self.lo).cmp(&(other.hi, other.lo))
    }
}

#[cfg(test)]
mod cmp_tests {
    use u128::{u128, MAX, ZERO, ONE};

    #[test]
    fn test_ord() {
        let a = ZERO;
        let b = ONE;
        let c = u128::from_parts(1, 0);
        let d = MAX;

        assert!(a < b);
        assert!(a <= b);
        assert!(c > b);
        assert!(c == c);
        assert!(d != c);
        assert!(d >= c);
    }
}

//}}}

//{{{ Not, BitAnd, BitOr, BitXor

impl Not for u128 {
    type Output = Self;
    fn not(self) -> Self {
        u128 { lo: !self.lo, hi: !self.hi }
    }
}

impl BitAnd for u128 {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        u128 { lo: self.lo & other.lo, hi: self.hi & other.hi }
    }
}

impl BitOr for u128 {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        u128 { lo: self.lo | other.lo, hi: self.hi | other.hi }
    }
}

impl BitXor for u128 {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        u128 { lo: self.lo ^ other.lo, hi: self.hi ^ other.hi }
    }
}

impl Not for Wrapping<u128> {
    type Output = Self;
    fn not(self) -> Self {
        Wrapping(!self.0)
    }
}

impl BitAnd for Wrapping<u128> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Wrapping(self.0 & other.0)
    }
}

impl BitOr for Wrapping<u128> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        Wrapping(self.0 | other.0)
    }
}

impl BitXor for Wrapping<u128> {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        Wrapping(self.0 ^ other.0)
    }
}

forward_assign!(BitAndAssign(bitand_assign, bitand) for u128);
forward_assign!(BitOrAssign(bitor_assign, bitor) for u128);
forward_assign!(BitXorAssign(bitxor_assign, bitxor) for u128);

#[cfg(test)]
mod bitwise_tests {
    use u128::u128;

    #[test]
    fn test_not() {
        assert_eq!(u128::from_parts(0x491d3b2d80d706a6, 0x1eb41c5d2ad1a379),
                    !u128::from_parts(0xb6e2c4d27f28f959, 0xe14be3a2d52e5c86));
    }

    #[test]
    fn test_bit_and() {
        assert_eq!(u128::from_parts(0x8aff8559dc82aa91, 0x8bbf525fb0c5cd79) &
                    u128::from_parts(0x8dcecc950badb6f1, 0xb26ab6ca714bce40),
                    u128::from_parts(0x88ce84110880a291, 0x822a124a3041cc40));
    }

    #[test]
    fn test_bit_or() {
        assert_eq!(u128::from_parts(0xe3b7e0ae1e8f8beb, 0x5c76dd080dd43e30) |
                    u128::from_parts(0x35591b16599e2ece, 0x2e2957ca426d7b07),
                    u128::from_parts(0xf7fffbbe5f9fafef, 0x7e7fdfca4ffd7f37));
    }

    #[test]
    fn test_bit_xor() {
        assert_eq!(u128::from_parts(0x50b17617e8f6ee49, 0x1b06f037a9187c71) ^
                    u128::from_parts(0x206f313ea29823bd, 0x66e0bc7aa198785a),
                    u128::from_parts(0x70de47294a6ecdf4, 0x7de64c4d0880042b));
    }
}

//}}}

//{{{ Shl, Shr

impl u128 {
    /// Panic-free bitwise shift-left; yields `self << (shift % 128)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(7).wrapping_shl(66), u128::from_parts(28, 0));
    /// assert_eq!(u128::new(7).wrapping_shl(128), u128::new(7));
    /// assert_eq!(u128::new(7).wrapping_shl(129), u128::new(14));
    /// ```
    pub fn wrapping_shl(self, shift: u32) ->  u128 {
        let lo = self.lo;
        let hi = self.hi;

        let (lo, hi) = if (shift & 64) != 0 {
            (0, lo.wrapping_shl(shift & 63))
        } else {
            let new_lo = lo.wrapping_shl(shift);
            let mut new_hi = hi.wrapping_shl(shift);
            if (shift & 127) != 0 {
                new_hi |= lo.wrapping_shr(64u32.wrapping_sub(shift));
            }
            (new_lo, new_hi)
        };

        u128::from_parts(hi, lo)
    }

    /// Panic-free bitwsie shift-right; yields `self >> (shift % 128)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::max_value().wrapping_shr(66), u128::new(0x3fffffffffffffff));
    /// assert_eq!(u128::new(7).wrapping_shr(128), u128::new(7));
    /// assert_eq!(u128::new(7).wrapping_shr(129), u128::new(3));
    /// ```
    pub fn wrapping_shr(self, shift: u32) -> u128 {
        let lo = self.lo;
        let hi = self.hi;

        let (hi, lo) = if (shift & 64) != 0 {
            (0, hi.wrapping_shr(shift & 63))
        } else {
            let new_hi = hi.wrapping_shr(shift);
            let mut new_lo = lo.wrapping_shr(shift);
            if (shift & 127) != 0 {
                new_lo |= hi.wrapping_shl(64u32.wrapping_sub(shift));
            }
            (new_hi, new_lo)
        };

        u128::from_parts(hi, lo)
    }

    /// Shifts `self` left by `other` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean indicating whether
    /// the shift value was larger than or equal to the number of bits (128). If the shift value is
    /// too large, then value is masked by `0x7f`, and this value is then used to perform the shift.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(7).overflowing_shl(66), (u128::from_parts(28, 0), false));
    /// assert_eq!(u128::new(7).overflowing_shl(128), (u128::new(7), true));
    /// assert_eq!(u128::new(7).overflowing_shl(129), (u128::new(14), true));
    /// ```
    pub fn overflowing_shl(self, other: u32) -> (u128, bool) {
        (self.wrapping_shl(other), other >= 128)
    }

    /// Shifts `self` right by `other` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean indicating whether
    /// the shift value was larger than or equal to the number of bits (128). If the shift value is
    /// too large, then value is masked by `0x7f`, and this value is then used to perform the shift.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::max_value().overflowing_shr(66), (u128::new(0x3fffffffffffffff), false));
    /// assert_eq!(u128::new(7).overflowing_shr(128), (u128::new(7), true));
    /// assert_eq!(u128::new(7).overflowing_shr(129), (u128::new(3), true));
    /// ```
    pub fn overflowing_shr(self, other: u32) -> (u128, bool) {
        (self.wrapping_shr(other), other >= 128)
    }
}

forward_shift! {
    /// Checked shift left. Computes `self << other`, returning `None` if the shift is larger than
    /// or equal to the number of bits in `self` (128).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(7).checked_shl(66), Some(u128::from_parts(28, 0)));
    /// assert_eq!(u128::new(7).checked_shl(128), None);
    /// assert_eq!(u128::new(7).checked_shl(129), None);
    /// ```
    impl Shl(shl, checked_shl, wrapping_shl, overflowing_shl) for u128
}
forward_shift! {
    /// Checked shift right. Computes `self >> other`, returning `None` if the shift is larger than
    /// or equal to the number of bits in `self` (128).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::max_value().checked_shr(66), Some(u128::new(0x3fffffffffffffff)));
    /// assert_eq!(u128::new(7).checked_shr(128), None);
    /// assert_eq!(u128::new(7).checked_shr(129), None);
    /// ```
    impl Shr(shr, checked_shr, wrapping_shr, overflowing_shr) for u128
}
forward_assign!(ShlAssign<u8|u16|u32|u64|usize|i8|i16|i32|i64|isize>(shl_assign, shl) for u128);
forward_assign!(ShrAssign<u8|u16|u32|u64|usize|i8|i16|i32|i64|isize>(shr_assign, shr) for u128);

#[cfg(test)]
mod shift_tests {
    use u128::u128;

    #[test]
    fn test_shl() {
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 0,
                    u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 1,
                    u128::from_parts(0x3cb8f00361caebee, 0xa7e13b58b651e2a4));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 64,
                    u128::from_parts(0x53f09dac5b28f152, 0x0));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 120,
                    u128::from_parts(0x5200000000000000, 0x0));

        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) << 0,
                    u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) << 1,
                    u128::from_parts(0xf004a6c7bb9aa3b0, 0xa13af1c94601179a));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) << 64,
                    u128::from_parts(0x509d78e4a3008bcd, 0x0));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) << 120,
                    u128::from_parts(0xcd00000000000000, 0x0));
    }

    #[test]
    fn test_shr() {
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 0,
                    u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 1,
                    u128::from_parts(0xf2e3c00d872bafb, 0xa9f84ed62d9478a9));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 64,
                    u128::from_parts(0x0, 0x1e5c7801b0e575f7));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 120,
                    u128::from_parts(0x0, 0x1e));

        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) >> 0,
                    u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) >> 1,
                    u128::from_parts(0x7c0129b1eee6a8ec, 0x284ebc72518045e6));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) >> 64,
                    u128::from_parts(0x0, 0xf8025363ddcd51d8));
        assert_eq!(u128::from_parts(0xf8025363ddcd51d8, 0x509d78e4a3008bcd) >> 120,
                    u128::from_parts(0x0, 0xf8));
    }

    #[test]
    #[should_panic(expected="shift operation overflowed")]
    fn test_shl_overflow() {
        let _ = u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 128;
    }

    #[test]
    #[should_panic(expected="shift operation overflowed")]
    fn test_shr_overflow() {
        let _ = u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 256;
    }
}

#[cfg(all(test, extprim_channel="unstable"))]
mod shift_bench {
    use u128::u128;
    use test::{Bencher, black_box};

    // randomize shift range to avoid possible branch prediction effect.
    const BENCH_SHIFTS: &'static [u32] = &[
        77, 45, 57, 7, 34, 75, 38, 89, 89, 66, 16, 111, 66, 123, 14, 80, 94, 43,
        46, 86, 121, 31, 123, 33, 23, 57, 50, 28, 26, 46, 8, 88, 74, 55, 108,
        127, 1, 70, 73, 2, 1, 45, 36, 96, 124, 124, 91, 63, 25, 94, 8, 68, 41,
        127, 107, 10, 111, 98, 97, 72, 78, 10, 125, 17, 62, 3, 65, 67, 13, 41,
        68, 109, 23, 100, 98, 16, 78, 13, 0, 63, 107, 64, 13, 23, 69, 73, 2, 38,
        16, 9, 124, 120, 39, 119, 3, 15, 25, 11, 84, 102, 69, 58, 39, 116, 66,
        87, 111, 17, 11, 29, 35, 123, 23, 38, 43, 85, 32, 7, 34, 84, 27, 35,
        122, 64, 33, 83, 78, 105, 31, 5, 58, 25, 21, 34, 15, 94, 10, 23, 48, 89,
        23, 99, 110, 105, 32, 7, 116, 31, 10, 14, 22, 84, 40, 57, 7, 35, 8, 95,
        121, 66, 95, 103, 26, 62, 24, 36, 48, 58, 122, 66, 37, 56, 35, 87, 36,
        41, 75, 37, 25, 40, 60, 39, 94, 18, 33, 113, 34, 66, 34, 34, 88, 95, 81,
        115, 10, 67, 33, 34, 23, 53, 10, 119, 54, 107, 37, 17, 85, 42, 83, 85,
        102, 104, 94, 24, 97, 104, 93, 9, 95, 75, 41, 112, 64, 63, 72, 3, 26,
        65, 103, 88, 121, 105, 98, 82, 89, 30, 37, 64, 68, 41, 93, 57, 105, 100,
        108, 102, 44, 17, 61, 72, 33, 126, 73, 105, 0, 119, 97, 28, 9, 101, 44,
    ];

    #[bench]
    fn bench_shl(bencher: &mut Bencher) {
        let number = u128::from_parts(9741918172058430398, 3937562729638942691);
        bencher.iter(|| {
            for i in BENCH_SHIFTS {
                black_box(number.wrapping_shl(*i));
            }
        });
    }

    #[bench]
    fn bench_shr(bencher: &mut Bencher) {
        let number = u128::from_parts(9741918172058430398, 3937562729638942691);
        bencher.iter(|| {
            for i in BENCH_SHIFTS {
                black_box(number.wrapping_shr(*i));
            }
        });
    }

}

//}}}

//{{{ Mul

/// Computes the product of two unsigned 64-bit integers. Returns a 128-bit
/// integer.
#[cfg(not(all(target_arch="x86_64", extprim_channel="unstable")))]
fn u64_long_mul(left: u64, right: u64) -> u128 {
    let a = left >> 32;
    let b = left & 0xffffffff;
    let c = right >> 32;
    let d = right & 0xffffffff;

    let lo = b.wrapping_mul(d);
    let (mid, carry) = a.wrapping_mul(d).overflowing_add(b.wrapping_mul(c));
    let hi = a.wrapping_mul(c).wrapping_add(if carry { 1 << 32 } else { 0 });

    u128::from_parts(hi, lo).wrapping_add(u128::from_parts(mid >> 32, mid << 32))
}

#[cfg(all(target_arch="x86_64", extprim_channel="unstable"))]
fn u64_long_mul(left: u64, right: u64) -> u128 {
    unsafe {
        let mut result: u128 = ::std::mem::uninitialized();
        llvm_asm!("
            movq $2, %rax
            mulq $3
            movq %rax, $0
            movq %rdx, $1
        "
        : "=r"(result.lo), "=r"(result.hi)
        : "r"(left), "r"(right)
        : "rax", "rdx");
        result
    }
}

impl u128 {
    /// Wrapping (modular) multiplication. Computes `self * other`, wrapping around at the boundary
    /// of the type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).wrapping_mul(u128::new(9)), u128::new(54));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// let b = u128::max_value() - u128::new(4);
    /// assert_eq!(a.wrapping_mul(b), u128::new(15));
    /// ```
    pub fn wrapping_mul(self, other: u128) -> u128 {
        let a = self.hi;
        let b = self.lo;
        let c = other.hi;
        let d = other.lo;
        let mut low = u64_long_mul(b, d);
        let ad = a.wrapping_mul(d);
        let bc = b.wrapping_mul(c);
        low.hi = low.hi.wrapping_add(ad).wrapping_add(bc);
        low
    }

    /// Calculates the multiplication of `self` and `other`.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).overflowing_mul(u128::new(9)), (u128::new(54), false));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// let b = u128::max_value() - u128::new(4);
    /// assert_eq!(a.overflowing_mul(b), (u128::new(15), true));
    /// ```
    pub fn overflowing_mul(self, other: u128) -> (u128, bool) {
        let a = self.hi;
        let b = self.lo;
        let c = other.hi;
        let d = other.lo;

        let (hi, hi_overflow_mul) = match (a, c) {
            (a, 0) => a.overflowing_mul(d),
            (0, c) => c.overflowing_mul(b),
            (a, c) => (a.wrapping_mul(d).wrapping_add(c.wrapping_mul(b)), true),
        };

        let mut low = u64_long_mul(b, d);
        let (hi, hi_overflow_add) = low.hi.overflowing_add(hi);
        low.hi = hi;

        (low, hi_overflow_mul || hi_overflow_add)
    }

    /// Saturating integer multiplication. Computes `self * other`, saturating at the numeric
    /// bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).saturating_mul(u128::new(9)), u128::new(54));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// let b = u128::max_value() - u128::new(4);
    /// assert_eq!(a.saturating_mul(b), u128::max_value());
    /// ```
    pub fn saturating_mul(self, other: u128) -> u128 {
        self.checked_mul(other).unwrap_or(MAX)
    }

    /// Wrapping (modular) multiplication with a 64-bit number. Computes `self * other`, wrapping
    /// around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).wrapping_mul_64(9), u128::new(54));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// assert_eq!(a.wrapping_mul_64(7), u128::max_value() - u128::new(20));
    /// ```
    pub fn wrapping_mul_64(self, other: u64) -> u128 {
        let mut low = u64_long_mul(self.lo, other);
        low.hi = low.hi.wrapping_add(self.hi.wrapping_mul(other));
        low
    }

    /// Calculates the multiplication of `self` and `other` with a 64-bit number.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic
    /// overflow would occur. If an overflow would have occurred then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).overflowing_mul_64(9), (u128::new(54), false));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// assert_eq!(a.overflowing_mul_64(7), (u128::max_value() - u128::new(20), true));
    /// ```
    pub fn overflowing_mul_64(self, other: u64) -> (u128, bool) {
        let mut low = u64_long_mul(self.lo, other);
        let (hi, hi_overflow_mul) = self.hi.overflowing_mul(other);
        let (hi, hi_overflow_add) = low.hi.overflowing_add(hi);
        low.hi = hi;
        (low, hi_overflow_mul || hi_overflow_add)
    }

    /// Saturating integer multiplication with a 64-bit number. Computes `self * other`, saturating
    /// at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).saturating_mul_64(9), u128::new(54));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// assert_eq!(a.saturating_mul_64(7), u128::max_value());
    /// ```
    pub fn saturating_mul_64(self, other: u64) -> u128 {
        self.checked_mul_64(other).unwrap_or(MAX)
    }
}

forward_symmetric!(
    /// Checked integer multiplication. Computes `self * other`, returning `None` if underflow or
    /// overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).checked_mul(u128::new(9)), Some(u128::new(54)));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// let b = u128::max_value() - u128::new(4);
    /// assert_eq!(a.checked_mul(b), None);
    /// ```
    impl Mul(mul, checked_mul, wrapping_mul, overflowing_mul) for u128
);
forward_symmetric!(
    /// Checked integer multiplication with a 64-bit number. Computes `self * other`, returning
    /// `None` if underflow or overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(6).checked_mul_64(9), Some(u128::new(54)));
    ///
    /// let a = u128::max_value() - u128::new(2);
    /// assert_eq!(a.checked_mul_64(7), None);
    /// ```
    impl Mul<u64>(mul, checked_mul_64, wrapping_mul_64, overflowing_mul_64) for u128
);
forward_assign!(MulAssign(mul_assign, mul) for u128);
forward_assign!(MulAssign<u64>(mul_assign, mul) for u128);

impl Mul<u128> for u64 {
    type Output = u128;

    fn mul(self, other: u128) -> u128 {
        other * self
    }
}

impl Mul<Wrapping<u128>> for Wrapping<u64> {
    type Output = Wrapping<u128>;

    fn mul(self, other: Wrapping<u128>) -> Wrapping<u128> {
        other * self
    }
}

impl CheckedMul for u128 {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        Self::checked_mul(*self, *other)
    }
}

#[cfg(test)]
mod mul_tests {
    use std::u64;
    use u128::{u128, u64_long_mul, ZERO, ONE, MAX};

    #[test]
    fn test_u64_long_mul() {
        assert_eq!(u128::from_parts(0xaaa4d56f5b2f577, 0x916fb81166049cc3),
                    u64_long_mul(6263979403966582069, 2263184174907185431));
        assert_eq!(u128::new(10), u64_long_mul(2, 5));
        assert_eq!(u128::from_parts(0xfffffffffffffffe, 1),
                    u64_long_mul(u64::MAX, u64::MAX));
    }

    #[test]
    fn test_mul() {
        assert_eq!(u128::new(6263979403966582069) * u128::new(2263184174907185431),
                    u128::from_parts(0xaaa4d56f5b2f577, 0x916fb81166049cc3));
        assert_eq!(u128::from_parts(47984616521, 3126587552720577884) * u128::new(323057793),
                    u128::from_parts(15501804311280354074, 13195922651658531676));
        assert_eq!(ONE * ONE, ONE);
        assert_eq!(ZERO * ONE, ZERO);
        assert_eq!(ZERO * ZERO, ZERO);
        assert_eq!(MAX * ONE, MAX);
        assert_eq!(MAX * ZERO, ZERO);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_mul_overflow_10_10() {
        let _ = u128::from_parts(1, 0) * u128::from_parts(1, 0);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_mul_overflow_80_80() {
        let _ = u128::from_parts(0x80000000_00000000, 0) * u128::from_parts(0x80000000_00000000, 0);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_mul_overflow_max_max() {
        let _ = MAX * MAX;
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_mul_overflow_max_2() {
        let _ = MAX * u128::new(2);
    }

    #[test]
    fn test_mul_64() {
        assert_eq!(u128::new(6263979403966582069) * 2263184174907185431u64,
                    u128::from_parts(0xaaa4d56f5b2f577, 0x916fb81166049cc3));
        assert_eq!(u128::from_parts(47984616521, 3126587552720577884) * 323057793u64,
                    u128::from_parts(15501804311280354074, 13195922651658531676));
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_mul_64_overflow_max_2() {
        let _ = MAX * 2u64;
    }


    #[test]
    fn test_wrapping_overflowing_mul() {
        let a = u128::from_parts(0xc1b27561c3e63bad, 0x53b0ad364ee597dc);
        let b = u128::from_parts(0x50f5d9a72dd704f3, 0x5ecee7a38577df37);
        let c = u128::from_parts(0xf5651b2427082a5e, 0x0052af17d5e04444);
        assert_eq!(a.wrapping_mul(b), c);
        assert_eq!(a.overflowing_mul(b), (c, true));
        assert_eq!(a.checked_mul(b), None);
        assert_eq!(a.saturating_mul(b), MAX);

        let a = u128::from_parts(15266745824950921091, 7823906177946456204);
        let b = u128::new(8527117857836076447);
        let c = u128::from_parts(15018621813448572278, 1743241062838166260);
        assert_eq!(a.wrapping_mul(b), c);
        assert_eq!(a.overflowing_mul(b), (c, true));
        assert_eq!(a.checked_mul(b), None);
        assert_eq!(a.saturating_mul(b), MAX);

        assert_eq!(b.wrapping_mul(a), c);
        assert_eq!(b.overflowing_mul(a), (c, true));
        assert_eq!(b.checked_mul(a), None);
        assert_eq!(b.saturating_mul(a), MAX);

        assert_eq!(ONE.wrapping_mul(ONE), ONE);
        assert_eq!(ONE.overflowing_mul(ONE), (ONE, false));
        assert_eq!(ONE.checked_mul(ONE), Some(ONE));
        assert_eq!(ONE.saturating_mul(ONE), ONE);

        assert_eq!(MAX.wrapping_mul(ONE), MAX);
        assert_eq!(MAX.overflowing_mul(ONE), (MAX, false));
        assert_eq!(MAX.checked_mul(ONE), Some(MAX));
        assert_eq!(MAX.saturating_mul(ONE), MAX);
    }
}

#[cfg(all(test, extprim_channel="unstable"))]
mod mul_bench {
    use u128::{u128, u64_long_mul};
    use test::{Bencher, black_box};

    const BENCH_LONG_MUL: &'static [u64] = &[
        11738324199100816218, 3625949024665125869, 11861868675607089770, 0,
        6847039601565126724, 5990205122755364850, 9702538440775714705, 1,
        10515012783906113246, 124429589608972701, 16050761648142104263, 2,
        5351676941151834955, 6016449362915734881, 2914632825655711546, 65536,
        7683069626972557929, 2782994233456154833, 4294967296, 281474976710656,
    ];

    const BENCH_MUL: &'static [u128] = &[
        u128 { lo: 13698662153774026983, hi: 11359772643830585857 },
        u128 { lo: 2369395906159065085, hi: 9392107235602601877 },
        u128 { lo: 1316137604845241724, hi: 3387495557620150388 },
        u128 { lo: 4377298216549927656, hi: 4459898349916441418 },
        u128 { lo: 0, hi: 1 },
        u128 { lo: 4002933201893849592, hi: 16874811549516268507 },
        u128 { lo: 13499130554936672837, hi: 7450290244389993204 },
        u128 { lo: 14853481505607028172, hi: 9904715859096779071 },
        u128 { lo: 5904460318883801886, hi: 1039448585925084376 },
        u128 { lo: 2, hi: 0 },
        u128 { lo: 16506484467360819289, hi: 14931546970023365577 },
        u128 { lo: 14721531095705410753, hi: 14699503783417097848 },
        u128 { lo: 10292416800274947511, hi: 14856377574170601940 },
        u128 { lo: 17255829222190888162, hi: 11606899158687852303 },
        u128 { lo: 11087763062048402971, hi: 14746910067372570493 },
        u128 { lo: 4294967296, hi: 4294967296 },
        u128 { lo: 11389837759419328446, hi: 14469025657316200340 },
        u128 { lo: 18363409626181059962, hi: 2420940920506351250 },
        u128 { lo: 18224881384786225007, hi: 15381587162621094041 },
        u128 { lo: 1727909608960628680, hi: 8964631137233999389 }
    ];

    #[bench]
    fn bench_u64_long_mul(bencher: &mut Bencher) {
        bencher.iter(|| {
            for a in BENCH_LONG_MUL {
                for b in BENCH_LONG_MUL.iter() {
                    black_box(u64_long_mul(*a, *b));
                }
            }
        });
    }

    #[bench]
    fn bench_mul(bencher: &mut Bencher) {
        bencher.iter(|| {
            for a in BENCH_MUL {
                for b in BENCH_MUL {
                    black_box(a.wrapping_mul(*b));
                }
            }
        });
    }

    #[bench]
    fn bench_mul_64(bencher: &mut Bencher) {
        bencher.iter(|| {
            for a in BENCH_MUL {
                for b in BENCH_MUL {
                    black_box(a.wrapping_mul_64(b.lo));
                }
            }
        });
    }
}

//}}}

//{{{ Div, Rem

impl u128 {
    /// Wrapping (modular) division. Computes `self / other`. Wrapped division on unsigned types is
    /// just normal division. There's no way wrapping could ever happen. This function exists, so
    /// that all operations are accounted for in the wrapping operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `other` is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).wrapping_div(u128::new(8)), u128::new(12));
    /// ```
    pub fn wrapping_div(self, other: u128) -> u128 {
        self.checked_div(other)
            .unwrap_or_else(|| panic!("attempted to divide by zero"))
    }

    /// Wrapping (modular) remainder. Computes `self % other`. Wrapped remainder calculation on
    /// unsigned types is just the regular remainder calculation. There's no way wrapping could
    /// ever happen. This function exists, so that all operations are accounted for in the wrapping
    /// operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `other` is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).wrapping_rem(u128::new(8)), u128::new(4));
    /// ```
    pub fn wrapping_rem(self, other: u128) -> u128 {
        self.checked_rem(other)
            .unwrap_or_else(|| panic!("attempted remainder with a divisor of zero"))
    }

    /// Calculates the divisor when `self` is divided by `other`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `other` is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).overflowing_div(u128::new(8)), (u128::new(12), false));
    /// ```
    pub fn overflowing_div(self, other: u128) -> (u128, bool) {
        (self.wrapping_div(other), false)
    }

    /// Calculates the remainder when `self` is divided by `other`.
    ///
    /// Returns a tuple of the remainder along with a boolean indicating whether
    /// an arithmetic overflow would occur. Note that for unsigned integers
    /// overflow never occurs, so the second value is always `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `other` is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).overflowing_rem(u128::new(8)), (u128::new(4), false));
    /// ```
    pub fn overflowing_rem(self, other: u128) -> (u128, bool) {
        (self.wrapping_rem(other), false)
    }

    /// Checked integer division. Computes `self / other`, returning `None` if `other == 0`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).checked_div(u128::new(8)), Some(u128::new(12)));
    /// assert_eq!(u128::new(100).checked_div(u128::zero()), None);
    /// ```
    pub fn checked_div(self, other: u128) -> Option<u128> {
        if other == ZERO {
            None
        } else {
            Some(udiv128(self, other))
        }
    }

    /// Checked integer remainder. Computes `self % other`, returning `None` if `other == 0`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::new(100).checked_rem(u128::new(8)), Some(u128::new(4)));
    /// assert_eq!(u128::new(100).checked_rem(u128::zero()), None);
    /// ```
    pub fn checked_rem(self, other: u128) -> Option<u128> {
        if other == ZERO {
            None
        } else {
            Some(umod128(self, other))
        }
    }
}

impl Div for u128 {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self.wrapping_div(other)
    }
}

impl Rem for u128 {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        self.wrapping_rem(other)
    }
}

impl Div for Wrapping<u128> {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        Wrapping(self.0.wrapping_div(other.0))
    }
}

impl Rem for Wrapping<u128> {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        Wrapping(self.0.wrapping_rem(other.0))
    }
}

forward_assign!(DivAssign(div_assign, div) for u128);
forward_assign!(RemAssign(rem_assign, rem) for u128);

impl CheckedDiv for u128 {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        Self::checked_div(*self, *other)
    }
}

/// Computes the divisor and remainder simultaneously. Returns `(a/b, a%b)`.
///
/// Unlike the primitive types, calling this is likely faster than calling `a/b` and `a%b`
/// separately.
///
/// # Panics
///
/// This function will panic if `denominator` is 0.
///
/// # Examples
///
/// ```rust
/// use extprim::u128::{div_rem, u128};
///
/// assert_eq!(div_rem(u128::new(100), u128::new(8)), (u128::new(12), u128::new(4)));
/// ```
pub fn div_rem(numerator: u128, denominator: u128) -> (u128, u128) {
    if denominator == ZERO {
        panic!("attempted to divide by zero");
    } else {
        udivmod128(numerator, denominator)
    }
}

#[cfg(test)]
mod div_rem_tests {
    use u128::{u128, ONE, ZERO, div_rem};

    #[test]
    fn test_div() {
        assert_eq!(u128::from_parts(9071183389512669386, 9598842501673620991) /
                    u128::new(6108228772930395530),
                    u128::from_parts(1, 8948071126007945734));
        assert_eq!(u128::from_parts(3450248868015763521, 12952733755616785885) /
                    u128::new(10250320568692650382),
                    u128::new(6209157794858157762));
        assert_eq!(u128::from_parts(10328265298226767242, 6197012475834382470) /
                    u128::from_parts(3051664430350890703, 4511783754636171344),
                    u128::new(3));

        // Test case copied from https://github.com/rust-lang/rust/issues/41228
        assert_eq!(u128::from_parts(3, 1) / u128::from_parts(3, 0), ONE);
    }

    #[test]
    #[should_panic(expected="attempted to divide by zero")]
    fn test_div_by_zero() {
        let _ = ONE / ZERO;
    }

    #[test]
    fn test_rem() {
        assert_eq!(u128::from_parts(9071183389512669386, 9598842501673620991) %
                    u128::new(6108228772930395530),
                    u128::new(5166992697756803267));
        assert_eq!(u128::from_parts(3450248868015763521, 12952733755616785885) %
                    u128::new(10250320568692650382),
                    u128::new(5507621082750620737));
        assert_eq!(u128::from_parts(10328265298226767242, 6197012475834382470) %
                    u128::from_parts(3051664430350890703, 4511783754636171344),
                    u128::from_parts(1173272007174095132, 11108405285635420054));
    }

    #[test]
    #[should_panic(expected="attempted remainder with a divisor of zero")]
    fn test_rem_by_zero() {
        let _ = ONE % ZERO;
    }

    #[test]
    fn test_div_rem() {
        assert_eq!(div_rem(u128::from_parts(10328265298226767242, 6197012475834382470),
                            u128::from_parts(3051664430350890703, 4511783754636171344)),
                    (u128::new(3),
                        u128::from_parts(1173272007174095132, 11108405285635420054)));
    }
}

//}}}

//{{{ Casting

fn ldexp(base: f64, exp: u32) -> f64 {
    // TODO the built-in `ldexp` is deprecated. Find alternate native implementation instead.
    base * 2.0 * (1u64 << (exp-1)) as f64
}

impl ToPrimitive for u128 {
    fn to_i64(&self) -> Option<i64> {
        if self.hi != 0 {
            None
        } else {
            self.lo.to_i64()
        }
    }

    fn to_u64(&self) -> Option<u64> {
        if self.hi != 0 {
            None
        } else {
            Some(self.lo)
        }
    }

    fn to_f64(&self) -> Option<f64> {
        if self.hi != 0 {
            let shift_size = 64 - self.hi.leading_zeros();
            let truncated = (*self >> shift_size).lo as f64;
            Some(ldexp(truncated, shift_size))
        } else {
            self.lo.to_f64()
        }
    }

    #[cfg(extprim_has_stable_i128)]
    fn to_i128(&self) -> Option<I128> {
        if self.hi < 0x80000000_00000000 {
            Some(self.as_built_in() as I128)
        } else {
            None
        }
    }

    #[cfg(extprim_has_stable_i128)]
    fn to_u128(&self) -> Option<U128> {
        Some(self.as_built_in())
    }
}

impl FromPrimitive for u128 {
    fn from_u64(n: u64) -> Option<u128> {
        ToExtraPrimitive::to_u128(&n)
    }

    fn from_i64(n: i64) -> Option<u128> {
        ToExtraPrimitive::to_u128(&n)
    }

    fn from_f64(n: f64) -> Option<u128> {
        ToExtraPrimitive::to_u128(&n)
    }
}

impl ToExtraPrimitive for u128 {
    fn to_u128(&self) -> Option<u128> {
        Some(*self)
    }

    fn to_i128(&self) -> Option<i128> {
        if self.hi >= 0x8000_0000_0000_0000 {
            None
        } else {
            Some(i128(*self))
        }
    }
}

impl From<u8> for u128 {
    fn from(arg: u8) -> Self {
        u128::new(arg as u64)
    }
}

impl From<u16> for u128 {
    fn from(arg: u16) -> Self {
        u128::new(arg as u64)
    }
}

impl From<u32> for u128 {
    fn from(arg: u32) -> Self {
        u128::new(arg as u64)
    }
}

impl From<u64> for u128 {
    fn from(arg: u64) -> Self {
        u128::new(arg)
    }
}

#[cfg(extprim_has_stable_i128)]
impl From<U128> for u128 {
    fn from(arg: U128) -> Self {
        u128::from_built_in(arg)
    }
}

#[cfg(test)]
mod conv_tests {
    use u128::{u128, MAX};
    use num_traits::ToPrimitive;

    #[test]
    fn test_u128_to_f64() {
        assert_eq!(u128::new(0).to_f64(), Some(0.0f64));
        assert_eq!(u128::new(1).to_f64(), Some(1.0f64));
        assert_eq!(u128::new(2).to_f64(), Some(2.0f64));
        assert_eq!(MAX.to_f64(), Some(340282366920938463463374607431768211455.0f64));
    }

    #[test]
    #[cfg(extprim_has_stable_i128)]
    fn test_builtin_u128_to_u128() {
        assert_eq!(u128::from_built_in(0x35d2c4473082b8c1_8b704240ca1021b8u128), u128::from_parts(0x35d2c4473082b8c1, 0x8b704240ca1021b8));
        assert_eq!(u128::from_parts(0x35d2c4473082b8c1, 0x8b704240ca1021b8).as_built_in(), 0x35d2c4473082b8c1_8b704240ca1021b8u128);
    }
}

//}}}

//{{{ Constants

impl u128 {
    /// Returns the smallest unsigned 128-bit integer (0).
    pub fn min_value() -> u128 { MIN }

    /// Returns the largest unsigned 128-bit integer
    /// (`340_282_366_920_938_463_463_374_607_431_768_211_455`).
    pub fn max_value() -> u128 { MAX }

    /// Returns the constant 0.
    pub fn zero() -> u128 { ZERO }

    /// Returns the constant 1.
    pub fn one() -> u128 { ONE }
}

impl Bounded for u128 {
    fn min_value() -> Self { MIN }
    fn max_value() -> Self { MAX }
}

impl Zero for u128 {
    fn zero() -> Self { ZERO }
    fn is_zero(&self) -> bool { *self == ZERO }
}

impl One for u128 {
    fn one() -> Self { ONE }
}

//}}}

//{{{ PrimInt

impl u128 {
    /// Returns the number of ones in the binary representation of `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let n = u128::from_str_radix("6f32f1ef8b18a2bc3cea59789c79d441", 16).unwrap();
    /// assert_eq!(n.count_ones(), 67);
    /// ```
    pub fn count_ones(self) -> u32 {
        self.lo.count_ones() + self.hi.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self` (including leading zeros).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let n = u128::from_str_radix("6f32f1ef8b18a2bc3cea59789c79d441", 16).unwrap();
    /// assert_eq!(n.count_zeros(), 61);
    /// ```
    pub fn count_zeros(self) -> u32 {
        self.lo.count_zeros() + self.hi.count_zeros()
    }

    /// Returns the number of leading zeros in the binary representation of `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::zero().leading_zeros(), 128);
    /// assert_eq!(u128::one().leading_zeros(), 127);
    /// assert_eq!(u128::max_value().leading_zeros(), 0);
    /// assert_eq!((u128::one() << 24u32).leading_zeros(), 103);
    /// assert_eq!((u128::one() << 124u32).leading_zeros(), 3);
    /// ```
    pub fn leading_zeros(self) -> u32 {
        if self.hi == 0 {
            64 + self.lo.leading_zeros()
        } else {
            self.hi.leading_zeros()
        }
    }

    /// Returns the number of trailing zeros in the binary representation of `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::zero().trailing_zeros(), 128);
    /// assert_eq!(u128::one().trailing_zeros(), 0);
    /// assert_eq!((u128::one() << 24u32).trailing_zeros(), 24);
    /// assert_eq!((u128::one() << 124u32).trailing_zeros(), 124);
    /// ```
    pub fn trailing_zeros(self) -> u32 {
        if self.lo == 0 {
            64 + self.hi.trailing_zeros()
        } else {
            self.lo.trailing_zeros()
        }
    }

    /// Shifts the bits to the left by a specified amount, `shift`, wrapping the truncated bits to
    /// the end of the resulting integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let a = u128::from_str_radix("d0cf4b50cfe20765fff4b4e3f741cf6d", 16).unwrap();
    /// let b = u128::from_str_radix("19e96a19fc40ecbffe969c7ee839edba", 16).unwrap();
    /// assert_eq!(a.rotate_left(5), b);
    /// ```
    pub fn rotate_left(self, shift: u32) -> Self {
        let rotated = match shift & 63 {
            0 => self,
            n => u128 {
                lo: self.lo << n | self.hi >> 64u32.wrapping_sub(n),
                hi: self.hi << n | self.lo >> 64u32.wrapping_sub(n),
            },
        };
        if shift & 64 == 0 {
            rotated
        } else {
            u128 { lo: rotated.hi, hi: rotated.lo }
        }
    }

    /// Shifts the bits to the right by a specified amount, `shift`, wrapping the truncated bits to
    /// the beginning of the resulting integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let a = u128::from_str_radix("d0cf4b50cfe20765fff4b4e3f741cf6d", 16).unwrap();
    /// let b = u128::from_str_radix("6e867a5a867f103b2fffa5a71fba0e7b", 16).unwrap();
    /// assert_eq!(a.rotate_right(5), b);
    /// ```
    pub fn rotate_right(self, shift: u32) -> Self {
        self.rotate_left(128u32.wrapping_sub(shift))
    }

    /// Reverses the byte order of the integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use extprim::u128::u128;
    ///
    /// let a = u128::from_str_radix("0123456789abcdef1112223334445556", 16).unwrap();
    /// let b = u128::from_str_radix("5655443433221211efcdab8967452301", 16).unwrap();
    /// assert_eq!(a.swap_bytes(), b);
    /// ```
    pub fn swap_bytes(self) -> Self {
        u128 { lo: self.hi.swap_bytes(), hi: self.lo.swap_bytes() }
    }

    /// Converts an integer from big endian to the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    pub fn from_be(x: Self) -> Self {
        if cfg!(target_endian="big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts an integer from little endian to the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    pub fn from_le(x: Self) -> Self {
        if cfg!(target_endian="little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts `self` to big endian from the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    pub fn to_be(self) -> Self {
        Self::from_be(self)
    }

    /// Converts self to little endian from the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    pub fn to_le(self) -> Self {
        Self::from_le(self)
    }

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    ///
    /// # Examples
    ///
    /// ```
    /// use extprim::u128::u128;
    /// use std::str::FromStr;
    ///
    /// assert_eq!(u128::new(5).pow(30), u128::from_str("931322574615478515625").unwrap());
    /// ```
    pub fn pow(self, exp: u32) -> Self {
        pow(self, exp as usize)
    }

    /// Returns `true` if and only if `self == 2**k` for some `k`.
    ///
    /// # Examples
    ///
    /// ```
    /// use extprim::u128::u128;
    ///
    /// assert!(!u128::new(0).is_power_of_two());
    /// assert!( u128::new(1).is_power_of_two());
    /// assert!( u128::new(2).is_power_of_two());
    /// assert!(!u128::new(3).is_power_of_two());
    /// ```
    pub fn is_power_of_two(self) -> bool {
        self != ZERO && (self & self.wrapping_sub(ONE)) == ZERO
    }

    /// Returns the smallest power of two greater than or equal to `self`. Unspecified behavior on
    /// overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::zero().next_power_of_two(), u128::new(1));
    /// assert_eq!(u128::one().next_power_of_two(), u128::new(1));
    /// assert_eq!(u128::new(384).next_power_of_two(), u128::new(512));
    /// assert_eq!(u128::new(0x80000000_00000001).next_power_of_two(), u128::from_parts(1, 0));
    /// assert_eq!(u128::from_parts(0x80000000_00000000, 0).next_power_of_two(), u128::from_parts(0x80000000_00000000, 0));
    /// ```
    pub fn next_power_of_two(self) -> Self {
        let leading_zeros = self.wrapping_sub(ONE).leading_zeros();
        ONE.wrapping_shl(128 - leading_zeros)
    }

    /// Returns the smallest power of two greater than or equal to `self`. If the next power of two
    /// is greater than the type's maximum value, `None` is returned, otherwise the power of two is
    /// wrapped in `Some`.
    ///
    /// # Examples
    ///
    /// ```
    /// use extprim::u128::u128;
    ///
    /// assert_eq!(u128::zero().checked_next_power_of_two(), Some(u128::new(1)));
    /// assert_eq!(u128::one().checked_next_power_of_two(), Some(u128::new(1)));
    /// assert_eq!(u128::new(384).checked_next_power_of_two(), Some(u128::new(512)));
    /// assert_eq!(u128::new(0x80000000_00000001).checked_next_power_of_two(), Some(u128::from_parts(1, 0)));
    /// assert_eq!(u128::from_parts(0x80000000_00000000, 0).checked_next_power_of_two(), Some(u128::from_parts(0x80000000_00000000, 0)));
    /// assert_eq!(u128::from_parts(0x80000000_00000000, 1).checked_next_power_of_two(), None);
    /// assert_eq!(u128::max_value().checked_next_power_of_two(), None);
    /// ```
    pub fn checked_next_power_of_two(self) -> Option<Self> {
        if self == ZERO {
            Some(ONE)
        } else {
            let leading_zeros = self.wrapping_sub(ONE).leading_zeros();
            ONE.checked_shl(128 - leading_zeros)
        }
    }
}

impl PrimInt for u128 {
    fn count_ones(self) -> u32 { Self::count_ones(self) }
    fn count_zeros(self) -> u32 { Self::count_zeros(self) }
    fn leading_zeros(self) -> u32 { Self::leading_zeros(self) }
    fn trailing_zeros(self) -> u32 { Self::trailing_zeros(self) }
    fn rotate_left(self, shift: u32) -> Self { Self::rotate_left(self, shift) }
    fn rotate_right(self, shift: u32) -> Self { Self::rotate_right(self, shift) }
    fn swap_bytes(self) -> Self { Self::swap_bytes(self) }
    fn from_be(x: Self) -> Self { Self::from_be(x) }
    fn from_le(x: Self) -> Self { Self::from_le(x) }
    fn to_be(self) -> Self { Self::to_be(self) }
    fn to_le(self) -> Self { Self::to_le(self) }
    fn pow(self, exp: u32) -> Self { Self::pow(self, exp) }

    fn signed_shl(self, shift: u32) -> Self {
        self << (shift as usize)
    }

    fn signed_shr(self, shift: u32) -> Self {
        (i128(self) >> (shift as usize)).0
    }

    fn unsigned_shl(self, shift: u32) -> Self {
        self << (shift as usize)
    }

    fn unsigned_shr(self, shift: u32) -> Self {
        self >> (shift as usize)
    }
}

impl Unsigned for u128 {
}

#[cfg(test)]
mod prim_int_tests {
    use std::u64;
    use u128::{u128, MAX, ZERO, ONE};

    #[test]
    fn test_rotate() {
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152).rotate_right(0),
                    u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152).rotate_right(1),
                    u128::from_parts(0xf2e3c00d872bafb, 0xa9f84ed62d9478a9));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152).rotate_right(3),
                    u128::from_parts(0x43cb8f00361caebe, 0xea7e13b58b651e2a));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152).rotate_right(64),
                    u128::from_parts(0x53f09dac5b28f152, 0x1e5c7801b0e575f7));
        assert_eq!(u128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152).rotate_right(120),
                    u128::from_parts(0x5c7801b0e575f753, 0xf09dac5b28f1521e));
    }

    #[test]
    fn test_swap_bytes() {
        assert_eq!(u128::from_parts(0xf0d6891695897d01, 0xb6e2f3a4b065e277).swap_bytes(),
                    u128::from_parts(0x77e265b0a4f3e2b6, 0x017d89951689d6f0));
    }

    #[test]
    fn test_leading_zeros() {
        assert_eq!(u128::from_parts(1, 0).leading_zeros(), 63);
        assert_eq!(u128::from_parts(1, 4).leading_zeros(), 63);
        assert_eq!(u128::from_parts(0, 1).leading_zeros(), 127);
        assert_eq!(u128::from_parts(0, 0).leading_zeros(), 128);
    }

    #[test]
    fn test_trailing_zeros() {
        assert_eq!(u128::from_parts(1, 0).trailing_zeros(), 64);
        assert_eq!(u128::from_parts(3, 0).trailing_zeros(), 64);
        assert_eq!(u128::from_parts(1, 4).trailing_zeros(), 2);
        assert_eq!(u128::from_parts(0, 1).trailing_zeros(), 0);
        assert_eq!(u128::from_parts(0, 0).trailing_zeros(), 128);
    }

    #[test]
    fn test_checked_add() {
        assert_eq!(Some(u128::from_parts(u64::MAX, 0)),
                    u128::from_parts(u64::MAX-1, u64::MAX)
                        .checked_add(u128::new(1)));
        assert_eq!(Some(u128::from_parts(u64::MAX, 0)), u128::new(1)
                        .checked_add(u128::from_parts(u64::MAX-1, u64::MAX)));
        assert_eq!(None, u128::from_parts(u64::MAX, 1)
                        .checked_add(u128::from_parts(u64::MAX, 2)));
        assert_eq!(None, MAX.checked_add(u128::new(1)));
    }

    #[test]
    fn test_checked_sub() {
        assert_eq!(None, ZERO.checked_sub(ONE));
        assert_eq!(None, ZERO.checked_sub(MAX));
        assert_eq!(None, ONE.checked_sub(MAX));
        assert_eq!(Some(ONE), ONE.checked_sub(ZERO));
        assert_eq!(Some(MAX), MAX.checked_sub(ZERO));
        assert_eq!(Some(MAX-ONE), MAX.checked_sub(ONE));
    }

    #[test]
    fn test_checked_mul() {
        assert_eq!(Some(ONE), ONE.checked_mul(ONE));
        assert_eq!(Some(MAX), MAX.checked_mul(ONE));
        assert_eq!(None, MAX.checked_mul(MAX));
        assert_eq!(None, MAX.checked_mul(u128::new(2)));
        assert_eq!(None, u128::from_parts(1, 0).checked_mul(u128::from_parts(1, 0)));
        let res = u128::from_parts(u64::MAX-1, 1);
        assert_eq!(Some(res), u128::new(u64::MAX).checked_mul(u128::new(u64::MAX)));
    }

    #[test]
    fn test_checked_div() {
        assert_eq!(Some(ONE), ONE.checked_div(ONE));
        assert_eq!(Some(MAX), MAX.checked_div(ONE));
        assert_eq!(Some(ZERO), ONE.checked_div(MAX));
        assert_eq!(Some(ZERO), ZERO.checked_div(MAX));
        assert_eq!(None, ONE.checked_div(ZERO));
        assert_eq!(None, MAX.checked_div(ZERO));
    }

    #[test]
    fn test_checked_next_power_of_two() {
        assert_eq!(u128::from_parts(0, 0x80000000_00000000).next_power_of_two(),
                    u128::from_parts(0, 0x80000000_00000000));
        assert_eq!(u128::from_parts(0, 0x80000000_00000001).next_power_of_two(),
                    u128::from_parts(1, 0));
        assert_eq!(u128::from_parts(1, 0).next_power_of_two(),
                    u128::from_parts(1, 0));
        assert_eq!(u128::from_parts(1, 1).next_power_of_two(),
                    u128::from_parts(2, 0));
        assert_eq!(u128::from_parts(0x80000000_00000000, 0).checked_next_power_of_two(),
                    Some(u128::from_parts(0x80000000_00000000, 0)));
        assert_eq!(u128::from_parts(0x80000000_00000000, 1).checked_next_power_of_two(),
                    None);
        assert_eq!(u128::from_parts(0x80000000_00000001, 0).checked_next_power_of_two(),
                    None);

    }
}

#[cfg(all(test, extprim_channel="unstable"))]
mod checked_add_sub_bench {
    use u128::u128;
    use test::{Bencher, black_box};

    const BENCH_CHECKED_ADD_SUB: &'static [u128] = &[
        u128 { lo: 8530639231766041497, hi: 1287710968871074399 },
        u128 { lo: 1203542656178406941, hi: 17699966409461566340 },
        u128 { lo: 718458371035876551, hi: 3606247509203879903 },
        u128 { lo: 9776046594219398139, hi: 11242044896228553946 },
        u128 { lo: 7902474877314354323, hi: 15571658655527718712 },
        u128 { lo: 12666717328207407901, hi: 18395053205720380381 },
        u128 { lo: 17339836091522731855, hi: 15731019889221707237 },
        u128 { lo: 8366128025082480321, hi: 13984191269538716594 },
        u128 { lo: 8593645006461074455, hi: 10189081980804969201 },
        u128 { lo: 8264027155501625330, hi: 6198464561866207623 },
        u128 { lo: 10849132074109635036, hi: 5777302818880052808 },
        u128 { lo: 8053806942953838280, hi: 4617639587817452744 },
        u128 { lo: 7575409236673560956, hi: 10773137480165156891 },
        u128 { lo: 4323210863932108621, hi: 16058751318664008901 },
        u128 { lo: 336314576898396552, hi: 8743495691718489785 },
        u128 { lo: 6527874161908570477, hi: 926686061690459595 },
        u128 { lo: 15442937728615642560, hi: 2666553580477360520 },
        u128 { lo: 11855805362816810591, hi: 17643219502201004064 },
        u128 { lo: 16313274500479459547, hi: 5436651574417345289 },
        u128 { lo: 15008613641935618684, hi: 12105224025714335156 },
    ];

    #[bench]
    fn bench_checked_add(bencher: &mut Bencher) {
        bencher.iter(|| {
            for a in BENCH_CHECKED_ADD_SUB {
                for b in BENCH_CHECKED_ADD_SUB {
                    black_box(a.checked_add(*b));
                }
            }
        })
    }

    #[bench]
    fn bench_checked_sub(bencher: &mut Bencher) {
        bencher.iter(|| {
            for a in BENCH_CHECKED_ADD_SUB {
                for b in BENCH_CHECKED_ADD_SUB {
                    black_box(a.checked_sub(*b));
                }
            }
        })
    }
}


//}}}

//{{{ FromStr, FromStrRadix

impl u128 {
    /// Converts a string slice in a given base to an integer.
    ///
    /// Leading and trailing whitespace represent an error.
    ///
    /// # Arguments
    ///
    /// - src: A string slice
    /// - radix: The base to use. Must lie in the range [2 ... 36].
    ///
    /// # Return value
    ///
    /// `Err(ParseIntError)` if the string did not represent a valid number. Otherwise, `Ok(n)`
    /// where `n` is the integer represented by `src`.
    pub fn from_str_radix(src: &str, radix: u32) -> Result<u128, ParseIntError> {
        assert!(radix >= 2 && radix <= 36,
                "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
                radix);

        if src.is_empty() {
            return Err(error::empty());
        }

        let mut result = ZERO;
        let radix64 = radix as u64;

        for c in src.chars() {
            let digit = c.to_digit(radix).ok_or_else(error::invalid_digit)?;
            let int_result = result.checked_mul_64(radix64).ok_or_else(error::overflow)?;
            let digit128 = u128::new(digit as u64);
            result = int_result.checked_add(digit128).ok_or_else(error::overflow)?;
        }

        Ok(result)
    }
}

impl Num for u128 {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, radix)
    }
}

impl FromStr for u128 {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, 10)
    }
}

#[cfg(test)]
mod from_str_tests {
    use u128::{u128, MAX, ZERO};
    use error;

    #[test]
    fn test_from_str_radix() {
        const TEST_RESULTS: &'static [&'static str] = &[
            "10011011100100101101000110001011110001010011011101110001100111001000101000101101010100100100010100111001011101010000110001010101",
            "110120222012101010211220122102022000210010022000111102212102202222012022120111212",
            "2123210231012023301103131301213020220231110210110321131100301111",
            "3330311440012420033140113104304110413013304434422141400",
            "13113233024433543105511522325553410033343505511205",
            "1634565460422653144356213116334346545422433412",
            "2334455061361233561471050552444247135206125",
            "13528171124818368023108014385382865276455",
            "206792664785365372185662205006093552725",
            "67649064a7890404084060a25479431a98470",
            "360187787119a95bb767ba32bb0a5b642505",
            "29c058245bb23487574aca216c29577b882",
            "3184907b028135c9183b72cdac9c103109",
            "4bd69b73d8a16036ebec88cd6bb33d335",
            "9b92d18bc537719c8a2d524539750c55",
            "1840gefbd6g31a6ecgg7gc50bd70g1g7",
            "49dheg38e0608a9f4a9267e4g4aagg5",
            "h0h83ahe8172ah96d68dfe26e94124",
            "3h0ea36ada20a526i53ee31044e1g5",
            "jde641e697f962kkidc27ce2edcj2",
            "57bb2c3jgc5h08a1ga70l48l6hc3b",
            "1c8ma26907bj977e8j19da70g8h9e",
            "b547gj6f5egh808nmcnebbeji765",
            "3i36o07m0i9185n46481i4noc990",
            "17f9kaldpa569n4p5gagei47konf",
            "cfq5a3mohb80l380dbnbkq58fdn",
            "4oqm8ncn25iij172m7giopbaol9",
            "1rrq11r63qkjr4s06jq142klq23",
            "oc5mpkf55e6kpj97prm765q0o5",
            "an9nde76jttn4ifukgsdinhsc8",
            "4rib8onh9ne6e8kbai8ksna32l",
            "28b35bg89n93in6l8rfpijv92b",
            "12ajr3pwad0qofcfuk1wbutlp7",
            "i3svxg6wovmba6en6lp37x4cu",
            "97kl2slyj5vbekzxp0lmn5v85",
        ];

        let v = u128::from_parts(11210252820717990300, 9956704808456227925);

        for (base2, res) in TEST_RESULTS.iter().enumerate() {
            assert_eq!(Ok(v), u128::from_str_radix(*res, (base2+2) as u32));
        }

        assert_eq!(Ok(ZERO), u128::from_str_radix("0", 2));
        assert_eq!(Ok(ZERO), u128::from_str_radix("0000000000000000000000000000000000", 36));
        assert_eq!(Err(error::invalid_digit()), u128::from_str_radix("123", 3));
        assert_eq!(Err(error::invalid_digit()), u128::from_str_radix("-1", 10));
        assert_eq!(Err(error::empty()), u128::from_str_radix("", 10));
        assert_eq!(Ok(MAX), u128::from_str_radix("f5lxx1zz5pnorynqglhzmsp33", 36));
        assert_eq!(Err(error::overflow()), u128::from_str_radix("f5lxx1zz5pnorynqglhzmsp34", 36));
        assert_eq!(Err(error::overflow()), u128::from_str_radix("f5lxx1zz5pnorynqglhzmsp43", 36));
    }
}

//}}}

//{{{ Binary, LowerHex, UpperHex, Octal, String, Show

impl fmt::Display for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if self.hi == 0 {
            self.lo.fmt(formatter)
        } else {
            const TEN19: u128 = u128 { lo: 10000000000000000000, hi: 0 };

            let mut buffer = [0u8; 39];
            let mut buf = FormatBuffer::new(&mut buffer);

            let (mid, lo) = div_rem(*self, TEN19);
            if mid.hi == 0 {
                write!(&mut buf, "{}{:019}", mid.lo, lo.lo)?;
            } else {
                let (hi, mid) = div_rem(mid, TEN19);
                write!(&mut buf, "{}{:019}{:019}", hi.lo, mid.lo, lo.lo)?;
            }

            formatter.pad_integral(true, "", unsafe { buf.into_str() })
        }
    }
}

impl fmt::Debug for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "u128!({})", self)
    }
}

impl fmt::Binary for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if self.hi == 0 {
            self.lo.fmt(formatter)
        } else {
            let mut buffer = [0u8; 128];
            let mut buf = FormatBuffer::new(&mut buffer);

            write!(&mut buf, "{:b}{:064b}", self.hi, self.lo)?;
            formatter.pad_integral(true, "0b", unsafe { buf.into_str() })
        }
    }
}

impl fmt::LowerHex for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if self.hi == 0 {
            self.lo.fmt(formatter)
        } else {
            let mut buffer = [0u8; 32];
            let mut buf = FormatBuffer::new(&mut buffer);

            write!(&mut buf, "{:x}{:016x}", self.hi, self.lo)?;
            formatter.pad_integral(true, "0x", unsafe { buf.into_str() })
        }
    }
}

impl fmt::UpperHex for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if self.hi == 0 {
            self.lo.fmt(formatter)
        } else {
            let mut buffer = [0u8; 32];
            let mut buf = FormatBuffer::new(&mut buffer);

            write!(&mut buf, "{:X}{:016X}", self.hi, self.lo)?;
            formatter.pad_integral(true, "0x", unsafe { buf.into_str() })
        }
    }
}

impl fmt::Octal for u128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        const MASK: u64 = (1 << 63) - 1;

        let lo = self.lo & MASK;
        let mid = (self.hi << 1 | self.lo >> 63) & MASK;
        let hi = self.hi >> 62;

        let mut buffer = [0u8; 43];
        let mut buf = FormatBuffer::new(&mut buffer);

        if hi != 0 {
            write!(&mut buf, "{:o}{:021o}{:021o}", hi, mid, lo)?;
        } else if mid != 0 {
            write!(&mut buf, "{:o}{:021o}", mid, lo)?;
        } else {
            return lo.fmt(formatter);
        }

        formatter.pad_integral(true, "0o", unsafe { buf.into_str() })
    }
}

#[cfg(test)]
mod show_tests {
    use u128::{u128, MAX};

    #[test]
    fn test_display() {
        assert_fmt_eq!("0", 1,
                       "{}", u128::new(0));
        assert_fmt_eq!("10578104835920319894", 20,
                       "{}", u128::new(10578104835920319894));
        assert_fmt_eq!("91484347284476727216111035283008240438", 38,
                       "{}", u128::from_parts(4959376403712401289, 46322452157807414));
        assert_fmt_eq!("221073131124184722582670274216994227164", 39,
                       "{}", u128::from_parts(11984398452150693167, 12960002013829219292));
        assert_fmt_eq!("340282366920938463463374607431768211455", 39,
                       "{}", MAX);
        assert_fmt_eq!("100000000000000000000000000000000000000", 39,
                       "{}", u128::from_parts(5421010862427522170, 687399551400673280));
        assert_fmt_eq!("+00340282366920938463463374607431768211455", 42,
                       "{:+042}", MAX);
    }

    #[test]
    fn test_binary() {
        assert_fmt_eq!("0", 1,
                       "{:b}", u128::new(0));
        assert_fmt_eq!("111001011001111000111001100100010100111010010001110101100101011", 63,
                       "{:b}", u128::new(8272862688628501291));
        assert_fmt_eq!("10101011011101011000001011010101101001110110100010000100010001111001010100010010110000000000100100101001100100010110111010011011", 128,
                       "{:b}", u128::from_parts(12354925006909113415, 10741859206816689819));
        assert_fmt_eq!("10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", 128,
                       "{:b}", u128::from_parts(9223372036854775808, 0));
        assert_fmt_eq!("11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", 128,
                       "{:b}", MAX);
    }

    #[test]
    fn test_hex() {
        assert_fmt_eq!("0", 1,
                       "{:x}", u128::new(0));
        assert_fmt_eq!("25c22f8602efedb5", 16,
                       "{:x}", u128::new(2720789377506602421));
        assert_fmt_eq!("2c73d4b3d1a46f081a04e1ea9846faee", 32,
                       "{:x}", u128::from_parts(3203137628772003592, 1874871742586354414));
        assert_fmt_eq!("80000000000000000000000000000000", 32,
                       "{:x}", u128::from_parts(9223372036854775808, 0));
        assert_fmt_eq!(" 0xA", 4,
                       "{:#4X}", u128::new(10));
        assert_fmt_eq!("25C22F8602EFEDB5", 16,
                       "{:X}", u128::new(2720789377506602421));
        assert_fmt_eq!("2C73D4B3D1A46F081A04E1EA9846FAEE", 32,
                       "{:X}", u128::from_parts(3203137628772003592, 1874871742586354414));
        assert_fmt_eq!("C000000000000000000000000000000", 31,
                       "{:X}", u128::from_parts(864691128455135232, 0));
    }

    #[test]
    fn test_octal() {
        assert_fmt_eq!("0", 1,
                       "{:o}", u128::new(0));
        assert_fmt_eq!("351462366146756037170", 21,
                       "{:o}", u128::new(4208138189379485304));
        assert_fmt_eq!("7000263630010212417200", 22,
                       "{:o}", u128::from_parts(3, 9229698078115241600));
        assert_fmt_eq!("3465177151267706210351536216110755202064135", 43,
                       "{:o}", u128::from_parts(16620520452737763444, 15533412710015854685));
        assert_fmt_eq!("3777777777777777777777777777777777777777777", 43,
                       "{:o}", u128::from_parts(18446744073709551615, 18446744073709551615));
        assert_fmt_eq!("2000000000000000000000000000000000000000000", 43,
                       "{:o}", u128::from_parts(9223372036854775808, 0));
    }
}

//}}}

//{{{ Sum, Product

impl Sum for u128 {
    fn sum<I>(iter: I) -> Self
        where I: Iterator<Item = Self>
    {
        iter.fold(ZERO, Add::add)
    }
}

impl Product for u128 {
    fn product<I>(iter: I) -> Self
        where I: Iterator<Item = Self>
    {
        iter.fold(ONE, Mul::mul)
    }
}

impl<'a> Sum<&'a u128> for u128 {
    fn sum<I>(iter: I) -> Self
        where I: Iterator<Item = &'a Self>
    {
        iter.fold(ZERO, |acc, elem| acc + *elem)
    }
}

impl<'a> Product<&'a u128> for u128 {
    fn product<I>(iter: I) -> Self
        where I: Iterator<Item = &'a Self>
    {
        iter.fold(ONE, |acc, elem| acc * *elem)
    }
}

#[cfg(test)]
mod iter_tests {
    use u128::{u128, ZERO, ONE, MIN, MAX};

    #[test]
    fn test_sum() {
        // Sum<u128>
        assert_eq!(ZERO, Vec::<u128>::new().into_iter().sum());
        assert_eq!(ZERO, vec![ZERO, ZERO, ZERO].into_iter().sum());
        assert_eq!(ONE, vec![ONE].into_iter().sum());
        assert_eq!(u128::from(3u64), vec![ONE, ONE, ONE].into_iter().sum());
        assert_eq!(MAX, vec![MAX].into_iter().sum());
        assert_eq!(MIN, vec![MIN].into_iter().sum());
        assert_eq!(u128::from_parts(7, 42), vec![u128::from_parts(7, 42)].into_iter().sum());

        // Sum<&'a u128>
        assert_eq!(ZERO, [].iter().sum());
        assert_eq!(ZERO, [ZERO, ZERO, ZERO].iter().sum());
        assert_eq!(ONE, [ONE].iter().sum());
        assert_eq!(u128::from(3u64), [ONE, ONE, ONE].iter().sum());
        assert_eq!(MAX, [MAX].iter().sum());
        assert_eq!(MIN, [MIN].iter().sum());
        assert_eq!(u128::from_parts(7, 42), [u128::from_parts(7, 42)].iter().sum());
    }

    #[test]
    fn test_product() {
        // Product<u128>
        assert_eq!(ONE, Vec::<u128>::new().into_iter().product());
        assert_eq!(ONE, vec![ONE, ONE, ONE, ONE, ONE, ONE].into_iter().product());
        assert_eq!(ZERO, vec![ONE, MAX, ZERO].into_iter().product());
        assert_eq!(MAX, vec![MAX].into_iter().product());
        assert_eq!(MAX, vec![ONE, MAX].into_iter().product());
        assert_eq!(MIN, vec![MIN].into_iter().product());
        assert_eq!(MIN, vec![ONE, MIN].into_iter().product());
        assert_eq!(MAX, vec![
            u128::from(3u64),
            u128::from(5u64),
            u128::from(17u64),
            u128::from(257u64),
            u128::from(641u64),
            u128::from(65537u64),
            u128::from(274177u64),
            u128::from(6700417u64),
            u128::from(67280421310721u64),
        ].into_iter().product());

        // Product<&'a u128>
        assert_eq!(ONE, [].iter().product());
        assert_eq!(ONE, [ONE, ONE, ONE, ONE, ONE, ONE].iter().product());
        assert_eq!(ZERO, [ONE, MAX, ZERO].iter().product());
        assert_eq!(MAX, [MAX].iter().product());
        assert_eq!(MAX, [ONE, MAX].iter().product());
        assert_eq!(MIN, [MIN].iter().product());
        assert_eq!(MIN, [ONE, MIN].iter().product());
        assert_eq!(MAX, [
            u128::from(3u64),
            u128::from(5u64),
            u128::from(17u64),
            u128::from(257u64),
            u128::from(641u64),
            u128::from(65537u64),
            u128::from(274177u64),
            u128::from(6700417u64),
            u128::from(67280421310721u64),
        ].iter().product());
    }
}

//}}}

