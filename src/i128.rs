//! Signed 128-bit integer.

use std::str::FromStr;
use std::fmt;
use std::ops::*;
use std::cmp::{PartialOrd, Ord, Ordering};
use std::num::ParseIntError;

use rand::{Rand, Rng};
use num_traits::*;

use u128::u128;
use error;
use traits::{ToExtraPrimitive, Wrapping};

//{{{ Structure

/// Number of bits a signed 128-bit number occupies.
pub const BITS: usize = 128;

/// Number of bytes a signed 128-bit number occupies.
pub const BYTES: usize = 16;

/// The smallest signed 128-bit integer
/// (`-170_141_183_460_469_231_731_687_303_715_884_105_728`).
pub const MIN: i128 = i128(u128 { lo: 0, hi: 0x8000000000000000 });

/// The largest signed 128-bit integer
/// (`170_141_183_460_469_231_731_687_303_715_884_105_727`).
pub const MAX: i128 = i128(u128 { lo: !0, hi: 0x7fffffffffffffff });

/// The constant 0.
pub const ZERO: i128 = i128(::u128::ZERO);

/// The constant 1.
pub const ONE: i128 = i128(::u128::ONE);

/// An signed 128-bit number.
#[derive(Default, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
#[allow(non_camel_case_types)]
pub struct i128(
    #[doc(hidden)]
    pub u128,
);

impl i128 {
    /// Constructs a new 128-bit integer from a 64-bit integer.
    pub fn new(lo: i64) -> i128 {
        i128(u128 { lo: lo as u64, hi: (lo >> 63) as u64 })
    }

    /// Constructs a new 128-bit integer from the high-64-bit and low-64-bit
    /// parts.
    ///
    /// ```
    /// use extprim::i128::i128;
    /// let number = i128::from_parts(-6692605943, 4362896299872285998);
    /// assert_eq!(format!("{}", number), "-123456789012345678901234567890");
    /// // Note: -123456789012345678901234567890 = -6692605943 << 64 | 4362896299872285998
    /// ```
    pub fn from_parts(hi: i64, lo: u64) -> i128 {
        i128(u128 { lo: lo, hi: hi as u64 })
    }

    /// Fetch the lower-64-bit of the number.
    pub fn low64(self) -> u64 {
        self.0.lo
    }

    /// Fetch the higher-64-bit of the number.
    pub fn high64(self) -> i64 {
        self.0.hi as i64
    }

    /// Convert this number to unsigned without checking.
    pub fn as_u128(self) -> u128 {
        self.0
    }
}

#[cfg(test)]
mod structure_tests {
    use i128::i128;
    use std::i64;

    #[test]
    fn test_new() {
        assert_eq!(i128::from_parts(0, 66), i128::new(66));
        assert_eq!(i128::from_parts(-1, !65), i128::new(-66));
        assert_eq!(i128::from_parts(-1, 0x8000000000000000), i128::new(i64::MIN));
    }
}

//}}}

//{{{ Rand

impl Rand for i128 {
    fn rand<R: Rng>(rng: &mut R) -> i128 {
        i128(u128::rand(rng))
    }
}

//}}}

//{{{ Add, Sub

impl i128 {
    pub fn wrapping_add(self, other: i128) -> i128 {
        i128(self.0.wrapping_add(other.0))
    }

    pub fn wrapping_sub(self, other: i128) -> i128 {
        i128(self.0.wrapping_sub(other.0))
    }

    pub fn wrapping_neg(self) -> i128 {
        i128(self.0.wrapping_neg())
    }

    pub fn overflowing_add(self, other: i128) -> (i128, bool) {
        let left_sign = self.is_negative();
        let right_sign = other.is_negative();
        let res = self.wrapping_add(other);
        let res_sign = res.is_negative();
        (res, left_sign == right_sign && res_sign != left_sign)
    }

    pub fn overflowing_sub(self, other: i128) -> (i128, bool) {
        let left_sign = self.is_negative();
        let right_sign = other.is_negative();
        let res = self.wrapping_sub(other);
        let res_sign = res.is_negative();
        (res, left_sign != right_sign && res_sign != left_sign)
    }

    pub fn overflowing_neg(self) -> (i128, bool) {
        (self.wrapping_neg(), self == MIN)
    }

    pub fn checked_neg(self) -> Option<i128> {
        match self.overflowing_neg() {
            (v, false) => Some(v),
            (_, true) => None,
        }
    }

    pub fn saturating_add(self, other: i128) -> i128 {
        self.checked_add(other)
            .unwrap_or_else(|| if other.is_negative() { MIN } else { MAX })
    }

    pub fn saturating_sub(self, other: i128) -> i128 {
        self.checked_sub(other)
            .unwrap_or_else(|| if other.is_negative() { MAX } else { MIN })
    }

    pub fn saturating_neg(self) -> i128 {
        self.checked_neg().unwrap_or(MAX)
    }
}

forward_symmetric!(Add(add, checked_add, wrapping_add, overflowing_add) for i128);
forward_symmetric!(Sub(sub, checked_sub, wrapping_sub, overflowing_sub) for i128);
forward_assign!(AddAssign(add_assign, add) for i128);
forward_assign!(SubAssign(sub_assign, sub) for i128);

impl Neg for i128 {
    type Output = Self;
    fn neg(self) -> Self {
        self.checked_neg().unwrap_or_else(|| panic!("arithmetic operation overflowed"))
    }
}

impl Neg for Wrapping<i128> {
    type Output = Self;
    fn neg(self) -> Self {
        Wrapping(self.0.wrapping_neg())
    }
}

impl CheckedAdd for i128 {
    fn checked_add(&self, other: &Self) -> Option<Self> {
        Self::checked_add(*self, *other)
    }
}

impl CheckedSub for i128 {
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        Self::checked_sub(*self, *other)
    }
}

impl Saturating for i128 {
    fn saturating_add(self, other: Self) -> Self {
        Self::saturating_add(self, other)
    }

    fn saturating_sub(self, other: Self) -> Self {
        Self::saturating_add(self, other)
    }
}

#[cfg(test)]
mod add_sub_tests {
    use i128::{i128, ONE, MAX, MIN};

    #[test]
    fn test_add() {
        assert_eq!(i128::from_parts(23, 12) + i128::from_parts(78, 45),
                    i128::from_parts(101, 57));
        assert_eq!(i128::from_parts(-0x0151b4d672066e52, 0x21b6c7c3766908a7) +
                    i128::from_parts(0x08a45eef16781327, 0xff1049ddf49ff8a8),
                    i128::from_parts(0x0752aa18a471a4d6, 0x20c711a16b09014f));
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_add_overflow_above() {
        MAX + ONE;
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_add_overflow_below() {
        MIN + i128::from_parts(-1, !0);
    }

    #[test]
    fn test_sub() {
        assert_eq!(i128::from_parts(78, 45) - i128::from_parts(23, 12),
                    i128::from_parts(55, 33));
        assert_eq!(i128::from_parts(23, 12) - i128::from_parts(78, 45),
                    i128::from_parts(-56, !32));
        assert_eq!(i128::from_parts(-0x0151b4d672066e52, 0x21b6c7c3766908a7) -
                    i128::from_parts(0x08a45eef16781327, 0xff1049ddf49ff8a8),
                    i128::from_parts(-0x09f613c5887e817a, 0x22a67de581c90fff));
        assert_eq!(i128::from_parts(3565142335064920496, 15687467940602204387) -
                    i128::from_parts(4442421226426414073, 17275749316209243331),
                    i128::from_parts(-877278891361493578, 16858462698102512672));
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_sub_overflow_above() {
        MAX - i128::from_parts(-1, !0);
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_sub_overflow_below() {
        MIN - ONE;
    }

    #[test]
    #[should_panic(expected="arithmetic operation overflowed")]
    fn test_neg_min() {
        -MIN;
    }

    #[test]
    fn test_neg() {
        let neg1 = i128::from_parts(-1, !0);
        assert_eq!(neg1, -ONE);
        assert_eq!(ONE, -neg1);

        assert_eq!(MIN.wrapping_neg(), MIN);
        assert_eq!(MIN.overflowing_neg(), (MIN, true));
        assert_eq!(MIN.saturating_neg(), MAX);
        assert_eq!(MIN.checked_neg(), None);
    }
}

//}}}

//{{{ PartialOrd, Ord

impl PartialOrd for i128 {
    fn partial_cmp(&self, other: &i128) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for i128 {
    fn cmp(&self, other: &i128) -> Ordering {
        (self.high64(), self.low64()).cmp(&(other.high64(), other.low64()))
    }
}

#[cfg(test)]
mod cmp_tests {
    use i128::{i128, MIN, MAX};
    use u128::u128;

    const TEST_CASES: &'static [i128; 7] = &[
        MIN,
        i128(u128 { lo: 0, hi: !0 }),
        i128(u128 { lo: !0, hi: !0 }),
        i128(u128 { lo: 0, hi: 0 }),
        i128(u128 { lo: 1, hi: 0 }),
        i128(u128 { lo: 0, hi: 1 }),
        MAX
    ];

    #[test]
    fn test_ord() {
        for (i, a) in TEST_CASES.iter().enumerate() {
            for (j, b) in TEST_CASES.iter().enumerate() {
                assert_eq!(i.cmp(&j), a.cmp(b));
            }
        }
    }
}

//}}}

//{{{ Not, BitAnd, BitOr, BitXor

impl Not for i128 {
    type Output = Self;
    fn not(self) -> Self {
        i128(!self.0)
    }
}

impl BitAnd for i128 {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        i128(self.0 & other.0)
    }
}

impl BitOr for i128 {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        i128(self.0 | other.0)
    }
}

impl BitXor for i128 {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        i128(self.0 ^ other.0)
    }
}

impl Not for Wrapping<i128> {
    type Output = Self;
    fn not(self) -> Self {
        Wrapping(!self.0)
    }
}

impl BitAnd for Wrapping<i128> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Wrapping(self.0 & other.0)
    }
}

impl BitOr for Wrapping<i128> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        Wrapping(self.0 | other.0)
    }
}

impl BitXor for Wrapping<i128> {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        Wrapping(self.0 ^ other.0)
    }
}

forward_assign!(BitAndAssign(bitand_assign, bitand) for i128);
forward_assign!(BitOrAssign(bitor_assign, bitor) for i128);
forward_assign!(BitXorAssign(bitxor_assign, bitxor) for i128);

#[cfg(test)]
mod bitwise_tests {
    use i128::i128;

    #[test]
    fn test_not() {
        assert_eq!(i128::from_parts(0x491d3b2d80d706a6, 0x1eb41c5d2ad1a379),
                    !i128::from_parts(-0x491d3b2d80d706a7, 0xe14be3a2d52e5c86));
    }

    #[test]
    fn test_bit_and() {
        assert_eq!(i128::from_parts(-0x75007aa6237d556f, 0x8bbf525fb0c5cd79) &
                    i128::from_parts(-0x7231336af452490f, 0xb26ab6ca714bce40),
                    i128::from_parts(-0x77317beef77f5d6f, 0x822a124a3041cc40));
    }

    #[test]
    fn test_bit_or() {
        assert_eq!(i128::from_parts(-0x1c481f51e1707415, 0x5c76dd080dd43e30) |
                    i128::from_parts(0x35591b16599e2ece, 0x2e2957ca426d7b07),
                    i128::from_parts(-0x8000441a0605011, 0x7e7fdfca4ffd7f37));
    }

    #[test]
    fn test_bit_xor() {
        assert_eq!(i128::from_parts(0x50b17617e8f6ee49, 0x1b06f037a9187c71) ^
                    i128::from_parts(0x206f313ea29823bd, 0x66e0bc7aa198785a),
                    i128::from_parts(0x70de47294a6ecdf4, 0x7de64c4d0880042b));
    }
}

//}}}

//{{{ Shl, Shr

impl i128 {
    pub fn wrapping_shl(self, shift: u32) -> i128 {
        i128(self.0.wrapping_shl(shift))
    }

    pub fn wrapping_shr(self, shift: u32) -> i128 {
        let hi = self.high64();
        let lo = self.low64();

        let (hi, lo) = if (shift & 64) != 0 {
            (hi >> 63, (hi >> (shift & 63)) as u64)
        } else {
            let new_hi = hi.wrapping_shr(shift);
            let mut new_lo = lo.wrapping_shr(shift);
            if (shift & 127) != 0 {
                new_lo |= (hi as u64).wrapping_shl(64u32.wrapping_sub(shift));
            }
            (new_hi, new_lo)
        };

        i128::from_parts(hi, lo)
    }

    pub fn overflowing_shl(self, other: u32) -> (i128, bool) {
        (self.wrapping_shl(other), other >= 128)
    }

    pub fn overflowing_shr(self, other: u32) -> (i128, bool) {
        (self.wrapping_shr(other), other >= 128)
    }
}

forward_shift!(Shl(shl, checked_shl, wrapping_shl, overflowing_shl) for i128);
forward_shift!(Shr(shr, checked_shr, wrapping_shr, overflowing_shr) for i128);
forward_assign!(ShlAssign<usize>(shl_assign, shl) for i128);
forward_assign!(ShrAssign<usize>(shr_assign, shr) for i128);

#[cfg(test)]
mod shift_tests {
    use i128::i128;

    #[test]
    fn test_shl() {
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 0,
                    i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 1,
                    i128::from_parts(0x3cb8f00361caebee, 0xa7e13b58b651e2a4));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 64,
                    i128::from_parts(0x53f09dac5b28f152, 0x0));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) << 120,
                    i128::from_parts(0x5200000000000000, 0x0));

        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) << 0,
                    i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) << 1,
                    i128::from_parts(-0xffb593844655c50, 0xa13af1c94601179a));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) << 64,
                    i128::from_parts(0x509d78e4a3008bcd, 0x0));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) << 120,
                    i128::from_parts(-0x3300000000000000, 0x0));
    }

    #[test]
    fn test_shr() {
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 0,
                    i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 1,
                    i128::from_parts(0x0f2e3c00d872bafb, 0xa9f84ed62d9478a9));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 64,
                    i128::from_parts(0x0, 0x1e5c7801b0e575f7));
        assert_eq!(i128::from_parts(0x1e5c7801b0e575f7, 0x53f09dac5b28f152) >> 120,
                    i128::from_parts(0x0, 0x1e));

        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) >> 0,
                    i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) >> 1,
                    i128::from_parts(-0x3fed64e11195714, 0x284ebc72518045e6));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) >> 64,
                    i128::from_parts(-1, 0xf8025363ddcd51d8));
        assert_eq!(i128::from_parts(-0x7fdac9c2232ae28, 0x509d78e4a3008bcd) >> 120,
                    i128::from_parts(-1, 0xfffffffffffffff8));
    }
}

#[cfg(all(test, extprim_channel="unstable"))]
mod shift_bench {
    use i128::i128;
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
    fn bench_shr(bencher: &mut Bencher) {
        let number = i128::from_parts(-8704825901651121218, 3937562729638942691);
        bencher.iter(|| {
            for i in BENCH_SHIFTS {
                black_box(number.wrapping_shr(*i));
            }
        });
    }
}

//}}}

//{{{ Mul

fn sign_abs(x: i128) -> (bool, u128) {
    if x.is_negative() {
        (true, x.0.wrapping_neg())
    } else {
        (false, x.0)
    }
}

fn from_sign_abs(sign: bool, abs: u128) -> i128 {
    i128(if sign { abs.wrapping_neg() } else { abs })
}

impl i128 {
    pub fn overflowing_mul(self, other: i128) -> (i128, bool) {
        if self == ZERO || other == ZERO {
            return (ZERO, false);
        }

        let (sa, a) = sign_abs(self);
        let (sb, b) = sign_abs(other);
        let res_is_neg = sa != sb;

        let (res, res_overflow) = a.overflowing_mul(b);
        let res = from_sign_abs(res_is_neg, res);
        (res, res_overflow || res.is_negative() != res_is_neg)
    }

    pub fn wrapping_mul(self, other: i128) -> i128 {
        i128(self.0.wrapping_mul(other.0))
    }

    pub fn saturating_mul(self, other: i128) -> i128 {
        self.checked_mul(other).unwrap_or_else(|| {
            if self.is_negative() == other.is_negative() { MAX } else { MIN }
        })
    }
}

forward_symmetric!(Mul(mul, checked_mul, wrapping_mul, overflowing_mul) for i128);
forward_assign!(MulAssign(mul_assign, mul) for i128);

impl CheckedMul for i128 {
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        Self::checked_mul(*self, *other)
    }
}

#[cfg(test)]
mod mul_tests {
    use i128::{i128, ONE, MAX, MIN};

    #[test]
    fn test_mul() {
        assert_eq!(i128::new(6263979403966582069) * i128::new(2263184174907185431),
                    i128::from_parts(0xaaa4d56f5b2f577, 0x916fb81166049cc3));
        assert_eq!(ONE * ONE, ONE);
        assert_eq!(ONE * MAX, MAX);
        assert_eq!(MIN * ONE, MIN);
        assert_eq!(i128::new(-4) * i128::new(-9), i128::new(36));
        assert_eq!(i128::new(-7) * i128::new(3), i128::new(-21));
        assert_eq!(i128::from_parts(1, 1) * i128::new(-9), i128::from_parts(-10, !8));
        assert_eq!(i128::from_parts(0x4000_0000_0000_0000, 0) * i128::new(-2), MIN);
    }

    #[test]
    fn test_wrapping_overflowing_mul() {
        let a = i128::from_parts(-6140994497999405230, 2270645839074617067);
        let b = i128::from_parts(8696394550295834000, 13800979035109902541);
        let c = i128::from_parts(-6771355848177145191, 5110157532910617135);

        assert_eq!(a.wrapping_mul(b), c);
        assert_eq!(a.overflowing_mul(b), (c, true));
        assert_eq!(a.checked_mul(b), None);
        assert_eq!(a.saturating_mul(b), MIN);

        assert_eq!(i128::new(-1).wrapping_mul(i128::new(-1)), ONE);
        assert_eq!(i128::new(-1).overflowing_mul(i128::new(-1)), (ONE, false));
        assert_eq!(i128::new(-1).checked_mul(i128::new(-1)), Some(ONE));
        assert_eq!(i128::new(-1).saturating_mul(i128::new(-1)), ONE);

        assert_eq!(MAX.wrapping_mul(i128::new(2)), i128::from_parts(-1, !1));
        assert_eq!(MAX.overflowing_mul(i128::new(2)), (i128::from_parts(-1, !1), true));
        assert_eq!(MAX.checked_mul(i128::new(2)), None);
        assert_eq!(MAX.saturating_mul(i128::new(2)), MAX);
    }
}

//}}}

//{{{ Div, Rem

impl i128 {
    pub fn wrapping_div(self, other: i128) -> i128 {
        let (sa, a) = sign_abs(self);
        let (sb, b) = sign_abs(other);
        let res = a.wrapping_div(b);
        from_sign_abs(sa != sb, res)
    }

    pub fn wrapping_rem(self, other: i128) -> i128 {
        let (sa, a) = sign_abs(self);
        let (_, b) = sign_abs(other);
        let res = a.wrapping_rem(b);
        from_sign_abs(sa, res)
    }

    pub fn overflowing_div(self, other: i128) -> (i128, bool) {
        if self == MIN && other == -ONE {
            (MIN, true)
        } else {
            (self.wrapping_div(other), false)
        }
    }

    pub fn overflowing_rem(self, other: i128) -> (i128, bool) {
        if self == MIN && other == -ONE {
            (ZERO, true)
        } else {
            (self.wrapping_div(other), false)
        }
    }

    pub fn checked_div(self, other: i128) -> Option<i128> {
        if other == ZERO || self == MIN && other == -ONE {
            None
        } else {
            Some(self.wrapping_div(other))
        }
    }

    pub fn checked_rem(self, other: i128) -> Option<i128> {
        if other == ZERO || self == MIN && other == -ONE {
            None
        } else {
            Some(self.wrapping_rem(other))
        }
    }
}

impl Div for i128 {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self.wrapping_div(other)
    }
}

impl Rem for i128 {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        self.wrapping_rem(other)
    }
}

impl Div for Wrapping<i128> {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        Wrapping(self.0.wrapping_div(other.0))
    }
}

impl Rem for Wrapping<i128> {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        Wrapping(self.0.wrapping_rem(other.0))
    }
}

forward_assign!(DivAssign(div_assign, div) for i128);
forward_assign!(RemAssign(rem_assign, rem) for i128);

impl CheckedDiv for i128 {
    fn checked_div(&self, other: &Self) -> Option<Self> {
        Self::checked_div(*self, *other)
    }
}

/// Computes the divisor and remainder simultaneously. Returns `(a/b, a%b)`.
///
/// Panics when overflow or if the denominator is zero. Unlike the primitive
/// types, calling this is likely faster than calling `a/b` and `a%b` separately.
pub fn div_rem(numerator: i128, denominator: i128) -> (i128, i128) {
    if cfg!(debug_assertions) && numerator == MIN && denominator == -ONE {
        panic!("arithmetic operation overflowed");
    }
    let (sn, n) = sign_abs(numerator);
    let (sd, d) = sign_abs(denominator);
    let (div, rem) = ::u128::div_rem(n, d);
    (from_sign_abs(sn != sd, div), from_sign_abs(sn, rem))
}

#[cfg(test)]
mod div_rem_tests {
    use i128::{i128, ONE, div_rem};

    #[test]
    fn test_div() {
        let nine = i128::new(9);
        let four = i128::new(4);
        let two = i128::new(2);

        assert_eq!(nine / four, two);
        assert_eq!(nine / -four, -two);
        assert_eq!((-nine) / four, -two);
        assert_eq!((-nine) / -four, two);
        assert_eq!(nine / two, four);
        assert_eq!(nine / -two, -four);
        assert_eq!((-nine) / two, -four);
        assert_eq!((-nine) / -two, four);
    }

    #[test]
    fn test_rem() {
        let nine = i128::new(9);
        let five = i128::new(5);
        let four = i128::new(4);

        assert_eq!(nine % five, four);
        assert_eq!(nine % -five, four);
        assert_eq!((-nine) % five, -four);
        assert_eq!((-nine) % -five, -four);
    }

    #[test]
    fn test_div_rem() {
        let nine = i128::new(9);
        let five = i128::new(5);
        let four = i128::new(4);

        assert_eq!(div_rem(nine, five), (ONE, four));
        assert_eq!(div_rem(nine, -five), (-ONE, four));
        assert_eq!(div_rem(-nine, five), (-ONE, -four));
        assert_eq!(div_rem(-nine, -five), (ONE, -four));
    }
}

//}}}

//{{{ NumCast, ToPrimitive, FromPrimitive

impl ToPrimitive for i128 {
    fn to_i64(&self) -> Option<i64> {
        let hi = self.high64();
        let lo = self.low64();

        if hi == 0 && (lo >> 63) == 0 || hi == -1 && (lo >> 63) != 0 {
            Some(lo as i64)
        } else {
            None
        }
    }

    fn to_u64(&self) -> Option<u64> {
        if self.high64() != 0 {
            None
        } else {
            Some(self.low64())
        }
    }
}

impl FromPrimitive for i128 {
    fn from_u64(n: u64) -> Option<i128> {
        Some(i128(u128::new(n)))
    }

    fn from_i64(n: i64) -> Option<i128> {
        Some(i128::new(n))
    }
}

impl ToExtraPrimitive for i128 {
    fn to_u128(&self) -> Option<u128> {
        if self.is_negative() {
            None
        } else {
            Some(self.0)
        }
    }

    fn to_i128(&self) -> Option<i128> {
        Some(*self)
    }
}

//}}}

//{{{ Constants

impl Bounded for i128 {
    fn min_value() -> Self {
        MIN
    }

    fn max_value() -> Self {
        MAX
    }
}

impl Zero for i128 {
    fn zero() -> Self {
        ZERO
    }

    fn is_zero(&self) -> bool {
        *self == ZERO
    }
}

impl One for i128 {
    fn one() -> Self {
        ONE
    }
}

//}}}

//{{{ PrimInt

impl PrimInt for i128 {
    fn count_ones(self) -> u32 { self.0.count_ones() }
    fn count_zeros(self) -> u32 { self.0.count_zeros() }
    fn leading_zeros(self) -> u32 { self.0.leading_zeros() }
    fn trailing_zeros(self) -> u32 { self.0.trailing_zeros() }
    fn rotate_left(self, shift: u32) -> i128 { i128(self.0.rotate_left(shift)) }
    fn rotate_right(self, shift: u32) -> i128 { i128(self.0.rotate_right(shift)) }
    fn swap_bytes(self) -> i128 { i128(self.0.swap_bytes()) }

    fn signed_shl(self, shift: u32) -> Self {
        self << (shift as usize)
    }

    fn signed_shr(self, shift: u32) -> Self {
        self >> (shift as usize)
    }

    fn unsigned_shl(self, shift: u32) -> Self {
        self << (shift as usize)
    }

    fn unsigned_shr(self, shift: u32) -> Self {
        i128(self.0 >> (shift as usize))
    }

    fn from_be(x: Self) -> Self {
        if cfg!(target_endian="big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    fn from_le(x: Self) -> Self {
        if cfg!(target_endian="little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    fn to_be(self) -> Self {
        PrimInt::from_be(self)
    }

    fn to_le(self) -> Self {
        PrimInt::from_le(self)
    }

    fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut acc = ONE;

        while exp > 1 {
            if (exp & 1) == 1 {
                acc *= base;
            }
            exp /= 2;
            base *= base;
        }

        if exp == 1 {
            acc *= base;
        }
        acc
    }
}

#[cfg(test)]
mod checked_tests {
    use std::u64;
    use std::i64;
    use i128::{i128, ZERO, ONE, MAX, MIN};

    #[test]
    fn test_checked_add() {
        assert_eq!(Some(ZERO), ONE.checked_add(-ONE));
        assert_eq!(Some(ZERO), (-ONE).checked_add(ONE));
        assert_eq!(Some(i128::new(-2)), (-ONE).checked_add(-ONE));
        assert_eq!(Some(i128::new(2)), ONE.checked_add(ONE));
        assert_eq!(Some(MAX), MAX.checked_add(ZERO));
        assert_eq!(Some(-ONE), MAX.checked_add(MIN));
        assert_eq!(None, MAX.checked_add(ONE));
        assert_eq!(None, MIN.checked_add(-ONE));
        assert_eq!(None, ONE.checked_add(MAX));
        assert_eq!(None, (-ONE).checked_add(MIN));
        assert_eq!(Some(ZERO), MAX.checked_add(-MAX));
        assert_eq!(None, MIN.checked_add(MIN));
    }

    #[test]
    fn test_checked_sub() {
        assert_eq!(Some(ZERO), ONE.checked_sub(ONE));
        assert_eq!(Some(ZERO), MAX.checked_sub(MAX));
        assert_eq!(Some(ZERO), MIN.checked_sub(MIN));
        assert_eq!(Some(-ONE), ZERO.checked_sub(ONE));
        assert_eq!(Some(MAX.wrapping_sub(ONE)), MAX.checked_sub(ONE));
        assert_eq!(Some(-MAX), ZERO.checked_sub(MAX));
        assert_eq!(None, ZERO.checked_sub(MIN));
        assert_eq!(None, MIN.checked_sub(ONE));
        assert_eq!(None, MAX.checked_sub(-ONE));
        assert_eq!(Some(MAX), MAX.checked_sub(ZERO));
        assert_eq!(Some(MIN), MIN.checked_sub(ZERO));
        assert_eq!(Some(-ONE), MIN.checked_sub(-MAX));
        assert_eq!(Some(i128::new(2)), ONE.checked_sub(-ONE));
    }

    #[test]
    fn test_checked_mul() {
        assert_eq!(Some(ONE), ONE.checked_mul(ONE));
        assert_eq!(Some(ZERO), MIN.checked_mul(ZERO));
        assert_eq!(Some(MIN), MIN.checked_mul(ONE));
        assert_eq!(None, MIN.checked_mul(i128::new(2)));
        assert_eq!(Some(MAX), MAX.checked_mul(ONE));
        assert_eq!(None, i128::new(2).checked_mul(MAX));
        assert_eq!(None, i128::from_parts(1, 0).checked_mul(i128::from_parts(1, 0)));
        assert_eq!(None, i128::from_parts(1, 0).checked_mul(i128::from_parts(0, u64::MAX)));
        assert_eq!(Some(-MAX), MAX.checked_mul(-ONE));
        assert_eq!(None, MIN.checked_mul(-ONE));
        assert_eq!(None, i128::from_parts(-1, 0).checked_mul(i128::from_parts(0, u64::MAX)));
        assert_eq!(Some(i128::from_parts(-i64::MAX, 0)), i128::from_parts(-1, 0).checked_mul(i128::new(i64::MAX)));
        assert_eq!(None, i128::from_parts(-1, 0).checked_mul(i128::new(i64::MIN)));
    }

    #[test]
    fn test_checked_div() {
        assert_eq!(Some(ONE), ONE.checked_div(ONE));
        assert_eq!(Some(ONE), (-ONE).checked_div(-ONE));
        assert_eq!(Some(MAX), MAX.checked_div(ONE));
        assert_eq!(Some(MIN), MIN.checked_div(ONE));
        assert_eq!(Some(ZERO), ONE.checked_div(MAX));
        assert_eq!(Some(ZERO), ZERO.checked_div(MAX));
        assert_eq!(Some(ZERO), ZERO.checked_div(MIN));
        assert_eq!(None, ONE.checked_div(ZERO));
        assert_eq!(None, MAX.checked_div(ZERO));
        assert_eq!(None, MIN.checked_div(ZERO));
        assert_eq!(Some(-MAX), MAX.checked_div(-ONE));
        assert_eq!(None, MIN.checked_div(-ONE));
    }
}

//}}}

//{{{ Signed

impl Signed for i128 {
    fn abs(&self) -> Self {
        if self.is_negative() {
            self.wrapping_neg()
        } else {
            *self
        }
    }

    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            ZERO
        } else {
            self.wrapping_sub(*other)
        }
    }

    fn is_positive(&self) -> bool {
        let hi = self.high64();
        let lo = self.low64();
        hi > 0 || hi == 0 && lo > 0
    }

    fn is_negative(&self) -> bool {
        self.high64() < 0
    }

    fn signum(&self) -> Self {
        let hi = self.high64();
        let lo = self.low64();
        if hi < 0 {
            -ONE
        } else if hi > 0 || lo > 0 {
            ONE
        } else {
            ZERO
        }
    }
}

//}}}

//{{{ FromStr, FromStrRadix

impl i128 {
    pub fn from_str_radix(src: &str, radix: u32) -> Result<i128, ParseIntError> {
        assert!(radix >= 2 && radix <= 36,
                "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
                radix);

        let mut src_chars = src.chars();
        let (is_negative, src) = match src_chars.next() {
            Some('-') => (true, src_chars.as_str()),
            Some(_) => (false, src),
            None => return Err(error::EMPTY.clone()),
        };

        match u128::from_str_radix(src, radix) {
            Ok(res) => {
                let res = from_sign_abs(is_negative, res);
                if res != ZERO && res.is_negative() != is_negative {
                    Err(if is_negative {
                        error::UNDERFLOW.clone()
                    } else {
                        error::OVERFLOW.clone()
                    })
                } else {
                    Ok(res)
                }
            },
            Err(e) => {
                if is_negative && e == *error::OVERFLOW {
                    Err(error::UNDERFLOW.clone())
                } else {
                    Err(e)
                }
            },
        }
    }
}

impl Num for i128 {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, radix)
    }
}

impl FromStr for i128 {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<i128, ParseIntError> {
        Self::from_str_radix(src, 10)
    }
}

#[cfg(test)]
mod from_str_tests {
    use i128::{i128, ZERO, ONE, MIN, MAX};
    use error;

    #[test]
    fn test_from_str_radix() {
        const NEG_TEST_RESULTS: &'static [&'static str] = &[
            "-1101001110000001100001110100110110011101000101000000010101010011111111110000011111001111010001011110010010111111100000110111000",
            "-22120002200011001100011122212011101112220120010100201111102212122012112012001022",
            "-1221300030032212303220220002222133332003321322023302113330012320",
            "-2231231421040121443301142220330220044211010312230031421",
            "-10132201224250532404323114055045240003123220242012",
            "-1212403560410303232526313225350346610154225424",
            "-1516014164663505002523776037172136227740670",
            "-8502604040148764345816110644385565465038",
            "-140569828839923299370138738435219767736",
            "-460253358a63a84a62856346973015326a085",
            "-24684544189b3b874708a686624448540308",
            "-1b5619074137abcca07c1b789a5bb40143a",
            "-218c480b6358d305699729902706a4db84",
            "-33d141e10db8d70b6249ae5224b7c97ab",
            "-69c0c3a6ce8a02a9ff83e7a2f25fc1b8",
            "-102b311fc29a372ecb13e199baf8acfe",
            "-31aaf9047ff3ec83haa539ab9419b68",
            "-bb3a85b4194a20if536h6heha6i35b",
            "-2c76aee5d2b9da7ae7fb3a2a63aj6g",
            "-d7b08bdk5fk2de09j5ed0gcg27f5b",
            "-3djbdj2fa4khdffaldl1b208ej2kg",
            "-11172kdka2cf0gj0im640g8gi0mkd",
            "-7enbdaajdc653dabmllnjll400i8",
            "-2d7gm5k79nf6mc3fc0ob55gcf39b",
            "-mlhn5khiebmai868llpeih4mnla",
            "-8f2i4194hn4aeof39jdbnh5e518",
            "-392krpg3g0r0d1001nj4jm5fkb4",
            "-19kq0qaqlnf9c535470kddq5ida",
            "-ghleobpr1dricb67pkro9ii1rq",
            "-79hp9koffuiiscaoiouar0fgp0",
            "-39o31qdjka0akvv0v7kbp5vgdo",
            "-1hhh74vud8w72snbpj5teksfw5",
            "-on7ixvje61183p5w49qovbwxe",
            "-catrg80wne60wsi5f2y4nefab",
            "-69e1equxg4kja5utg038kcgc8",
        ];

        let neg = i128::from_parts(-7620305690708017834, 34929685051752008);
        for (base2, res) in NEG_TEST_RESULTS.iter().enumerate() {
            let base = (base2 + 2) as u32;
            assert_eq!(Ok(neg), i128::from_str_radix(*res, base));
            assert_eq!(Ok(-neg), i128::from_str_radix(&res[1..], base));
        }

        assert_eq!(Ok(ZERO), i128::from_str_radix("0", 2));
        assert_eq!(Ok(ZERO), i128::from_str_radix("-0", 2));
        assert_eq!(Ok(ZERO), i128::from_str_radix("0000000000000000000000000000000000", 36));
        assert_eq!(Err(error::INVALID_DIGIT.clone()), i128::from_str_radix("123", 3));
        assert_eq!(Ok(-ONE), i128::from_str_radix("-1", 10));
        assert_eq!(Err(error::INVALID_DIGIT.clone()), i128::from_str_radix("~1", 10));
        assert_eq!(Err(error::EMPTY.clone()), i128::from_str_radix("", 10));
        assert_eq!(Ok(MAX), i128::from_str_radix("7ksyyizzkutudzbv8aqztecjj", 36));
        assert_eq!(Ok(MIN), i128::from_str_radix("-7ksyyizzkutudzbv8aqztecjk", 36));
        assert_eq!(Err(error::OVERFLOW.clone()), i128::from_str_radix("7ksyyizzkutudzbv8aqztecjk", 36));
        assert_eq!(Err(error::UNDERFLOW.clone()), i128::from_str_radix("-7ksyyizzkutudzbv8aqztecjl", 36));
    }
}

//}}}

//{{{ String, Binary, LowerHex, UpperHex, Octal, Show

// In Rust, all signed numbers will be printed as unsigned in binary, octal
// and hex mode.

impl fmt::Binary for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(formatter)
    }
}

impl fmt::LowerHex for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(formatter)
    }
}

impl fmt::UpperHex for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(formatter)
    }
}

impl fmt::Octal for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(formatter)
    }
}

impl fmt::Display for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if !self.is_negative() {
            self.0.fmt(formatter)
        } else if *self == MIN {
            formatter.pad_integral(false, "", "170141183460469231731687303715884105728")
        } else {
            let core_string = format!("{}", self.0.wrapping_neg());
            formatter.pad_integral(false, "", &*core_string)
        }
    }
}

impl fmt::Debug for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(formatter.write_str("i128!("));
        try!(fmt::Display::fmt(self, formatter));
        try!(formatter.write_str(")"));
        Ok(())
    }
}

#[cfg(test)]
mod show_tests {
    use i128::{i128, ZERO, ONE, MIN, MAX};

    #[test]
    fn test_show() {
        assert_eq!("0", format!("{}", ZERO));
        assert_eq!("1", format!("{}", ONE));
        assert_eq!("-1", format!("{}", -ONE));
        assert_eq!("170141183460469231731687303715884105727", format!("{}", MAX));
        assert_eq!("-170141183460469231731687303715884105727", format!("{}", -MAX));
        assert_eq!("-170141183460469231731687303715884105728", format!("{}", MIN));
        assert_eq!("-41001515780870386888810710836203638388",
                   format!("{}", i128::from_parts(-2222696624240918362,
                                                  11097545986877534604)));
        assert_eq!("+00170141183460469231731687303715884105727",
                   format!("{:+042}", MAX));
        assert_eq!("-00170141183460469231731687303715884105728",
                   format!("{:+042}", MIN));

        // Sanity test
        assert_eq!("ff", format!("{:x}", -1i8));
    }
}

//}}}
