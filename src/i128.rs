#![unstable]

//! Signed 128-bit integer.

use u128::u128;
use std::num::{Int, NumCast, SignedInt, FromStrRadix, FromPrimitive, ToPrimitive};
use std::mem::transmute_copy;
use std::str::FromStr;
use std::intrinsics::TypeId;
use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr, Neg, Not};
use std::cmp::{PartialOrd, Ord, Ordering};

#[cfg(not(target_arch="x86_64"))]
use std::intrinsics::{u64_add_with_overflow, u64_sub_with_overflow};

//{{{ Structure

/// Number of bits a signed 128-bit number occupies.
#[stable]
pub const BITS: uint = 128;

/// Number of bytes a signed 128-bit number occupies.
#[stable]
pub const BYTES: uint = 16;

/// The smallest signed 128-bit integer
/// (`-170_141_183_460_469_231_731_687_303_715_884_105_728`).
#[stable]
pub const MIN: i128 = i128(u128 { lo: 0, hi: 0x8000000000000000 });

/// The largest signed 128-bit integer
/// (`170_141_183_460_469_231_731_687_303_715_884_105_727`).
#[stable]
pub const MAX: i128 = i128(u128 { lo: !0, hi: 0x7fffffffffffffff });

/// The constant 0.
#[unstable]
pub const ZERO: i128 = i128(::u128::ZERO);

/// The constant 1.
#[unstable]
pub const ONE: i128 = i128(::u128::ONE);


/// An signed 128-bit number.
#[derive(Default, Copy, Clone, Hash, PartialEq, Eq, Rand)]
#[repr(C)]
#[allow(non_camel_case_types)]
#[unstable]
pub struct i128(
    #[doc(hidden)]
    pub u128,
);

impl i128 {
    /// Constructs a new 128-bit integer from a 64-bit integer.
    #[unstable]
    pub fn new(lo: i64) -> i128 {
        i128(u128 { lo: lo as u64, hi: (lo >> 63) as u64 })
    }

    /// Constructs a new 128-bit integer from the high-64-bit and low-64-bit
    /// parts.
    ///
    /// ```
    /// use extprim::i128::i128;
    /// let number = i128::from_parts(-6692605943, 4362896299872285998);
    /// assert_eq!(number.to_string(), "-123456789012345678901234567890");
    /// // Note: -123456789012345678901234567890 = -6692605943 << 64 | 4362896299872285998
    /// ```
    #[unstable]
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

//{{{ Add, Sub

impl Add for i128 {
    type Output = i128;
    #[inline(always)]
    fn add(self, other: i128) -> i128 {
        i128(self.0 + other.0)
    }
}

impl Sub for i128 {
    type Output = i128;
    #[inline(always)]
    fn sub(self, other: i128) -> i128 {
        i128(self.0 - other.0)
    }
}

impl Neg for i128 {
    type Output = i128;
    #[inline(always)]
    fn neg(self) -> i128 {
        i128(-self.0)
    }
}

#[cfg(test)]
mod add_sub_tests {
    use i128::{i128, ONE, MIN};

    #[test]
    fn test_add() {
        assert_eq!(i128::from_parts(23, 12) + i128::from_parts(78, 45),
                    i128::from_parts(101, 57));
        assert_eq!(i128::from_parts(-0x151b4d672066e52, 0x21b6c7c3766908a7) +
                    i128::from_parts(0x08a45eef16781327, 0xff1049ddf49ff8a8),
                    i128::from_parts(0x0752aa18a471a4d6, 0x20c711a16b09014f));
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
    fn test_neg() {
        let neg1 = i128::from_parts(-1, !0);
        assert_eq!(neg1, -ONE);
        assert_eq!(ONE, -neg1);
        assert_eq!(-MIN, MIN);
    }
}

//}}}

//{{{ PartialOrd, Ord

impl PartialOrd for i128 {
    #[inline(always)]
    fn partial_cmp(&self, other: &i128) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for i128 {
    #[inline(always)]
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
        i128(u128 { lo: 0, hi: -1 }),
        i128(u128 { lo: !0, hi: -1 }),
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
    type Output = i128;
    #[inline(always)]
    fn not(self) -> i128 {
        i128(!self.0)
    }
}

impl BitAnd for i128 {
    type Output = i128;
    #[inline(always)]
    fn bitand(self, other: i128) -> i128 {
        i128(self.0 & other.0)
    }
}

impl BitOr for i128 {
    type Output = i128;
    #[inline(always)]
    fn bitor(self, other: i128) -> i128 {
        i128(self.0 | other.0)
    }
}

impl BitXor for i128 {
    type Output = i128;
    #[inline(always)]
    fn bitxor(self, other: i128) -> i128 {
        i128(self.0 ^ other.0)
    }
}

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

impl Shl<uint> for i128 {
    type Output = i128;

    fn shl(self, shift: uint) -> i128 {
        i128(self.0 << shift)
    }
}

impl Shr<uint> for i128 {
    type Output = i128;

    fn shr(self, shift: uint) -> i128 {
        let hi = self.high64();
        let lo = self.low64();

        let (hi, lo) = if (shift & 64) != 0 {
            (hi >> 63, (hi >> (shift & 63)) as u64)
        } else {
            (hi >> shift, if shift == 0 {
                lo >> shift
            } else {
                lo >> shift | (hi as u64) << (64 - shift)
            })
        };

        i128::from_parts(hi, lo)
    }
}

#[cfg(test)]
mod shift_tests {
    use i128::i128;
    use test::{Bencher, black_box};

    // randomize shift range to avoid possible branch prediction effect.
    const BENCH_SHIFTS: &'static [uint] = &[
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

    #[bench]
    fn bench_shr(bencher: &mut Bencher) {
        let number = i128::from_parts(-8704825901651121218, 3937562729638942691);
        bencher.iter(|| {
            for i in BENCH_SHIFTS.iter() {
                black_box(number >> *i);
            }
        });
    }
}

//}}}

//{{{ Mul

impl Mul for i128 {
    type Output = i128;

    fn mul(self, other: i128) -> i128 {
        i128(self.0 * other.0)
    }
}

#[cfg(test)]
mod mul_tests {
    use i128::i128;

    #[test]
    fn test_mul() {
        assert_eq!(i128::new(6263979403966582069) * i128::new(2263184174907185431),
                    i128::from_parts(0xaaa4d56f5b2f577, 0x916fb81166049cc3));
        assert_eq!(i128::from_parts(-6140994497999405230, 2270645839074617067) *
                    i128::from_parts(8696394550295834000, 13800979035109902541),
                    i128::from_parts(-6771355848177145191, 5110157532910617135));
        assert_eq!(i128::new(1) * i128::new(1), i128::new(1));
        assert_eq!(i128::new(-4) * i128::new(-9), i128::new(36));
        assert_eq!(i128::new(-7) * i128::new(3), i128::new(-21));
        assert_eq!(i128::from_parts(1, 1) * i128::new(-9), i128::from_parts(-10, !8));
    }
}

//}}}

//{{{ Div, Rem

fn sign_abs(x: i128) -> (bool, u128) {
    if x.is_negative() {
        (true, (-x).0)
    } else {
        (false, x.0)
    }
}

impl Div for i128 {
    type Output = i128;

    fn div(self, other: i128) -> i128 {
        let (sa, a) = sign_abs(self);
        let (sb, b) = sign_abs(other);
        let res = a / b;
        i128(if sa != sb { -res } else { res })
    }
}

impl Rem for i128 {
    type Output = i128;

    fn rem(self, other: i128) -> i128 {
        let (sa, a) = sign_abs(self);
        let (_, b) = sign_abs(other);
        let res = a % b;
        i128(if sa { -res } else { res })
    }
}

/// Computes the divisor and remainder simultaneously. Returns `(a/b, a%b)`.
///
/// Panics if the denominator is zero. Unlike the primitive types, calling this
/// is likely faster than calling `a/b` and `a%b` separately.
#[unstable]
pub fn div_rem(numerator: i128, denominator: i128) -> (i128, i128) {
    let (sn, n) = sign_abs(numerator);
    let (sd, d) = sign_abs(denominator);
    let (div, rem) = ::u128::div_rem(n, d);
    (i128(if sn != sd { -div } else { div }), i128(if sn { -rem } else { rem }))
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

impl NumCast for i128 {
    fn from<T: ToPrimitive + 'static>(n: T) -> Option<i128> {
        // TODO: Rust doesn't support specialization, thus this mess.
        //       See rust-lang/rust#7059. LLVM is able to optimize this though.
        let typeid = TypeId::of::<T>();

        if typeid == TypeId::of::<i128>() {
            Some(unsafe { transmute_copy(&n) })
        } else if typeid == TypeId::of::<u128>() {
            let n: u128 = unsafe { transmute_copy(&n) };
            if (n.hi >> 63) != 0 {
                None
            } else {
                Some(i128(n))
            }
        } else if typeid == TypeId::of::<u64>() || typeid == TypeId::of::<uint>() {
            n.to_u64().map(|x| i128(u128::new(x)))
        } else {
            n.to_i64().map(i128::new)
        }
    }
}

#[cfg(test)]
mod num_cast_tests {
    use std::num::NumCast;
    use u128;
    use i128::{i128, ONE, MIN, MAX};

    #[test]
    fn test_num_cast() {
        assert_eq!(None::<i64>, NumCast::from(0x8000_0000_0000_0000u64)); // sanity check.
        assert_eq!(None::<i128>, NumCast::from(u128::MAX));
        assert_eq!(Some(ONE), NumCast::from(1i8));
        assert_eq!(Some(-ONE), NumCast::from(-1i8));
        assert_eq!(Some(i128::from_parts(0, 0x8000_0000_0000_0000)), NumCast::from(0x8000_0000_0000_0000u64));
        assert_eq!(Some(MAX), NumCast::from(MAX));
        assert_eq!(Some(MIN), NumCast::from(MIN));

        assert_eq!(Some(ONE), NumCast::from(i128::new(1)));
        assert_eq!(None::<i128>, NumCast::from(u128::u128::from_parts(0x8000_0000_0000_0000, 0)));
    }
}

//}}}

//{{{ Int

impl Int for i128 {
    fn zero() -> i128 { ZERO }
    fn one() -> i128 { ONE }
    fn min_value() -> i128 { MIN }
    fn max_value() -> i128 { MAX }

    fn count_ones(self) -> uint { self.0.count_ones() }
    fn leading_zeros(self) -> uint { self.0.leading_zeros() }
    fn trailing_zeros(self) -> uint { self.0.trailing_zeros() }
    fn rotate_left(self, shift: uint) -> i128 { i128(self.0.rotate_left(shift)) }
    fn rotate_right(self, shift: uint) -> i128 { i128(self.0.rotate_right(shift)) }
    fn swap_bytes(self) -> i128 { i128(self.0.swap_bytes()) }

    #[cfg(not(target_arch="x86_64"))]
    fn checked_add(self, other: i128) -> Option<i128> {
        self.high64().checked_add(other.high64()).and_then(|new_hi| {
            let (new_lo, carry) = unsafe { u64_add_with_overflow(self.low64(), other.low64()) };
            if carry {
                new_hi.checked_add(1).map(|new_hi_2| i128::from_parts(new_hi_2, new_lo))
            } else {
                Some(i128::from_parts(new_hi, new_lo))
            }
        })
    }

    #[allow(unused_assignments)]
    #[cfg(target_arch="x86_64")]
    fn checked_add(mut self, other: i128) -> Option<i128> {
        unsafe {
            let mut is_valid = 1u32;
            asm!("
                xorl %eax, %eax
                addq $3, $1
                adcq $4, $2
                cmovol %eax, $0
            "
            : "+r"(is_valid), "+r"(self.0.lo), "+r"(self.0.hi)
            : "r"(other.0.lo), "r"(other.0.hi)
            : "rax"
            );
            if is_valid != 0 {
                Some(self)
            } else {
                None
            }
        }
    }

    #[cfg(not(target_arch="x86_64"))]
    fn checked_sub(self, other: i128) -> Option<i128> {
        self.high64().checked_sub(other.high64()).and_then(|new_hi| {
            let (new_lo, borrow) = unsafe { u64_sub_with_overflow(self.low64(), other.low64()) };
            if borrow {
                new_hi.checked_sub(1).map(|new_hi_2| i128::from_parts(new_hi_2, new_lo))
            } else {
                Some(i128::from_parts(new_hi, new_lo))
            }
        })
    }

    #[allow(unused_assignments)]
    #[cfg(target_arch="x86_64")]
    fn checked_sub(mut self, other: i128) -> Option<i128> {
        unsafe {
            let mut is_valid = 1u32;
            asm!("
                xorl %eax, %eax
                subq $3, $1
                sbbq $4, $2
                cmovol %eax, $0
            "
            : "+r"(is_valid), "+r"(self.0.lo), "+r"(self.0.hi)
            : "r"(other.0.lo), "r"(other.0.hi)
            : "rax"
            );
            if is_valid != 0 {
                Some(self)
            } else {
                None
            }
        }
    }

    fn checked_mul(self, other: i128) -> Option<i128> {
        if self == ZERO || other == ZERO {
            return Some(ZERO);
        }

        let (sa, a) = sign_abs(self);
        let (sb, b) = sign_abs(other);
        let res_is_neg = sa != sb;

        a.checked_mul(b).and_then(|res| {
            let res = i128(if res_is_neg { -res } else { res });
            if res.is_negative() == res_is_neg {
                Some(res)
            } else {
                None
            }
        })
    }

    fn checked_div(self, other: i128) -> Option<i128> {
        if other == ZERO || self == MIN && other == -ONE {
            None
        } else {
            Some(self / other)
        }
    }
}

#[cfg(test)]
mod int_tests {
    use std::num::Int;
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
    }

    #[test]
    fn test_checked_sub() {
        assert_eq!(Some(ZERO), ONE.checked_sub(ONE));
        assert_eq!(Some(ZERO), MAX.checked_sub(MAX));
        assert_eq!(Some(ZERO), MIN.checked_sub(MIN));
        assert_eq!(Some(MAX-ONE), MAX.checked_sub(ONE));
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

//{{{ SignedInt

impl SignedInt for i128 {
    fn abs(self) -> i128 {
        if self.is_negative() {
            self
        } else {
            -self
        }
    }

    fn is_positive(self) -> bool {
        let hi = self.high64();
        let lo = self.low64();
        hi > 0 || hi == 0 && lo > 0
    }

    fn is_negative(self) -> bool {
        self.high64() < 0
    }

    fn signum(self) -> i128 {
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

impl FromStrRadix for i128 {
    fn from_str_radix(src: &str, radix: uint) -> Option<i128> {
        assert!(radix >= 2 && radix <= 36,
                "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
                radix);

        let (is_negative, src) = match src.slice_shift_char() {
            Some(('-', rest)) => (true, rest),
            Some(_) => (false, src),
            None => return None,
        };

        FromStrRadix::from_str_radix(src, radix).and_then(|res: u128| {
            let res = i128(if is_negative { -res } else { res });
            if res != ZERO && res.is_negative() != is_negative {
                None
            } else {
                Some(res)
            }
        })
    }
}

impl FromStr for i128 {
    fn from_str(src: &str) -> Option<i128> {
        FromStrRadix::from_str_radix(src, 10)
    }
}

#[cfg(test)]
mod from_str_tests {
    use i128::{i128, ZERO, ONE, MIN, MAX};
    use std::num::FromStrRadix;

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
            assert_eq!(Some(neg), FromStrRadix::from_str_radix(*res, base2+2));
            assert_eq!(Some(-neg), FromStrRadix::from_str_radix(res.slice_from(1), base2+2));
        }

        assert_eq!(Some(ZERO), FromStrRadix::from_str_radix("0", 2));
        assert_eq!(Some(ZERO), FromStrRadix::from_str_radix("-0", 2));
        assert_eq!(Some(ZERO), FromStrRadix::from_str_radix("0000000000000000000000000000000000", 36));
        assert_eq!(None::<i128>, FromStrRadix::from_str_radix("123", 3));
        assert_eq!(Some(-ONE), FromStrRadix::from_str_radix("-1", 10));
        assert_eq!(None::<i128>, FromStrRadix::from_str_radix("~1", 10));
        assert_eq!(None::<i128>, FromStrRadix::from_str_radix("", 10));
        assert_eq!(Some(MAX), FromStrRadix::from_str_radix("7ksyyizzkutudzbv8aqztecjj", 36));
        assert_eq!(Some(MIN), FromStrRadix::from_str_radix("-7ksyyizzkutudzbv8aqztecjk", 36));
        assert_eq!(None::<i128>, FromStrRadix::from_str_radix("7ksyyizzkutudzbv8aqztecjk", 36));
        assert_eq!(None::<i128>, FromStrRadix::from_str_radix("-7ksyyizzkutudzbv8aqztecjl", 36));
    }
}

//}}}

//{{{ Binary, LowerHex, UpperHex, Octal, Show

// As of 0.13, all signed numbers will be printed as unsigned in binary, octal
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

impl fmt::Show for i128 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if !self.is_negative() {
            self.0.fmt(formatter)
        } else if *self == MIN {
            formatter.pad_integral(false, "", "170141183460469231731687303715884105728")
        } else {
            let core_string = format!("{}", (-*self).0);
            formatter.pad_integral(false, "", &*core_string)
        }
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

