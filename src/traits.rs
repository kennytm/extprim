//! Traits for conversion between the extra primitive types.

use num_traits::{ToPrimitive, NumCast, One, Float};
#[cfg(feature="use-std")] use num_traits::Num;
use u128::u128;
use i128::i128;
#[cfg(extprim_has_stable_i128)] use compiler_rt::builtins::{U128, I128};
use std::ops::MulAssign;

/// Trait for converting itself into the extra primitive types.
///
/// # Note
///
/// Converting f32/f64 to u128/i128 will always succeed, even if they represent values outside of
/// the u128/i128 ranges. They will just return `Some(0)` on overflow. This is similar to how
/// `num_traits::ToPrimitive` treat the float conversions.
///
/// ```rust
/// use extprim::traits::ToExtraPrimitive;
/// use extprim::u128::u128;
/// use std::f64;
///
/// assert_eq!(680.0f64.to_u128(), Some(u128::new(680)));
/// assert_eq!(2.0f64.powi(64).to_u128(), Some(u128::from_parts(1, 0)));
///
/// // The following examples overflow, but they all still convert to 0.
/// assert_eq!(2.0f64.powi(128).to_u128(), Some(u128::zero()));
/// assert_eq!(f64::MAX.to_u128(), Some(u128::zero()));
/// assert_eq!(f64::INFINITY.to_u128(), Some(u128::zero()));
/// assert_eq!(f64::NAN.to_u128(), Some(u128::zero()));
/// ```
pub trait ToExtraPrimitive: ToPrimitive {
    /// Tries to convert itself into an unsigned 128-bit integer.
    fn to_u128(&self) -> Option<u128>;

    /// Tries to convert itself into a signed 128-bit integer.
    fn to_i128(&self) -> Option<i128>;
}

macro_rules! impl_to_extra_primitive_for_int {
    ($ty:ty) => {
        impl ToExtraPrimitive for $ty {
            fn to_u128(&self) -> Option<u128> {
                #[cfg(extprim_has_stable_i128)] {
                    ToPrimitive::to_u128(self).map(u128::from_built_in)
                }
                #[cfg(not(extprim_has_stable_i128))] {
                    self.to_u64().map(u128::new)
                }
            }

            fn to_i128(&self) -> Option<i128> {
                #[cfg(extprim_has_stable_i128)] {
                    ToPrimitive::to_i128(self).map(i128::from_built_in)
                }
                #[cfg(not(extprim_has_stable_i128))] {
                    match self.to_u64() {
                        Some(v) => Some(i128(u128::new(v))),
                        None => self.to_i64().map(i128::new),
                    }
                }
            }
        }
    }
}

impl_to_extra_primitive_for_int!(u8);
impl_to_extra_primitive_for_int!(i8);
impl_to_extra_primitive_for_int!(u16);
impl_to_extra_primitive_for_int!(i16);
impl_to_extra_primitive_for_int!(u32);
impl_to_extra_primitive_for_int!(i32);
impl_to_extra_primitive_for_int!(u64);
impl_to_extra_primitive_for_int!(i64);
impl_to_extra_primitive_for_int!(usize);
impl_to_extra_primitive_for_int!(isize);

#[cfg(extprim_has_stable_i128)]
impl_to_extra_primitive_for_int!(U128);
#[cfg(extprim_has_stable_i128)]
impl_to_extra_primitive_for_int!(I128);

macro_rules! impl_to_extra_primitive_for_float {
    ($float:ty, $d:expr, $e:expr, $f:expr) => {
        // static_assert!($e == 127-$d);
        // static_assert!($f == 126-$d);
        //
        impl ToExtraPrimitive for $float {
            fn to_u128(&self) -> Option<u128> {
                let (mantissa, exp, sign) = Float::integer_decode(*self);
                Some(match exp {
                    _ if sign < 0 => u128::zero(),
                    -$d ... 0 => u128::new(mantissa >> -exp),
                    1 ... $e => u128::new(mantissa) << exp,
                    _ => u128::zero(),
                })
            }

            fn to_i128(&self) -> Option<i128> {
                let (mantissa, exp, sign) = Float::integer_decode(*self);
                let abs = match exp {
                    -$d ... 0 => u128::new(mantissa >> -exp),
                    1 ... $f => u128::new(mantissa) << exp,
                    $e if sign == -1 && mantissa == (1 << $d) => u128::from_parts(0x80000000_00000000, 0),
                    _ => u128::zero(),
                };
                Some(if sign >= 0 {
                    abs.as_i128()
                } else {
                    abs.wrapping_neg().as_i128()
                })
            }
        }
    }
}

impl_to_extra_primitive_for_float!(f32, 23, 104, 103);
impl_to_extra_primitive_for_float!(f64, 52, 75, 74);

#[cfg(test)]
mod float_to_128_tests {
    use u128::u128;
    use i128::i128;
    use traits::ToExtraPrimitive;
    use std::{u64, i64, f32, f64};

    #[test]
    fn test_u64_to_u128() {
        assert_eq!(0u64.to_u128(), Some(u128::new(0)));
        assert_eq!(u64::MAX.to_u128(), Some(u128::new(u64::MAX)));
    }

    #[test]
    fn test_i64_to_u128() {
        assert_eq!(0i64.to_u128(), Some(u128::new(0)));
        assert_eq!(i64::MAX.to_u128(), Some(u128::new(0x7fffffff_ffffffff)));
        assert_eq!(i64::MIN.to_u128(), None);
    }

    #[test]
    fn test_u64_to_i128() {
        assert_eq!(0u64.to_i128(), Some(i128::new(0)));
        assert_eq!(u64::MAX.to_i128(), Some(i128::from_parts(0, u64::MAX)));
    }

    #[test]
    fn test_i64_to_i128() {
        assert_eq!(0i64.to_i128(), Some(i128::new(0)));
        assert_eq!(i64::MAX.to_i128(), Some(i128::new(i64::MAX)));
        assert_eq!(i64::MIN.to_i128(), Some(i128::new(i64::MIN)));
    }

    #[test]
    fn test_f64_to_u128() {
        assert_eq!(0.0f64.to_u128(), Some(u128::new(0)));
        assert_eq!(0.9f64.to_u128(), Some(u128::new(0)));
        assert_eq!(1.0f64.to_u128(), Some(u128::new(1)));
        assert_eq!(1.9f64.to_u128(), Some(u128::new(1)));
        assert_eq!(1.0e19f64.to_u128(), Some(u128::new(10000000000000000000)));
        assert_eq!(1.0e20f64.to_u128(), Some(u128::from_parts(5, 7766279631452241920)));
        assert_eq!(1.0e38f64.to_u128(), Some(u128::from_parts(5421010862427522048, 0)));
        assert_eq!(3.0e38f64.to_u128(), Some(u128::from_parts(16263032587282567168, 0)));
        assert_eq!(1.0e39f64.to_u128(), Some(u128::zero()));
        assert_eq!(340282366920938425684442744474606501888.0f64.to_u128(), Some(u128::from_parts(0xffffffff_fffff800, 0)));
        assert_eq!(340282366920938463463374607431768211456.0f64.to_u128(), Some(u128::zero()));
        assert_eq!((-0.0f64).to_u128(), Some(u128::zero()));
        assert_eq!((-1.0f64).to_u128(), Some(u128::zero()));
        assert_eq!((f64::NAN).to_u128(), Some(u128::zero()));
        assert_eq!((f64::MAX).to_u128(), Some(u128::zero()));
        assert_eq!((f64::MIN_POSITIVE).to_u128(), Some(u128::zero()));
        assert_eq!((f64::INFINITY).to_u128(), Some(u128::zero()));
    }

    #[test]
    fn test_f64_to_i128() {
        assert_eq!(0.0f64.to_i128(), Some(i128::new(0)));
        assert_eq!(0.9f64.to_i128(), Some(i128::new(0)));
        assert_eq!(1.0f64.to_i128(), Some(i128::new(1)));
        assert_eq!(1.9f64.to_i128(), Some(i128::new(1)));
        assert_eq!(1.0e19f64.to_i128(), Some(i128::from_parts(0, 10000000000000000000)));
        assert_eq!(1.0e20f64.to_i128(), Some(i128::from_parts(5, 7766279631452241920)));
        assert_eq!(1.0e38f64.to_i128(), Some(i128::from_parts(5421010862427522048, 0)));
        assert_eq!(3.0e38f64.to_i128(), Some(i128::zero()));
        assert_eq!(1.0e39f64.to_i128(), Some(i128::zero()));
        assert_eq!((-0.0f64).to_i128(), Some(i128::new(0)));
        assert_eq!((-0.9f64).to_i128(), Some(i128::new(0)));
        assert_eq!((-1.0f64).to_i128(), Some(i128::new(-1)));
        assert_eq!((-1.9f64).to_i128(), Some(i128::new(-1)));
        assert_eq!((-1.0e20f64).to_i128(), Some(i128::from_parts(-6, 10680464442257309696)));
        assert_eq!((-1.0e38f64).to_i128(), Some(i128::from_parts(-5421010862427522048, 0)));
        assert_eq!((-1.0e39f64).to_i128(), Some(i128::zero()));
        assert_eq!(170141183460469212842221372237303250944.0f64.to_i128(), Some(i128::from_parts(0x7fffffff_fffffc00, 0)));
        assert_eq!(170141183460469231731687303715884105728.0f64.to_i128(), Some(i128::zero()));
        assert_eq!((-170141183460469231731687303715884105728.0f64).to_i128(), Some(i128::min_value()));
        assert_eq!((-170141183460469269510619166673045815296.0f64).to_i128(), Some(i128::zero()));
        assert_eq!((f64::NAN).to_i128(), Some(i128::zero()));
        assert_eq!((f64::MAX).to_i128(), Some(i128::zero()));
        assert_eq!((f64::MIN_POSITIVE).to_i128(), Some(i128::zero()));
        assert_eq!((f64::INFINITY).to_i128(), Some(i128::zero()));
    }

    #[test]
    fn test_f32_to_u128() {
        assert_eq!(0.0f32.to_u128(), Some(u128::new(0)));
        assert_eq!(0.9f32.to_u128(), Some(u128::new(0)));
        assert_eq!(1.0f32.to_u128(), Some(u128::new(1)));
        assert_eq!(1.9f32.to_u128(), Some(u128::new(1)));
        assert_eq!(1.0e19f32.to_u128(), Some(u128::new(9999999980506447872)));
        assert_eq!(1.0e20f32.to_u128(), Some(u128::from_parts(5, 7766281635539976192)));
        assert_eq!(1.0e38f32.to_u128(), Some(u128::from_parts(5421010689110048768, 0)));
        assert_eq!(3.0e38f32.to_u128(), Some(u128::from_parts(16263032617085960192, 0)));
        assert_eq!((-0.0f32).to_u128(), Some(u128::zero()));
        assert_eq!((-1.0f32).to_u128(), Some(u128::zero()));
        assert_eq!((f32::NAN).to_u128(), Some(u128::zero()));
        assert_eq!((f32::MAX).to_u128(), Some(u128::from_parts(0xffffff0000000000, 0)));
        assert_eq!((f32::MIN_POSITIVE).to_u128(), Some(u128::zero()));
        assert_eq!((f32::INFINITY).to_u128(), Some(u128::zero()));
    }

    #[test]
    fn test_f32_to_i128() {
        assert_eq!(0.0f32.to_i128(), Some(i128::new(0)));
        assert_eq!(0.9f32.to_i128(), Some(i128::new(0)));
        assert_eq!(1.0f32.to_i128(), Some(i128::new(1)));
        assert_eq!(1.9f32.to_i128(), Some(i128::new(1)));
        assert_eq!(1.0e19f32.to_i128(), Some(i128::from_parts(0, 9999999980506447872)));
        assert_eq!(1.0e20f32.to_i128(), Some(i128::from_parts(5, 7766281635539976192)));
        assert_eq!(1.0e38f32.to_i128(), Some(i128::from_parts(5421010689110048768, 0)));
        assert_eq!(3.0e38f32.to_i128(), Some(i128::zero()));
        assert_eq!((-0.0f32).to_i128(), Some(i128::new(0)));
        assert_eq!((-0.9f32).to_i128(), Some(i128::new(0)));
        assert_eq!((-1.0f32).to_i128(), Some(i128::new(-1)));
        assert_eq!((-1.9f32).to_i128(), Some(i128::new(-1)));
        assert_eq!((-1.0e20f32).to_i128(), Some(i128::from_parts(-6, 10680462438169575424)));
        assert_eq!((-1.0e38f32).to_i128(), Some(i128::from_parts(-5421010689110048768, 0)));
        assert_eq!(170141173319264429905852091742258462720.0f32.to_i128(), Some(i128::from_parts(0x7fffff80_00000000, 0)));
        assert_eq!(170141183460469231731687303715884105728.0f32.to_i128(), Some(i128::zero()));
        assert_eq!((-170141183460469231731687303715884105728.0f32).to_i128(), Some(i128::min_value()));
        assert_eq!((-170141203742878835383357727663135391744.0f32).to_i128(), Some(i128::zero()));
        assert_eq!((f32::NAN).to_i128(), Some(i128::zero()));
        assert_eq!((f32::MAX).to_i128(), Some(i128::zero()));
        assert_eq!((f32::MIN_POSITIVE).to_i128(), Some(i128::zero()));
        assert_eq!((f32::INFINITY).to_i128(), Some(i128::zero()));
    }
}

#[cfg(extprim_channel = "unstable")]
impl<T: ToPrimitive> ToExtraPrimitive for T {
    default fn to_u128(&self) -> Option<u128> {
        ToPrimitive::to_u128(self).map(u128::from_built_in)
    }

    default fn to_i128(&self) -> Option<i128> {
        ToPrimitive::to_i128(self).map(i128::from_built_in)
    }
}

impl NumCast for u128 {
    fn from<T: ToPrimitive>(n: T) -> Option<u128> {
        #[cfg(extprim_has_stable_i128)] {
            ToPrimitive::to_u128(&n).map(u128::from_built_in)
        }
        #[cfg(not(extprim_has_stable_i128))] {
            panic!("cannot use this before Rust 1.26.0");
        }
    }
}

impl NumCast for i128 {
    fn from<T: ToPrimitive>(n: T) -> Option<i128> {
        #[cfg(extprim_has_stable_i128)] {
            ToPrimitive::to_i128(&n).map(i128::from_built_in)
        }
        #[cfg(not(extprim_has_stable_i128))] {
            panic!("cannot use this before Rust 1.26.0");
        }
    }
}

#[cfg(all(extprim_has_stable_i128, test))]
mod num_cast_tests {
    use std::u64;
    use num_traits::NumCast;
    use u128::u128;
    use i128::i128;

    #[test]
    fn test_num_cast_for_u128() {
        assert_eq!(None::<u64>, NumCast::from(-1i8)); // sanity check.
        assert_eq!(None::<u128>, NumCast::from(-1i8));
        assert_eq!(Some(u128::one()), NumCast::from(1i8));
        assert_eq!(Some(u128::new(u64::MAX)), NumCast::from(u64::MAX));
        assert_eq!(Some(u128::max_value()), NumCast::from(u128::max_value()));

        assert_eq!(Some(u128::one()), NumCast::from(i128::new(1)));
        assert_eq!(None::<u128>, NumCast::from(i128::new(-1)));
    }

    #[test]
    fn test_num_cast_for_i128() {
        assert_eq!(None::<i64>, NumCast::from(0x8000_0000_0000_0000u64)); // sanity check.
        assert_eq!(None::<i128>, NumCast::from(u128::max_value()));
        assert_eq!(Some(i128::one()), NumCast::from(1i8));
        assert_eq!(Some(-i128::one()), NumCast::from(-1i8));
        assert_eq!(Some(i128::from_parts(0, 0x8000_0000_0000_0000)), NumCast::from(0x8000_0000_0000_0000u64));
        assert_eq!(Some(i128::max_value()), NumCast::from(i128::max_value()));
        assert_eq!(Some(i128::min_value()), NumCast::from(i128::min_value()));

        assert_eq!(Some(i128::one()), NumCast::from(i128::new(1)));
        assert_eq!(None::<i128>, NumCast::from(u128::from_parts(0x8000_0000_0000_0000, 0)));
    }
}

/// Wrapper for `u128` and `i128` to turn arithmetic operators to wrapping ones.
///
/// Equivalent to `std::num::Wrapping`, but due to E0117 (orphan rule) we need to define it here to
/// implement operators on it.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Default)]
pub struct Wrapping<T>(pub T);

/// Raise `base` to the power of `exp`, using exponentiation by squaring.
///
/// # Examples
///
/// ```rust
/// use extprim::traits::pow;
///
/// assert_eq!(pow(10u64, 7), 10000000u64);
/// ```
#[deprecated(since="1.1.1", note="please use `num_traits::pow` instead")]
pub fn pow<T: Copy + One + MulAssign>(mut base: T, mut exp: u32) -> T {
    let mut acc = T::one();

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

/// Parses a Rust integer literal into an actual integral type.
///
/// If `is_negative` is true, a negative sign will be added to the string before the conversion.
///
/// # Examples
///
/// ```rust
/// use extprim::traits::parse_rust_int_lit;
/// use extprim::u128::u128;
/// use extprim::i128::i128;
///
/// assert_eq!(parse_rust_int_lit::<u128>("100_000", false).unwrap(), u128::new(100_000));
/// assert_eq!(parse_rust_int_lit::<u128>("0xffffffff_ffffffff_22222222_22222222", false).unwrap(),
///             u128::from_parts(0xffffffff_ffffffff, 0x22222222_22222222));
/// assert_eq!(parse_rust_int_lit::<i128>("0b111", true).unwrap(), i128::new(-0b111));
/// assert_eq!(parse_rust_int_lit::<i128>("0x80000000_00000000_00000000_00000000", true).unwrap(),
///             i128::min_value());
/// ```
#[cfg(feature="use-std")] // TODO should be usable even without std.
pub fn parse_rust_int_lit<T: Num>(s: &str, is_negative: bool) -> Result<T, T::FromStrRadixErr> {
    let mut c = s.chars();
    let (base, digits) = if c.next() != Some('0') {
        (10, s)
    } else {
        match c.next() {
            Some('b') | Some('B') => (2, c.as_str()),
            Some('o') | Some('O') => (8, c.as_str()),
            Some('x') | Some('X') => (16, c.as_str()),
            _ => (10, s),
        }
    };

    let sign = if is_negative { "-" } else { "" };
    let digits = format!("{}{}", sign, digits.replace("_", ""));
    T::from_str_radix(&digits, base)
}

