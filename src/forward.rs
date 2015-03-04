use u128::u128;
use i128::i128;

use std::ops::*;

#[cfg(not(ndebug))]
use std::num::wrapping::OverflowingOps;

#[cfg(ndebug)]
use std::num::wrapping::WrappingOps;

macro_rules! forward_checked {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty => $o:ty : $overflowing:ident, $wrapping:ident) => {
        impl $imp for $t {
            type Output = $o;

            #[cfg(not(ndebug))]
            fn $method(self, other: $u) -> $o {
                let (res, overflow) = self.$overflowing(other);
                assert!(!overflow, "arithmetic operation overflowed");
                res
            }

            #[cfg(ndebug)]
            fn $method(self, other: $u) -> $o {
                self.$wrapping(other)
            }
        }
    }
}

macro_rules! forward_shift {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl $imp<$u> for $t {
            type Output = $t;

            #[inline]
            fn $method(self, shift: $u) -> $t {
                self.$method(shift as u32)
            }
        }
    }
}

// These 2 macros are copied from core::ops.

macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        #[unstable]
        impl<'a> $imp for &'a $t {
            type Output = <$t as $imp>::Output;

            #[inline]
            fn $method(self) -> <$t as $imp>::Output {
                $imp::$method(*self)
            }
        }
    }
}

macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        #[unstable]
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        #[unstable]
        impl<'a> $imp<&'a $u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        #[unstable]
        impl<'a, 'b> $imp<&'a $u> for &'b $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}

forward_checked!{impl Add, add for u128, u128 => u128 : overflowing_add, wrapping_add}
forward_checked!{impl Sub, sub for u128, u128 => u128 : overflowing_sub, wrapping_sub}
forward_checked!{impl Mul, mul for u128, u128 => u128 : overflowing_mul, wrapping_mul}
forward_checked!{impl Add, add for i128, i128 => i128 : overflowing_add, wrapping_add}
forward_checked!{impl Sub, sub for i128, i128 => i128 : overflowing_sub, wrapping_sub}
forward_checked!{impl Mul, mul for i128, i128 => i128 : overflowing_mul, wrapping_mul}

forward_ref_binop!{impl Add, add for u128, u128}
forward_ref_binop!{impl Sub, sub for u128, u128}
forward_ref_unop!{impl Neg, neg for u128}
forward_ref_unop!{impl Not, not for u128}
forward_ref_binop!{impl BitAnd, bitand for u128, u128}
forward_ref_binop!{impl BitOr, bitor for u128, u128}
forward_ref_binop!{impl BitXor, bitxor for u128, u128}

forward_shift!{impl Shl, shl for u128, i8}
forward_shift!{impl Shl, shl for u128, u8}
forward_shift!{impl Shl, shl for u128, i16}
forward_shift!{impl Shl, shl for u128, u16}
forward_shift!{impl Shl, shl for u128, i32}
forward_shift!{impl Shl, shl for u128, i64}
forward_shift!{impl Shl, shl for u128, u64}
forward_shift!{impl Shl, shl for u128, isize}
forward_shift!{impl Shl, shl for u128, usize}
forward_shift!{impl Shr, shr for u128, i8}
forward_shift!{impl Shr, shr for u128, u8}
forward_shift!{impl Shr, shr for u128, i16}
forward_shift!{impl Shr, shr for u128, u16}
forward_shift!{impl Shr, shr for u128, i32}
forward_shift!{impl Shr, shr for u128, i64}
forward_shift!{impl Shr, shr for u128, u64}
forward_shift!{impl Shr, shr for u128, isize}
forward_shift!{impl Shr, shr for u128, usize}
forward_shift!{impl Shl, shl for i128, i8}
forward_shift!{impl Shl, shl for i128, u8}
forward_shift!{impl Shl, shl for i128, i16}
forward_shift!{impl Shl, shl for i128, u16}
forward_shift!{impl Shl, shl for i128, i32}
forward_shift!{impl Shl, shl for i128, i64}
forward_shift!{impl Shl, shl for i128, u64}
forward_shift!{impl Shl, shl for i128, isize}
forward_shift!{impl Shl, shl for i128, usize}
forward_shift!{impl Shr, shr for i128, i8}
forward_shift!{impl Shr, shr for i128, u8}
forward_shift!{impl Shr, shr for i128, i16}
forward_shift!{impl Shr, shr for i128, u16}
forward_shift!{impl Shr, shr for i128, i32}
forward_shift!{impl Shr, shr for i128, i64}
forward_shift!{impl Shr, shr for i128, u64}
forward_shift!{impl Shr, shr for i128, isize}
forward_shift!{impl Shr, shr for i128, usize}



forward_ref_binop!{impl Shl, shl for u128, i8}
forward_ref_binop!{impl Shl, shl for u128, u8}
forward_ref_binop!{impl Shl, shl for u128, i16}
forward_ref_binop!{impl Shl, shl for u128, u16}
forward_ref_binop!{impl Shl, shl for u128, i32}
forward_ref_binop!{impl Shl, shl for u128, u32}
forward_ref_binop!{impl Shl, shl for u128, i64}
forward_ref_binop!{impl Shl, shl for u128, u64}
forward_ref_binop!{impl Shl, shl for u128, isize}
forward_ref_binop!{impl Shl, shl for u128, usize}
forward_ref_binop!{impl Shr, shr for u128, i8}
forward_ref_binop!{impl Shr, shr for u128, u8}
forward_ref_binop!{impl Shr, shr for u128, i16}
forward_ref_binop!{impl Shr, shr for u128, u16}
forward_ref_binop!{impl Shr, shr for u128, i32}
forward_ref_binop!{impl Shr, shr for u128, u32}
forward_ref_binop!{impl Shr, shr for u128, i64}
forward_ref_binop!{impl Shr, shr for u128, u64}
forward_ref_binop!{impl Shr, shr for u128, isize}
forward_ref_binop!{impl Shr, shr for u128, usize}


