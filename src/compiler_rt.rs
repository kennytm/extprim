pub use self::detail::{udiv128, umod128, udivmod128};

#[cfg(extprim_has_stable_i128)]
pub mod builtins {
    pub type I128 = i128;
    pub type U128 = u128;
}

#[cfg(all(target_pointer_width="64", unix))]
mod detail {
    use u128::u128;
    use std::mem::uninitialized;

    // Prefer to use the C version if possible. Those should be more up-to-date.
    extern "C" {
        fn __udivti3(a: u128, b: u128) -> u128;
        fn __umodti3(a: u128, b: u128) -> u128;
        fn __udivmodti4(a: u128, b: u128, rem: *mut u128) -> u128;
    }

    pub fn udiv128(a: u128, b: u128) -> u128 {
        unsafe { __udivti3(a, b) }
    }

    pub fn umod128(a: u128, b: u128) -> u128 {
        unsafe { __umodti3(a, b) }
    }

    pub fn udivmod128(a: u128, b: u128) -> (u128, u128) {
        unsafe {
            let mut rem = uninitialized();
            let div = __udivmodti4(a, b, &mut rem);
            (div, rem)
        }
    }
}

#[cfg(not(all(target_pointer_width="64", unix)))]
mod detail {
    use u128::{u128, ZERO};
    use std::mem::uninitialized;

    pub fn udiv128(a: u128, b: u128) -> u128 {
        udivmodti4(a, b, None)
    }

    pub fn umod128(a: u128, b: u128) -> u128 {
        udivmod128(a, b).1
    }

    pub fn udivmod128(a: u128, b: u128) -> (u128, u128) {
        let mut rem = unsafe { uninitialized() };
        let div = udivmodti4(a, b, Some(&mut rem));
        (div, rem)
    }

    fn udivmodti4(n: u128, d: u128, rem: Option<&mut u128>) -> u128 {
        // Source is based on
        // http://llvm.org/klaus/compiler-rt/blob/master/lib/builtins/udivmodti4.c.
        // compiler-rt is an LLVM project. It is licensed in MIT and UIOSL.

        if n < d {
            rem.map(|r| { *r = n; });
            return ZERO;
        }

        let sr = match (n.hi, n.lo, d.hi, d.lo) {
            (0, x, 0, y) => {
                rem.map(|r| {
                    r.hi = 0;
                    r.lo = x % y;
                });
                return u128::new(x / y);
            },
            (x, 0, y, 0) => {
                rem.map(|r| {
                    r.hi = x % y;
                    r.lo = 0;
                });
                return u128::new(x / y);
            },
            (_, _, dh, 0) if dh.is_power_of_two() => {
                rem.map(|r| {
                    r.lo = n.lo;
                    r.hi = n.hi & (dh - 1);
                });
                return u128::new(n.hi >> dh.trailing_zeros());
            },
            (_, _, 0, dl) if dl.is_power_of_two() => {
                rem.map(|r| {
                    r.lo = n.lo & (dl - 1);
                    r.hi = 0;
                });
                return n >> dl.trailing_zeros();
            }
            _ => {
                d.leading_zeros() - n.leading_zeros() + 1
            },
        };

        let mut q = n << (128 - sr);
        let mut r = n >> sr;
        let mut carry = 0;
        for _ in 0 .. sr {
            r = r << 1;
            r.lo |= q.hi >> 63;
            q = q << 1;
            q.lo |= carry;
            carry = 0;
            if r >= d {
                r = r - d;
                carry = 1;
            }
        }
        q = q << 1;
        q.lo |= carry;
        rem.map(|rp| { *rp = r; });
        q
    }
}


