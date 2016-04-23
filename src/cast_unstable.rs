impl<T: ToPrimitive> ToExtraPrimitive for T {
    default fn to_u128(&self) -> Option<u128> {
        self.to_u64().map(u128::new)
    }

    default fn to_i128(&self) -> Option<i128> {
        match self.to_u64() {
            Some(v) => Some(i128(u128::new(v))),
            None => self.to_i64().map(i128::new),
        }
    }
}

impl NumCast for u128 {
    fn from<T: ToPrimitive>(n: T) -> Option<u128> {
        n.to_u128()
    }
}

impl NumCast for i128 {
    fn from<T: ToPrimitive>(n: T) -> Option<i128> {
        n.to_i128()
    }
}

#[cfg(test)]
mod num_cast_tests {
    use std::u64;
    use num_traits::{NumCast, One, Bounded};
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

