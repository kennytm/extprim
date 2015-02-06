use core::num::ParseIntError;
use std::str::FromStr;

lazy_static! {
    pub static ref INVALID_DIGIT: ParseIntError = <i8 as FromStr>::from_str("?").unwrap_err();
    pub static ref UNDERFLOW: ParseIntError = <i8 as FromStr>::from_str("-999").unwrap_err();
    pub static ref OVERFLOW: ParseIntError = <i8 as FromStr>::from_str("999").unwrap_err();
    pub static ref EMPTY: ParseIntError = <i8 as FromStr>::from_str("").unwrap_err();
}

#[cfg(test)]
mod local_parse_int_error_tests {
    use std::error::Error;
    use error;

    #[test]
    fn test_local_parse_int_error_to_std() {
        let test_cases = &[
            (&*error::INVALID_DIGIT, "invalid digit found in string"),
            (&*error::EMPTY, "cannot parse integer from empty string"),
            (&*error::OVERFLOW, "number too large to fit in target type"),
            (&*error::UNDERFLOW, "number too small to fit in target type"),
        ];

        for &(err, desc) in test_cases {
            assert_eq!(err.description(), desc);
        }
    }
}
