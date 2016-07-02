use core::num::ParseIntError;
use core::mem::transmute;

pub fn invalid_digit() -> ParseIntError {
    unsafe { transmute(1u8) }
}

pub fn underflow() -> ParseIntError {
    unsafe { transmute(3u8) }
}

pub fn overflow() -> ParseIntError {
    unsafe { transmute(2u8) }
}

pub fn empty() -> ParseIntError {
    unsafe { transmute(0u8) }
}

pub fn is_overflow(e: &ParseIntError) -> bool {
    *e == overflow()
}

#[cfg(test)]
mod tests {
    use error;

    #[test]
    fn test_local_parse_int_error_to_std() {
        assert_fmt_eq!("invalid digit found in string", 29, "{}", error::invalid_digit());
        assert_fmt_eq!("cannot parse integer from empty string", 38, "{}", error::empty());
        assert_fmt_eq!("number too large to fit in target type", 38, "{}", error::overflow());
        assert_fmt_eq!("number too small to fit in target type", 38, "{}", error::underflow());
    }
}

