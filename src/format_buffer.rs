use std::fmt;
use std::str::from_utf8_unchecked;

/// An internal structure used to format numbers. This is not intended for general use, since
/// irrelevant error checking is intentionally omitted.
pub struct FormatBuffer<'a> {
    buffer: &'a mut [u8],
    len: usize,
}

impl<'a> FormatBuffer<'a> {
    pub fn new(buffer: &mut [u8]) -> FormatBuffer {
        FormatBuffer {
            buffer: buffer,
            len: 0,
        }
    }

    pub unsafe fn into_str(self) -> &'a str {
        from_utf8_unchecked(&self.buffer[.. self.len])
    }
}

impl<'a> fmt::Write for FormatBuffer<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes = s.as_bytes();
        let new_len = self.len + bytes.len();
        self.buffer[self.len .. new_len].copy_from_slice(bytes);
        self.len = new_len;
        Ok(())
    }
}

#[cfg(test)]
macro_rules! assert_fmt_eq {
    ($expected:expr, $max_len:expr, $($args:expr),*) => {
        {
            use ::std::fmt::Write;

            let mut buffer = [0u8; $max_len];
            let mut buf = ::format_buffer::FormatBuffer::new(&mut buffer);
            write!(&mut buf, $($args),*).unwrap();
            assert_eq!($expected, unsafe { buf.into_str() });
        }
    }
}

#[test]
fn test_format_buffer() {
    assert_fmt_eq!("001234", 6, "{:06}", 1234);
    assert_fmt_eq!("5678", 16, "{}{}{}", 5, 6, 78);
}

