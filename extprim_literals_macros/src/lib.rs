#[macro_use] extern crate procedural_masquerade;
extern crate proc_macro;
extern crate extprim;

use extprim::u128::u128;
use extprim::i128::i128;
use extprim::traits::parse_rust_int_lit;

define_proc_macros! {
    pub fn internal_extprim_literals_macros_u128(input: &str) -> String {
        match parse_rust_int_lit::<u128>(input, false) {
            Ok(value) => format!("
                const VALUE: ::extprim::u128::u128 = ::extprim::u128::u128 {{
                    lo: {0},
                    hi: {1},
                }};
            ", value.lo, value.hi),
            Err(e) => panic!("{}", e),
        }
    }

    pub fn internal_extprim_literals_macros_i128(input: &str) -> String {
        let mut trimmed_input = input;
        let is_negative = input.starts_with("-");
        if is_negative {
            trimmed_input = input[1..].trim_left();
        }
        match parse_rust_int_lit::<i128>(trimmed_input, is_negative) {
            Ok(value) => format!("
                const VALUE: ::extprim::i128::i128 = ::extprim::i128::i128(::extprim::u128::u128{{
                    lo: {0},
                    hi: {1},
                }});
            ", value.0.lo, value.0.hi),
            Err(e) => panic!("{}", e),
        }
    }
}
