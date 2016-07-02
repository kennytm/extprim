//! Literal macros for `extprim`.
//!
//! This crate provides a compiler plugin (on nightly) or syntex extension (on stable) so that the
//! `extprim` types can be constructed at compile-time using the `i128!()` and `u128!()` macros.
//!
//! Setup as compiler plugin (nightly)
//! ==================================
//!
//! Add `extprim_literals` to the dev-dependencies in `Cargo.toml`:
//!
//! ```toml
//! [dev-dependencies]
//! extprim_literals = "1.1.0"
//! ```
//!
//! Then just use the plugin:
//!
//! ```rust
//! #![feature(plugin)]
//! #![plugin(extprim_literals)]
//!
//! use extprim::u128::u128;
//!
//! const TEN: u128 = u128!(10);
//! ```
//!
//! Setup as syntex extension (stable)
//! ==================================
//!
//! Supply a `build.rs`, and add `syntex` and `extprim_literals` to the build-dependencies in
//! `Cargo.toml`:
//!
//! ```toml
//! [package]
//! build = "build.rs"
//!
//! [build-dependencies]
//! extprim_literals = "1.1.0"
//! syntex = "0.36.0"
//! ```
//!
//! Register `extprim_literals` to `syntex` in `build.rs`:
//!
//! ```no_run
//! extern crate syntex;
//! extern crate extprim_literals;
//!
//! use syntex::Registry;
//! use std::env;
//! use std::path::Path;
//!
//! fn main() {
//!     let mut registry = Registry::new();
//!     extprim_literals::register(&mut registry);
//!
//!     let src = Path::new("src/consts.rs.in");
//!     let dst = Path::new(&env::var("OUT_DIR").unwrap()).join("consts.rs");
//!
//!     registry.expand("extprim_literals", &src, &dst).unwrap();
//! }
//! ```
//!
//! Use the macros in `src/consts.rs.in`:
//!
//! ```ignore
//! use extprim::u128::u128;
//!
//! const TEN: u128 = u128!(10);
//! ```
//!
//! Include the expanded file in `src/consts.rs`:
//!
//! ```no_run
//! include!(concat!(env!("OUT_DIR"), "/consts.rs"));
//! ```

#![cfg_attr(extprim_literals_channel="unstable", feature(plugin_registrar, rustc_private))]
#[cfg(extprim_literals_channel="unstable")] extern crate rustc_plugin;
#[cfg(extprim_literals_channel="unstable")] extern crate syntax;

#[cfg(extprim_literals_channel="stable")] extern crate syntex_syntax as syntax;

extern crate syntex;
extern crate extprim;

use syntax::ext::base::{ExtCtxt, MacResult, MacEager, DummyResult};
use syntax::ext::build::AstBuilder;
use syntax::codemap::{Span, Spanned, respan};
use syntax::ast::{Name, LitKind, LitIntType, UintTy};
#[cfg(extprim_literals_channel="stable")] use syntax::ast::TokenTree;
#[cfg(extprim_literals_channel="unstable")] use syntax::tokenstream::TokenTree;
use syntax::parse::token::{Token, Lit, BinOpToken};

use extprim::u128::u128;
use extprim::i128::i128;
use extprim::traits::parse_rust_int_lit;

use std::num::ParseIntError;
use std::error::Error;

/// Creates an unsigned 128-bit integer at compile time. The content can be any integer literals
/// supported by Rust, e.g.
///
/// ```no_run
/// u128!(190645052318211650775886739373212217031);
/// u128!(290_016_114_491_568_400_953_264_683_755_668_101_244);
/// u128!(0x1755_7146_02da_b606_e059_515e_7938_5189);
/// u128!(0o3653247246101356646675471111622746760005231);
/// u128!(0b11001001000000101100010000101110100001100110100100110110000100011110110110010111);
/// ```
#[cfg(feature="doc_only")]
#[macro_export]
macro_rules! u128 {
    ($lit:expr) => { ... };
}

/// Creates a signed 128-bit integer at compile time. The content can be any integer literals
/// supported by Rust, e.g.
///
/// ```no_run
/// i128!(123623219786789911069641050508607316353);
/// i128!(+1241909465635371210237387091769850650);
/// i128!(-42128403654828209595896121373164578595);
/// i128!(-0x34c1b7a2_2955e5bb_03cc1a88_342b9e8d);
/// i128!(0o1_151760_574675_745253_103376_166404_235110_762614);
/// i128!(-0b11000111001101001100001010010111110101000101011011011111101111111111110101110110);
/// ```
#[cfg(feature="doc_only")]
#[macro_export]
macro_rules! i128 {
    ($lit:expr) => { ... };
    (+$lit:expr) => { ... };
    (-$lit:expr) => { ... };
}

#[cfg(extprim_literals_channel="unstable")]
#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut rustc_plugin::Registry) {
    reg.register_macro("u128", create_u128);
    reg.register_macro("i128", create_i128);
}

/// Register the `extprim_literals` macros to the `syntex` registry.
///
/// Calling this with a nightly compiler will cause panic.
#[cfg(extprim_literals_channel="unstable")]
pub fn register(_: &mut syntex::Registry) {
    panic!("Should not call `extprim_literals::register` in nightly!");
}

#[cfg(extprim_literals_channel="stable")]
pub fn register(reg: &mut syntex::Registry) {
    reg.add_macro("u128", create_u128);
    reg.add_macro("i128", create_i128);
}

const U64_TYPE: LitIntType = LitIntType::Unsigned(UintTy::U64);

enum ParseError {
    ParseIntError(ParseIntError),
    ExpectingIntegerLiteral,
    ExpectingPlusOrMinus,
    InvalidU128Content,
    InvalidI128Content,
}

impl ParseError {
    fn description(&self) -> &str {
        match *self {
            ParseError::ParseIntError(ref e) => e.description(),
            ParseError::ExpectingIntegerLiteral => "Expecting an integer literal here",
            ParseError::ExpectingPlusOrMinus => "Expecting `+` or `-` here",
            ParseError::InvalidU128Content => "Wrong u128 literal syntax, it should look like `u128!(0x2468_abcd)`",
            ParseError::InvalidI128Content => "Wrong i128 literal syntax, it should look like `i128!(-23_456_789)`",
        }
    }
}

/// Translate `u128!(1234567…)` to `::u128::u128 { lo: …, hi: … }`
fn create_u128<'c>(cx: &'c mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'c> {
    match parse_u128(sp, tts) {
        Err(e) => {
            cx.span_err(e.span, e.node.description());
            DummyResult::expr(sp)
        }
        Ok(number) => {
            let u128_ident = cx.ident_of("u128");
            let u128_path = cx.path_global(sp, vec![cx.ident_of("extprim"), u128_ident, u128_ident]);
            MacEager::expr(cx.expr_struct(sp, u128_path, vec![
                cx.field_imm(sp,
                    cx.ident_of("hi"),
                    cx.expr_lit(sp, LitKind::Int(number.hi, U64_TYPE))
                ),
                cx.field_imm(sp,
                    cx.ident_of("lo"),
                    cx.expr_lit(sp, LitKind::Int(number.lo, U64_TYPE))
                ),
            ]))
        }
    }
}

/// Translate `i128!(1234567…)` to `i128::i128(u128::u128 { hi: …, lo: … })`.
fn create_i128<'c>(cx: &'c mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'c> {
    match parse_i128(sp, tts) {
        Err(e) => {
            cx.span_err(e.span, e.node.description());
            DummyResult::expr(sp)
        }
        Ok(number) => {
            let extprim_ident = cx.ident_of("extprim");
            let u128_ident = cx.ident_of("u128");
            let i128_ident = cx.ident_of("i128");
            let u128_path = cx.path_global(sp, vec![extprim_ident, u128_ident, u128_ident]);
            let i128_path = vec![extprim_ident, i128_ident, i128_ident];
            MacEager::expr(cx.expr_call_global(sp, i128_path, vec![
                cx.expr_struct(sp, u128_path, vec![
                    cx.field_imm(sp,
                        cx.ident_of("hi"),
                        cx.expr_lit(sp, LitKind::Int(number.0.hi, U64_TYPE))
                    ),
                    cx.field_imm(sp,
                        cx.ident_of("lo"),
                        cx.expr_lit(sp, LitKind::Int(number.0.lo, U64_TYPE))
                    ),
                ])
            ]))
        }
    }
}


fn parse_u128(sp: Span, tts: &[TokenTree]) -> Result<u128, Spanned<ParseError>> {
    if tts.len() != 1 {
        return Err(respan(sp, ParseError::InvalidU128Content));
    }
    let number = try!(extract_number_from_token_tree(&tts[0]));
    parse_rust_int_lit(&number.as_str(), /*is_negative*/false)
        .map_err(|e| respan(sp, ParseError::ParseIntError(e)))
}


fn parse_i128(sp: Span, tts: &[TokenTree]) -> Result<i128, Spanned<ParseError>> {
    let length = tts.len();
    if length == 0 || length > 2 {
        return Err(respan(sp, ParseError::InvalidI128Content));
    }

    let number = try!(extract_number_from_token_tree(&tts[length-1]));
    let is_negative = length == 2 && match tts[0] {
        TokenTree::Token(_, Token::BinOp(BinOpToken::Plus)) => false,
        TokenTree::Token(_, Token::BinOp(BinOpToken::Minus)) => true,
        ref t => return Err(respan(t.get_span(), ParseError::ExpectingPlusOrMinus)),
    };

    parse_rust_int_lit(&number.as_str(), is_negative)
        .map_err(|e| respan(sp, ParseError::ParseIntError(e)))
}


fn extract_number_from_token_tree(t: &TokenTree) -> Result<Name, Spanned<ParseError>> {
    match *t {
        TokenTree::Token(_, Token::Literal(Lit::Integer(number), _)) => Ok(number),
        _ => Err(respan(t.get_span(), ParseError::ExpectingIntegerLiteral))
    }
}

