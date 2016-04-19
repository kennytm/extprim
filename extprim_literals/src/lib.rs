#![cfg_attr(extprim_literals_channel="unstable", feature(plugin_registrar, rustc_private))]
#[cfg(extprim_literals_channel="unstable")] extern crate rustc_plugin;
#[cfg(extprim_literals_channel="unstable")] extern crate syntax;

#[cfg(extprim_literals_channel="stable")] extern crate syntex_syntax as syntax;

extern crate syntex;
extern crate extprim;
extern crate num_traits;

use syntax::ext::base::{ExtCtxt, MacResult, MacEager, DummyResult};
use syntax::ext::build::AstBuilder;
use syntax::codemap::{Span, Spanned, respan};
use syntax::ast::{TokenTree, Name, LitKind, LitIntType, UintTy};
use syntax::parse::token::{Token, Lit, BinOpToken};

use num_traits::Num;

use extprim::u128::u128;
use extprim::i128::i128;

use std::num::ParseIntError;
use std::error::Error;

#[cfg(extprim_literals_channel="unstable")]
#[plugin_registrar]
pub fn plugin_registrar(reg: &mut rustc_plugin::Registry) {
    reg.register_macro("u128", create_u128);
    reg.register_macro("i128", create_i128);
}

#[cfg(extprim_literals_channel="unstable")]
pub fn register(_: &mut syntex::Registry) {
    panic!("Should not call this in nightly!");
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
    from_literal(number, /*is_negative*/false)
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

    from_literal(number, is_negative)
        .map_err(|e| respan(sp, ParseError::ParseIntError(e)))
}


fn extract_number_from_token_tree(t: &TokenTree) -> Result<Name, Spanned<ParseError>> {
    match *t {
        TokenTree::Token(_, Token::Literal(Lit::Integer(number), _)) => Ok(number),
        _ => Err(respan(t.get_span(), ParseError::ExpectingIntegerLiteral))
    }
}


fn from_literal<T: Num>(name: Name, is_negative: bool) -> Result<T, T::FromStrRadixErr> {
    let s = name.as_str();
    let (base, digits) = if s.len() < 2 {
        (10, &*s)
    } else {
        match s.split_at(2) { // FIXME: Don't panic if index #2 is not a unicode boundary
            ("0x", d) | ("0X", d) => (16, d),
            ("0o", d) | ("0O", d) => (8, d),
            ("0b", d) | ("0B", d) => (2, d),
            _ => (10, &*s),
        }
    };
    let sign = if is_negative { "-" } else { "" };
    let digits = format!("{}{}", sign, digits.replace('_', ""));
    T::from_str_radix(&digits, base)
}

