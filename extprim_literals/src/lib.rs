#![allow(unstable)]

#![feature(slicing_syntax)]
#![feature(plugin_registrar)]
#![feature(quote)]

extern crate extprim;
extern crate syntax;
extern crate rustc;

use std::num::{cast, Int};

use extprim::u128::u128;
use extprim::i128::i128;

use syntax::ast::TokenTree;
use syntax::ast::TokenTree::TtToken;
use syntax::parse::token::Token::{Literal, BinOp};
use syntax::parse::token::BinOpToken::{Minus, Plus};
use syntax::parse::token::Lit::Integer;
use syntax::codemap::Span;
use syntax::ext::base::{ExtCtxt, MacResult, MacExpr, DummyResult};

use rustc::plugin::Registry;

#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("u128", create_u128);
    reg.register_macro("i128", create_i128);
}


/// Translate `u128!(1234567…)` to `u128 { lo: …, hi: … }`
fn create_u128(cx: &mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'static> {
    let res: Result<u128, &str> = match tts {
        [TtToken(_, Literal(Integer(number), _))] => {
            let number_str = number.as_str();
            match from_literal(number_str, false) {
                Some(number) => Ok(number),
                None => Err("u128 literal is too large"),
            }
        },
        _ => Err("Usage: u128!(1234567)"),
    };

    match res {
        Ok(number) => {
            let hi = number.hi;
            let lo = number.lo;
            MacExpr::new(quote_expr!(cx,
                ::extprim::u128::u128 { lo: $lo, hi: $hi }
            ))
        }
        Err(err_msg) => {
            cx.span_err(sp, err_msg);
            DummyResult::expr(sp)
        }
    }
}

fn create_i128(cx: &mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'static> {
    let res = match tts {
        [TtToken(_, BinOp(Minus)), TtToken(_, Literal(Integer(number), _))] =>
            Ok(from_literal(number.as_str(), true)),
        [TtToken(_, BinOp(Plus)), TtToken(_, Literal(Integer(number), _))] =>
            Ok(from_literal(number.as_str(), false)),
        [TtToken(_, Literal(Integer(number), _))] =>
            Ok(from_literal(number.as_str(), false)),
        _ => Err("Usage: i128!(-1234567)"),
    };

    res.and_then(|opt_number: Option<i128>| {
        match opt_number {
            Some(number) => {
                let hi = number.0.hi;
                let lo = number.0.lo;
                Ok(MacExpr::new(quote_expr!(cx,
                    ::extprim::i128::i128(::extprim::u128::u128 { lo: $lo, hi: $hi })
                )))
            }
            None => Err("i128 literal is too large")
        }
    }).unwrap_or_else(|err_msg| {
        cx.span_err(sp, err_msg);
        DummyResult::expr(sp)
    })
}


macro_rules! try_option {
    ($e:expr) => (
        match $e {
            Some(e) => e,
            None => return None,
        }
    );
}

fn from_literal<T: Int>(s: &str, is_negative: bool) -> Option<T> {
    let mut res: T = Int::zero();
    let mut base: T = cast(10u64).unwrap();

    for c in s.chars() {
        match c {
            'x' => { base = cast(16u64).unwrap(); },
            'o' => { base = cast(8u64).unwrap(); },
            'b' if base == cast(10u64).unwrap() => { base = cast(2u64).unwrap(); }
            '_' => {},
            _ => {
                let digit = cast(try_option!(c.to_digit(16))).unwrap();
                res = try_option!(res.checked_mul(base));
                if is_negative {
                    res = try_option!(res.checked_sub(digit));
                } else {
                    res = try_option!(res.checked_add(digit));
                }
            }
        }
    }

    Some(res)
}

