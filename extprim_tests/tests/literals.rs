#![cfg_attr(extprim_tests_channel="unstable", feature(const_fn, i128_type))]
#[cfg(extprim_tests_channel="unstable")] extern crate rustc_i128;

include!(concat!(env!("OUT_DIR"), "/literals.rs"));
