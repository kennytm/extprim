#![feature(asm)]
#![feature(slicing_syntax)]
#![feature(macro_rules)]

//! This crate provides some extra primitive types.

extern crate test;

macro_rules! try_option {
    ($e:expr) => (
        match $e {
            Some(e) => e,
            None => return None,
        }
    );
}

pub mod u128;
pub mod i128;
mod compiler_rt;

