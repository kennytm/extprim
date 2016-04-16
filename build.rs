extern crate rustc_version;
use rustc_version::{version_meta, Channel};
use std::{env, fs};

pub fn main() {
    let channel = match version_meta().channel {
        Channel::Dev | Channel::Nightly => "unstable",
        Channel::Beta | Channel::Stable => "stable",
    };
    println!("cargo:rustc-cfg=extprim_channel=\"{}\"", channel);

    let src = format!("src/cast_{}.rs", channel);
    let target = format!("{}/cast.rs", env::var("OUT_DIR").unwrap());
    fs::copy(src, target).unwrap();
}

