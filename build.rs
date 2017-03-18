extern crate rustc_version;
use rustc_version::{version_meta, Channel};

pub fn main() {
    let channel = match version_meta().unwrap().channel {
        Channel::Dev | Channel::Nightly => "unstable",
        Channel::Beta | Channel::Stable => "stable",
    };
    println!("cargo:rustc-cfg=extprim_channel=\"{}\"", channel);
}

