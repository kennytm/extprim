extern crate rustc_version;
extern crate semver;
use rustc_version::{version_meta, Channel};
use semver::Version;

pub fn main() {
    let version = version_meta().unwrap();
    let channel = match version.channel {
        Channel::Dev | Channel::Nightly => "unstable",
        Channel::Beta | Channel::Stable => "stable",
    };
    println!("cargo:rustc-cfg=extprim_channel=\"{}\"", channel);
    if version.semver >= Version::new(1, 26, 0) {
        println!("cargo:rustc-cfg=extprim_has_stable_i128");
    }
}

