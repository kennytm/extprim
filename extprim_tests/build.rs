extern crate rustc_version;
extern crate syntex;
extern crate extprim_literals;

use rustc_version::{version_meta, Channel};
use syntex::Registry;

use std::{fs, env};
use std::path::{Path, PathBuf};
use std::ffi::OsStr;

struct Plugin {
    out_dir: PathBuf,
    is_unstable: bool,
}

impl Plugin {
    fn new(is_unstable: bool) -> Plugin {
        Plugin {
            out_dir: PathBuf::from(env::var("OUT_DIR").unwrap()),
            is_unstable: is_unstable,
        }
    }

    fn run(&self) {
        for file in fs::read_dir("tests").unwrap() {
            let file = file.unwrap();
            if file.file_type().unwrap().is_file() {
                let path = file.path();
                if path.extension() == Some(OsStr::new("rs_syntex")) {
                    self.apply(&path);
                }
            }
        }
    }

    fn apply(&self, path: &Path) {
        let mut target_path = self.out_dir.join(path.file_name().unwrap());
        target_path.set_extension("rs");
        if self.is_unstable {
            fs::copy(path, target_path).unwrap();
        } else {
            let mut registry = Registry::new();
            extprim_literals::register(&mut registry);
            registry.expand("extprim_literals", path, &target_path).unwrap();
        }
    }
}


fn main() {
    let is_unstable = match version_meta().channel {
        Channel::Dev | Channel::Nightly => true,
        Channel::Beta | Channel::Stable => false,
    };

    let channel = if is_unstable { "unstable" } else { "stable" };
    println!("cargo:rustc-cfg=extprim_tests_channel=\"{}\"", channel);

    let plugin = Plugin::new(is_unstable);
    plugin.run();
}
