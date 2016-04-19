#![cfg_attr(extprim_tests_channel="unstable", feature(plugin))]
#![cfg_attr(extprim_tests_channel="unstable", plugin(extprim_literals))]

include!(concat!(env!("OUT_DIR"), "/literals.rs"));

