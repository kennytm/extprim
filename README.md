extprim
=======

[![Travis (Linux and OS X) Build status](https://travis-ci.org/kennytm/extprim.svg?branch=master)](https://travis-ci.org/kennytm/extprim)
[![AppVeyor (Windows) Build status](https://ci.appveyor.com/api/projects/status/59h8ugya24odwtgd/branch/master?svg=true)](https://ci.appveyor.com/project/kennytm/extprim/branch/master)
[![Coverage Status](https://coveralls.io/repos/github/kennytm/extprim/badge.svg?branch=master)](https://coveralls.io/github/kennytm/extprim?branch=master)
[![crates.io](http://meritbadge.herokuapp.com/extprim)](https://crates.io/crates/extprim)
[![MIT / Apache 2.0](https://img.shields.io/badge/license-MIT%20%2f%20Apache%202.0-blue.svg)](./LICENSE-APACHE.txt)

> *Thanks to [RFC 1504 “int128”](https://github.com/rust-lang/rfcs/blob/master/text/1504-int128.md), you can use `i128`
> and `u128` directly on nightly Rust starting from 1.16. Using the built-in types are preferred.*

Extra primitive types for stable Rust. Currently includes:

* `u128` (unsigned 128-bit integers)
* `i128` (signed 128-bit integers)

[Documentation](https://docs.rs/extprim)

You may also find other primitive types in other crates:

* `u12` → [twelve_bit](https://crates.io/crates/twelve_bit)
* `f16` → [half](https://crates.io/crates/half)
* `d128` → [decimal](https://crates.io/crates/decimal)
* `Complex<T>` → [num-complex](https://crates.io/crates/num-complex)

Usage
-----

```toml
# Cargo.toml
[dependencies]
extprim = "1"
```

If you want to use the `u128!()` and `i128!()` macros, please include the `extprim_literals` plugin.

```toml
# Cargo.toml
[dependencies]
extprim = "1"
extprim_literals = "2"
```

Example
-------

```rust
#[macro_use]
extern crate extprim_literals;
extern crate extprim;

use std::str::FromStr;
use extprim::i128::i128;

fn main() {
    let a = i128::from_str("100000000000000000000000000000000000000").unwrap();
            // convert string to u128 or i128
    let b = i128::new(10).pow(38);
            // 64-bit integers can be directly new'ed
    assert_eq!(a, b);

    let c = i128::from_parts(5421010862427522170, 687399551400673280);
            // represent using the higher- and lower-64-bit parts
    let d = c - a;
            // standard operators like +, -, *, /, %, etc. work as expected.
    assert_eq!(d, i128::zero());

    const e: i128 = i128!(100000000000000000000000000000000000000);
            // use the literal macros
    assert_eq!(a, e);
}
```

