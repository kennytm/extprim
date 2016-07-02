#!/bin/sh

TARGET=aarch64-apple-ios

rustup run stable cargo rustc --target $TARGET --release --no-default-features -- --emit asm -C no-stack-check
cat target/$TARGET/release/extprim.s | c++filt | expand -t 8 | sed 's/\$LT\$/</g;s/\$GT\$/>/g;s/\$C\$/,/g;s/\$u20\$/ /g;s/\$u27\$/'"'"'/g;s/\$u7b\$/{/g;s/\$u7d\$/}/g;' > lib.s

