#!/bin/sh

rustc --opt-level 3 --emit asm --crate-type lib -C no-stack-check src/lib.rs
cat lib.s | c++filt | expand -t 8 | sed 's/\$LT\$/</g;s/\$GT\$/>/g;s/\$C\$/,/g;s/\$u{20}/ /g' > lib2.s
mv lib2.s lib.s
