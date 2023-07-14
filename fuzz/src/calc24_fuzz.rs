
#![no_main]

use inrust::calc24::*;
//#[macro_use] extern crate libfuzzer_sys;

//impl<'a> arbitrary::Arbitrary<'a> for &[Rational] { }     // XXX:

// https://rust-fuzz.github.io/book/
// XXX: rustup override set nightly

// cargo +nightly fuzz run calc24
// cargo +nightly fuzz coverage calc24
// cargo cov -- show fuzz/target/aarch64-apple-darwin/release/calc24 --format=html \
//      -instr-profile=fuzz/coverage/calc24/coverage.profdata > fuzz/coverage/calc24/index.html

libfuzzer_sys::fuzz_target!(|data: [i8; 5]| {   // XXX:
    let nums = data[1..].iter().map(|&n| Rational::from(n as i32)).collect::<Vec<_>>();
    calc24_coll(&(data[0] as i32).into(), &nums, DynProg);
});

