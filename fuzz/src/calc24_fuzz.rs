
#![no_main]

//#[macro_use] extern crate libfuzzer_sys;

//impl<'a> arbitrary::Arbitrary<'a> for &[Rational] { }     // XXX:

// cargo +nightly fuzz run calc24       # https://rust-fuzz.github.io/book/
// cargo +nightly fuzz coverage calc24  # XXX: rustup override set nightly
// cargo cov -- show fuzz/target/aarch64-apple-darwin/release/calc24 --format=html \
//      -instr-profile=fuzz/coverage/calc24/coverage.profdata > fuzz/coverage/calc24/index.html

libfuzzer_sys::fuzz_target!(|data: [i8; 5]| {   use inrust::calc24::*;  // XXX:
    let nums = data[1..].iter().map(|&n| (n as i32).into()).collect::<Vec<_>>();
    calc24_coll(&(data[0] as i32).into(), &nums, DynProg);
});

