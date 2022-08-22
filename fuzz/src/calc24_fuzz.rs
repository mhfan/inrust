
#![no_main]

use inrust::calc24::*;
use libfuzzer_sys::fuzz_target;
//#[macro_use] extern crate libfuzzer_sys;

//impl<'a> arbitrary::Arbitrary<'a> for Rational {}

// https://rust-fuzz.github.io/book/
// XXX: rustup override set nightly

// cargo +nightly fuzz run calc24
// cargo +nightly fuzz coverage calc24
// cargo cov -- show fuzz/target/aarch64-apple-darwin/release/calc24 --format=html \
//      -instr-profile=fuzz/coverage/calc24/coverage.profdata > fuzz/coverage/calc24/index.html

fuzz_target!(|data: Vec<Rational>| {
    if data.len() < 3 || 6 < data.len() { return }  // FIXME: why return don't work?
    if data.iter().any(|rn| rn.denom() == &0 || 100 < rn.numer().abs() ||
                                                100 < rn.denom().abs()) { return }
    let nums = data.iter().skip(1).map(|n| Rc::new((*n).into())).collect::<Vec<_>>();
    calc24_algo(&data[0], &nums, DynProg (false));
});