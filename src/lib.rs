
//! module/crate level documentation
// src/lib.rs (default library entry point)

#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

//pub use A::B::C as D;

//pub mod external_mod;     // mod file or dir with various mod.rs, relative to src/.
pub mod calc24;
pub mod prime;
pub mod list;

pub mod misc {
use num_traits::PrimInt;
pub struct Fibonacci<T> { curr: T, next: T }
impl<T: PrimInt> Iterator for Fibonacci<T> {
    fn next(&mut self) -> Option<Self::Item> {
        let new_next = self.curr + self.next;

        self.curr = self.next;
        self.next = new_next;

        Some(self.curr)
    }   type Item = T;
}

/// ```
/// # use inrust::misc::fibonacci;
/// assert_eq!(fibonacci().nth(0), Some(1));
/// assert_eq!(fibonacci().nth(1), Some(1));
/// assert_eq!(fibonacci().nth(4), Some(5));
/// ```
pub fn fibonacci<T: PrimInt>() -> Fibonacci<T> {    // Returns a Fibonacci sequence generator
    Fibonacci::<T> { curr: T::zero(), next: T::one() }
}

/** https://gist.github.com/synecdoche/9ade913c891dda6fcf1cdac823e7d524
 *
 * Given a set of type T, return a Vec containing the powerset, i.e. the set of all subsets.
 *
 * This works by treating each int the range [0, 2**n) (where n is the length of the set)
 * as a bitmask, selecting only the members of the original set whose corresponding
 * positional bits are flipped on in each mask.
 ```
    let set = vec![1, 2, 3];
    let psv = inrust::misc::powerset(&set);
    assert_eq!(psv.len(), 1 << set.len());
    vec![vec![], vec![1, 2, 3], vec![1], vec![2, 3], vec![2], vec![1, 3], vec![1, 2], vec![3]]
        .iter().enumerate().for_each(|(i, v)| v.iter().zip(psv[i].iter())
        .for_each(|(a, b)| assert_eq!(&a, b)));
 ```
 * pub fn powerset<T: Clone + Copy>(set: &[T]) -> Vec<Vec<T>>
 */
pub fn powerset<T>(set: &[T]) -> Vec<Vec<&T>> {
    let m = set.len();  let n = 1 << m;
    let mut psv = Vec::with_capacity(n);
    debug_assert!(m < std::mem::size_of::<usize>() * 8);

    for x in 0..n/2 {   // processing in pair wise more efficiently
        let (mut s0, mut s1) = (Vec::with_capacity(m), Vec::with_capacity(m));
        set.iter().enumerate().for_each(|(i, e)|
            if (1 << i) & x != 0 { s0.push(e) } else { s1.push(e) });
        psv.push(s0);   psv.push(s1);
    }   psv

    /* for mask in 0..n {   let (mut ss, mut bits) = (vec![], mask);
        while 0 < bits {
            let rightmost = bits & !(bits - 1);     // isolate the rightmost bit to select one
            let idx = rightmost.trailing_zeros();   // turn the isolated bit into an array index
            ss.push(&slice[idx as usize]);  bits &= bits - 1;   // zero the trailing bit
        }  psv.push(ss);
    }      psv */
}

/// ```
/// let str = "Hello, World!";
/// assert_eq!(inrust::misc::shell_pipe("echo", &[str], "").unwrap(), str.to_owned() + "\n");
/// ```
pub fn shell_pipe(prog: &str, args: &[&str], inps: &str) -> std::io::Result<String> {
    // https://doc.rust-lang.org/rust-by-example/std_misc/process/pipe.html
    use std::process::{Command, Stdio};

    Command::new(prog).args(args).stdin(Stdio::piped())
        .stdout(Stdio::piped()).spawn().and_then(|proc| {
            use std::io::{Read, Write, Error, ErrorKind::BrokenPipe};
            proc.stdin .ok_or_else(|| Error::from(BrokenPipe))
                .and_then(|mut stdin| stdin.write_all(inps.as_bytes()))?;
            proc.stdout.ok_or_else(|| Error::from(BrokenPipe))
                .and_then(|mut stdout| {
                    let mut outs = String::new();
                    stdout.read_to_string(&mut outs)?;
                    Ok(outs)
                })
        })
}

pub fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];     // for &item in list {}
    for item in list { if largest < item { largest = item } }  largest
}

#[cfg_attr(coverage_nightly, coverage(off))] //#[cfg(not(tarpaulin_include))]
#[cfg(feature = "num-bigint")] pub fn calc_pi() {
    // a streaming/spigot algorithm, https://rosettacode.org/wiki/Pi
    use num_bigint::BigInt;
    let mut first = true;

    let mut q = BigInt::from(1);
    let mut r = BigInt::from(0);
    let mut t = BigInt::from(1);
    let mut k = BigInt::from(1);
    let mut n = BigInt::from(3);
    let mut l = BigInt::from(3);

    loop {
        if &q * 4 + &r - &t < &n * &t {
            print!("{}", n);
            if first { print!("."); first = false; }
            let nr = (&r - &n * &t) * 10;
            n = (&q * 3 + &r) * 10 / &t - &n * 10;
            q *= 10;    r = nr;
        } else {
            let nr = (&q * 2 + &r) * &l;
            let nn = (&q * &k * 7 + 2 + &r * &l) / (&t * &l);
            q *= &k;    k += 1;     n = nn;
            t *= &l;    l += 2;     r = nr;
        }
    }
}
}

mod m {
    #[allow(dead_code)] pub fn g() { }
    // No public path (`m` not public) from root,
    // so `g` is not accessible from the outside of the crate.
}

//#![feature(test)]
//extern crate test;

#[cfg(test)] mod tests {    // unit test sample
    // Need to import items from parent module. Has access to non-public members.
    //use test::Bencher;
    use super::*;

    //#[should_panic(expect = "some panic string")] //#[should_panic]
    #[test] fn test_g() -> Result<(), String> {     m::g();
        if 0 == 0 { Ok(()) } else { Err(String::from("Failed")) }
    }
}

/* src/lib.rs is also the default entry point for proc macros
extern crate proc_macro;    // Apparently needed to be imported like this.
use proc_macro::TokenStream;

//#[proc_macro_attribute]     // Can now be used as `#[my_attribute]`
//pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream { item }

// https://github.com/AlephAlpha/build-time
//static BUILD_TIME: Lazy<DateTime<Utc>> = Lazy::new(Utc::now);

#[proc_macro] pub fn build_time(input: TokenStream) -> TokenStream {
    let current = chrono::Local::now(); //BUILD_TIME;
    let timestr = if input.is_empty() { current.to_rfc3339() } else {
        let fmtstr = syn::parse_macro_input!(input as syn::LitStr);
        //let fmtstr: syn::LitStr = syn::parse(input).unwrap();
        current.format(&fmtstr.value()).to_string()
    };

    let lit = syn::LitStr::new(&timestr, proc_macro2::Span::call_site());
    quote::quote!(#lit).into()
} */
