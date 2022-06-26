// https://cheats.rs

// src/lib.rs (default library entry point)

/* https://lib.rs/crates/build_timestamp

extern crate syn;
extern crate time;
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro]
pub fn build_time(input: TokenStream) -> TokenStream {
    // TODO support passing the name of the generated const as an argument
    // TODO proper error handling

    let time = time::now_utc();
    let fmtstr: syn::LitStr = syn::parse(input).unwrap();
    let ftime = time::strftime(&fmtstr.value(), &time).unwrap();

    let mut out_str = String::new();
    out_str.push_str("const BUILD_TIME: &str = \"");
    out_str.push_str(&ftime);
    out_str.push_str("\";");
    out_str.parse().unwrap()
} */

//#![feature(test)]
//extern crate test;

pub fn f() -> i32 { 0 }     // Public item in root, accessible from the outside.
//pub mod external_mod;     // mod file or dir with various mod.rs, relative to src/.
pub mod comp24;
//pub mod list;

mod m {
    #[allow(dead_code)]
    pub fn g() { }
    // No public path (`m` not public) from root,
    // so `g` is not accessible from the outside of the crate.
}

#[cfg(test)]
mod tests { // unit test sample
    //use test::Bencher;
    // Need to import items from parent module. Has access to non-public members.
    use super::*;

    #[test]
    //#[should_panic]
    //#[should_panic(expect = "some panic string")]
    fn test_f() { assert_eq!(f(), 0); }

    #[test]
    fn test_g() -> Result<(), String> {
        if 0 == 0 { Ok(()) } else { Err(String::from("Failed")) }
    }
}

/* src/lib.rs is also the default entry point for proc macros
extern crate proc_macro;    // Apparently needed to be imported like this.

use proc_macro::TokenStream;

#[proc_macro_attribute]     // Can now be used as `#[my_attribute]`
pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream { item } */
