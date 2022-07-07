
// src/lib.rs (default library entry point)

#![allow(dead_code)]
pub fn f() -> i32 { 0 }     // Public item in root, accessible from the outside.
//pub mod external_mod;     // mod file or dir with various mod.rs, relative to src/.
pub mod comp24;
//pub mod list;

mod m {
    pub fn g() { }
    // No public path (`m` not public) from root,
    // so `g` is not accessible from the outside of the crate.
}

//#![feature(test)]
//extern crate test;

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

//#[proc_macro_attribute]     // Can now be used as `#[my_attribute]`
//pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream { item }

// https://github.com/AlephAlpha/build-time
//static BUILD_TIME: Lazy<DateTime<Utc>> = Lazy::new(Utc::now);

#[proc_macro]
pub fn build_time(input: TokenStream) -> TokenStream {
    let current = chrono::Local::now();
    let timestr = if input.is_empty() { current.to_rfc3339() } else {
        let fmtstr = syn::parse_macro_input!(input as syn::LitStr);
        //let fmtstr: syn::LitStr = syn::parse(input).unwrap();
        current.format(&fmtstr.value()).to_string()
    };

    let lit = syn::LitStr::new(&timestr, proc_macro2::Span::call_site());
    quote::quote!(#lit).into()
} */
