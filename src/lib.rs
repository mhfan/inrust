// https://cheats.rs

// src/lib.rs (default library entry point)

pub fn f() -> i32 { 0 }
// Public item in root, accessible from the outside.

//pub mod external_mod;     // mod file or dir with various mod.rs, relative to src/.

mod m {
    #[allow(dead_code)]
    pub fn g() { }
    // No public path (`m` not public) from root,
    // so `g` is not accessible from the outside of the crate.
}

#[cfg(test)]
mod tests {  // unit test sample
    use super::f;   // Need to import items from parent module. Has access to non-public members.
    #[test]
    //#[should_panic]
    //#[should_panic(expect = "some panic string")]
    fn testf() {
        assert_eq!(f(), 0);
    }

    #[test]
    fn testg() -> Result<(), String> {
        if 0 == 0 { Ok(()) } else { Err(String::from("Failed")) }
    }
}

/* src/lib.rs is also the default entry point for proc macros
extern crate proc_macro;    // Apparently needed to be imported like this.

use proc_macro::TokenStream;

#[proc_macro_attribute]     // Can now be used as `#[my_attribute]`
pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream { item }
*/
