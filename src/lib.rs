
// src/lib.rs (default library entry point)

pub fn f() { }
//pub fn f() -> i32 { 0 }
// Public item in root, accessible from the outside.

mod m {
    #[allow(dead_code)]
    pub fn g() { }
    // No public path (`m` not public) from root,
    // so `g` is not accessible from the outside of the crate.
}

#[cfg(test)]
mod test {  // unit test sample
    use super::f;   // Need to import items from parent module. Has access to non-public members.
    #[test]
    fn testf() {
        assert_eq!(f(), 0);
    }
}

/* tests/sample.rs (sample integration test)

#[test]
fn sample_test() {
    assert_eq!(study_rust::f(), 123);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}
*/

/* src/lib.rs is also the default entry point for proc macros
extern crate proc_macro;    // Apparently needed to be imported like this.

use proc_macro::TokenStream;

#[proc_macro_attribute]     // Can now be used as `#[my_attribute]`
pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream { item }
*/
