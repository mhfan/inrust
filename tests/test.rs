
//use study_rust;

//mod common;   // subdirectory module

#[test]
fn sample_test() {
    assert_eq!(study_rust::f(), 0);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}
