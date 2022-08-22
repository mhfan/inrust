
//mod common;   // subdirectory module

#[test] fn test_largest() {
    let array = [1, 2, 3];
    assert_eq!(inrust::largest(&array), &array[2]);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}
