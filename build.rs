
// https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html

fn main() {
    let calc24_cpp = "src/calc24.cpp";
    println!("cargo:rerun-if-changed={calc24_cpp}");
    println!("cargo:rerun-if-changed=src/calc24.h");

    #[cfg(feature = "cc")] cc::Build::new().cpp(true).flag("-std=c++20").opt_level(2)
        .define("NDEBUG", None) //.define("USE_LIST", None)//.define("RUN_TEST", None)
        .file(calc24_cpp).compile("calc24");   // libcalc24.a
}
