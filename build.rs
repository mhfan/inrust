
// https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html

fn main() {
    let comp24_cpp = "src/comp24.cpp";
    println!("cargo:rerun-if-changed={comp24_cpp}");
    println!("cargo:rerun-if-changed=src/comp24.h");

    #[cfg(feature = "cc")] cc::Build::new().cpp(true).flag("-std=c++2a").opt_level(2)
        .define("NDEBUG", None) //.define("USE_LIST", None)//.define("RUN_TEST", None)
        .file(comp24_cpp).compile("comp24");   // libcomp24.a
}
