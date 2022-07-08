
// https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html

fn main() {
    let comp24_cpp = "src/comp24.cpp";
    println!("cargo:rerun-if-changed={comp24_cpp}");
    cc::Build::new().cpp(true).flag("-std=c++20").opt_level(2)
        //.define("USE_LIST", None)//.define("RUN_TEST", None)
        .file(comp24_cpp).compile("comp24");   // output libcomp24.a indeed
}
