
// https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html

fn main() {
    let calc24_cpp = "src/calc24.cpp";
    println!("cargo:rerun-if-changed={calc24_cpp}");

    //println!("cargo:rerun-if-changed=src/calc24.h");
    //println!("cargo:rerun-if-changed=src/cpp/");    // scan files under the path directory

    #[cfg(feature = "cc")] cc::Build::new().cpp(true).flag("-std=c++20").opt_level(2)
        //.define("USE_LIST", None)//.define("RUN_TEST", None)  // libcalc24.a
        .define("NDEBUG", None).file(calc24_cpp).compile("calc24");

    println!("cargo:rerun-if-changed=.git/index");
    let output = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"]).output().unwrap();
    println!("cargo:rustc-env=BUILD_GIT_HASH={}", String::from_utf8(output.stdout).unwrap());

    //println!("cargo:rustc-env=BUILD_TIMESTAMP={}",  // XXX: not run on every build
    //    chrono::Local::now().format("%H:%M:%S%:z %Y-%m-%d"));

    //println!("cargo:rerun-if-changed=build.rs");    // XXX: prevent re-run indead
}
