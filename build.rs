
use std::path::Path;

fn main() {     // https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html
    //println!("cargo:rerun-if-changed=build.rs");    // XXX: prevent re-run indead
    // By default, cargo always re-run the build script if any file within the package
    // is changed, and no any rerun-if instruction is emitted.
    println!("cargo:rerun-if-changed=src");    // scan files under the path directory
    println!("cargo:rustc-env=BUILD_TIMESTAMP={}",
        chrono::Local::now().format("%H:%M:%S%z %Y-%m-%d"));

    let output = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"]).output().unwrap();
    println!("cargo:rustc-env=BUILD_GIT_HASH={}", String::from_utf8(output.stdout).unwrap());
    println!("cargo:rerun-if-changed={}", Path::new(".git").join("index").display());

    #[allow(unused)] let mut calc24_file = Path::new("src").join("calc24.rs");
    #[cfg(feature = "cxx")] let mut build = cxx_build::bridge(calc24_file);
    #[cfg(not(feature = "cxx"))] #[cfg(feature = "cc")] let mut build = cc::Build::new();

    #[cfg(any(feature = "cc", feature = "cxx"))] { calc24_file.set_extension("cpp");
        build.cpp(true).flag("-std=c++20").flag("-Wno-misleading-indentation")
        //.define("USE_LIST", None)//.define("RUN_TEST", None)  // libcalc24.a
        .opt_level(2).define("NDEBUG", None).file(&calc24_file).compile("calc24");

        println!("cargo:rerun-if-changed={}", calc24_file.display());
        calc24_file.set_extension("h");
        println!("cargo:rerun-if-changed={}", calc24_file.display());
    }
}

