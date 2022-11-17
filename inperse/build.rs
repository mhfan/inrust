
// https://doc.rust-lang.org/stable/cargo/reference/build-scripts.html

fn main() {
    let (twcfg, twcss) = ("tailwind.config.js", "tailwind_base.css");
    println!("cargo:rerun-if-changed={twcfg}");
    println!("cargo:rerun-if-changed={twcss}");
    println!("cargo:rerun-if-changed=src/");
    //println!("cargo:rerun-if-changed=build.rs");    // XXX: prevent re-run indead

/*  npm install -D tailwindcss; npm install tw-elements
    npx tailwindcss init  # generate a mininum tailwind.config.js
    npx tailwindcss -m -i tailwind_base.css -o static/tailwind.css #-c tailwind.config.js #-w

    sh -c "[ ! -d node_modules ] && npm i; npm run build_css_static"

    std::process::Command::new("npx").args(&["tailwindcss", "-m", //"-c", twcfg,
        "-i", twcss, "-o", "static/tailwind.css"]).status().unwrap();
 */

    std::process::Command::new("npm").args(&["run", "build_css_static"]).status().unwrap();
}

