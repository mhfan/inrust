
#![warn(clippy::all, rust_2018_idioms)]
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]
// hide console window on Windows in release

#[cfg(not(target_arch = "wasm32"))] fn main() {     // When compiling natively:
    tracing_subscriber::fmt::init();    // Log to stdout (if you run with `RUST_LOG=debug`).

    eframe::run_native( "inegui", eframe::NativeOptions::default(),
        Box::new(|cc| Box::new(inegui::TemplateApp::new(cc))),
    );
}

#[cfg(target_arch = "wasm32")] fn main() {  // when compiling to web using trunk.
    console_error_panic_hook::set_once();   // Make sure panics are logged using `console.error`.
    tracing_wasm::set_as_global_default();  // Redirect tracing to console.log and friends:

    eframe::start_web("inegui_canvas", eframe::WebOptions::default(),   // hardcode it
        Box::new(|cc| Box::new(eframe_template::TemplateApp::new(cc))),
    ).expect("failed to start eframe");
}

