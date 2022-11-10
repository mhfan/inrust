
use dioxus::prelude::*;

fn main() {
    #[cfg(not(target_arch = "wasm32"))] //dioxus::desktop::launch(app);
    dioxus::desktop::launch_cfg(app, |cfg|
        cfg.with_window(|win|
                win.with_title(env!("CARGO_PKG_NAME")))
           .with_custom_head("<link rel='stylesheet' href='dist/tailwind.css'/>".into())
        //   .with_custom_head("<script src='https://cdn.tailwindcss.com'/>".into())
        //   .with_custom_index(r"<!DOCTYPE html><html>...</html>".into())
    );

    #[cfg(target_arch = "wasm32")] {
        wasm_logger::init(wasm_logger::Config::default());  // init debug tool for WebAssembly
        //console_error_panic_hook::set_once();     // did in dioxus::web::launch?
        dioxus::web::launch(app);
    }
}

//fn not_found(cx: Scope) -> Element { cx.render(rsx! { Redirect{ to: "/" } }) }

fn app(cx: Scope) -> Element {
    //let win = dioxus::desktop::use_window(&cx);

    cx.render(rsx!(
        /* Router {
            Route { to: "/indiox", self::homepage{} }
            Route { to: "", self::not_found{} }
        } */

        //script { src: "https://cdn.tailwindcss.com" }
        //link { rel: "stylesheet",
        //    href: "https://unpkg.com/tailwindcss@^2.0/dist/tailwind.min.css" }
        //link { rel: "stylesheet",
        //    href: "https://cdn.jsdelivr.net/npm/tw-elements/dist/css/index.min.css" }

        style { ["html { background-color: #15191D; color: #DCDCDC; }
            body { font-family: Courier, Monospace; text-align: center; height: 100vh; }
        "] }

        //div { "Hello, world!" }
        div { style: "text-align: center;",
            h1 { "🌗 Dioxus 🚀" }
            h3 { "Frontend that scales." }
            p { "Dioxus is a portable, performant, and ergonomic framework for building cross-platform user interfaces in Rust." }
        }
    ))
}

