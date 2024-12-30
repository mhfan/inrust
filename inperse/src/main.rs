
//#[cfg(target_arch = "wasm32")] #[global_allocator]
//static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

mod tmpl;

use perseus::prelude::{Html, PerseusApp, ErrorViews/*, plugins::Plugins*/};
use sycamore::prelude::{view, Scope, View};

// XXX: PERSEUS_BASE_PATH=https://mhfan.github.io/inperse perseus export/serve
// https://framesurge.sh/perseus/en-US/docs/0.3.4/reference/deploying/relative-paths/

// Initialize our app with the `perseus_warp` package's default server (fully customizable)
#[perseus::main(perseus_warp::dflt_server)] // perseus_(integration, warp, axum, actix_web)
pub fn main<G: Html>() -> PerseusApp<G> {
    // Create a new template at `index`, which maps to our landing page
    PerseusApp::new().template(crate::tmpl::index::get_template())
        //.template(Template::build("about").view(about_page).build())

        .locales_and_translations_manager("en-US", &["zh-CN"])
        // Our landing page. Going to `/` will cause a redirect to `/en-US`,
        // or `/zh-CN` based on the user's locale settings in their browser,
        // all automatically. If nothing matches, the default `en-US` will be used.

        //.global_state_creator(crate::tmpl::index::get_global_state_creator())
        .index_view(|cx| view! { cx, html { head { meta(charset="UTF-8")
            meta(name="viewport", content="width=device-width, initial-scale=1.0")
            link(rel="icon",      href=".perseus/static/favicon.ico")
            title { "24 Puzzle" }

            // Perseus automatically resolves `/.perseus/static/` URLs to
            // the contents of the `static/` directory at the project root
            link(rel="stylesheet", href=".perseus/static/tailwind.css")
            //script(src="https://cdn.tailwindcss.com")

            style { r"html { background-color: #15191D; color: #DCDCDC; }
                body { font-family: Courier, Monospace; text-align: center; height: 100vh; }
            " }
        }   body {
            div(class="spin-container", id="spinner") {
                style { r"
.spin-container { position: absolute; display: flex;
  justify-content: center; width: 100vw; margin-top: 8rem;
}

@keyframes spin { to { transform: rotate(360deg); } }
.spin-anim { color: #e5e7eb; stroke: #2563eb; animation: spin 1s linear infinite; }
"               }
                svg(viewBox="0 0 100 100", class="spin-anim", xmlns="http://www.w3.org/2000/svg",
                    aria-hidden="true", fill="none", stroke-width="5", width="100", height="100") {
                    circle(cx="50", cy="50", r="45", stroke="currentColor")
                    path(d="M50,5a45,45 0 0 1 45,45",
                        stroke-linecap="round", stroke="currentStroke")
                }
            }

            perseus::prelude::PerseusRoot()
            // Quirk: this creates a wrapper `<div>` around the root `<div>` by necessity
        }}}).error_views(ErrorViews::unlocalized_development_default())
        // .error_views(get_error_views)

        /*.plugins(Plugins::new().plugin(perseus_size_opt::perseus_size_opt,
            perseus_size_opt::SizeOpts::default()))
        .plugins(Plugins::new().plugin(perseus_tailwind::get_tailwind_plugin,
            perseus_tailwind::TailwindOptions { in_file: "src/tailwind.css".into(),
                // Don't put this in /static, it will trigger build loops
                out_file: "generated/tailwind.css".into() }))*/
}

#[allow(dead_code)] fn about_page<G: Html>(cx: Scope) -> View<G> {
    view! { cx, p { r"This is an example webapp created with Perseus!" } }
}
