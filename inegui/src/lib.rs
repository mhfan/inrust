
#![warn(clippy::all, rust_2018_idioms)]

mod app;
mod backend_panel;
pub use app::TemplateApp;
pub(crate) mod frame_history;

