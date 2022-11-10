
use crate::backend_panel::BackendPanel;

// TODO: puffin_profiler

/// We derive Deserialize/Serialize so we can persist app state on shutdown.
#[derive(serde::Deserialize, serde::Serialize)] #[serde(default)]
// if we add new fields, give them default values when deserializing old state
pub struct TemplateApp {
    label: String,  // Example stuff:
    #[serde(skip)] value: f32,  // this how you opt-out of serialization of a member

    #[serde(skip)] is_existing: bool,
    #[serde(skip)] can_exit: bool,
    picked_path: Option<String>,
    #[serde(skip)] backend: BackendPanel,
}

impl Default for TemplateApp {
    fn default() -> Self { Self {
        label: "Hello egui!".to_owned(), value: 2.7,
        is_existing: false, can_exit: false,
        backend: BackendPanel::default(),
        picked_path: None,
    }}
}

impl TemplateApp {
    /// Called once before the first frame.
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        // This is also where you can customized the look at feel of egui using
        // `cc.egui_ctx.set_visuals` and `cc.egui_ctx.set_fonts`.

        // Load previous app state (if any).
        // Note that you must enable the `persistence` feature for this to work.
        if let Some(storage) = cc.storage {
            return eframe::get_value(storage, eframe::APP_KEY).unwrap_or_default();
        }

        Default::default()
    }
}

impl eframe::App for TemplateApp {
    /// Called by the frame work to save state before shutdown.
    fn save(&mut self, storage: &mut dyn eframe::Storage) {
        eframe::set_value(storage, eframe::APP_KEY, self);
        // XXX: how to save theme style?
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn on_close_event(&mut self) -> bool { self.is_existing = true; self.can_exit }

    /// Called each time the UI needs repainting, which may be many times per second.
    /// Put your widgets into a `SidePanel`, `TopPanel`, `CentralPanel`, `Window` or `Area`.
    fn update(&mut self, ctx: &egui::Context, frame: &mut eframe::Frame) {
        //let Self { label, value } = self;

        // Examples of how to create different panels and windows. Pick whichever suits you.
        // Tip: a good default choice is to just keep the `CentralPanel`.
        // For inspiration and more examples, go to https://emilk.github.io/egui

        #[cfg(not(target_arch = "wasm32"))]     // no File->Quit on web pages!
        egui::TopBottomPanel::top("top_panel").show(ctx, |ui| {
            // The top panel is often a good place for a menu bar:
            egui::menu::bar(ui, |ui| {
                ui.menu_button("File", |ui| {
                    if ui.button("Open").clicked() {    ui.close_menu();
                        if let Some(path) = rfd::FileDialog::new().pick_file() {
                            self.picked_path = Some(path.display().to_string());
                        }
                    }

                    if ui.button("Quit").clicked() {    ui.close_menu();
                        self.is_existing = true;
                    }
                });
            });
        });

        self.backend.open = true;
        self.backend.update(ctx, frame);
        if self.backend.open || ctx.memory().everything_is_visible() {
            egui::SidePanel::left("backend_panel").show(ctx, |ui| {
                self.backend.ui(ui, frame);
                ui.separator();

                ui.horizontal(|ui| {
                    if ui.button("Reset egui")
                        .on_hover_text("Forget scroll, positions, sizes etc").clicked() {
                        *ui.ctx().memory() = Default::default();
                    }

                    if ui.button("Reset everything").clicked() {
                        self.backend = Default::default();
                        *ui.ctx().memory() = Default::default();
                    }
                });
            });
        }   self.backend.end_of_frame(ctx);

        // The central panel the region left after adding TopPanel's and SidePanel's
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.vertical_centered(|ui| ui.heading("Central Panel"));
            ui.separator();

            ui.vertical_centered(|ui| {
                ui.add_space(10.0);
                ui.horizontal(|ui| {
                    ui.label("13 Cards Back of Poker Spade");
                });

                ui.add_space(10.0);
                ui.horizontal(|ui| {
                    ui.spacing_mut().item_spacing.x = 10.0;
                    ui.spacing_mut().item_spacing.y = 10.0;
                    if ui.selectable_label(false, "+").clicked() { };
                    if ui.selectable_label(false, "-").clicked() { };
                    if ui.selectable_label(false, "×").clicked() { };
                    if ui.selectable_label(false, "÷").clicked() { };
                });

                ui.add_space(10.0);
                ui.horizontal(|ui| {
                    if ui.selectable_label(false, "N1").changed() { };
                    if ui.selectable_label(false, "N2").clicked() { };
                    if ui.selectable_label(false, "N3").clicked() { };
                    if ui.selectable_label(false, "N4").clicked() { };
                });

                ui.add_space(10.0);
                ui.horizontal(|ui| {
                    if ui.button("Compose").clicked() { };
                    if ui.button("Commit").clicked() { };
                    if ui.button("Reset").clicked() { };
                    if ui.button("New").clicked() { };
                });
            });

            ui.with_layout(egui::Layout::bottom_up(egui::Align::LEFT),
                |ui| ui.horizontal(|ui| {
                    ui.spacing_mut().item_spacing.x = 0.0;
                    ui.label("IN RUST/CODE WE TRUST - ");
                    ui.hyperlink_to("mhfan", "mailto: mhfan@ustc.edu");
                    ui.label(", powered by ");
                    ui.hyperlink_to("egui", "https://github.com/emilk/egui");
                    ui.label(" and ");
                    ui.hyperlink_to("eframe", "https://github.com/emilk/egui/tree/master/eframe");
                    egui::warn_if_debug_build(ui);
                }));    // XXX: how to make the whole horizontal layout right-aligned?
        });

        #[cfg(not(target_arch = "wasm32"))] if self.is_existing {
            egui::Window::new("REALLY confirm to quit?")
                .anchor(egui::Align2::CENTER_CENTER, egui::vec2(0.0 ,0.0))
                .collapsible(false).resizable(false).show(ctx, |ui|
                    ui.vertical_centered(|ui| ui.horizontal(|ui| {
                        if ui.button("Not yet").clicked() { self.is_existing = false }
                        ui.separator();
                        if ui.button("Yes!").clicked() {    self.can_exit = true;
                            frame.close()
                        }
                    })));    // XXX: why isn't the horizontal layout centered?
        }

        if !ctx.input().raw.dropped_files.is_empty() { // Collect dropped files:
            preview_files_being_dropped(ctx);
            //self.dropped_files = ctx.input().raw.dropped_files.clone();   // TODO:
        }

        if false {
            egui::Window::new("Window Tips").show(ctx, |ui| {
                ui.label("Windows can be moved by dragging them.");
                ui.label("They are automatically sized based on contents.");
                ui.label("You can turn on resizing and scrolling if you like.");
                ui.label("You would normally chose either panels OR windows.");
            });
        }
    }
}

fn preview_files_being_dropped(ctx: &egui::Context) {
    use std::fmt::Write as _;
    use egui::*;

    let mut text = "Dropping files:".to_owned();
    for file in &ctx.input().raw.hovered_files {
        if let Some(path) = &file.path {
            write!(text, "\n{}", path.display()).ok();
        } else if !file.mime.is_empty() {
            write!(text, "\n{}", file.mime).ok();
        } else { text += "\n???"; }
    }

    let screen_rect = ctx.input().screen_rect();
    let painter = ctx.layer_painter(LayerId::new(Order::Foreground,
        Id::new("file_drop_target")));

    painter.rect_filled(screen_rect, 0.0, Color32::from_black_alpha(192));
    painter.text(screen_rect.center(), Align2::CENTER_CENTER, text,
        TextStyle::Heading.resolve(&ctx.style()), Color32::WHITE);
}
