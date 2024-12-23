
use dioxus::prelude::*;
use inrust::calc24::*;
use instant::Instant;
use std::collections::VecDeque;

use web_sys::{HtmlElement, HtmlInputElement};
use {dioxus::web::WebEventExt, wasm_bindgen::JsCast};

struct Game24State {
    goal: Rational,
    nums: Vec<Rational>,

    //#[serde(skip)]
    deck: Vec<u8>,  // hold all cards number
    spos: u8,       // shuffle position

    ncnt: u8,       // combined numbers count
    tnow: Instant,  // timing

    opr_elm:   Option<HtmlInputElement>,    // element of selected operator
    opd_elq: VecDeque<HtmlInputElement>,    // elements queue of selected operands
}

impl Game24State {
    fn new() -> Self {
        let mut game24 = Self {  goal: 24.into(), nums: vec![],
            deck: (0..13*4).collect(), spos: 0, ncnt: 1, tnow: Instant::now(),
            opr_elm: None, opd_elq: VecDeque::new(),
        };  game24.dealer(4);   game24
    }

    fn dealer(&mut self, cnt: u8) {
        let mut rng = rand::thread_rng();
        //let dst = rand::distributions::Uniform::new(1, 100);
        //let cnt = if 0 < cnt { cnt } else { self.nums.len() as u8 };

        loop {  use rand::seq::SliceRandom;
            if self.deck.len() < (self.spos + cnt) as usize { self.spos = 0; }
            if self.spos == 0 {   self.deck.shuffle(&mut rng); }

            self.nums = self.deck[self.spos as usize..]
                .partial_shuffle(&mut rng, cnt as usize).0.iter().map(|&n|
                    Rational::from((n as i32 % 13) + 1)).collect();     self.spos += cnt;
            //self.nums = (&mut rng).sample_iter(dst).take(4).map(Rational::from).collect();

            if !calc24_first(&self.goal, &self.nums, DynProg).is_empty() { break }
        }   self.tnow = Instant::now();
    }

    fn form_expr(&mut self, eqm_state: &mut Signal<Option<bool>>) {
        let opd = &self.opd_elq;
        let opr = self.opr_elm.as_ref().unwrap();

        opd.iter().for_each(|elm| set_aria_checked(elm, false));
        let str = format!("({} {} {})", opd[0].value(), opr.value(), opd[1].value());
        opd[0].set_size(str.len() as u32);  opd[0].set_value(&str);
        opd[1].set_size(3);         set_display_none(&opd[1], true);
        opr.set_checked(false);     //opd[1].set_hidden(true);

        self.opd_elq.clear();       self.opr_elm = None;
        self.ncnt += 1;     if self.ncnt == self.nums.len() as u8 {
            //let str = str.chars().map(|ch|
            //    match ch { '×' => '*', '÷' => '/', _ => ch }).collect::<String>();
            eqm_state.set(Some(str.parse::<Expr>().is_ok_and(|e| e.value() == &self.goal)));
        }
    }
}

fn set_display_none(elm: &HtmlElement, hide: bool) {
    let attr = "style";
    let _ = if hide { elm.set_attribute(attr, "display: none;")
    } else { elm.remove_attribute(attr) };
}

fn set_aria_checked(elm: &HtmlElement, checked: bool) {
    let attr = "aria-checked";
    let _ = if checked { elm.set_attribute(attr, "true")
    } else { elm.remove_attribute(attr) };
}

fn main() {
    //dioxus::logger::initialize_default(); //tracing::info!("initialized");
    #[cfg(not(feature = "desktop"))]  dioxus::launch(app);

    #[cfg(feature = "desktop")] { use dioxus::desktop::{self, WindowBuilder};
    LaunchBuilder::desktop().with_cfg(desktop::Config::new()
        .with_window(WindowBuilder::new().with_title(env!("CARGO_PKG_NAME")))
        .with_custom_index(include_str!("../index.html").replace(r"{base_path}", "."))
    ).launch(app) };
}

fn app() -> Element {
    let head_style = r"html { background-color: #15191D; color: #DCDCDC; }
        body { font-family: Courier, Monospace; text-align: center; height: 100vh; }";

    use dioxus::document::{Link, Style/*, Title, Script, Meta*/};
    rsx! {
        /* Router { // XXX:
            Route { to: "/indiox", self::solver{} }
            Route { to: "", self::not_found{} }
        } */

        //Title { "24 Puzzle" } // respect index.html and Dioxus.toml
        //Link { rel: "icon",       href: "assets/favicon.ico" }
        Link { rel: "stylesheet", href: "assets/tailwind.css" }
        //Script { src: "https://cdn.tailwindcss.com" }
        Style { {head_style} }

        header { class: "text-4xl m-8",
            a { href: env!("CARGO_PKG_REPOSITORY"),
                dangerous_inner_html: include_str!("../assets/gh-corner.html"),
                class: "github-corner", "aria-label": "View source on GitHub", }
            a { href: "https://github.com/mhfan/inrust", "24 Challenge" }
        }   self::solver {}
        footer { class: "m-4", "Copyright © 2024 by "
            a { href: "https://github.com/mhfan", "mhfan" }
        }
    }
}

//fn not_found() -> Element { rsx!(Redirect{ to: "/" }) }

//static GAME24: GlobalSignal<Game24State> = Signal::global(Game24State::new);
fn solver() -> Element {    // TODO: l10n
    //use_context_provider(|| Game24State::new);
    //let mut game24 = use_context::<Game24State>();
    let mut ovr_state = use_signal(|| true);
    let mut resolving = use_signal(|| false);
    let mut eqm_state = use_signal(|| Option::<bool>::None);
    let mut game24 = use_signal(Game24State::new);

    use_effect(move || {    // clear_state, redundant first time
        let mut game = game24.write();
        if 1 != game.ncnt { game.ncnt = 1; }

        for elm in game.opd_elq.iter() {
            set_aria_checked(elm, false);   //elm.set_size(3);
        }   game.opd_elq.clear();

        let coll = web_sys::window().unwrap().document().unwrap()
            .get_element_by_id("nums-group").unwrap().children();
        for i in 0..coll.length() {     // XXX:
            let inp = coll.item(i).unwrap()
                .dyn_into::<HtmlInputElement>().unwrap();
            inp.set_size(3);    //inp.set_hidden(false);
            set_display_none(&inp, false);
        }

        if let Some(opr) = &game.opr_elm {
            opr.set_checked(false);     game.opr_elm = None;
        }   let _ = ovr_state.read();

        if  eqm_state.peek().is_some() { eqm_state.set(None); }
        if *resolving.peek() { resolving.set(false); }
    });

    let num_editable = move |evt: Event<MouseData>|
        if game24.peek().ncnt == 1 {
            let inp = evt.as_web_event().target().unwrap()
                .dyn_into::<HtmlInputElement>().unwrap();
            inp.set_read_only(false);   inp.focus().unwrap();
    };

    let num_changed = move |evt: Event<FormData>| {
        let inp = evt.as_web_event().target().unwrap()
            .dyn_into::<HtmlInputElement>().unwrap();

        if  inp.check_validity() {  inp.set_read_only(true);
            let mut game = game24.write();
            let nums =  &mut game.nums;

            let val = inp.value().parse::<Rational>().unwrap();
            if let Ok(idx) = inp.get_attribute("id").unwrap().get(1..).unwrap()
                .parse::<u8>() { nums[idx as usize] = val; } else { game.goal = val; }

            if *resolving.peek() { resolving.set(false); }
            game.tnow = Instant::now();
        } else if inp.focus().is_ok() { inp.select(); }
    };

    let num_focusout = |evt: Event<FocusData>| {
        let inp = evt.as_web_event().target().unwrap()
            .dyn_into::<HtmlInputElement>().unwrap();
        if !inp.read_only() { inp.set_read_only(true); }
    };

    let num_checked = move |evt: Event<MouseData>| async move {
        let inp = evt.as_web_event().target().unwrap()
            .dyn_into::<HtmlInputElement>().unwrap();
        let mut game = game24.write();
        let opd = &mut game.opd_elq;
        let mut idx = opd.len();

        if  opd.iter().enumerate().any(|(i, elm)|
            if elm.is_same_node(Some(inp.as_ref())) { idx = i; true } else { false }) {
            opd.remove(idx);    set_aria_checked(&inp, false);
            use_before_render(move || inp.blur().unwrap());
            //use_effect(move || inp.blur().unwrap());
        } else {                set_aria_checked(&inp, true);
            if 1 < idx { set_aria_checked(&opd.pop_front().unwrap(), false); }
            opd.push_back(inp);
            if 0 < idx && game.opr_elm.is_some() { game.form_expr(&mut eqm_state); }
        }
    };

    let num_class = "px-4 py-2 my-4 w-fit appearance-none select-text \
        read-only:bg-transparent bg-stone-200 border border-purple-200 \
        text-center text-2xl text-purple-600 font-semibold \
        hover:text-white hover:bg-purple-600 hover:border-transparent \
        focus:outline-none focus:ring-2 focus:ring-purple-600 focus:ring-offset-2 \
        shadow-xl invalid:border-red-500 invalid:border-2";

    let ctrl_class = "px-4 py-2 m-4 text-gray-900 font-bold bg-gradient-to-r \
        from-stone-200 via-stone-400 to-stone-500 rounded-lg hover:bg-gradient-to-br \
        focus:ring-4 focus:outline-none focus:ring-stone-300 shadow-lg shadow-stone-500/50 \
        dark:focus:ring-stone-800 dark:shadow-lg dark:shadow-stone-800/80";

    let _edit_style = r"[contenteditable='true'].single-line br { display: none; }
        [contenteditable='true'].single-line { white-space: nowrap; overflow: hidden; }
        [contenteditable='true'].single-line  * { display: inline; white-space: nowrap; }";

    rsx! { main { class: "mt-auto mb-auto",
            /* div { id: "play-cards", class: "relative", hidden: true,
                img { src: "poker-modern-qr-Maze/2C.svg",
                    class: "inline-block absolute origin-bottom-left -rotate-[15deg]", }
                img { src: "poker-modern-qr-Maze/3D.svg",
                    class: "inline-block absolute origin-bottom-left -rotate-[5deg]", }
                img { src: "poker-modern-qr-Maze/4H.svg",
                    class: "inline-block absolute origin-bottom-left  rotate-[5deg]", }
                img { src: "poker-modern-qr-Maze/5S.svg",
                    class: "inline-block absolute origin-bottom-left  rotate-[15deg]", }
            }   // TODO: */

            p { class: "hidden",
                "Click on a operator and two numbers to form expression, " br {}
                "repeat the process until all numbers are consumed, " br {}
                "the final expression will be determined automatically." br {} br {}
            }

            fieldset { id: "ops-group", "data-bs-toggle": "tooltip",
                title: "Click to (un)check\nDrag over to replace/exchange",
                "disabled": format!("{}", eqm_state.read().is_some() || !*ovr_state.read()),
                // use onclick instead of onchange for capable of de-selection
                onclick: move |evt| if let Ok(inp) = evt.as_web_event().target().unwrap()
                    .dyn_into::<HtmlInputElement>() {   let mut game = game24.write();
                    if  inp.is_same_node(game.opr_elm.as_ref().map(|elm| elm.as_ref())) {
                        game.opr_elm = None;    inp.set_checked(false);     return
                    }   game.opr_elm = Some(inp);
                    if  game.opd_elq.len() == 2 { game.form_expr(&mut eqm_state); }
                },

                for op in [ "+", "-", "×", "÷" ] { div { class: "mx-6 my-4 inline-block",
                    input { r#type: "radio", name: "ops", id: "{op}",
                        class: "hidden peer",          value: "{op}",
                    }   // require value='xxx', default is 'on'

                    label { "for": "{op}", draggable: "true",
                        class: "px-4 py-2 bg-indigo-600 text-white text-3xl font-bold \
                        hover:bg-indigo-400 peer-checked:outline-none peer-checked:ring-2 \
                        peer-checked:ring-indigo-500 peer-checked:ring-offset-2 \
                        peer-checked:bg-transparent rounded-md shadow-xl", "{op}"
                    }
                } }
            }

            div { id: "expr-skel", //style { {_edit_style} }
                if *ovr_state.read() { span { id: "nums-group", "data-bs-toggle": "tooltip",
                    title: "Click to (un)check\nDouble click to input\nDrag over to exchange",
                    ondoubleclick: num_editable, onchange: num_changed,
                    onclick: num_checked, onfocusout: num_focusout,
                    for (idx, num) in game24.peek().nums.iter().enumerate() {
                        /*let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);
                        // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode

                        let court = [ "T", "J", "Q", "K" ];
                        let suits = [ "S", "C", "D", "H" ];     // "♣♦♥♠"
                        let _ = format!(r"{}{}.svg", match num { 1 => "A".to_owned(),
                            2..=9 => num.to_string(),
                            10..=13 => court[(num - 10) as usize].to_owned(),
                            _ => "?".to_owned() }, suits[sid as usize]);     //num  // TODO: */

                        input { r#type: "text", id: "N{idx}", value: "{num}", name: "nums",
                            maxlength: "6", size: "3", readonly: "true", draggable: "true",
                            placeholder: "?", "inputmode": "numeric", pattern: r"-?\d+(\/\d+)?",
                            class: "{num_class} aria-checked:ring-purple-600 aria-checked:ring \
                            rounded-full mx-2",     // XXX: why won't update on re-rendering?
                        }   // https://regexr.com, https://regex101.com
                    }       // https://rustexp.lpil.uk
                } } else { input { r#type: "text", id: "overall", name: "operands",
                    "data-bs-toggle": "tooltip", title: "Input space separated numbers",
                    placeholder: "???", //minlength: "32", size: "16",
                    inputmode: "numeric", pattern: r"\s*(-?\d+(\/\d+)?\s*){{2,9}}",
                    class: "{num_class} aria-checked:ring-purple-600 aria-checked:ring \
                    rounded-full mx-2", onchange: move |evt| {
                        if *resolving.peek() { resolving.set(false); }
                        let inp = evt.as_web_event().target().unwrap()
                            .dyn_into::<HtmlInputElement>().unwrap();
                        let vs  = inp.value();  if inp.check_validity() && !vs.is_empty() {
                            game24.write().nums = vs.split_ascii_whitespace()
                                .filter_map(|s| s.parse::<Rational>().ok()).collect();
                            //resolving.set(true);
                        } else if inp.focus().is_ok() { inp.select(); }
                    },
                } }

                //"data-bs-toggle": "collapse", "data-bs-target": "#all-solutions",
                //    "aria-expanded": "false", "aria-controls": "all-solutions",
                button { ondoubleclick: move |_| resolving.set(true),   //text-white
                    class: "px-4 py-2 m-4 text-3xl font-bold rounded-md focus:ring-indigo-500 \
                    aria-checked:ring-2 aria-checked:text-lime-500 aria-checked:ring-lime-400 \
                    aria-[checked=false]:text-red-500 aria-[checked=false]:ring-red-400 \
                    hover:outline-none hover:ring-2 hover:ring-indigo-400 focus:ring-offset-2 \
                    aria-[checked=false]:ring-2", "data-bs-toggle": "tooltip",
                    title: "Double click to get solutions", "aria-checked": {
                        match *eqm_state.peek() { Some(bl) => bl.to_string(), _ => "".to_owned() }
                    },  match *eqm_state.read() { Some(true) => "=", Some(false) => "≠", _ => "≠?" }
                }

                input { r#type: "text", id: "G", readonly: "true", value: "{game24.peek().goal}",
                    ondoubleclick: num_editable, onchange: num_changed, onfocusout: num_focusout,
                    placeholder: "??", "inputmode": "numeric", pattern: r"-?\d+(\/\d+)?",
                    maxlength: "8", size: "4", class: "{num_class} rounded-md",
                    "data-bs-toggle": "tooltip", title: "Double click to input new goal",
                }
            }

            p { class: "hidden peer-invalid:visible relative -top-[1rem] text-red-500 font-light",
                "Invalid integer number input, please correct it!"
            }   // hidden or display:none, invisible will cause layout shift

            div { id: "ctrl-btns",
                input { r#type: "reset", value: "Dismiss", class: "{ctrl_class}",
                    "data-bs-toggle": "tooltip", title: "Click to dismiss expr.",
                    onclick: move |_| { let state = *ovr_state.peek(); ovr_state.set(state); },
                }

                select { class: "{ctrl_class} appearance-none", "data-bs-toggle": "tooltip",
                    title: "Click to set numbers count\nOverall - single element for all numbers",
                    name: "count-ctrl", onchange: move |evt| {
                        let val = evt.value().parse::<u8>().unwrap();
                        if  val == 1 {  game24.write().nums.clear();  ovr_state.set(false);
                        } else {        game24.write().dealer(val);   ovr_state.set(true); }
                    },

                    option { value: "1", "Overall" } // selected: !*ovr_state.read(),
                    for n in 4..=6 { option { value: "{n}", selected: format!("{}",
                        /* *ovr_state.read() && */n == game24.peek().nums.len()), "{n} nums" } }
                }

                button { class: "{ctrl_class}", onclick: move |_| { if *ovr_state.peek() {
                        let mut game = game24.write();
                        let len = game.nums.len() as u8;    game.dealer(len);
                        ovr_state.set(true); } else { ovr_state.set(false); }
                }, "data-bs-toggle": "tooltip", title: "Click to refresh new", "Refresh" }
            }

            if *eqm_state.read() == Some(true) { div {
                id: "timer", class: "mx-1 font-sans text-yellow-600 absolute left-0",
                "data-bs-toggle": "tooltip", title: "Time for calculation",
                {format!("{:.1}s", game24.peek().tnow.elapsed().as_secs_f32())}
            } }

            if *resolving.read() && !game24.peek().nums.is_empty() { ul {
                id: "all-solutions", class: "overflow-y-auto ml-auto mr-auto \
                w-fit text-left text-lime-500 text-xl", "data-bs-toggle": "tooltip",
                title: "All inequivalent solutions", {game24.with_peek(|game| {
                    let exps = calc24_coll(&game.goal, &game.nums, DynProg);
                    let cnt  = exps.len();

                    rsx! { for s in exps { li { { s.chars().map(|ch|
                        match ch { '*' => '×', '/' => '÷', _ => ch }).collect::<String>()
                    } } }
                            if 5 < cnt { span { class: "text-white", "Got {cnt} solutions" }
                    } else  if cnt < 1 { span { class: "text-red-500", "Got NO solutions!" } } }
                })}
            } }
    } }
}

