
use dioxus::prelude::*;
use inrust::calc24::*;
use instant::Instant;

struct Game24State {
    goal: Rational,
    nums: Vec<Rational>,

    //#[serde(skip)]
    deck: Vec<u8>,  // hold all cards number
    spos: u8,       // shuffle position

    _cnt: u8,       // combined numbers count
    tnow: Instant,  // timing

    //opr_elm:   Option<HtmlInputElement>,    // element of selected operator
    //opd_elq: VecDeque<HtmlInputElement>,    // elements queue of selected operands
}

impl Game24State {
    fn new() -> Self {
        let mut game24 = Self {  goal: 24.into(), nums: vec![],
            deck: (0..13*4).collect(), spos: 0, _cnt: 1, tnow: Instant::now(),
            //opr_elm: None, opd_elq: VecDeque::new(),
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
}

fn main() {                           //dioxus_desktop::launch(app);
    //dioxus_logger::init(log::LevelFilter::Info).expect("failed to init logger");
    #[cfg(not(target_arch = "wasm32"))] dioxus_desktop::launch_cfg(app,
        dioxus_desktop::Config::new().with_window(
            dioxus_desktop::WindowBuilder::new().with_title(env!("CARGO_PKG_NAME")))
        .with_custom_head("<link rel='stylesheet' href='dist/tailwind.css'/>".into())
        //.with_custom_head("<script src='https://cdn.tailwindcss.com'/>".into())
        //.with_custom_index(r"<!DOCTYPE html><html>...</html>".into())
    );

    #[cfg(target_arch = "wasm32")] { //Config::new(log::Level::Trace)
        wasm_logger::init(wasm_logger::Config::default());  // init debug tool for WebAssembly
        //console_error_panic_hook::set_once();     // did in dioxus_web::launch?
        dioxus_web::launch(app);
    }
}

//fn not_found(cx: Scope) -> Element { rsx!(cx, Redirect{ to: "/" }) }

fn app(cx: Scope) -> Element {  //let win = dioxus_desktop::use_window(&cx);
    let ovr_state = use_state(cx, || true);
    let resolving = use_state(cx, || false);
    let eqm_state = use_state(cx, || Option::<bool>::None);
    let game24 = use_ref(cx, Game24State::new);

    let num_class = "px-4 py-2 my-4 w-fit appearance-none select-text
        read-only:bg-transparent bg-stone-200 border border-purple-200
        text-center text-2xl text-purple-600 font-semibold
        hover:text-white hover:bg-purple-600 hover:border-transparent
        focus:outline-none focus:ring-2 focus:ring-purple-600 focus:ring-offset-2
        shadow-xl invalid:border-red-500 invalid:border-2";

    let ctrl_class = "px-4 py-2 m-4 text-gray-900 font-bold bg-gradient-to-r
        from-stone-200 via-stone-400 to-stone-500 rounded-lg hover:bg-gradient-to-br
        focus:ring-4 focus:outline-none focus:ring-stone-300 shadow-lg shadow-stone-500/50
        dark:focus:ring-stone-800 dark:shadow-lg dark:shadow-stone-800/80";

    //log::info!("");
    cx.render(rsx! {    //render_lazy!(rsx!( //rsx!(cx,
        /* Router { // XXX:
            Route { to: "/indiox", self::homepage{} }
            Route { to: "", self::not_found{} }
        } */

        //script { src: "https://cdn.tailwindcss.com" }
        //link { rel: "stylesheet",
        //    href: "https://unpkg.com/tailwindcss@^2.0/dist/tailwind.min.css" }
        //link { rel: "stylesheet",
        //    href: "https://cdn.jsdelivr.net/npm/tw-elements/dist/css/index.min.css" }

        style { r"html {{ background-color: #15191D; color: #DCDCDC; }}
            body {{ font-family: Courier, Monospace; text-align: center; height: 100vh; }}"
        }

        header { class: "text-4xl m-8",
            a { href: format_args!("{}", env!("CARGO_PKG_REPOSITORY")),
                dangerous_inner_html: format_args!("{}",
                    include_str!("../assets/gh-corner.html")),
                class: "github-corner", "aria-label": "View source on GitHub", }
            a { href: "https://github.com/mhfan/inrust", "24 Challenge" }
        }

        main { class: "mt-auto mb-auto",
            div { id: "play-cards", class: "relative", hidden: true,
                img { src: "poker-modern-qr-Maze/2C.svg",
                    class: "inline-block absolute origin-bottom-left -rotate-[15deg]", }
                img { src: "poker-modern-qr-Maze/3D.svg",
                    class: "inline-block absolute origin-bottom-left -rotate-[5deg]", }
                img { src: "poker-modern-qr-Maze/4H.svg",
                    class: "inline-block absolute origin-bottom-left  rotate-[5deg]", }
                img { src: "poker-modern-qr-Maze/5S.svg",
                    class: "inline-block absolute origin-bottom-left  rotate-[15deg]", }
            }   // TODO:

            p { class: "hidden",
                "Click on a operator and two numbers to form expression, " br {}
                "repeat the process until all numbers are consumed, " br {}
                "the final expression will be determined automatically." br {} br {}
            }

            fieldset { id: "ops-group", "data-bs-toggle": "tooltip",
                title: "Click to (un)check\nDrag over to replace/exchange",
                "disabled": format_args!("{}", eqm_state.get().is_some() || !*ovr_state.get()),
                //onclick: ops_selected, // how to cache selected operator element/component?

                [ "+", "-", "×", "÷" ].into_iter().map(|op| rsx! {
                    div { class: "mx-6 my-4 inline-block",
                        input { "type": "radio", name: "ops", id: "{op}",
                            class: "hidden peer",          value: "{op}",
                        }   // require value='xxx', default is 'on'

                        label { "for": "{op}", draggable: "true",
                            class: "px-4 py-2 bg-indigo-600 text-white text-3xl font-bold
                            hover:bg-indigo-400 peer-checked:outline-none peer-checked:ring-2
                            peer-checked:ring-indigo-500 peer-checked:ring-offset-2
                            peer-checked:bg-transparent rounded-md shadow-xl", "{op}" }
                    }
                })
            }

            div { id: "expr-skel",
              if *ovr_state.get() { rsx! {
                span { id: "nums-group", "data-bs-toggle": "tooltip",
                    title: "Click to (un)check\nDouble click to input\nDrag over to exchange",
                    //ondblclick: num_editable, onchange: num_changed, onclick: num_checked,
                    game24.read().nums.iter().enumerate().map(|(idx, num)| {
                        /*let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);
                        // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode

                        let court = [ "T", "J", "Q", "K" ];
                        let suits = [ "S", "C", "D", "H" ];     // "♣♦♥♠"
                        let _ = format!(r"{}{}.svg", match num { 1 => "A".to_owned(),
                            2..=9 => num.to_string(),
                            10..=13 => court[(num - 10) as usize].to_owned(),
                            _ => "?".to_owned() }, suits[sid as usize]);     //num  // TODO: */

                        rsx! { input { "type": "text", id: "N{idx}", value: "{num}", name: "nums",
                            maxlength: "6", size: "3", readonly: "true", draggable: "true",
                            placeholder: "?", "inputmode": "numeric", pattern: r"-?\d+(\/\d+)?",
                            class: "{num_class} aria-checked:ring-purple-600 aria-checked:ring
                            rounded-full mx-2", }}  // https://regexr.com, https://regex101.com
                    })
                }
              }} else { rsx! {
                input { "type": "text", id: "overall", name: "operands",
                    "data-bs-toggle": "tooltip", title: "Input space seperated numbers",
                    placeholder: "???", //minlength: "32", size: "16",
                    inputmode: "numeric", pattern: r"\s*(-?\d+(\/\d+)?\s*){{2,9}}",
                    class: "{num_class} aria-checked:ring-purple-600 aria-checked:ring
                    rounded-full mx-2", onchange: |evt| {   resolving.set(false);
                        game24.with_mut(|game24| game24.nums =
                            evt.data.value.split_ascii_whitespace()
                                .filter_map(|s| s.parse::<Rational>().ok()).collect()); }, }
              }}

                //"data-bs-toggle": "collapse", "data-bs-target": "#all-solutions",
                //    "aria-expanded": "false", "aria-controls": "all-solutions",
                button { ondblclick: |_| resolving.set(true),
                    class: "px-4 py-2 m-4 text-3xl font-bold rounded-md focus:ring-indigo-500
                    aria-checked:ring-2 aria-checked:text-lime-500 aria-checked:ring-lime-400
                    aria-[checked=false]:text-red-500 aria-[checked=false]:ring-red-400
                    hover:outline-none hover:ring-2 hover:ring-indigo-400 focus:ring-offset-2
                    aria-[checked=false]:ring-2",   //text-white
                    "data-bs-toggle": "tooltip", title: "Double click to get solutions",
                    aria_checked: "{eqm_state.get():?}", match *eqm_state.get() {
                        Some(true) => "=", Some(false) => "≠", _ => "≠?" }
                }

                input { "type": "text", id: "G", readonly: "true", value: "{game24.read().goal}",
                    //ondblclick: num_editable, onchange: num_changed,    // FIXME:
                    placeholder: "??", "inputmode": "numeric", pattern: r"-?\d+(\/\d+)?",
                    maxlength: "8", size: "4", class: "{num_class} rounded-md",
                    "data-bs-toggle": "tooltip", title: "Double click to input new goal",
                }

            /*style { r"
                [contenteditable='true'].single-line { white-space: nowrap; overflow: hidden; }
                [contenteditable='true'].single-line br { display: none; }
                [contenteditable='true'].single-line  * { display: inline; white-space: nowrap; }
            " }*/
            }

            p { class: "hidden peer-invalid:visible relative -top-[1rem] text-red-500 font-light",
                "Invalid integer number input, please correct it!"
            }   // invisible vs hidden

            div { id: "ctrl-btns",
                input { "type": "reset", value: "Dismiss", class: "{ctrl_class}",
                    "data-bs-toogle": "tooltip", title: "Click to dismiss expr.",
                    onclick: |_| ovr_state.needs_update(),
                }

                select { class: "{ctrl_class} appearance-none", "data-bs-toogle": "tooltip",
                    title: "Click to set numbers count\nOverall - single element for all numbers",
                    onchange: |evt| { let val = evt.data.value.parse::<u8>().unwrap();
                        if val == 1 {
                            game24.with_mut(|game24| game24.nums.clear());  ovr_state.set(false);
                        } else {
                            game24.with_mut(|game24| game24.dealer(val));   ovr_state.set(true);
                        }   resolving.set(false);
                    },

                    option { value: "1", selected: !ovr_state, "Overall" }
                    (4..=6).map(|n| rsx! { option { value: "{n}", selected: format_args!("{}",
                            *ovr_state.get() && n == game24.read().nums.len()), "{n} nums" }})
                }

                button { class: "{ctrl_class}", onclick: |_| if *ovr_state.get() {
                        game24.with_mut(|game24| game24.dealer(game24.nums.len() as u8));
                        resolving.set(false);
                    //} else {    ovr_state.needs_update();     // XXX:
                    }, "data-bs-toogle": "tooltip", title: "Click to refresh new", "Refresh" }
            }

            if *eqm_state.get() == Some(true) { rsx! {
                div { id: "timer", class: "mx-1 font-sans text-yellow-600 absolute left-0",
                    "data-bs-toggle": "tooltip", title: "Time for calculation",
                    format!("{:.1}s", game24.read().tnow.elapsed().as_secs_f32())
                }
            }}

            if *resolving.get() && !game24.read().nums.is_empty() { rsx! {
                ul { id: "all-solutions", class: "overflow-y-auto ml-auto mr-auto 
                    w-fit text-left text-lime-500 text-xl", "data-bs-toggle": "tooltip",
                    title: "All inequivalent solutions",  game24.with(|game24| {
                    let exps = calc24_coll(&game24.goal, &game24.nums, DynProg);
                    let cnt  = exps.len();

                    exps.into_iter().map(|str| rsx! { li { str.chars().map(|ch|
                        match ch { '*' => '×', '/' => '÷', _ => ch }).collect::<String>()
                    }}).chain(std::iter::once_with(move ||  // capatured 'cnt' by value
                        if    5 < cnt     { rsx! {
                            span { class: "text-white", format_args!("Got {cnt} solutions") }}
                        } else if cnt < 1 { rsx! {
                            span { class: "text-red-500", "Got NO solutions!" }
                        }} else { rsx! { "" } }
                    ))
                })}
            }}
        }

        footer { class: "m-4", "Copyright © 2022 by " 
            a { href: "https://github.com/mhfan", "mhfan" }
        }
    })
}

