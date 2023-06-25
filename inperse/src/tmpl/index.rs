
use perseus::{t, web_log, engine_only_fn, prelude::{Template, BuildPaths, StateGeneratorInfo}};
use sycamore::{prelude::{view, View, Html, Scope, Signal}, rt::{Event, JsCast}};
use web_sys::{HtmlElement, HtmlInputElement, HtmlSelectElement};
use serde::{Serialize, Deserialize};
use std::collections::VecDeque;

use inrust::calc24::*;
use instant::Instant;

/*#[derive(Serialize, Deserialize)] #[serde(remote = "Rational")]
struct RNumI32(#[serde(getter = "Rational::numer")] i32,
               #[serde(getter = "Rational::denom")] i32);

impl From<RNumI32> for Rational {
    fn from(rn: RNumI32) -> Self { Self::new_raw(rn.0, rn.1) }
}*/     //#[serde(with = "RNumI32")]...

#[derive(Serialize, Deserialize, Clone, perseus::UnreactiveState)]
struct PageState {}

#[derive(Clone/*, Serialize, Deserialize, perseus::ReactiveState*/)]
/*#[rx(alias = "Game24StateRx")] */struct Game24State {
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

    fn form_expr(&mut self, eqm_state: &Signal<Option<bool>>) {
        let opd = &self.opd_elq;
        let opr = self.opr_elm.as_ref().unwrap();

        let str = format!("({} {} {})", opd[0].value(), opr.value(), opd[1].value());
        opd[0].set_size(str.len() as u32);  opd[0].set_value(&str);
        opd.iter().for_each(|elm| set_checked(elm, false));
        opd[1].set_hidden(true);    opr.set_checked(false);

        self.opd_elq.clear();       self.opr_elm = None;
        self.ncnt += 1;     if self.ncnt == self.nums.len() as u8 {
            let str = str.chars().map(|ch|
                match ch { '×' => '*', '÷' => '/', _ => ch }).collect::<String>();
            eqm_state.set(Some(str.parse::<Expr>().unwrap().value() == &self.goal));
        }
    }
}

fn set_checked(elm: &HtmlElement, checked: bool) {
    if checked { elm.   set_attribute("aria-checked", "true").unwrap();
    } else {     elm.remove_attribute("aria-checked").unwrap(); }
}

#[sycamore::component] fn _show_solutions<G: Html>(cx: Scope) -> View<G> { view! { cx, } }

//#[perseus::auto_scope] // XXX: for ReactiveState
fn index_page<G: Html>(cx: Scope, _state: PageState) -> View<G> {
    //let gh_corner = view! { cx, };
    //#[component] fn gh_corner<G: Html>(cx: Scope) -> View<G> { }

    let num_class  = "px-4 py-2 my-4 w-fit appearance-none select-text
        read-only:bg-transparent bg-stone-200 border border-purple-200
        text-center text-2xl text-purple-600 font-semibold
        hover:text-white hover:bg-purple-600 hover:border-transparent
        focus:outline-none focus:ring-2 focus:ring-purple-600 focus:ring-offset-2
        shadow-xl invalid:border-red-500 invalid:border-2";

    let ctrl_class = "px-4 py-2 m-4 text-gray-900 font-bold bg-gradient-to-r
        from-stone-200 via-stone-400 to-stone-500 rounded-lg hover:bg-gradient-to-br
        focus:ring-4 focus:outline-none focus:ring-stone-300 shadow-lg shadow-stone-500/50
        dark:focus:ring-stone-800 dark:shadow-lg dark:shadow-stone-800/80";

    use sycamore::prelude::*;
    web_log!("try for debugging");  // perseus snoop serve/build

    let ovr_state = create_signal(cx, true);
    let resolving = create_signal(cx, false);
    let eqm_state = create_signal(cx, Option::<bool>::None);
    let game24 = create_signal(cx, Game24State::new());
    //static Game24: RefCell<Game24State> = RefCell::new(Game24State::new());   // XXX:

    create_effect(cx, || {  ovr_state.track();  // clear_state
        let mut game24 = game24.modify();
        if !game24.opd_elq.is_empty() { game24.opd_elq.clear(); }
        if let Some(opr) = &game24.opr_elm {
            opr.set_checked(false);     game24.opr_elm = None;
        }

        if *resolving.get_untracked() { resolving.set(false); }
        if  eqm_state.get_untracked().is_some() { eqm_state.set(None); }
        if 1 != game24.ncnt { game24.ncnt = 1; }
    });

    /*use std::time::Duration;
    use sycamore::motion::create_tweened_signal;
    let tweened = create_tweened_signal(cx, 0.0f32,
        Duration::from_millis(100), |v| v + 0.1);
    tweened.set(100.0);     // set target value

    //let eqm_node = create_node_ref(cx);   // XXX:
    //let eqm_elm = eqm_node.get::<DomNode>().unchecked_into::<HtmlElement>(); */

    let num_editable = |e: Event| if 1 == game24.get_untracked().ncnt {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        //let end = inp.value().len() as u32; inp.set_selection_range(end, end).unwrap();
        inp.set_read_only(false);   inp.focus().unwrap();
    };

    let num_focusout = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        if !inp.read_only() { inp.set_read_only(true); }
    };

    let num_changed = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();

        if  inp.check_validity() {  inp.set_read_only(true);
            let mut game24 = game24.modify();
            let nums =  &mut game24.nums;

            let val = inp.value().parse::<Rational>().unwrap();
            if let Ok(idx) = inp.get_attribute("id").unwrap().get(1..).unwrap()
                .parse::<u8>() { nums[idx as usize] = val; } else { game24.goal = val; }

            if *resolving.get_untracked() { resolving.set(false); }
            game24.tnow = Instant::now();
        } else if inp.focus().is_ok() { inp.select(); }
    };

    let num_checked = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        let mut game24 = game24.modify();
        let opd = &mut game24.opd_elq;
        let mut idx = opd.len();

        if  opd.iter().enumerate().any(|(i, elm)|
            if elm.is_same_node(Some(inp.as_ref())) { idx = i; true } else { false }) {
            opd.remove(idx);    inp.blur().unwrap();
                 set_checked(&inp, false);
        } else { set_checked(&inp, true);

            if 1 < idx { set_checked(&opd.pop_front().unwrap(), false);
            }   opd.push_back(inp);

            if 0 < idx && game24.opr_elm.is_some() { game24.form_expr(eqm_state); }
        }
    };

    view! { cx,
        // <!--#include file="gh-corner.html" -->
        // https://en.wikipedia.org/wiki/Server_Side_Includes
        //object(type="text/html", data=".perseus/static/gh-corner.html")

        header(class="text-4xl m-8") {  //(gh_corner)     // interpolation
            a(href=env!("CARGO_PKG_REPOSITORY"),
                dangerously_set_inner_html=include_str!("../../static/gh-corner.html"),
                class="github-corner", aria-label="View source on GitHub")
            a(href="https://github.com/mhfan/inrust") { (t!(cx, "header")) }
        }

        main(class="mt-auto mb-auto") {
            div(id="play-cards")    // TODO:

            p(class="hidden") {
                "Click on a operator and two numbers to form expression, " br()
                "repeat the process until all numbers are consumed, " br()
                "the final expression will be determined automatically." br() br()
            }

            fieldset(id="ops-group", on:click=|e: Event|
                // use onclick instead of onchange for capable of de-selection
                if let Ok(inp) = e.target().unwrap().dyn_into::<HtmlInputElement>() {
                    let mut game24 = game24.modify();
                    if  inp.is_same_node(game24.opr_elm.as_ref().map(|elm|
                        elm.as_ref())) { game24.opr_elm = None;
                        inp.set_checked(false);     return
                    }                    game24.opr_elm = Some(inp);
                    if game24.opd_elq.len() == 2 { game24.form_expr(eqm_state); }
                }, disabled=eqm_state.get().is_some() || !*ovr_state.get(),
                data-bs-toggle="tooltip", title=t!(cx, "ops-tips")) {

                (View::new_fragment([ "+", "-", "×", "÷" ].into_iter().map(|op| view! { cx,
                    div(class="mx-6 my-4 inline-block") {
                        input(type="radio", id=op, value=op, name="ops", class="hidden peer")

                        label(for=op, draggable="true",
                            class="px-4 py-2 bg-indigo-600 text-white text-3xl font-bold
                            hover:bg-indigo-400 peer-checked:outline-none peer-checked:ring-2
                            peer-checked:ring-indigo-500 peer-checked:ring-offset-2
                            peer-checked:bg-transparent rounded-md shadow-xl") { (op) }
                    }
                }).collect()))
            }

            div(id="expr-skel") {
              (if *ovr_state.get() { view! { cx,
                span(id="nums-group", data-bs-toggle="tooltip", title=t!(cx, "num-tips"),
                    on:focusout=num_focusout, on:dblclick=num_editable,
                    on:change=num_changed, on:click=num_checked) {

                    //Indexed(iterable = game24.nums, view = |cx, num| view! { ... })
                  (View::new_fragment(game24.get_untracked()
                        .nums.iter().enumerate().map(|(idx, &num)| {
                    /*let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);
                    // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode

                    let court = [ "T", "J", "Q", "K" ];
                    let suits = [ "S", "C", "D", "H" ];     // "♣♦♥♠"
                    let _ = format!(r"{}{}.svg", match num {
                        1 => "A".to_owned(), 2..=9 => num.to_string(),
                        10..=13 => court[(num - 10) as usize].to_owned(),
                        _ => "?".to_owned() }, suits[sid as usize]);     //num  // TODO: */

                    view! { cx, input(type="text", id=format!("N{idx}"), value=num.to_string(),
                        maxlength="6", size="3", readonly=true, name="nums", draggable="true",
                        placeholder="?", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                        class=format!("{num_class} aria-checked:ring-purple-600
                        aria-checked:ring rounded-full mx-2"))
                    }}).collect()  // https://regexr.com, https://regex101.com
                  ))
                }
              }} else { view! { cx,
                input(type="text", id="overall", name="operands", //hidden=*ovr_state.get(),
                    data-bs-toggle="tooltip", title=t!(cx, "space-nums"),
                    placeholder="???", //minlength="32", size="16",
                    inputmode="numeric", pattern=r"\s*(-?\d+(\/\d+)?\s*){2,9}",
                    class=format!("{num_class} aria-checked:ring-purple-600 aria-checked:ring
                    rounded-full mx-2"), on:change=|e: Event| {
                        if *resolving.get_untracked() { resolving.set(false); }
                        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
                        let vs  = inp.value();  if inp.check_validity() && !vs.is_empty() {
                            game24.modify().nums = vs.split_ascii_whitespace()
                                .filter_map(|s| s.parse::<Rational>().ok()).collect();
                            //resolving.set(true);
                        } else if inp.focus().is_ok() { inp.select(); }
                    }, )
              }})

                // data-bs-toggle="collapse" data-bs-target="#all-solutions"
                //       aria-expanded="false" aria-controls="all-solutions"
                button(on:dblclick=|_| resolving.set(true),
                    aria-checked=format!("{:?}", *eqm_state.get()),
                    class="px-4 py-2 m-4 text-3xl font-bold rounded-md aria-checked:ring-2
                    aria-checked:text-lime-500 aria-checked:ring-lime-400
                    aria-[checked=false]:text-red-500 aria-[checked=false]:ring-red-400
                    aria-[checked=false]:ring-2 hover:outline-none hover:ring-indigo-400
                    hover:ring-2 focus:ring-indigo-500 focus:ring-offset-2", //text-white
                    data-bs-toggle="tooltip", title=t!(cx, "get-solutions")) {
                        (match *eqm_state.get() { Some(true)  => "=",
                                                  Some(false) => "≠", _ => "≠?" })
                }

                input(type="text", id="G", value=game24.get_untracked().goal.to_string(),
                    on:focusout=num_focusout, on:dblclick=num_editable, on:change=num_changed,
                    placeholder="??", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                    maxlength="8", size="4", class=format!("{num_class} rounded-md"),
                    data-bs-toggle="tooltip", title=t!(cx, "input-goal"), readonly=true)

                /*style { r"
                    [contenteditable='true'].single-line {
                        white-space: nowrap; overflow: hidden; }
                    [contenteditable='true'].single-line br { display: none; }
                    [contenteditable='true'].single-line  * { display: inline;
                        white-space: nowrap; }
                " }*/
            }

            p(class="hidden peer-invalid:visible
                relative -top-[1rem] text-red-500 font-light") {
                "Invalid integer number input, please correct it!"
            }   // invisible vs hidden

            div(id="ctrl-btns") {
                input(type="reset", value=t!(cx, "dismiss"), class=ctrl_class,
                    on:click=|_| ovr_state.trigger_subscribers(),
                    data-bs-toogle="tooltip", title=t!(cx, "dismiss-tips"))

                select(class=format!("{ctrl_class} appearance-none"),
                    on:change=|e: Event| {  let cnt = e.target().unwrap()
                        .dyn_into::<HtmlSelectElement>().unwrap().value().parse::<u8>().unwrap();
                        if 1 == cnt { game24.modify().nums.clear(); ovr_state.set(false);
                        } else {      game24.modify().dealer(cnt);  ovr_state.set(true); }
                    }, data-bs-toogle="tooltip", title=t!(cx, "change-count")) {

                    option(value="1") { "Overall" }
                    (View::new_fragment((4..=6).map(|n| view! { cx, option(value=n.to_string(),
                        selected=game24.get_untracked().nums.len() == n) {
                            (format!("{n} nums")) }}).collect()))
                }

                button(class=ctrl_class, data-bs-toogle="tooltip", title=t!(cx, "refresh-tips"),
                    on:click=|_| { if *ovr_state.get_untracked() {
                        game24.modify().dealer(game24.get_untracked().nums.len() as u8);
                    }   ovr_state.trigger_subscribers(); }) { (t!(cx, "refresh")) }
            }

            (if *eqm_state.get() == Some(true) { view! { cx,  // XXX: nested view! { cx, }
                div(id="timer", class="mx-1 font-sans text-yellow-600 absolute left-0",
                    data-bs-toggle="tooltip", title=t!(cx, "time-calc")) { (format!("{:.1}s",
                        game24.get_untracked().tnow.elapsed().as_secs_f32())) }
            }} else { view! { cx, } })

            (if *resolving.get() && !game24.get_untracked().nums.is_empty() {
                view! { cx, ul(id="all-solutions", class="overflow-y-auto
                    ml-auto mr-auto w-fit text-left text-lime-500 text-xl",
                    data-bs-toggle="tooltip", title=t!(cx, "solutions")) {

                (View::new_fragment({   let game24 = game24.get_untracked();
                    let exps = calc24_coll(&game24.goal, &game24.nums, DynProg);
                    let cnt  = exps.len();

                    exps.into_iter().map(|str| view! { cx, li { (str.chars()
                        .map(|ch| match ch { '*' => '×', '/' => '÷', _ => ch })
                        .collect::<String>())}}).chain(std::iter::once_with(||
                            if    5 < cnt     { view! { cx, span(class="text-white") {
                                (t!(cx, "sol-total", { "cnt" = cnt })) }}
                            } else if cnt < 1 { view! { cx, span(class="text-red-500") {
                                (t!(cx, "sol-none")) }}
                            } else { view! { cx, } }
                        )).collect()
                }))
            }}} else { view! { cx, } })
        }

        footer(class="m-4") { span { (t!(cx, "copyright")) } " by "
            a(href="https://github.com/mhfan") { "mhfan" } } // XXX: move to index_view/footer?
    }
}

#[engine_only_fn] fn add_head(cx: Scope) -> View<sycamore::prelude::SsrNode> {
    view! { cx, title { (t!(cx, "title")) } }
}

// Unlike in build state, in request state we get access to the information that
// the user sent with their HTTP request.
#[engine_only_fn] async fn get_request_state(_info: StateGeneratorInfo<()>,
    _req: perseus::Request) -> PageState { PageState { } }
    //Result<PageState, BlamedError<std::convert::Infallible>>

// This function will be run when you build your app, to generate default state ahead-of-time
#[allow(dead_code)] #[engine_only_fn] async fn get_build_state(_info: StateGeneratorInfo<()>)
    //Result<PageState, BlamedError<std::io::Error>>
    -> PageState { PageState { } }

// This will run every time `.revalidate_after()` permits the page to be revalidated.
// This acts as a secondary check, and can perform arbitrary logic to check
// if we should actually revalidate a page
#[allow(dead_code)] #[engine_only_fn] async fn should_revalidate(_info: StateGeneratorInfo<()>,
    _req: perseus::Request) -> bool { true }
    // For simplicity's sake, this will always say we should revalidate,
    // but you could make this check any condition

// This just returns a vector of all the paths we want to generate for underneath `build_paths`
// (the template's name and root path). Like for build state, this function is asynchronous,
// so you could fetch these paths from a database or the like. Note that everything you export
// from here will be prefixed with `<template-name>/` when it becomes a URL in your app.
//
// Note also that there's almost no point in using build paths without build state, as every
// page would come out exactly the same (unless you differentiated them on the client...)
#[allow(dead_code)] async fn get_build_paths() -> BuildPaths {
    BuildPaths { paths: vec![], extra: ().into() }
}

pub fn get_template<G: Html>() -> Template<G> {
    Template::build("index").view_with_unreactive_state(index_page)
        //.revalidate_after(Duration::new(5, 0))    // "5s".to_string()
        //.should_revalidate_fn(should_revalidate)
        //.amalgamate_states_fn(amalgamate_states)
        .request_state_fn(get_request_state)
        //.build_state_fn(get_build_state)
        //.build_paths_fn(get_build_paths)
        .incremental_generation()
        .head(add_head).build()
}
