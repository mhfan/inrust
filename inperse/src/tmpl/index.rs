
use perseus::{t, web_log, engine_only_fn, prelude::{Template, BuildPaths, StateGeneratorInfo}};
use sycamore::{prelude::{view, View, Html, Scope}, rt::{Event, JsCast}};
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

#[derive(Serialize, Deserialize, Clone, perseus::ReactiveState)]
#[rx(alias = "Game24StateRx")] struct Game24State {
    goal: Rational,
    nums: Vec<Rational>,

    //#[serde(skip)]
    deck: Vec<i32>, // hold all cards number
    spos: u8,       // shuffle position

    ncnt: u8,
}

impl Game24State {
    fn new() -> Self {
        let mut game24 = Self {  goal: 24.into(), nums: vec![],
            deck: (0..52).collect(), spos: 0, ncnt: 1,
        };  game24.nums = dealer(4, &mut game24.deck, &mut game24.spos, &game24.goal);
            game24
    }
}

fn dealer(n: u8, deck: &mut [i32], spos: &mut u8, goal: &Rational) -> Vec<Rational> {
    //let dst = distributions::Uniform::new(1, 100);
    let mut rng = rand::thread_rng();
    let mut nums: Vec<Rational>;
    use rand::seq::SliceRandom;

    loop {  if *spos == 0 { deck.shuffle(&mut rng); }
        nums = deck[*spos as usize..].partial_shuffle(&mut rng, n as usize).0
            .iter().map(|n| Rational::from((n % 13) + 1)).collect();
        *spos += n;     if (deck.len() as u8) < *spos + n { *spos = 0; }
        //nums = (&mut rng).sample_iter(dst).take(4).map(Rational::from).collect();

        if !calc24_first(goal, &nums, DynProg).is_empty() { break }
    }   nums
}

fn form_expr(opd: &mut VecDeque<HtmlInputElement>, opr: &mut Option<HtmlInputElement>,
    ncnt: &mut u8, nlen: u8, goal: &Rational) -> Option<bool> {     // XXX:
    let opr_ref = opr.as_ref().unwrap();
    let str = format!("({} {} {})", opd[0].value(), opr_ref.value(), opd[1].value());

    opd[1].set_size(str.len() as u32);  opd[1].set_value(&str);
    opd.iter().for_each(|elm| set_checked(elm, false));
    opr_ref.set_checked(false);     opd[0].set_hidden(true);

    opd.clear();    *opr = None;    *ncnt += 1;     if *ncnt == nlen {
        let str = str.chars().map(|ch|
            match ch { '×' => '*', '÷' => '/', _ => ch }).collect::<String>();
        Some(str.parse::<Expr>().unwrap().value() == goal)
    } else { None }
}

fn set_checked(elm: &HtmlElement, checked: bool) {
    if checked { elm.   set_attribute("aria-checked", "true").unwrap();
    } else {     elm.remove_attribute("aria-checked").unwrap(); }
}

#[sycamore::component] fn _show_solutions<G: Html>(cx: Scope) -> View<G> { view! { cx, } }

#[perseus::auto_scope] fn index_page<G: Html>(cx: Scope, game24: &Game24StateRx) -> View<G> {
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
    let tnow = create_signal(cx, Instant::now());
    let opr_elm = create_signal(cx, Option::<HtmlInputElement>::None);
    let opd_elq = create_signal(cx, VecDeque::<HtmlInputElement>::new());
    let eqm_state = create_signal(cx, Some(Option::<bool>::None));

    create_effect(cx, || {  game24.nums.track();
        if *resolving.get_untracked() { resolving.set(false); }
        if let Some(opr) = &*opr_elm.get_untracked() { opr.set_checked(false); }

        if !matches!(*eqm_state.get_untracked(), Some(None)) { eqm_state.set(Some(None)); }
        if 1 != *game24.ncnt.get_untracked() { game24.ncnt.set(1); }
    });

    /*use std::time::Duration;
    use sycamore::motion::create_tweened_signal;
    let tweened = create_tweened_signal(cx, 0.0f32,
        Duration::from_millis(100), |v| v + 0.1);
    tweened.set(100.0);     // set target value

    //let eqm_node = create_node_ref(cx);   // XXX:
    //let eqm_elm = eqm_node.get::<DomNode>().unchecked_into::<HtmlElement>(); */

    let num_editable = |e: Event| if 1 == *game24.ncnt.get_untracked() {
        e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap().set_read_only(false);
        //let end = inp.value().len() as u32; inp.set_selection_range(end, end).unwrap();
    };

    let num_changed = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        //if  inp.read_only() { return }

        if  inp.check_validity() {  inp.set_read_only(true);
            let mut nums = game24.nums.get_untracked().to_vec();
            let val = inp.value().parse::<Rational>().unwrap();
            if let Ok(idx) = inp.get_attribute("id").unwrap().get(1..).unwrap()
                .parse::<u8>() {    nums[idx as usize] = val;
                     game24.nums.set_silent(nums);
            } else { game24.goal.set_silent(val); }
        } else if inp.focus().is_ok() { inp.select(); }

        if *resolving.get_untracked() { resolving.set(false); }
        tnow.set_silent(Instant::now());
    };

    let num_checked = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        let mut opd = opd_elq.modify();
        let mut idx = opd.len();
        //inp.blur().unwrap();

        if  opd.iter().enumerate().any(|(i, elm)|
            if elm.is_same_node(Some(inp.as_ref())) { idx = i; true } else { false }) {
            opd.remove(idx);    set_checked(&inp, false);
        } else {                set_checked(&inp, true);

            if 1 < idx { set_checked(&opd.pop_front().unwrap(), false); }
            let mut opr = opr_elm.modify(); opd.push_back(inp);

            if 0 < idx && opr.is_some() {   let eqs =
                form_expr(&mut opd, &mut opr, &mut game24.ncnt.modify(),
                    game24.nums.get_untracked().len() as u8, &game24.goal.get_untracked());
                if eqs.is_some() { eqm_state.set(Some(eqs)); }
            }
        }
    };

    let num_update = |cnt: u8| {
        debug_assert!(cnt < 10, "too big to solve!");
        let ovr = *ovr_state.get_untracked();
        if 1 == cnt || (0 == cnt && !ovr) {
            game24.nums.trigger_subscribers();
            eqm_state.set(None);    ovr_state.set(false);   return
        }

        if !ovr { ovr_state.set(true); }
        let cnt = if 0 < cnt { cnt } else { game24.nums.get_untracked().len() as u8 };
        game24.nums.set(dealer(cnt, &mut game24.deck.modify(),
            &mut game24.spos.modify(),  &game24.goal.get_untracked()));
        tnow.set_silent(Instant::now());
    };

    view! { cx,
        // <!--#include file="gh-corner.html" -->
        // https://en.wikipedia.org/wiki/Server_Side_Includes
        //object(type="text/html", data=".perseus/static/gh-corner.html")

        header(class="text-4xl m-4") {  //(gh_corner)     // interpolation
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

            fieldset(id="ops-group", on:change=|e: Event| {
                    let (mut opr, mut opd) = (opr_elm.modify(), opd_elq.modify());
                    *opr = e.target().unwrap().dyn_into::<HtmlInputElement>().ok();

                    if opd.len() == 2 {     let eqs =   // XXX: repeat code snippet
                        form_expr(&mut opd, &mut opr, &mut game24.ncnt.modify(),
                             game24.nums.get_untracked().len() as u8,
                            &game24.goal.get_untracked());
                        if eqs.is_some() { eqm_state.set(Some(eqs)); }
                    }
                }, disabled= *game24.ncnt.get() == game24.nums.get_untracked().len() as u8 ||
                    !*ovr_state.get(), data-bs-toggle="tooltip", title=t!(cx, "ops-tips")) {

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
                    on:dblclick=num_editable, on:change=num_changed, on:click=num_checked) {

                    //Indexed(iterable = game24.get().nums, view = |cx, num| view! { ... })
                    (View::new_fragment(game24.nums.get().iter().enumerate().map(|(idx, &num)| {
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
                ))}
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
                            game24.nums.set_silent(vs.split_ascii_whitespace()
                                .filter_map(|s| s.parse::<Rational>().ok()).collect());
                            eqm_state.set(Some(None));  //resolving.set(true);
                        } else if inp.focus().is_ok() { inp.select(); }
                    }, )
              }})

                // data-bs-toggle="collapse" data-bs-target="#all-solutions"
                //       aria-expanded="false" aria-controls="all-solutions"
                button(on:dblclick=|_| resolving.set(true),
                    aria-checked=match *eqm_state.get() {
                        Some(Some(bl)) => bl.to_string(), _ => "".to_owned() },

                    class="px-4 py-2 m-4 text-3xl font-bold rounded-md aria-checked:ring-2
                    aria-checked:text-lime-500 aria-checked:ring-lime-400
                    aria-[checked=false]:text-red-500 aria-[checked=false]:ring-red-400
                    aria-[checked=false]:ring-2 hover:outline-none hover:ring-indigo-400
                    hover:ring-2 focus:ring-indigo-500 focus:ring-offset-2", //text-white
                    data-bs-toggle="tooltip", title=t!(cx, "get-solutions")) {
                        (match *eqm_state.get() { Some(Some(true)) => "=",
                            Some(Some(false)) => "≠", _ => "≠?" })
                }

                input(type="text", id="G", value=game24.goal.get_untracked().to_string(),
                    on:dblclick=num_editable, on:change=num_changed, readonly=true,
                    placeholder="??", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                    maxlength="8", size="4", class=format!("{num_class} rounded-md"),
                    data-bs-toggle="tooltip", title=t!(cx, "input-goal"))

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
                input(type="reset", value=t!(cx, "dismiss"), class=ctrl_class, on:click=|_| {
                        game24.nums.trigger_subscribers();  ovr_state.trigger_subscribers();
                    }, data-bs-toogle="tooltip", title=t!(cx, "dismiss-tips"))

                select(class=format!("{ctrl_class} appearance-none"),
                    on:change=move |e: Event| num_update(e.target().unwrap()
                    .dyn_into::<HtmlSelectElement>().unwrap().value().parse::<u8>().unwrap()),
                    data-bs-toogle="tooltip", title=t!(cx, "change-count")) {

                    option(value="1") { "Overall" }
                    (View::new_fragment((4..=6).map(|n| view! { cx, option(value=n.to_string(),
                        selected=n == game24.nums.get_untracked().len()) {
                            (format!("{n} nums")) }}).collect()))
                }

                button(class=ctrl_class, data-bs-toogle="tooltip", title=t!(cx, "refresh-tips"),
                    on:click=move |_| num_update(0)) { (t!(cx, "refresh")) }
            }

            (if *eqm_state.get() == Some(Some(true)) { view! { cx,  // XXX: nested view! { cx, }
                div(id="timer", class="mx-1 font-sans text-yellow-600 absolute left-0",
                    data-bs-toggle="tooltip", title=t!(cx, "time-calc")) {
                        (format!("{:.1}s", tnow.get_untracked().elapsed().as_secs_f32()))
                }
            }} else { view! { cx, } })

            (if *resolving.get() && None != *eqm_state.get_untracked() {
                view! { cx, ul(id="all-solutions", class="overflow-y-auto
                    ml-auto mr-auto w-fit text-left text-lime-500 text-xl",
                    data-bs-toggle="tooltip", title=t!(cx, "solutions")) {

                (View::new_fragment({
                    let exps = calc24_coll(&game24.goal.get(), &game24.nums.get(), DynProg);
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
    _req: perseus::Request) -> Game24State { Game24State::new() }
    //Result<Game24State, BlamedError<std::convert::Infallible>>

// This function will be run when you build your app, to generate default state ahead-of-time
#[allow(dead_code)] #[engine_only_fn] async fn get_build_state(_info: StateGeneratorInfo<()>) ->
    //Result<Game24State, BlamedError<std::io::Error>>
    Game24State { Game24State::new() }

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
    Template::build("index").view_with_state(index_page).head(add_head)
        //.revalidate_after(Duration::new(5, 0))    // "5s".to_string()
        //.should_revalidate_fn(should_revalidate)
        //.amalgamate_states_fn(amalgamate_states)
        .request_state_fn(get_request_state)
        //.build_state_fn(get_build_state)
        //.build_paths_fn(get_build_paths)
        .incremental_generation()
        .build()
}
