
use perseus::{t, web_log, Template, RenderFnResult, RenderFnResultWithCause};
use sycamore::{prelude::{view, View, Html, Scope}, rt::Event};

use inrust::calc24::*;
//use instant::Instant;

#[perseus::make_rx(IndexPageStateRx)] pub struct IndexPageState {
    //pub greeting: String,
    game24: Game24,
}

use serde::{Serialize, Deserialize};
/*#[derive(Serialize, Deserialize)] #[serde(remote = "Rational")]
struct RNumI32(#[serde(getter = "Rational::numer")] i32,
               #[serde(getter = "Rational::denom")] i32);

impl From<RNumI32> for Rational {
    fn from(rn: RNumI32) -> Self { Self::new_raw(rn.0, rn.1) }
}*/     //#[serde(with = "RNumI32")]...

#[derive(Clone, Serialize, Deserialize)] struct Game24 {
    goal: Rational,
    nums: Vec<Rational>,

    //#[serde(skip)]
    deck: Vec<i32>, // hold all cards number
    spos: usize,    // shuffle position

    ncnt: usize,
    //tnow: Instant,
}

impl Game24 {
    fn new() -> Self {
        let mut game = Self { goal: 24.into(), nums: vec![],
            deck: (0..52).collect(), spos: 0, ncnt: 1, //tnow: Instant::now(),
        };  game.dealer(4);     game
    }

    fn dealer(&mut self, n: usize) {
        use rand::{thread_rng, seq::SliceRandom};
        let mut rng = thread_rng();

        loop {  if self.spos == 0 { self.deck.shuffle(&mut rng); }
            self.nums = self.deck[self.spos..].partial_shuffle(&mut rng,
                n).0.iter().map(|n| Rational::from((n % 13) + 1)).collect();
            self.spos += n; if self.deck.len() < self.spos + n { self.spos = 0; }

            if !calc24_first(&self.goal, &self.nums, DynProg).is_empty() { break }
        }   //self.tnow = Instant::now();
    }
}

#[sycamore::component] fn _show_solutions<G: Html>(cx: Scope) -> View<G> {
    view! { cx, }
}

#[perseus::template_rx] pub fn index_page<'a, G: Html>(cx: Scope<'a>,
    state: IndexPageStateRx<'a>) -> View<G> {
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

    use {sycamore::rt::JsCast, web_sys::HtmlInputElement};
    use  sycamore::reactive::{create_signal, create_effect};

    web_log!("try for debugging");  // perseus snoop serve/build
    //let game24 = create_signal(cx, Game24::new());
    let game24 = state.game24;
    let nlen = game24.get_untracked().nums.len();

    let cnt_vs = create_signal(cx, nlen.to_string());
    let resolve  = create_signal(cx, false);

    create_effect(cx, || {
        let cnt = cnt_vs.get().parse::<u8>().unwrap() as usize;
        debug_assert!(cnt < 10, "too big to solve!");
        resolve.set(false);     game24.modify().dealer(cnt);
    });

    let num_editable = |e: Event| if 1 == game24.get().ncnt {
        e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap().set_read_only(false);
        //let end = inp.value().len() as u32; inp.set_selection_range(end, end).unwrap();
    };

    let num_changed = |e: Event| {
        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
        if  inp.read_only() { return }

        if  inp.check_validity() {  inp.set_read_only(true);
            let mut game24 = game24.modify();
            let val = inp.value().parse::<Rational>().unwrap();
            if let Ok(idx) = inp.get_attribute("id").unwrap().parse::<u8>() {
                game24.nums[idx as usize] = val } else { game24.goal = val }
        } else if inp.focus().is_ok() { inp.select() }
    };

    view! { cx,
        // <!--#include file="gh-corner.html" -->
        // https://en.wikipedia.org/wiki/Server_Side_Includes
        //object(type="text/html", data=".perseus/static/gh-corner.html")

        header(class="text-4xl m-4") {  //(gh_corner)     // interpolation
            a(href=env!("CARGO_PKG_REPOSITORY"),
                dangerously_set_inner_html=include_str!("../../static/gh-corner.html"),
                class="github-corner", aria-label="View source on GitHub")
            a(href="https://github.com/mhfan/inrust") { (t!("header", cx)) }
        }

        main(class="mt-auto mb-auto") {
            div(id="play-cards")    // TODO:

            p(class="hidden") {
                "Click on a operator and two numbers to form expression, " br()
                "repeat the process until all numbers are consumed, " br()
                "the final expression will be determined automatically." br() br()
            }

            fieldset(id="ops-group", on:change = |_| { web_log!("TODO: ops changed"); },
                disabled={ let game24 = game24.get(); game24.ncnt == game24.nums.len() },
                data-bs-toggle="tooltip", title=t!("ops-tips", cx)) {
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
                span(id="nums-group", //ref=self.grp_elm.clone(),
                    data-bs-toggle="tooltip", title=t!("num-tips", cx),
                    on:dblclick=num_editable, on:focusout=num_changed, on:click=|e: Event| {
                        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
                        let attr = "aria-checked";  let ts = "true";
                        inp.set_attribute(attr, if inp.get_attribute(attr) ==
                            Some(ts.into()) { "false" } else { ts }).unwrap();  // FIXME:
                    }) { //Indexed(iterable = game24.get().nums, view = |cx, num| view! { ... })
                    (View::new_fragment(game24.get().nums.iter().enumerate().map(|(idx, &num)| {
                    /*let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);

                    let court = [ "T", "J", "Q", "K" ];
                    let suits = [ "S", "C", "D", "H" ];     // "♣♦♥♠"
                    let _ = format!(r"{}{}.svg", match num {
                        1 => "A".to_owned(), 2..=9 => num.to_string(),
                        10..=13 => court[(num - 10) as usize].to_owned(),
                        _ => "?".to_owned() }, suits[sid as usize]);     //num  // TODO: */

                    view! { cx, // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode
                        input(type="text", id=format!("N{idx}"),
                            value=num.to_string(), name="nums",
                            maxlength="6", size="3", readonly=true, draggable="true",
                            placeholder="?", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                            class=format!("{num_class} aria-checked:ring-purple-600
                            aria-checked:ring rounded-full mx-2"))
                    }}).collect()   // https://regexr.com
                ))}

                // data-bs-toggle="collapse" data-bs-target="#all-solutions"
                //       aria-expanded="false" aria-controls="all-solutions"
                button(on:dblclick = |_| resolve.set(true), //ref=self.eqm_elm.clone(),
                    class="px-4 py-2 m-4 text-3xl font-bold rounded-md aria-checked:ring-2
                    aria-checked:text-lime-500 aria-checked:ring-lime-400
                    aria-[checked=false]:text-red-500 aria-[checked=false]:ring-red-400
                    aria-[checked=false]:ring-2 hover:outline-none hover:ring-indigo-400
                    hover:ring-2 focus:ring-indigo-500 focus:ring-offset-2", //text-white
                    data-bs-toggle="tooltip", title=t!("get-solutions", cx)) { "≠?" }

                input(type="text", id="G", value=game24.get_untracked().goal.to_string(),
                    on:dblclick=num_editable, on:blur=num_changed, readonly=true,
                    placeholder="??", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                    maxlength="8", size="4", class=format!("{num_class} rounded-md"),
                    data-bs-toggle="tooltip", title=t!("input-goal", cx))

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
                input(type="reset", value=t!("dismiss", cx), class=ctrl_class,
                    on:click=|_| game24.trigger_subscribers(),  // XXX:
                    data-bs-toogle="tooltip", title=t!("dismiss-tips", cx))

                select(class=format!("{ctrl_class} appearance-none"), bind:value = cnt_vs,
                    data-bs-toogle="tooltip", title=t!("change-count", cx)) {
                    (View::new_fragment((4..=6).map(|n| view! { cx,
                        option(value=n.to_string(), selected = n == nlen) {
                            (format!("{n} nums")) } }).collect() ))
                }
                button(class=ctrl_class, on:click = |_| {  resolve.set(false);
                    game24.modify().dealer(game24.get().nums.len());
                }, data-bs-toogle="tooltip", title=t!("refresh-tips", cx)) { (t!("refresh", cx)) }
            }

            (if *resolve.get() { view! { cx, ul(id="all-solutions", class="overflow-y-auto
                    ml-auto mr-auto w-fit text-left text-lime-500 text-xl",
                    data-bs-toggle="tooltip", title=t!("solutions", cx)) {

                (View::new_fragment({      let game24 = game24.get();
                    let exps = calc24_coll(&game24.goal, &game24.nums, DynProg);
                    let cnt = exps.len();

                    exps.into_iter().map(|str| view! { cx, li { (str.chars()
                        .map(|ch| match ch { '*' => '×', '/' => '÷', _ => ch })
                        .collect::<String>())}}).chain(std::iter::once_with(||
                            if 5 < cnt { view! { cx, (t!("sol-total", { "cnt" = cnt }, cx))
                            }} else { view! { cx, } })).collect()
                }))
            }}} else { view! { cx, } })
        }

        footer(class="m-4") { span { (t!("copyright", cx)) } " by "
            a(href="https://github.com/mhfan") { "mhfan" } } // XXX: move to index_view/footer?
    }
}

#[perseus::head] pub fn add_head(cx: Scope, _props: IndexPageState) -> View<perseus::SsrNode> {
    view! { cx, title { (t!("title", cx)) } }
}

#[cfg(not(target_arch = "wasm32"))] use perseus::Request;
// Unlike in build state, in request state we get access to the information that
// the user sent with their HTTP request.
#[perseus::request_state] pub async fn get_request_state(_path: String, _locale: String,
    _req: Request) -> RenderFnResultWithCause<IndexPageState> {
    Ok(IndexPageState { game24: Game24::new() })
}

// This function will be run when you build your app, to generate default state ahead-of-time
#[perseus::build_state] pub async fn get_build_state(_path: String, _locale: String) ->
    RenderFnResultWithCause<IndexPageState> {
    Ok(IndexPageState { game24: Game24::new() })
}

// This will run every time `.revalidate_after()` permits the page to be revalidated.
// This acts as a secondary check, and can perform arbitrary logic to check
// if we should actually revalidate a page
#[perseus::should_revalidate] pub async fn should_revalidate(_path: String, _locale: String,
    _req: perseus::Request) -> RenderFnResultWithCause<bool> {
    // For simplicity's sake, this will always say we should revalidate,
    // but you could make this check any condition
    Ok(true)
}

// This just returns a vector of all the paths we want to generate for underneath `build_paths`
// (the template's name and root path). Like for build state, this function is asynchronous,
// so you could fetch these paths from a database or the like. Note that everything you export
// from here will be prefixed with `<template-name>/` when it becomes a URL in your app.
//
// Note also that there's almost no point in using build paths without build state, as every
// page would come out exactly the same (unless you differentiated them on the client...)
pub async fn get_build_paths() -> RenderFnResult<Vec<String>> { Ok(vec![]) }

pub fn get_template<G: Html>() -> Template<G> {
    Template::new("index").template(index_page).head(add_head)
        //.revalidate_after(Duration::new(5, 0))    // "5s".to_string()
        //.should_revalidate_fn(should_revalidate)
        //.amalgamate_states_fn(amalgamate_states)
        .request_state_fn(get_request_state)
        //.build_state_fn(get_build_state)
        //.build_paths_fn(get_build_paths)
        .incremental_generation()
}
