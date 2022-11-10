
use perseus::{t, web_log, Template, RenderFnResultWithCause};
use sycamore::{prelude::{view, View, Html, Scope}};
use sycamore::rt::Event;

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
    view! { cx,
    }
}

#[perseus::template_rx] pub fn index_page<'a, G: Html>(cx: Scope<'a>,
    state: IndexPageStateRx<'a>) -> View<G> {
    //#[component] fn gh_corner<G: Html>(cx: Scope) -> View<G> { }
    let gh_corner = view! { cx,
        a(href={ env!("CARGO_PKG_REPOSITORY") },
            class="github-corner", aria-label="View source on GitHub") {
          svg(width="60", height="60", viewBox="0 0 250 250", aria-hidden="true",
                style="fill: #ddd; color: #151513; position: absolute;
                top: 0; border: 0; right: 0;") {

            path(d="M0,0 L115,115 L130,115 L142,142 L250,250 L250,0 Z")
            path(d="M128.3,109.0 C113.8,99.7 119.0,89.6 119.0,89.6 C122.0,82.7 120.5,78.6
                120.5,78.6 C119.2,72.0 123.4,76.3 123.4,76.3 C127.3,80.9 125.5,87.3 125.5,87.3
                C122.9,97.6 130.6,101.9 134.4,103.2", style="transform-origin: 130px 106px;",
                fill="currentColor", class="octo-arm")

            path(d="M115.0,115.0 C114.9,115.1 118.7,116.5 119.8,115.4 L133.7,101.6 C136.9,99.2
                139.9,98.4 142.2,98.6 C133.8,88.0 127.5,74.4 143.8,58.0 C148.5,53.4 154.0,51.2
                159.7,51.0 C160.3,49.4 163.2,43.6 171.4,40.1 C171.4,40.1 176.1,42.5 178.8,56.2
                C183.1,58.6 187.2,61.8 190.9,65.4 C194.5,69.0 197.7,73.2 200.1,77.6 C213.8,80.2
                216.3,84.9 216.3,84.9 C212.7,93.1 206.9,96.0 205.4,96.6 C205.1,102.4 203.0,107.8
                198.3,112.5 C181.9,128.9 168.3,122.5 157.7,114.1 C157.9,116.9 156.7,120.9
                152.7,124.9 L141.0,136.5 C139.8,137.7 141.6,141.9 141.8,141.8 Z",
                fill="currentColor", class="octo-body")
          }     // https://github.com/tholman/github-corners

            style { ".github-corner:hover .octo-arm {
                        animation: octocat-wave 560ms ease-in-out }
                @keyframes octocat-wave {
                    0%,100% { transform: rotate(0) }
                    20%,60% { transform: rotate(-25deg) }
                    40%,80% { transform: rotate(10deg) }
                }
                @media (max-width: 500px) {
                     .github-corner:hover .octo-arm { animation: none }
                     .github-corner       .octo-arm {
                        animation: octocat-wave 560ms ease-in-out }
                }"
            }
        }
    };

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

    use {sycamore::rt::JsCast, web_sys::HtmlInputElement};
    use  sycamore::reactive::{create_signal, create_effect};

    //web_log!("try for debugging");  // perseus snoop serve/build
    //let game24 = create_signal(cx, Game24::new());
    let game24 = state.game24;
    let nlen = game24.get().nums.len();

    let cnt_vs = create_signal(cx, nlen.to_string());
    let resolve = create_signal(cx, false);

    create_effect(cx, || {
        let cnt = cnt_vs.get().parse::<u8>().unwrap() as usize;
        if 9 < cnt { web_log!("too big to support: {cnt}"); return }
        resolve.set(false);     game24.modify().dealer(cnt);
    });

    view! { cx,     //header { } main { } footer { }
        // <!--#include file="gh-corner.html" -->
        // https://en.wikipedia.org/wiki/Server_Side_Includes
        //object(type="text/html", data=".perseus/static/gh-corner.html")
        //div(dangerously_set_inner_html="...")

        h1(class="text-4xl m-4") {  (gh_corner)     // interpolation
            a(href="https://github.com/mhfan/inrust") { (t!("header", cx)) }
        }

        main(class="mt-auto mb-auto") {
            div(id="play-cards")    // TODO:

            p(class="hidden") {
                "Click on a operator and two numbers to form expression, " br()
                "repeat the process until all numbers are consumed, " br()
                "the final expression will be determined automatically." br() br()
            }

            //p { (t!((*state.greeting.get()).as_str(), cx)) }
            //a(href="about", id="about-link") { "About!" }

            div(id="ops-group", data-bs-toggle="tooltip", on:change = |_| { /*ops_checked*/ },
                title="Click to (un)check\nDrag over to replace/exchange") {
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
                span(id="nums-group", data-bs-toggle="tooltip", //ref=self.grp_elm.clone(),
                    title="Click to (un)check\nDouble click to input\nDrag over to exchange",
                    //on:dblclick=num_editable, on:click=num_checked, on:blur=num_changed,
                ) { (View::new_fragment(game24.get().nums
                    .iter().enumerate().map(|(idx, &num)| {
                    /*let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);

                    let court = [ "T", "J", "Q", "K" ];
                    let suits = [ "S", "C", "D", "H" ];     // "♣♦♥♠"
                    let _ = format!(r"{}{}.svg", match num {
                        1 => "A".to_owned(), 2..=9 => num.to_string(),
                        10..=13 => court[(num - 10) as usize].to_owned(),
                        _ => "?".to_owned() }, suits[sid as usize]);     //num  // TODO: */

                    view! { cx, // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode
                        input(type="text", value=num.to_string(), id=format!("N{idx}"),
                            maxlength="3", size="3", readonly=true, draggable="true",
                            placeholder="?", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                            class=format!("{num_class} rounded-full mx-2"))
                    }}).collect()   // https://regexr.com
                ))}

                // data-bs-toggle="collapse" data-bs-target="#all-solutions"
                //       aria-expanded="false" aria-controls="all-solutions"
                button(on:dblclick = |_| resolve.set(true), //ref=self.eqm_elm.clone(),
                    class="px-4 py-2 m-4 text-3xl font-bold rounded-md
                    hover:outline-none hover:ring-2 hover:ring-indigo-400
                    focus:ring-indigo-500 focus:ring-offset-2", //text-white
                    data-bs-toggle="tooltip", title="Double click to get solutions") { "≠?" }

                input(type="text", id="G", value = game24.get_untracked().goal.to_string(),
                    readonly=true, on:dblclick = |e: Event| {
                        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
                            inp.set_read_only(false);
                        //let end = inp.value().len() as u32;
                        //inp.set_selection_range(end, end).unwrap();
                    }, on:blur = |e: Event| {
                        let inp = e.target().unwrap().dyn_into::<HtmlInputElement>().unwrap();
                        if  inp.read_only() { return }

                        if  inp.check_validity() { inp.set_read_only(true);
                            game24.modify().goal = inp.value().parse::<Rational>().unwrap();
                        } else { inp.focus().unwrap();   inp.select(); }
                    }, placeholder="??", inputmode="numeric", pattern=r"-?\d+(\/\d+)?",
                    maxlength="4", size="4", class=format!("{num_class} rounded-md"),
                    data-bs-toggle="tooltip", title="Double click to input new goal")

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
                input(type="reset", value="Restore", class=ctrl_class, //on:click=restore,
                    data-bs-toogle="tooltip", title="Click reset to initial")

                select(class=format!("{ctrl_class} appearance-none"), bind:value = cnt_vs,
                    data-bs-toogle="tooltip", title="Click to select numbers count") {
                    (View::new_fragment((4..=6).map(|n| view! { cx,
                        option(value=n.to_string(), selected = n == nlen) {
                            (format!("{n} nums")) } }).collect() ))
                }
                button(class=ctrl_class, on:click = move |_| {
                    resolve.set(false);     game24.modify().dealer(nlen);
                }, data-bs-toogle="tooltip", title="Click to refresh new") { "Refresh" }
            }

            (if *resolve.get() { view! { cx,
                div(id="all-solutions", class="overflow-y-auto ml-auto mr-auto
                    w-fit text-left text-lime-500 text-xl",
                    data-bs-toggle="tooltip", title="All inequivalent solutions") {

                    (View::new_fragment({ let game24 = game24.get();
                        calc24_coll(&game24.goal, &game24.nums, DynProg).into_iter()
                            .map(|str| { view! { cx, (str.chars().map(|ch| match ch {
                                '*' => '×', '/' => '÷', _ => ch }).collect::<String>()) br()
                            }}).collect() }))
                }}
            } else { view! { cx, } })
        }

        // XXX: move to index_view/footer?
        p(class="m-4") { "Copyright © 2022 " a(href="https://github.com/mhfan") { "mhfan" } }
    }
}

#[perseus::head] pub fn head(cx: Scope, _props: IndexPageState) -> View<perseus::SsrNode> {
    view! { cx, title { (t!("title", cx)) } }
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

pub fn get_template<G: Html>() -> Template<G> {
    Template::new("index").template(index_page).head(head)
        .build_state_fn(get_build_state).incremental_generation()
        .should_revalidate_fn(should_revalidate)
        //.amalgamate_states_fn(amalgamate_states)
        //.revalidate_after(Duration::new(5, 0))    // "5s".to_string()
        //.request_state_fn(get_request_state)
        //.build_paths_fn(get_build_paths)
}
