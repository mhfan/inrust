/****************************************************************
 * $ID: main.rs          四, 09  6 2022 18:09:34 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 四, 09  6 2022 18:10:04 +0800       by mhfan #
 ****************************************************************/

// https://cheats.rs
// https://course.rs
// https://doc.rust-lang.org/book/
// https://doc.rust-lang.org/reference/
// https://doc.rust-lang.org/rust-by-example/index.html
// curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh

use yansi::Paint;   // Color, Style

//#[allow(unused_macros)]
//macro_rules! var_args { ($($args:expr),*) => {{ }} }  //$(f($args);)*   // XXX:
//macro_rules! printvar { ($var:expr) => { println!("{}: {:?}", stringify!($var), $var) } }

//#![no_main]
// src/main.rs (default application entry point)
fn main()/* -> Result<(), Box<dyn Error>>*/ {
    println!(r"{} v{}, {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
        //env!("CARGO_COMMIT_SHORT_HASH"), //env!("CARGO_BUILD_TIMESTAMP"),  // TODO:
        env!("CARGO_PKG_AUTHORS"));     //option_env!("ENV_VAR_NAME");
    //std::env::args().skip(1).for_each(|it| eprint!(" {it:?}") );
    //env::var("CASE_INSENSITIVE").is_err();    // run time environment

    if !atty::is(atty::Stream::Stdout) { Paint::disable() }
    if cfg!(windows) && !Paint::enable_windows_ascii() { Paint::disable() }

    //include_bytes!("relative_path");  //include!("relative_path");    // XXX:
    //panic!("Test a panic.");

    //std::thread::sleep(std::time::Duration::from_secs(1));
    //let x: Result<u32, &str> = Err("Emergency Failure");  //x.expect("Testing expect");
    //for i in (1..5).rev() { println!("{i:?}") }

    /* way of recursive closure:
    struct Fact<'s> { f: &'s dyn Fn(&Fact, u32) -> u32 }
    let fact = Fact { f: &|fact, x| if x == 0 {1} else {x * (fact.f)(fact, x - 1)} };
    println!("{}", (fact.f)(&fact, 5)); */

    hello_rust::comp24::comp24_main();
    //guess_number();
    //calc_pi();

    //Ok(())
}

#[cfg(not(tarpaulin_include))]
#[allow(dead_code)] fn guess_number() {     // interactive function
    //struct Param { max: i32, lang: bool }; let param = Param { max: 100, lang: true };
    //struct Param(i32, bool); let param = Param(100, true); //let param = (100, true);
    let (max, lang) = (100, false);

    struct _Tips<'a> { title: &'a str, prompt: &'a str,
            too_big: &'a str, too_small: &'a str, bingo: &'a str }
    let [ title, prompt, too_big, too_small, bingo ] = if lang {
        [ "猜数字游戏", "输入你猜的数字: ", "太大了", "太小了", "对了!" ]
    } else {
        [ "Guess the number", "Input a number you guess: ",
            "Too large", "Too small", "Bingo!" ]
    };  // i18n mechanism?

    use rand::Rng;
    let secret = rand::thread_rng().gen_range(1..=max); //dbg!(secret);
    println!("\n### {title} (1~{}) ###", Paint::cyan(max).bold());

    //use std::io::prelude::*;
    use std::{io::Write, cmp::Ordering};
    let _result = 'label: loop {    // unused prefixed with underscore
        print!("\n{}", Paint::white(prompt).dimmed());

        let mut guess = String::new();
        std::io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        std::io::stdin().read_line(&mut guess).expect("Failed to read!");
        let guess = guess.trim();

        //let guess: i32 = guess.parse().expect("Please type a number");
        //match guess.parse::<i32>() { Ok(_guess) => { }, _ => () }
        if let Ok(guess) = guess.parse::<i32>() { // isize
            //if (guess < secret) { } else if (secret < guess) { } else { }
            match guess.cmp(&secret) {
                Ordering::Greater =>    println!("[{}]", Paint::magenta(too_big)),
                Ordering::Less    =>    println!("[{}]", Paint::yellow(too_small)),
                Ordering::Equal   => {  println!("[{}]", Paint::green(bingo)); break 1 }
            }
        } else if guess.eq_ignore_ascii_case("quit") { break 'label 0 }
        //guess.make_ascii_lowercase();  //guess.to_lowercase();
    };
}

// vim:sts=4 ts=8 sw=4 noet
