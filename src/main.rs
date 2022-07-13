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

#![allow(dead_code)]

use std::{env, cmp::Ordering/*, error::Error*/};
use std::io::prelude::*;
//pub use A::B::C as D;
use yansi::Paint;   // Color, Style

//#[allow(unused_macros)]
//macro_rules! var_args { ($($args:expr),*) => {{ }} }  //$(f($args);)*   // XXX:
//macro_rules! printvar { ($var:expr) => { println!("{}: {:?}", stringify!($var), $var) } }

//std::any::type_name::<T>()

//#![no_main]
// src/main.rs (default application entry point)
fn main()/* -> Result<(), Box<dyn Error>>*/ {
    //println!("Build @ {}", BUILD_TIMESTAMP);  // TODO:
    print!(r"{} v{}, args:", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
    env::args().skip(1).for_each(|it| print!(" {it:?}") );
    //println!(" {:?}", env::args().collect::<Vec<String>>());
    println!("\n{}", env!("CARGO_PKG_AUTHORS"));

    //env::var("CASE_INSENSITIVE").is_err();   //option_env!("ENV_VAR_NAME");

    if !atty::is(atty::Stream::Stdout) { Paint::disable() }
    if cfg!(windows) && !Paint::enable_windows_ascii() { Paint::disable() }

    println!(r"Hello, world!");  //panic!("Test a panic.");

    //include!("relative_path");    // XXX:

    //use std::time::Duration;
    //std::thread::sleep(Duration::from_secs(1));

    //let x: Result<u32, &str> = Err("Emergency Failure");  //x.expect("Testing expect");

    //let _a = [1, 2, 3, 4, 5];
    //let _a = [1; 5]; //_a.len();
    //for i in _a { println!("{i:?}") }
    //for i in (1..5).rev() { println!("{i:?}") }

    /* way of recursive closure:
    struct Fact<'s> { f: &'s dyn Fn(&Fact, u32) -> u32 }
    let fact = Fact { f: &|fact, x| if x == 0 {1} else {x * (fact.f)(fact, x - 1)} };
    println!("{}", (fact.f)(&fact, 5)); */

    use hello_rust::comp24::*;
    comp24_main();

    //guess_number();
    //calc_pi();

    //Ok(())
}

// https://doc.rust-lang.org/rust-by-example/std_misc/process/pipe.html
pub fn shell_pipe(prog: &str, args: &[&str], inps: &str) -> String {
    use std::process::{Command, Stdio};
    //use std::io::prelude::*;

    let proc = match Command::new(prog)
        .args(args).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn() {
        Err(why) => panic!("Couldn't spawn {prog}: {why}"),
        Ok(proc) => proc,
    };

    if let Err(why) = proc.stdin.unwrap().write_all(inps.as_bytes()) {
        panic!("Couldn't write to {prog}: {why}")
    }

    let mut outs = String::new();
    if let Err(why) = proc.stdout.unwrap().read_to_string(&mut outs) {
        panic!("Couldn't read from {prog}: {why}")
    }   outs
}

/* https://gist.github.com/synecdoche/9ade913c891dda6fcf1cdac823e7d524
 * Given a slice of type T, return a Vec containing the powerset,
 * i.e. the set of all subsets.
 *
 * This works by treating each int the range [0, 2**n) (where n is the length of the slice)
 * as a bitmask, selecting only the members of the original slice whose corresponding
 * positional bits are flipped on in each mask.
 */
pub fn powerset<T>(slice: &[T]) -> Vec<Vec<&T>> {
    let m = slice.len();
    debug_assert!(m < std::mem::size_of::<usize>() * 8);
    let n = (1 << m) as usize;
    let mut psv = Vec::with_capacity(n);

    for x in 0..n/2 {
        let (mut s0, mut s1) = (Vec::with_capacity(m), Vec::with_capacity(m));
        slice.iter().enumerate().for_each(|(i, e)|
            if (1 << i) & x != 0 { s0.push(e) } else { s1.push(e) });
        psv.push(s0);   psv.push(s1);
    }   psv

    /* for mask in 0..n {
        let (mut ss, mut bits) = (vec![], mask);
        while 0 < bits {
            // isolate the rightmost bit to select one item
            let rightmost = bits & !(bits - 1);
            // turn the isolated bit into an array index
            let idx = rightmost.trailing_zeros() as usize;
            ss.push(&slice[idx]);  bits &= bits - 1;   // zero the trailing bit
        }  psv.push(ss);
    }      psv */
}

pub fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];     // for &item in list {}
    for item in list { if  largest < item { largest = item } }  largest
}

fn guess_number() {    // interactive function
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

fn calc_pi() {    // a streaming/spigot algorithm     // https://rosettacode.org/wiki/Pi
    use num_bigint::BigInt;
    let mut first = true;

    let mut q = BigInt::from(1);
    let mut r = BigInt::from(0);
    let mut t = BigInt::from(1);
    let mut k = BigInt::from(1);
    let mut n = BigInt::from(3);
    let mut l = BigInt::from(3);

    loop {
        if &q * 4 + &r - &t < &n * &t {
            print!("{}", n);
            if first { print!("."); first = false; }
            let nr = (&r - &n * &t) * 10;
            n = (&q * 3 + &r) * 10 / &t - &n * 10;
            q *= 10;    r = nr;
        } else {
            let nr = (&q * 2 + &r) * &l;
            let nn = (&q * &k * 7 + 2 + &r * &l) / (&t * &l);
            q *= &k;    k += 1;     n = nn;
            t *= &l;    l += 2;     r = nr;
        }
    }
}

// vim:sts=4 ts=8 sw=4 noet
