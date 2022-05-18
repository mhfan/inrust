
use std::{io::{self, Write}, cmp::Ordering/*, time::Duration, error::Error*/};
//pub use A::B:C as D;

//#[allow(unused_macros)]
//macro_rules! var_args { ($($args:expr),*) => {{ }} }  //$(f($args);)*   // XXX
//macro_rules! printvar { ($var:expr) => { println!("{}: {:?}", stringify!($var), $var); } }

// src/main.rs (default application entry point)
fn main()/* -> Result<(), Box<dyn Error>>*/ {
    print!("{} v{}, args:", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
    std::env::args().skip(1).for_each(|itor| print!(" {itor:?}") );
    //println!(" {:?}", std::env::args().collect::<Vec<String>>());

    //std::env::var("CASE_INSENSITIVE").is_err();   //option_env!("ENV_VAR_NAME");

    println!("\nHello, world!\n");  //panic!("Test a panic.");

    //use std::time::Duration;
    //std::thread::sleep(Duration::from_secs(1));

    //let x: Result<u32, &str> = Err("Emergency Failure");  //x.expect("Testing expect");

    //let _a = [1, 2, 3, 4, 5];
    //let _a = [1; 5]; //_a.len();
    //for i in _a { println!("{i:?}"); }
    //for i in (1..5).rev() { println!("{i:?}"); }

    guess_number();
    //compute_24();
    //_calc_pi();
    //Ok(())
}

#[allow(dead_code)]
fn  compute_24() {
    let mut goal = 24;

    let args: Vec<String> = std::env::args().skip(1).collect();
    if !args.is_empty() {
        if let Ok(_goal) = args[0].parse::<i32>() { goal = _goal; }
    }   println!("### Game {} computation ###", goal);

    loop {
        print!("\nInput a data series: ");

        let mut datas = String::new();
        io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        io::stdin().read_line(&mut datas).expect("Failed to read!");
        let mut datas: Vec<&str>  = datas.trim().split(' ')
                .filter(|s| !s.is_empty()).collect();

        if datas[0].starts_with(&['g', 'G']) {  //dbg!(&datas);
            if let Ok(_goal) = datas[0][1..].parse::<i32>() {
                println!("\n### Reset GOAL to {} ###", goal = _goal);
            }   datas.remove(0);
        } else if datas[0].eq_ignore_ascii_case("quit") { break }

        // TODO: output all results friendly
     };
}

use rand::Rng;
#[allow(dead_code)]
fn  guess_number() {    // interactive function
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

    let secret = rand::thread_rng().gen_range(1..=max); //dbg!(secret);
    println!("### {title} (1~{max}) ###");

    let _result = 'label: loop {    // unused prefixed with underscore
        print!("\n{prompt}");

        let mut guess = String::new();
        io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        io::stdin().read_line(&mut guess).expect("Failed to read!");
        let guess = guess.trim();

        //let guess: i32 = guess.parse().expect("Please type a number");
        //match guess.parse::<i32>() { Ok(_guess) => { }, _ => () }
        if let Ok(guess) = guess.parse::<i32>() { // isize
            //if (guess < secret) { } else if (secret < guess) { } else { }
            match guess.cmp(&secret) {
                Ordering::Greater =>    println!("[{too_big}]"),
                Ordering::Less    =>    println!("[{too_small}]"),
                Ordering::Equal   => {  println!("[{bingo}]"); break 1 }
            }
        } else if guess.eq_ignore_ascii_case("quit") { break 'label 0 }
        //guess.make_ascii_lowercase();  //guess.to_lowercase();
    };
}

#[allow(dead_code)]
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];

    // for &item in list {}
    for item in list { if  largest < item { largest = item; } }
    largest
}

fn  _calc_pi() {    // a streaming/spigot algorithm     // https://rosettacode.org/wiki/Pi
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
            q *= 10;
            r = nr;
        } else {
            let nr = (&q * 2 + &r) * &l;
            let nn = (&q * &k * 7 + 2 + &r * &l) / (&t * &l);
            q *= &k;
            t *= &l;
            l += 2;
            k += 1;
            n = nn;
            r = nr;
        }
    }
}
