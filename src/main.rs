
use std::{env, io::{self, Write}, cmp::Ordering/*, time::Duration, error::Error*/};
//pub use A::B:C as D;

//#[allow(unused_macros)]
//macro_rules! var_args { ($($args:expr),*) => {{ }} }  //$(f($args);)*   // XXX
//macro_rules! printvar { ($var:expr) => { println!("{}: {:?}", stringify!($var), $var); } }

// src/main.rs (default application entry point)
fn main()/* -> Result<(), Box<dyn Error>>*/ {
    print!("{} v{}, args:", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
    env::args().skip(1).for_each(|itor| print!(" {itor:?}") );
    //println!(" {:?}", env::args().collect::<Vec<String>>());

    //env::var("CASE_INSENSITIVE").is_err();   //option_env!("ENV_VAR_NAME");

    println!("\nHello, world!\n");  //panic!("Test a panic.");

    //use std::time::Duration;
    //std::thread::sleep(Duration::from_secs(1));

    //let x: Result<u32, &str> = Err("Emergency Failure");  //x.expect("Testing expect");

    //let _a = [1, 2, 3, 4, 5];
    //let _a = [1; 5]; //_a.len();
    //for i in _a { println!("{i:?}"); }
    //for i in (1..5).rev() { println!("{i:?}"); }

    compute_24();
    guess_number();
    //_calc_pi();

    //Ok(())
}

fn  compute_24_algo<ST: AsRef<str>, T: Iterator<Item = ST> + std::fmt::Debug>(nums: T)
        /*-> Result<(), std::error::Error>*/ {
    #[derive(Debug)]
    struct Rational(i32, i32);
    //type Rational = (i32, i32);
    //struct Rational { n: i32, d: i32 }
    #[derive(Debug)]
    enum Value { Void, Valid, R(Rational) }
    //enum Value { Void, Valid, R(i32, i32) }

    #[derive(Debug)]
    enum Ops { Plus, Minus, Multiply, Divide }
    #[derive(Debug)]
    enum NoE { Num, Exp_ { a: Box<Expr>, op: Ops, b: Box<Expr> } }
    #[derive(Debug)]
    struct Expr { val: Rational, noe: NoE }

    impl std::fmt::Display for Ops {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, r"{}", match self {
                Ops::Plus     => '+', Ops::Minus    => '-',
                Ops::Multiply => '*', Ops::Divide   => '/',
            })
        }
    }

    impl std::fmt::Display for Rational {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.1 == 1 { write!(f, r"{}", self.0) } else {
                write!(f, r"{}/{}", self.0, self.1)
            }
        }
    }

    impl Expr {
        fn display(&self, sop: &Ops) -> String {
            if let NoE::Exp_ { a, op, b } = &self.noe {
                let es = a.display(sop) + &op.to_string() + &b.display(sop);
                if matches!(sop, Ops::Multiply | Ops::Divide) &&
                   matches!( op, Ops::Plus     | Ops::Minus) {
                    // the precedence of 'op' is less than 'sop':
                    return String::from(r"(") + &es + ")"
                }   es
            } else {
                assert_eq!(self.val.1, 1);
                //self.val.0.to_string()
                self.val.to_string()
            }
        }

        fn execuete(&mut self) {
            if let NoE::Exp_ { a, op, b } = &self.noe {
                //a.execute(); b.execuete();
                match op {
                    Ops::Plus     => {
                        self.val.0 = a.val.0 * b.val.1 + a.val.1 * b.val.0;
                        self.val.1 = a.val.1 * b.val.1;
                    }
                    Ops::Minus    => {
                        self.val.0 = a.val.0 * b.val.1 - a.val.1 * b.val.0;
                        self.val.1 = a.val.1 * b.val.1;
                    }
                    Ops::Multiply => {
                        self.val.0 = a.val.0 * b.val.0;
                        self.val.1 = a.val.1 * b.val.1;
                    }
                    Ops::Divide   => if b.val.1 != 0 {
                        self.val.0 = a.val.0 * b.val.1;
                        self.val.1 = a.val.1 * b.val.0;
                    } else { self.val.1 = 0; }
                }
            }
        }
    }

    let nums: Vec<Expr> = nums.map(|str| str.as_ref().parse::<i32>())
            .inspect(|res| if let Err(e) = res { eprintln!("Error parsing data: {e}")})
            .filter_map(Result::ok) // XXX:
            .map(|num| Expr { val: Rational(num, 1), noe: NoE::Num }).collect();
    let mut expr: Vec<Expr>;
dbg!(nums);

    // TODO: output all result expressions friendly
    //todo!();  //unimplemented!();

    //Ok(())
}

#[allow(dead_code)]
fn  compute_24() {
    let mut goal = 24;

    let mut nums = env::args().peekable();
    nums.next();    // skip the executable path
    if let Some(opt) = nums.peek() {
        if opt == "-g" {    nums.next();
            if let Some(gs) = &nums.next() {
                match gs.parse::<i32>() {
                    Ok(_goal) => goal = _goal,
                    Err(e) => eprintln!("Error parsing GOAL: {e}"),
                }
            } else { eprintln!("Lack parameter for GOAL!"); }
        }

        compute_24_algo(nums);
    }

    println!("### Game {goal} computation ###");
    loop {  print!("\nInput a data series: ");

        let mut nums = String::new();
        io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        io::stdin().read_line(&mut nums).expect("Failed to read!");
        let mut nums  = nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(first) = nums.peek() {
            if first.starts_with(&['g', 'G']) {
                match first[1..].parse::<i32>() {
                    Ok(_goal) => println!("\n### Reset GOAL to {} ###", goal = _goal),
                    Err(e) => eprintln!("Error parsing GOAL: {e}"),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("quit") { break }
        }

        compute_24_algo(nums);
    }
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
