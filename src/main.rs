
use std::{env, fmt, io::{self, Write}, cmp::Ordering, rc::Rc/*, error::Error*/};
//pub use A::B:C as D;

//#[allow(unused_macros)]
//macro_rules! var_args { ($($args:expr),*) => {{ }} }  //$(f($args);)*   // XXX
//macro_rules! printvar { ($var:expr) => { println!("{}: {:?}", stringify!($var), $var); } }

// src/main.rs (default application entry point)
fn main()/* -> Result<(), Box<dyn Error>>*/ {
    print!("{} v{}, args:", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
    env::args().skip(1).for_each(|it| print!(" {it:?}") );
    //println!(" {:?}", env::args().collect::<Vec<String>>());
    print!("\n{}\n", env!("CARGO_PKG_AUTHORS"));

    //env::var("CASE_INSENSITIVE").is_err();   //option_env!("ENV_VAR_NAME");

    println!("Hello, world!");  //panic!("Test a panic.");

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

use yansi::Paint;   // Color, Style

fn compute_24_algo<ST: AsRef<str>, T: Iterator<Item = ST> +
        fmt::Debug>(goal: i32, nums: T) /*-> Result<(), std::error::Error>*/ {
    //#[derive(Clone, Debug)]
    //struct Rational(i32, i32);
    //struct Rational { n: i32, d: i32 }

    //std::ops::{Add, Sub, Mul, Div}
    /* impl std::ops::Add for Rational {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output { todo!() }
    } */

    //enum Value { Void, Valid, R(Rational) }
    //type Value = Option<Rational>;

    type Rational = (i32, i32);
    type Oper = char;

    //#[derive(Debug)]
    struct Expr { v: Rational, m: Option<(Rc<Expr>, Oper, Rc<Expr>)> }

    impl Expr {
        fn new(a: &Rc<Expr>, op: Oper, b: &Rc<Expr>) -> Self {
            Self { v: Expr::operate(a, op, b),
                   m: Some((Rc::clone(a), op, Rc::clone(b))) }
        }

        fn from(num: i32) -> Self { Self { v: /*Rational*/(num, 1), m: None } }
        fn operate(a: &Expr, op: Oper, b: &Expr) -> Rational {
            let mut val = a.v;  // just for initialize val

            match op {
                '+' => { val.0 = a.v.0 * b.v.1 + a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                '-' => { val.0 = a.v.0 * b.v.1 - a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                '*' => { val.0 = a.v.0 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                '/' =>   if b.v.1 != 0 {
                    val.0 = a.v.0 * b.v.1;
                    val.1 = a.v.1 * b.v.0;
                } else { val.1 = 0; }  // invalidation

                _ => unimplemented!("operator '{}'", op)
            }

            // Calculate the greatest common denominator for two numbers
            fn _gcd(a: i32, b: i32) -> i32 {
                let (mut m, mut n) = (a, b);
                while m != 0 {  // Use Euclid's algorithm
                    let temp = m;
                    m = n % temp;
                    n = temp;
                }   n.abs()
            }

            fn _simplify(v: &Rational) -> Rational {
                let gcd = _gcd(v.0, v.1);
                (v.0 / gcd, v.1 / gcd)
            }

            val //Expr::_simplify(&val)     // XXX:
        }

        fn eqn(&self, n: i32) -> bool { self.v.1 != 0 && self.v.0 == self.v.1 * n }

        fn acceptable(a: &Expr, op: Oper, b: &Expr) -> bool {   // assuming a < b
            if let Some((_, aop, ..)) = &a.m {
                // hereafter 'c' is upper expr. 'b'
                // ((a . b) . c) => (a . (b . c))
                if *aop == op { return false }

                // ((a - b) + c) => ((a + c) - b)
                // ((a / b) * c) => ((a * c) / b)
                match (aop, op) { ('-', '+') | ('/', '*') => return false, _ => () }
            }

            if let Some((ba, bop, ..)) = &b.m {
                match (op, bop) {   // here 'c' is upper expr. 'a'
                    // (c + (a + b)) => (a + (c + b)) if a < c
                    // (c * (a * b)) => (a * (c * b)) if a < c
                    ('+', '+') | ('*', '*') => if ba.as_ref() < a { return false }

                    // (c + (a - b)) => ((c + a) - b)
                    // (c * (a / b)) => ((c * a) / b)
                    // (c - (a - b)) => ((c + b) - a)
                    // (c / (a / b)) => ((c * b) / a)
                    ('+', '-') | ('*', '/') | ('-', '-') | ('/', '/') => return false,

                    _ => ()
                }
            }   true
        }

        fn is_subn_expr(&self) -> bool {
            if let Some((a, op, b)) = &self.m {
                // find ((a - b) * x / y) where a < b
                if *op == '-' && a < b { return true }
                if matches!(op, '*' | '/') { return a.is_subn_expr() || b.is_subn_expr() }
            }   false
        }
    }

    // context-free grammar, Chomsky type 2/3, Kleen Algebra
    // TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

    impl fmt::Display for Expr {   // XXX: How to reuse for Debug?
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if let Some((a, op, b)) = &self.m {
                //#[allow(clippy::logic_bug)]
                let braket = if let Some((_, aop, ..)) = &a.m { //true ||
                    matches!(aop, '+' | '-') && matches!(op, '*' | '/') } else { false };

                if  braket { write!(f, r"(")? }     write!(f, r"{a}")?;
                if  braket { write!(f, r")")? }     write!(f, r"{op}")?;

                let braket = if let Some((_, bop, ..)) = &b.m { //true ||
                    matches!(op, '/') && matches!(bop, '*' | '/') ||
                   !matches!(op, '+') && matches!(bop, '+' | '-') } else { false };

                if  braket { write!(f, r"(")? }     write!(f, r"{b}")?;
                if  braket { write!(f, r")")? }
            } else if  self.v.1 == 0 { write!(f, r"(INV)")? } else {
                let braket = self.v.0 * self.v.1 < 0;
                if  braket { write!(f, r"(")? }     write!(f, r"{}", self.v.0)?;
                if  self.v.1 != 1 { write!(f, r"/{}", self.v.1)? }
                if  braket { write!(f, r")")? }
            }   Ok(())
        }
    }

    impl std::cmp::Eq for Expr { }
    impl std::cmp::PartialEq for Expr {
        fn eq(&self, r: &Expr) -> bool {
            self.v.1 != 0 && r.v.1 != 0 && self.v.0 * r.v.1 == self.v.1 * r.v.0
        }
    }

    impl std::cmp::Ord for Expr {
        fn cmp(&self, r: &Self) -> Ordering {
            let (a, b) = (self.v.0 * r.v.1, self.v.1 * r.v.0);  a.cmp(&b)
        }
    }

    impl std::cmp::PartialOrd for Expr {
        fn partial_cmp(&self, r: &Self) -> Option<Ordering> {
            if self.v.1 == 0 || r.v.1 == 0 { None } else {
                let (a, b) = (self.v.0 * r.v.1, self.v.1 * r.v.0);
                a.partial_cmp(&b)
            }
        }
    }

    impl std::hash::Hash for Expr {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            if let Some((a, op, b)) = &self.m {
                a.hash(state);  op.hash(state);  b.hash(state);     // XXX: recursions
            } else { self.v.hash(state) }
        }
    }

    const OPS: [Oper; 4] = ['+', '-', '*', '/'];
    // TODO: accept rational numbers input
    let nums: Vec<_> = nums.map(|str| str.as_ref().parse::<i32>())
            .inspect(|res| if let Err(e) = res { eprintln!("Error parsing data: {e}")})
            .filter_map(Result::ok).collect();
    //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));

    let exps = compute_24_splitset(&nums.iter()
        .map(|n| Rc::new(Expr::from(*n))).collect::<Vec<_>>());
    let exps = exps.into_iter()
        .filter(|e| e.eqn(goal)).collect::<Vec<_>>();
    exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));

    //use itertools::Itertools;
    use std::collections::HashSet;
    /*let mut exps = HashSet::new();
    compute_24_recursive(goal, &nums.iter()
        .map(|n| Rc::new(Expr::from(*n))).collect::<Vec<_>>(), &mut exps);
    exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));*/

    if exps.is_empty() { eprintln!("{}", Paint::yellow("Found no expressions!")); } else {
        //eprintln!("Got {} results!", Paint::yellow(exps.len()).bold());
    }

    // divide and conque with numbers
    fn compute_24_splitset(nv: &[Rc<Expr>]) -> Vec<Rc<Expr>> {
        let mut exps = Vec::new();
        if nv.len() < 2 { for e in nv { exps.push(e.clone()); } return exps }

        assert!(nv.len() < 128);
        let plen = (1 << nv.len()) as u128;
        let mut hs = vec![];

        for mask in 1..plen/2 {
            let (mut s0, mut s1) = (vec![], vec![]);
            let pick_item =
                |ss: &mut Vec<_>, mut bits: u128| while 0 < bits {
                // isolate the rightmost bit to select one item
                let rightmost = bits & !(bits - 1);
                // turn the isolated bit into an array index
                let idx = rightmost.trailing_zeros() as usize;
                let item = (*nv.get(idx).unwrap()).clone();
                bits &= bits - 1;   // zero the trailing bit
                ss.push(item);      //print!(" {idx}");
            };

            // split true sub sets
            pick_item(&mut s0,  mask);              //print!(";");
            pick_item(&mut s1, !mask & (plen - 1)); //println!();

            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};

            // skip duplicated (s0, s1)
            let mut hasher = DefaultHasher::new();
            s0.hash(&mut hasher);   let h0 = hasher.finish();
            if hs.contains(&h0) { continue } else { hs.push(h0) }

            let mut hasher = DefaultHasher::new();
            s1.hash(&mut hasher);   let h1 = hasher.finish();
            if h1 != h0 { if hs.contains(&h1) { continue } else { hs.push(h1) } }

            let (s0, s1) =
                (compute_24_splitset(&s0), compute_24_splitset(&s1));

            s0.iter().for_each(|a| s1.iter().for_each(|b| {
            //s0.iter().cartesian_product(s1).for_each(|(&a, &b)| { });
                let (a, b) = if a < b { (a, b) } else { (b, a) };
                OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
                    if !Expr::acceptable(a, *op, b) { return }

                    // (c - (a - b) * x / y) => (c + (b - a) * x / y) if (a < b)
                    if *op == '-' && !a.is_subn_expr() || *op == '/' && !a.eqn(0) {
                        // swap sub-expr. for order mattered (different values) operators
                        exps.push(Rc::new(Expr::new(b, *op, a)));
                    }

                    if *op == '/' && b.eqn(0) { return }    // skip invalid expr.
                    exps.push(Rc::new(Expr::new(a, *op, b)));
                });
            }));
        }   exps
    }

    #[allow(dead_code)]
    // construct expressions down up from numbers
    fn compute_24_recursive(goal: i32, nv: &[Rc<Expr>], exps: &mut HashSet<Rc<Expr>>) {
        if nv.len() == 1 { if nv[0].eqn(goal) { exps.insert(nv[0].clone()); } return }

        let mut hs = HashSet::new();
        // XXX: How to construct unique expressions over different combination orders?
        nv.iter().enumerate().for_each(|(i, a)|
            nv.iter().skip(i+1).for_each(|b| {
        //nv.iter().tuple_combinations::<(_,_)>().for_each(|(a, b)| { });
                // traverse all expr. combinations, make (a, b) in ascending order
                let (a, b) = if a < b { (a, b) } else { (b, a) };
                if hs.insert((a, b)) {  // skip exactly same combinations
                    let nv = nv.iter().filter(|&e|
                        !std::ptr::eq(e, a) && !std::ptr::eq(e, b))
                        .cloned().collect::<Vec<_>>();  // drop sub-expr.

                    //eprintln!("-> ({} ? {})", a.v, b.v);
                    OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
                        if !Expr::acceptable(a, *op, b) { return }

                        // (c - (a - b) * x / y) => (c + (b - a) * x / y) if (a < b)
                        if *op == '-' && !a.is_subn_expr() || *op == '/' && !a.eqn(0) {
                            // swap sub-expr. for order mattered (different values) operators
                            let mut nv = nv.to_vec();
                            nv.push(Rc::new(Expr::new(b, *op, a)));
                            compute_24_recursive(goal, &nv, exps);
                        }

                        if *op == '/' && b.eqn(0) { return }    // skip invalid expr.
                        let mut nv = nv.to_vec();
                        nv.push(Rc::new(Expr::new(a, *op, b)));
                        compute_24_recursive(goal, &nv, exps);
                    });
                }
            }));
    }

    //todo!();
    //Ok(())
}

#[allow(dead_code)]
fn compute_24() {
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

        compute_24_algo(goal, nums);
    }

    println!("\n### Solve {} computation ###", Paint::magenta(goal).bold());
    loop {  print!("\n{}", Paint::white("Input a string of integers: ").dimmed());

        let mut nums = String::new();
        io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        io::stdin().read_line(&mut nums).expect("Failed to read!");
        let mut nums  = nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(first) = nums.peek() {
            if first.starts_with(&['g', 'G']) {
                match first[1..].parse::<i32>() {
                    Ok(_goal) => {  goal = _goal;
                        println!("### Reset GOAL to {} ###", Paint::magenta(goal).bold());
                    }
                    Err(e) => eprintln!("Error parsing GOAL: {e}"),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("quit") { break }
        }

        compute_24_algo(goal, nums);
    }
}

/* https://gist.github.com/synecdoche/9ade913c891dda6fcf1cdac823e7d524
 * Given a slice of type T, return a Vec containing the powerset,
 * i.e. the set of all subsets.
 *
 * This works by treating each int the range [0, 2**n) (where n is the length of the slice)
 * as a bitmask, selecting only the members of the original slice whose corresponding
 * positional bits are flipped on in each mask.
 */
pub fn _powerset<T: Clone>(slice: &[T]) -> Vec<Vec<T>> {
    let mut v = Vec::new();
    for mask in 0..(1 << slice.len()) as u128 {
        assert!(slice.len() < 128);
        let (mut ss, mut bits) = (vec![], mask);
        while 0 < bits {
            // isolate the rightmost bit to select one item
            let rightmost = bits & !(bits - 1);
            // turn the isolated bit into an array index
            let idx = rightmost.trailing_zeros() as usize;
            let item = (*slice.get(idx).unwrap()).clone();
            ss.push(item);  bits &= bits - 1;   // zero the trailing bit
        }   v.push(ss);
    }       v
}

#[allow(dead_code)]
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
    println!("\n### {title} (1~{max}) ###");

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
pub fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];

    // for &item in list {}
    for item in list { if  largest < item { largest = item; } }
    largest
}

fn _calc_pi() {    // a streaming/spigot algorithm     // https://rosettacode.org/wiki/Pi
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
