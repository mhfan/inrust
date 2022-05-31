
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

#[allow(dead_code)]
fn  compute_24_algo<ST: AsRef<str>, T: Iterator<Item = ST> +
        fmt::Debug>(goal: i32, nums: T) /*-> Result<(), std::error::Error>*/ {
    #[derive(Clone, Debug)]
    struct Rational(i32, i32);
    //type Rational = (i32, i32);
    //struct Rational { n: i32, d: i32 }
    //enum Value { Void, Valid, R(Rational) }
    //type Value = Option<Rational>;

    //struct _Oper(char);
    #[derive(Clone, Hash, Debug)]
    enum Oper { Plus, Minus, Multiply, Divide }
    #[derive(Clone, Debug)]
    enum NoE { Num, Exp_ { a: Rc<Expr>, op: Rc<Oper>, b: Rc<Expr> } }
    #[derive(Clone, Debug)]
    struct Expr { val: Rational, noe: NoE }
    //struct _Expr { v: Rational, e: Option<(Rc<Expr>, Rc<Oper>, Rc<Expr>)> }

    impl fmt::Display for Oper {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, r"{}", match self {
                Oper::Plus  => '+', Oper::Multiply => '*',
                Oper::Minus => '-', Oper::Divide   => '/' })
        }
    }

    impl fmt::Display for Rational {   // XXX: how to reuse for Debug?
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.1 == 0 { write!(f, r"(INV)") } else {
                let bracket = self.0 * self.1 < 0;
                write!(f, r"{}{}{}{}", if bracket { r"(" } else { r"" }, self.0,
                    if self.1 == 1 { String::new() } else { format!(r"/{}", self.1) },
                                       if bracket { r")" } else { r"" })
            }
        }
    }

    impl fmt::Display for Expr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if let NoE::Exp_ { a, op, b } = &self.noe {
                let (mut ls, mut rs) = (a.to_string(), b.to_string());
                let lop = op.as_ref();

                if let NoE::Exp_ { op, .. } = &a.noe {
                    let op = op.as_ref();
                    let braket = matches!(op, Oper::Minus | Oper::Plus) &&
                        matches!(lop, Oper::Divide | Oper::Multiply);
                    if braket { ls = format!(r"({})", ls); }
                }

                if let NoE::Exp_ { op, .. } = &b.noe {
                    let op = op.as_ref();
                    let braket = matches!(lop, Oper::Divide) &&
                            matches!( op, Oper::Divide | Oper::Multiply) ||
                           !matches!(lop, Oper::Plus) &&
                            matches!( op, Oper::Minus  | Oper::Plus);
                    if braket { rs = format!(r"({})", rs); }
                }

                write!(f, r"{}{}{}", ls, lop, rs)
            } else { write!(f, r"{}", self.val) }
        }
    }

    impl Expr {
        fn from(num: i32) -> Self { Self { val: Rational(num, 1), noe: NoE::Num } }
        fn new(a: &Rc<Expr>, op: &Rc<Oper>, b: &Rc<Expr>) -> Self {
            Self {  val: Expr::operate(a, op, b),
                    noe: NoE::Exp_ { a: Rc::clone(a), op: Rc::clone(op),
                                     b: Rc::clone(b) } }
        }

        fn operate(a: &Expr, op: &Oper, b: &Expr) -> Rational {
            let mut val = Rational(0, 0);

            match op {
                Oper::Plus     => {
                    val.0 = a.val.0 * b.val.1 + a.val.1 * b.val.0;
                    val.1 = a.val.1 * b.val.1;
                }
                Oper::Minus    => {
                    val.0 = a.val.0 * b.val.1 - a.val.1 * b.val.0;
                    val.1 = a.val.1 * b.val.1;
                }
                Oper::Multiply => {
                    val.0 = a.val.0 * b.val.0;
                    val.1 = a.val.1 * b.val.1;
                }
                Oper::Divide   =>   if b.val.1 != 0 {
                    val.0 = a.val.0 * b.val.1;
                    val.1 = a.val.1 * b.val.0;
                } else { val.1 = 0; }  // invalidation
            }

            if  val.1 != 0 && val.1 != 1 && val.0 % val.1 == 0 {
                val.0 /= val.1;   val.1  = 1;
            }   val
        }

        fn eqn(&self, n: i32) -> bool { self.val.1 != 0 && self.val.0 == self.val.1 * n }
    }

    impl std::cmp::Eq for Expr { }
    impl std::cmp::PartialEq for Expr {
        fn eq(&self, r: &Expr) -> bool {
            self.val.1 != 0 && r.val.1 != 0 && self.val.0 * r.val.1 == self.val.1 * r.val.0
        }
    }

    impl std::cmp::Ord for Expr {
        fn cmp(&self, r: &Self) -> Ordering {
            let (a, b) = (self.val.0 * r.val.1, self.val.1 * r.val.0);
            a.cmp(&b)
        }
    }

    impl std::cmp::PartialOrd for Expr {
        fn partial_cmp(&self, r: &Self) -> Option<Ordering> {
            if self.val.1 == 0 || r.val.1 == 0 { None } else {
                let (a, b) = (self.val.0 * r.val.1, self.val.1 * r.val.0);
                a.partial_cmp(&b)
            }
        }
    }

    impl std::hash::Hash for Expr {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            if let NoE::Exp_ { a, op, b } = &self.noe {
                a.hash(state);  b.hash(state);  op.hash(state);
            } else {
                self.val.0.hash(state);     self.val.1.hash(state);
            }
        }
    }

    //const OPS: [Oper; 4] = [ '+', '-', '*', '/' ];
    const OPS: [Oper; 4] = [ Oper::Plus, Oper::Minus, Oper::Multiply, Oper::Divide ];

    let ops: Vec<_> = OPS.into_iter().map(Rc::new).collect();
    let nums: Vec<_> = nums.map(|str| str.as_ref().parse::<i32>())
            .inspect(|res| if let Err(e) = res { eprintln!("Error parsing data: {e}")})
            .filter_map(Result::ok).collect();
    //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));

    let mut exps: Vec<Rc<Expr>> = Vec::new();
    compute_24_recursive(goal, &ops, &nums.iter()
        .map(|n| Rc::new(Expr::from(*n))).collect::<Vec<_>>(), &mut exps);
    exps.iter().for_each(|e| println!("{}", e));
    eprintln!("Got {} results!", exps.len());

    fn compute_24_recursive(goal: i32, ops: &[Rc<Oper>],
            nv: &[Rc<Expr>], exps: &mut Vec<Rc<Expr>>) {
        if nv.len() == 1 { if nv[0].eqn(goal) { exps.push(nv[0].clone()); } return; }

        use std::collections::HashSet;
        let mut hs = HashSet::new();

        nv.iter().enumerate().for_each(|(i, a)|
            nv.iter().skip(i+1).enumerate().for_each(|(j, b)|
                if hs.insert((a, b)) {
                    let j = i + 1 + j;
                    let nv: Vec<_> = nv.iter().enumerate().filter_map(|(k, e)|
                        if k != i && k != j { Some(e.clone()) } else { None }).collect();
                    let (_a, _b) = if a < b { (a, b) } else { (b, a) };

                    //eprintln!("-> ({} ? {})", _a.val, _b.val);
                    ops.iter().for_each(|op| {
                        if matches!(op.as_ref(), Oper::Minus | Oper::Divide) {
                            let mut nv = nv.to_vec();
                            nv.push(Rc::new(Expr::new(_b, op, _a)));
                            compute_24_recursive(goal, ops, &nv, exps);
                        }

                        let mut nv = nv.to_vec();
                        nv.push(Rc::new(Expr::new(_a, op, _b)));
                        compute_24_recursive(goal, ops, &nv, exps);
                    });
                }));
    }

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

        compute_24_algo(goal, nums);
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

        compute_24_algo(goal, nums);
    }
}

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

    use rand::Rng;
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
