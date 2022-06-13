/****************************************************************
 * $ID: comp24.rs        四, 09  6 2022 18:09:34 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 四, 09  6 2022 18:10:33 +0800       by mhfan #
 ****************************************************************/

//pub mod comp24 {

//use std::io::prelude::*;
pub use std::{fmt, rc::Rc, io::Write, cmp::{Ordering, PartialEq}};

pub use yansi::Paint;   // Color, Style
//pub use itertools::Itertools;
pub use std::collections::HashSet;
//pub use rustc_hash::FxHashSet as HashSet;
// faster than std version according to https://nnethercote.github.io/perf-book/hashing.html

#[derive(Debug)]
pub struct Rational(i32, i32);
//struct Rational { n: i32, d: i32 }
//type Rational = (i32, i32);

//std::ops::{Add, Sub, Mul, Div}
/* impl std::ops::Add for Rational {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { todo!() }
} */

impl core::convert::From<i32> for Rational { fn from(n: i32) -> Self { Self(n, 1) } }

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //Expr::_simplify(&self);   // XXX:
        if  self.1 == 0 { write!(f, r"(INV)")? } else {
            let braket = self.0 * self.1 < 0 || self.1 != 1;
            if  braket { write!(f, r"(")? }     write!(f, r"{}", self.0)?;
            if  self.1 != 1 { write!(f, r"/{}", self.1)? }
            if  braket { write!(f, r")")? }
        }   Ok(())
    }
}

impl std::str::FromStr for Rational {
    type Err = std::num::ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v = s.split('/').collect::<Vec<_>>();
        let (n, mut d) = (v[0].parse::<i32>()?, 1);
        if 1 < v.len() { d = v[1].parse::<i32>()? }
        Ok(Rational(n, d))
    }
}

impl std::cmp::Eq for Rational { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl PartialEq for Rational {
    fn eq(&self, rhs: &Self) -> bool {
        self.1 != 0 && rhs.1 != 0 && self.0 * rhs.1 == self.1 * rhs.0
    }
}

impl std::cmp::Ord for Rational {   // XXX: What if self/rhs is not valid rational number?
    fn cmp(&self, rhs: &Self) -> Ordering { (self.0 * rhs.1).cmp(&(self.1 * rhs.0)) }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        if self.1 == 0 || rhs.1 == 0 { None } else {
            (self.0 * rhs.1).partial_cmp(&(self.1 * rhs.0))
        }
    }
}

//const Add: Oper = Oper('+');
//const Sub: Oper = Oper('-');
//const Mul: Oper = Oper('*');
//const Div: Oper = Oper('/');
const OPS: [Oper; 4] = [Oper('+'), Oper('-'), Oper('*'), Oper('/')];
//enum Oper { Add(char), Sub(char), Mul(char), Div(char), }
#[derive(Clone, Copy)]  // low cost
pub struct Oper(char);  // newtype idiom
//type Oper = char;       // type alias

//#[derive(Debug)]
//enum Value { Void, Valid, R(Rational) }
//type Value = Option<Rational>;

//#[derive(Debug)]
pub struct Expr { pub v: Rational, pub m: Option<(Rc<Expr>, Oper, Rc<Expr>)> }

impl Expr {
    fn new(a: &Rc<Self>, op: Oper, b: &Rc<Self>) -> Self {
        Self { v: Self::operate(a, op, b),
               m: Some((Rc::clone(a), op, Rc::clone(b))) }
    }

    fn operate(a: &Self, op: Oper, b: &Self) -> Rational {
        let mut val = Rational(0, 0);
        match op.0 {
            '+' => { val.0 = a.v.0 * b.v.1 + a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
            '-' => { val.0 = a.v.0 * b.v.1 - a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
            '*' => { val.0 = a.v.0 * b.v.0;  val.1 = a.v.1 * b.v.1; }
            '/' => if b.v.1 != 0 {
                     val.0 = a.v.0 * b.v.1;  val.1 = a.v.1 * b.v.0;
            } else { val.1 = 0; }  // invalidation

            _ => unimplemented!("operator '{}'", op.0)
        }   val //Self::_simplify(&val)     // XXX:
    }

    fn _simplify(v: &Rational) -> Rational {    // XXX: move to impl Rational
        // Calculate the greatest common denominator for two numbers
        fn _gcd(a: i32, b: i32) -> i32 {
            let (mut m, mut n) = (a, b);
            while m != 0 {  // Use Euclid's algorithm
                let temp = m;
                m = n % temp;
                n = temp;
            }   n.abs()
        }

        let gcd = _gcd(v.0, v.1);
        Rational(v.0 / gcd, v.1 / gcd)
    }

    fn acceptable(a: &Self, op: Oper, b: &Self) -> bool {   // premise a < b
        if let Some((_, aop, ..)) = &a.m {
            // ((a . b) . B) => (a . (b . B))
            if aop.0 == op.0 { return false }

            // ((a - b) + B) => ((a + B) - b)
            // ((a / b) * B) => ((a * B) / b)
            match (aop.0, op.0) { ('-', '+') | ('/', '*') => return false, _ => () }
        }

        if let Some((ba, bop, ..)) = &b.m {
            match (op.0, bop.0) {
                // (A + (a + b)) => (a + (A + b)) if a < A
                // (A * (a * b)) => (a * (A * b)) if a < A
                ('+', '+') | ('*', '*') => if ba.v < a.v { return false }

                // (A + (a - b)) => ((A + a) - b)
                // (A * (a / b)) => ((A * a) / b)
                // (A - (a - b)) => ((A + b) - a)
                // (A / (a / b)) => ((A * b) / a)
                ('+', '-') | ('*', '/') | ('-', '-') | ('/', '/') => return false,

                _ => ()
            }
        }   true    // to keep human friendly expression form ONLY
    }

    fn is_subn_expr(&self) -> bool {
        if let Some((a, op, b)) = &self.m {
            if matches!(op.0, '*' | '/') {
                return a.is_subn_expr() || b.is_subn_expr() }
            if op.0 == '-' && a.v < b.v { return true }
            // find ((a - b) * x / y) where a < b
        }   false
    }
}

impl fmt::Display for Expr {   // XXX: Is it possible to reuse it for Debug trait?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((a, op, b)) = &self.m {
            //#[allow(clippy::logic_bug)]
            let braket = if let Some((_, aop, ..)) = &a.m { //true ||
                matches!(aop.0, '+' | '-') &&
                matches!( op.0, '*' | '/') } else { false };

            if  braket { write!(f, r"(")? }     write!(f, r"{a}")?;
            if  braket { write!(f, r")")? }     write!(f, r"{}", op.0)?;

            let braket = if let Some((_, bop, ..)) = &b.m { //true ||
                op.0 == '/' && matches!(bop.0, '*' | '/') ||
                op.0 != '+' && matches!(bop.0, '+' | '-') } else { false };

            if  braket { write!(f, r"(")? }     write!(f, r"{b}")?;
            if  braket { write!(f, r")")? }
        } else { write!(f, r"{}", self.v)? }    Ok(())
    }
}

impl std::cmp::Eq for Expr { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl PartialEq for Expr { fn eq(&self, rhs: &Self) -> bool { self.v == rhs.v } }
impl std::hash::Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if let Some((a, op, b)) = &self.m {
            a.hash(state);  op.0.hash(state);   b.hash(state);
        } else { self.v.0.hash(state); self.v.1.hash(state); }
        // XXX: have recursions, yet occasionally collision
    }
}

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

// divide and conque with numbers
pub fn comp24_splitset(nv: &[Rc<Expr>]) -> Vec<Rc<Expr>> {
    let (plen, mut hs) = ((1 << nv.len()), vec![]);
    let mut exps = Vec::new();
    if plen == 2 { exps.push(nv[0].clone()); return exps }

    //let mut used = HashSet::default();
    //let all_unique = nv.iter().all(|e| used.insert(e));

    for mask in 1..plen/2 {
        let (mut s0, mut s1) = (vec![], vec![]);
        let pick_item =
            |ss: &mut Vec<_>, mut bits: u64| while 0 < bits {
            // isolate the rightmost bit to select one item
            let rightmost = bits & !(bits - 1);
            // turn the isolated bit into an array index
            let idx = rightmost.trailing_zeros() as usize;
            let item = (*nv.get(idx).unwrap()).clone();
            bits &= bits - 1;   // zero the trailing bit
            ss.push(item);      //eprint!(" {idx}");
        };

        // split true sub sets
        pick_item(&mut s0,  mask);              //eprint!(";");
        pick_item(&mut s1, !mask & (plen - 1)); //eprintln!();

        //if !all_unique {
        use std::collections::hash_map::DefaultHasher;
        //use rustc_hash::FxHasher as DefaultHasher;
        use std::hash::{Hash, Hasher};

        // skip duplicated (s0, s1)
        let mut hasher = DefaultHasher::default();
        s0.hash(&mut hasher);   let h0 = hasher.finish();
        if hs.contains(&h0) { continue } else { hs.push(h0) }

        let mut hasher = DefaultHasher::default();
        s1.hash(&mut hasher);   let h1 = hasher.finish();
        if h1 != h0 { if hs.contains(&h1) { continue } else { hs.push(h1) } }
        //}

        /*if 1 < s0.len() { */s0 = comp24_splitset(&s0);// }
        /*if 1 < s1.len() { */s1 = comp24_splitset(&s1);// }

        //s0.iter().cartesian_product(s1).for_each(|(&a, &b)| { });
        s0.iter().for_each(|a| s1.iter().for_each(|b| {
            let (a, b) = if a.v < b.v { (a, b) } else { (b, a) };
            //eprintln!("-> ({a}) ? ({b})");
            OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
                if !Expr::acceptable(a, *op, b) { return }

                // swap sub-expr. for order mattered (different values) operators
                if a != b && (op.0 == '/'/* &&  a.v.0 != 0*/ ||
                              op.0 == '-' && !a.is_subn_expr()) {
                    exps.push(Rc::new(Expr::new(b, *op, a)));
                }

                // keep (a - b) * x / y - B for negative goal?
                // (A - (a - b) * x / y) => (A + (a - b) * x / y) if (a < b)
                if //op.0 == '/' && b.v.0 == 0 ||     // skip invalid expr.?
                   op.0 == '-' && b.is_subn_expr() { return }
                exps.push(Rc::new(Expr::new(a, *op, b)));
            });
        }));
    }   exps
}

// construct expressions down up from numbers
pub fn comp24_construct(goal: &Rational, nv: &[Rc<Expr>], exps: &mut HashSet<Rc<Expr>>) {
    if nv.len() == 1 { if nv[0].v == *goal { exps.insert(nv[0].clone()); } return }
    let mut hs = HashSet::new();

    // XXX: How to construct unique expressions over different combination orders?
    //nv.iter().tuple_combinations::<(_,_)>().for_each(|(a, b)| { });
    nv.iter().enumerate().for_each(|(i, a)|
        nv.iter().skip(i+1).for_each(|b| {
            // traverse all expr. combinations, make (a, b) in ascending order
            let (a, b) = if a.v < b.v { (a, b) } else { (b, a) };
            if !hs.insert((a, b)) { return }    // skip exactly same combinations
            //eprintln!("-> ({a}) ? ({b})");

            let nv = nv.iter().filter(|&e|
                !std::ptr::eq(e, a) && !std::ptr::eq(e, b))
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
                if !Expr::acceptable(a, *op, b) { return }

                // swap sub-expr. for order mattered (different values) operators
                if a != b && (op.0 == '/'/* &&  a.v.0 != 0*/ ||
                              op.0 == '-' && !a.is_subn_expr()) {
                    let mut nv = nv.to_vec();
                    nv.push(Rc::new(Expr::new(b, *op, a)));
                    comp24_construct(goal, &nv, exps);
                }

                // keep (a - b) * x / y - B for negative goal?
                // (A - (a - b) * x / y) => (A + (a - b) * x / y) if (a < b)
                if //op.0 == '/' && b.v.0 == 0 ||     // skip invalid expr.?
                   op.0 == '-' && b.is_subn_expr() { return }
                let mut nv = nv.to_vec();
                nv.push(Rc::new(Expr::new(a, *op, b)));
                comp24_construct(goal, &nv, exps);
            });
        }));
}

fn comp24_helper<I, S>(goal: &Rational, nums: I, algo: bool)
    where I: Iterator<Item = S>, S: AsRef<str> {
    let nums = nums.map(|str| str.as_ref().parse::<Rational>())
        .inspect(|res| if let Err(why) = res { eprintln!("Error parsing data: {why}")})
        .filter_map(Result::ok)
        .map(|rn| Rc::new(Expr { v: rn, m: None })).collect::<Vec<_>>();
    //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));

    let exps = if algo {
        debug_assert!(nums.len() < 64);     // XXX: max u128 for bitmask
        comp24_splitset(&nums).into_iter()
            .filter(|e| e.v == *goal).collect::<Vec<_>>()
    } else {
        let mut exhs = HashSet::default();
        comp24_construct(goal, &nums, &mut exhs);
        exhs.into_iter().collect::<Vec<_>>()
    };

        exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));
    if  exps.is_empty() { eprintln!("{}", Paint::yellow("Found no expressions!")) } else {
        //eprintln!("Got {} results!", Paint::yellow(exps.len()).bold());
    }   //todo!();  //Ok(())
}

pub fn comp24_main() {
    let mut goal = Rational::from(24);
    let mut nums = std::env::args().peekable();
    nums.next();    // skip the executable path

    if let Some(opt) = nums.peek() {
        if opt == "-g" {    nums.next();
            if let Some(gs) = &nums.next() {
                match gs.parse::<Rational>() {
                    Ok(_goal) => goal = _goal,
                    Err(e) => eprintln!("Error parsing GOAL: {e}"),
                }
            } else { eprintln!("Lack parameter for GOAL!") }
        }   comp24_helper(&goal, nums, true);
    }

    println!("\n### Solve {} computation ###", Paint::magenta(&goal).bold());
    loop {
        print!("\n{}{}{}", Paint::white("Input integers/rationals for ").dimmed(),
            Paint::cyan(&goal), Paint::white(": ").dimmed());

        let mut nums = String::new();
        std::io::stdout().flush().expect("Failed to flush!"); //.unwrap();
        std::io::stdin().read_line(&mut nums).expect("Failed to read!");
        let mut nums  = nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(first) = nums.peek() {
            if first.starts_with(&['g', 'G']) {
                match first[1..].parse::<Rational>() {
                    Ok(_goal) => {  goal = _goal;
                        println!("### Reset GOAL to {} ###", Paint::magenta(&goal).bold());
                    }
                    Err(e) => eprintln!("Error parsing GOAL: {e}"),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("quit") { break }
        }   comp24_helper(&goal, nums, true);
    }
}

//}

mod tests {     // unit test
    // Need to import items from parent module. Has access to non-public members.

    #[test]
    fn test_rational() {
        use super::*;

        let cases = [
            (Rational::from(0), "0"), (Rational(1, 2), "(1/2)"),
            (Rational::from(1), "1"), (Rational::from(-1), "(-1)"),
        ];

        cases.iter().for_each(|it| {
            println!("Test rational display/parse: {}", it.0);
            assert_eq!(it.0.to_string(), it.1);
            assert_eq!(it.0, it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<Rational>().unwrap()); });
    }

    #[test]
    fn test_comp24() {
        use super::*;

        let cases = [
            ( 24, vec![ 0], vec![], 0),
            ( 24, vec![24], vec!["24"], -1i32),
            ( 24, vec![ 8, 8, 8, 8], vec![], 0),
            ( 24, vec![ 1, 2, 3, 4], vec!["1*2*3*4", "2*3*4/1",
                "(1+3)*(2+4)", "4*(1+2+3)"], -1),
            ( 24, vec![ 8, 8, 3, 3], vec!["8/(3-8/3)"], -1),
            ( 24, vec![ 5, 5, 5, 1], vec!["(5-1/5)*5"], -1),
            ( 24, vec![10, 9, 7, 7], vec!["10+(9-7)*7"], -1),
            (100, vec![13,14,15,16,17], vec!["16+(17-14)*(13+15)",
                "(17-13)*(14+15)-16"], -1),
            (100, vec![ 1, 2, 3, 4, 5], vec![], 7),
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 75),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 304),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 2054),
        ];

        cases.iter().for_each(|it| {
            let assert_closure = |exps: &[Rc<Expr>]| {
                exps.iter().for_each(|e| println!("  {e}"));
                if 0 < it.3 { assert_eq!(exps.len(), it.3 as usize) } else {
                    assert!(exps.len() == it.2.len());
                    if  exps.len() == 1 { assert_eq!(exps[0].to_string(), it.2[0]) } else {
                        exps.iter().for_each(|e|
                            assert!(it.2.contains(&e.to_string().as_str())));
                    }
                }
            };

            println!("Test compute {} from {:?}, expect {} expressions.",
                it.0, it.1, if 0 < it.3 { it.3 as usize } else { it.2.len() });
            let nums = it.1.iter().map(|&n|
                Rc::new(Expr { v: n.into(), m: None })).collect::<Vec<_>>();

            let exps = comp24_splitset(&nums).into_iter()
                .filter(|e| e.v == it.0.into()).collect::<Vec<_>>();
            println!("  Got {} expressions by algo-splitset:", exps.len());
            assert_closure(&exps);

            if 0 < it.3 { return }  // XXX: skip slow test running
            let mut exps = HashSet::default();
            comp24_construct(&it.0.into(), &nums, &mut exps);
            let exps = exps.into_iter().collect::<Vec<_>>();
            println!("  Got {} expressions by algo-construct:", exps.len());
            assert_closure(&exps);
        });
    }

    //#[bench]
}

// vim:sts=4 ts=8 sw=4 noet