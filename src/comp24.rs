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
        if self.1 == 0 { write!(f, r"(INV)")? } else {
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

//enum Oper { Add(char), Sub(char), Mul(char), Div(char), }
#[derive(Clone, Copy)]  // low cost
pub struct Oper(char);  // newtype idiom
//type Oper = char;       // type alias

//#[derive(Debug)]
//enum Value { Void, Valid, R(Rational) }
//type Value = Option<Rational>;

//#[derive(Debug)]
pub struct Expr { pub v: Rational, m: Option<(Rc<Expr>, Oper, Rc<Expr>)> }

impl Expr {
    #[inline(always)]
    fn new(a: &Rc<Self>, op: Oper, b: &Rc<Self>) -> Self {
        #[inline(always)]
        fn operate(a: &Expr, op: Oper, b: &Expr) -> Rational {
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

        Self { v: operate(a, op, b),
               m: Some((Rc::clone(a), op, Rc::clone(b))) }
    }

    fn _simplify(v: &Rational) -> Rational {    // XXX: move to impl Rational?
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

    #[inline(always)]
    fn form_expr_exec<F: FnMut(Rc<Self>)>(a: &Rc<Self>, b: &Rc<Self>, mut func: F) {
        //const Add: Oper = Oper('+');
        //const Sub: Oper = Oper('-');
        //const Mul: Oper = Oper('*');
        //const Div: Oper = Oper('/');
        const OPS: [Oper; 4] = [Oper('+'), Oper('-'), Oper('*'), Oper('/')];

        OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
            if !acceptable(a, *op, b) { return }

            // swap sub-expr. for order mattered (different values) operators
            if a != b && (op.0 == '/' &&  a.v.0 != 0 ||     // skip invalid expr.
                          op.0 == '-' && !is_subn_expr(a)) {
                func(Rc::new(Self::new(b, *op, a)));
            }

            // keep (a - b) * x / y - B for negative goal?
            // (A - (a - b) * x / y) => (A + (a - b) * x / y) if (a < b)
            if op.0 == '/' && b.v.0 == 0 ||     // skip invalid expr.
               op.0 == '-' && is_subn_expr(b) { return }
            func(Rc::new(Self::new(a, *op, b)));
        });

        #[inline(always)]
        fn acceptable(a: &Expr, op: Oper, b: &Expr) -> bool {   // premise a < b
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

        #[inline(always)]
        fn is_subn_expr(e: &Expr) -> bool {
            if let Some((a, op, b)) = &e.m {
                if matches!(op.0, '*' | '/') { return is_subn_expr(a) || is_subn_expr(b) }
                if op.0 == '-' && a.v < b.v  { return true }
                // find ((a - b) * x / y) where a < b
            }   false
        }
    }
}

impl core::convert::From<Rational> for Expr {
    fn from(r: Rational) -> Self { Self { v: r, m: None } }
}

impl core::convert::From<i32> for Expr {
    fn from(n: i32) -> Self { Rational::from(n).into() }
}

impl fmt::Display for Expr {   // XXX: Is it possible to reuse it for Debug trait?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((a, op, b)) = &self.m {
            //#[allow(clippy::logic_bug)]
            let braket = if let Some((_, aop, ..)) = &a.m { //true ||
                matches!(aop.0, '+' | '-') && matches!(op.0, '*' | '/') } else { false };

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
        //self.to_string().hash(state); return;
        if let Some((a, op, b)) = &self.m {
            a.hash(state);  op.0.hash(state);   b.hash(state);
        } else { self.v.0.hash(state); self.v.1.hash(state); }
        // XXX: have recursions, yet occasionally collision
    }
}

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

pub fn comp24_dynprog(goal: &Rational, nums: &[Rc<Expr>]) -> Vec<Rc<Expr>> {
    use std::cell::RefCell;     // for interior mutability, shared ownership
    let pow = 1 << nums.len();   // size of powerset
    let mut vexp = Vec::with_capacity(pow);
    (0..pow).for_each(|_| { vexp.push(RefCell::new(Vec::new())) });
    for i in 0..nums.len() { vexp[1 << i].borrow_mut().push(nums[i].clone()); }

    for x in 3..pow {
        let mut ex = vexp[x].borrow_mut();
        let mut hs = HashSet::new();

        // XXX: How to skip duplicate combinations over different 'x'
        for i in 1..(x+1)/2 {
            if x & i != i { continue }  let j = x - i;
            //if j < i { continue }   // skip symmetric computation

            let (si, sj) = (vexp[i].borrow(), vexp[j].borrow());

            //si.iter().cartesian_product(sj).for_each(|(&a, &b)| { });
            si.iter().for_each(|a| sj.iter().for_each(|b| {
                let (a, b) = if a.v < b.v { (a, b) } else { (b, a) };
                if !hs.insert((a.clone(), b.clone())) { return }
                //eprintln!("-> ({a}) ? ({b})");

                Expr::form_expr_exec(a, b, |e| ex.push(e));
            }));
        }
    }

    let exps = vexp.last().unwrap().borrow().iter()
        .filter(|e| e.v == *goal).cloned().collect::<Vec<_>>(); exps
}

//use crate::list::List;
//use std::collections::LinkedList as List;

// divide and conque with numbers
pub fn comp24_splitset(nums: &[Rc<Expr>]) -> Vec<Rc<Expr>> {
    if nums.len() == 1 { return nums.to_vec() }

    //let mut used = HashSet::default();
    //let all_unique = nums.iter().all(|e| used.insert(e));

    let (pow, mut exps, mut hs) = (1 << nums.len(), Vec::new(), Vec::new());
    for mask in 1..pow/2 {
        let (mut ns0, mut ns1) = (Vec::new(), Vec::new());

        let pick_item = |ss: &mut Vec<_>, mut bits: usize|
            while 0 < bits {
            // isolate the rightmost bit to select one item
            let rightmost = bits & !(bits - 1);
            // turn the isolated bit into an array index
            let idx = rightmost.trailing_zeros() as usize;

            let item = nums[idx].clone();
            bits &= bits - 1;   // zero the trailing bit
            ss.push(item);      //eprint!(" {idx}");
        };

        // split true sub sets
        pick_item(&mut ns0,  mask);              //eprint!(";");
        pick_item(&mut ns1, !mask & (pow - 1)); //eprintln!();

        //if !all_unique {      // no gain no penality for performance
        //use rustc_hash::FxHasher as DefaultHasher;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        // skip duplicate (ns0, ns1)
        let mut hasher = DefaultHasher::default();
        ns0.hash(&mut hasher);   let h0 = hasher.finish();
        if hs.contains(&h0) { continue } else { hs.push(h0) }

        let mut hasher = DefaultHasher::default();
        ns1.hash(&mut hasher);   let h1 = hasher.finish();
        if h1 != h0 { if hs.contains(&h1) { continue } else { hs.push(h1) } }
        //}

        if 1 < ns0.len() { ns0 = comp24_splitset(&ns0); }
        if 1 < ns1.len() { ns1 = comp24_splitset(&ns1); }

        //ns0.iter().cartesian_product(ns1).for_each(|(&a, &b)| { });
        ns0.iter().for_each(|a| ns1.iter().for_each(|b| {
            let (a, b) = if a.v < b.v { (a, b) } else { (b, a) };
            Expr::form_expr_exec(a, b, |e| exps.push(e));
            //eprintln!("-> ({a}) ? ({b})");
        }));
    }   exps
}

// construct expressions down up from numbers
pub fn comp24_construct(goal: &Rational, nums: &[Rc<Expr>], exps: &mut HashSet<Rc<Expr>>) {
    if nums.len() == 1 { if nums[0].v == *goal { exps.insert(nums[0].clone()); } return }
    let mut hs = HashSet::new();

    // XXX: How to skip duplicates over different combination orders?
    //nums.iter().tuple_combinations::<(_, _)>().for_each(|(a, b)| { });
    nums.iter().enumerate().for_each(|(i, a)|
        nums.iter().skip(i+1).for_each(|b| {
            // traverse all expr. combinations, make (a, b) in ascending order
            let (a, b) = if a.v < b.v { (a, b) } else { (b, a) };
            if !hs.insert((a, b)) { return }    // skip exactly same combinations
            //eprintln!("-> ({a}) ? ({b})");

            let nums = nums.iter().filter(|&e|
                !std::ptr::eq(e, a) && !std::ptr::eq(e, b))
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            Expr::form_expr_exec(a, b, |e| {
                let mut nums = nums.to_vec();   nums.push(e);
                comp24_construct(goal, &nums, exps);
            });
        }));
}

#[derive(Debug, Clone, Copy)]
pub enum Comp24Algo { DynProg, SplitSet, Construct, }
pub  use Comp24Algo::*;

#[inline(always)]
pub fn comp24_algo(goal: &Rational, nums: &[Rc<Expr>], algo: Comp24Algo) -> Vec<Rc<Expr>> {
    match algo {
        SplitSet => comp24_splitset(nums).into_iter()
            .filter(|e| e.v == *goal).collect::<Vec<_>>(),
        DynProg  => comp24_dynprog(goal, nums),

        Construct => {
            let mut exps = HashSet::default();
            comp24_construct(goal, nums, &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }
    }
}

 fn comp24_helper<I, S>(goal: &Rational, nums: I, algo: Comp24Algo)
    where I: Iterator<Item = S>, S: AsRef<str> {
    let nums = nums.map(|str| str.as_ref().parse::<Rational>())
        .inspect(|res| if let Err(why) = res { eprintln!("Error parsing data: {why}")})
        .filter_map(Result::ok).map(|rn| Rc::new(rn.into())).collect::<Vec<_>>();
    //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));

    debug_assert!(nums.len() < 64);     // XXX: max u128 for bitmask
    let exps = comp24_algo(goal, &nums, algo);
        exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));

    let len = exps.len();
    if  len < 1 && !nums.is_empty() {
        eprintln!("{}", Paint::yellow("Found no expressions!")) } else if 50 < len {
         println!("Got {} expressions!", Paint::cyan(len).bold());
    }
}

pub fn comp24_main() {
    let mut goal = 24.into();
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
        }   comp24_helper(&goal, nums, SplitSet);
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
        }   comp24_helper(&goal, nums, SplitSet);
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
            ( 24, vec![24], vec!["24"], 0),
            ( 24, vec![ 8, 8, 8, 8], vec![], 0),
            ( 24, vec![ 8, 8, 3, 3], vec!["8/(3-8/3)"], 0),
            ( 24, vec![ 5, 5, 5, 1], vec!["(5-1/5)*5"], 0),
            ( 24, vec![10, 9, 7, 7], vec!["10+(9-7)*7"], 0),
            ( 24, vec![ 1, 2, 3, 4], vec!["1*2*3*4", "2*3*4/1",
                                          "(1+3)*(2+4)", "4*(1+2+3)"], 0),
            (100, vec![13,14,15,16,17], vec!["16+(17-14)*(13+15)",
                                             "(17-13)*(14+15)-16"], 0),
            (  5, vec![ 1, 2, 3], vec!["1*(2+3)", "(2+3)/1", "2*3-1",
                                       "2+1*3", "2/1+3", "2+3/1", "1*2+3", ], 0),
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 75),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 304),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 2054),
        ];

        cases.iter().for_each(|it| {
            let (goal, nums, res, cnt) = it;
            let cnt = if 0 < *cnt { *cnt } else { res.len() };
            println!("Test compute {} from {:?}, expect {} expr.",
                Paint::cyan(goal), Paint::cyan(nums), Paint::cyan(cnt));

            let nums = nums.iter().map(|&n| Rc::new(n.into())).collect::<Vec<_>>();
            let goal = (*goal).into();

            let assert_closure = |goal: &Rational, nums: &[Rc<Expr>], algo: Comp24Algo| {
                let exps = comp24_algo(goal, nums, algo);

                println!("  Got {} expr. by algo-{:?}:",
                    Paint::magenta(exps.len()), Paint::magenta(algo));

                exps.iter().for_each(|e| {
                    println!("    {}", Paint::green(e));
                    if !res.is_empty() { assert!(res.contains(&e.to_string().as_str())) }
                }); assert!(exps.len() == cnt);
            };

            assert_closure(&goal, &nums, SplitSet);

            if 50 < cnt { return }  // XXX: skip slow test running
            assert_closure(&goal, &nums, DynProg);

            if  5 < cnt { return }  // XXX: skip incorrect caused by hash collision
            assert_closure(&goal, &nums, Construct);
        });
    }

    //#[bench]
    fn _bench_comp24() {
        use super::*;

        use rand::{Rng, thread_rng, distributions::Uniform};
        let (mut rng, dst) = (thread_rng(), Uniform::new(1, 100));

        // repeat ? times
        let (goal, nums) = (rng.sample(dst),
            rng.sample_iter(dst).take(6).collect::<Vec<_>>());
        println!("Benchmark compute {} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
        let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
        let goal = goal.into();

        let _exps = comp24_algo(&goal, &nums, DynProg);
        let _exps = comp24_algo(&goal, &nums, SplitSet);
        let _exps = comp24_algo(&goal, &nums, Construct);

        // TODO:
    }

}

// vim:sts=4 ts=8 sw=4 noet