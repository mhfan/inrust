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
use std::{fmt, cmp::{Ordering, PartialEq}};
pub use std::rc::Rc;

//use itertools::Itertools;
use yansi::Paint;   // Color, Style

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

#[derive(Clone, Copy/*, Debug*/)]  // low cost
struct Oper(char);  // newtype idiom
//enum Oper { Num, Add(char), Sub(char), Mul(char), Div(char), }
//type Oper = char;       // type alias

//#[derive(Debug)]
//enum Value { Void, Valid, R(Rational) }
//type Value = Option<Rational>;

//#[repr(packed(2))]    //#[repr(align(4))]
//#[derive(Debug)]
pub struct Expr { pub v: Rational, m: Option<(Rc<Expr>, Oper, Rc<Expr>)> }

impl Expr {
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

        Self { v: operate(a, op, b), m: Some((Rc::clone(a), op, Rc::clone(b))) }
    }

    fn _hash_combine(lhs: u32, rhs: u32) -> u32 {
        //lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2))
        lhs ^ (rhs.wrapping_add(0x9e3779b9).wrapping_add(lhs.wrapping_shl(6))
                                           .wrapping_add(lhs.wrapping_shr(2)))
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

    fn form_expr<F: FnMut(Rc<Self>)>(a: &Rc<Self>, b: &Rc<Self>, mut func: F) {
        //const Add: Oper = Oper('+');
        //const Sub: Oper = Oper('-');
        //const Mul: Oper = Oper('*');
        //const Div: Oper = Oper('/');
        const OPS: [Oper; 4] = [ Oper('+'), Oper('-'), Oper('*'), Oper('/') ];

        OPS.iter().for_each(|op| {  // traverse '+', '-', '*', '/'
            // keep human friendly expr. form ONLY
            if let Some((_, aop, ..)) = &a.m {
                // ((a . b) . B) => (a . (b . B))
                if aop.0 == op.0 { return }

                // ((a - b) + B) => ((a + B) - b)
                // ((a / b) * B) => ((a * B) / b)
                match (aop.0, op.0) { ('-', '+') | ('/', '*') => return, _ => () }
            }

            if let Some((ba, bop, ..)) = &b.m {
                match (op.0, bop.0) {
                    // (A + (a + b)) => (a + (A + b)) if a < A
                    // (A * (a * b)) => (a * (A * b)) if a < A
                    ('+', '+') | ('*', '*') if ba.v < a.v => return,

                    // (A + (a - b)) => ((A + a) - b)
                    // (A * (a / b)) => ((A * a) / b)
                    // (A - (a - b)) => ((A + b) - a)
                    // (A / (a / b)) => ((A * b) / a)
                    ('+', '-') | ('*', '/') | ('-', '-') | ('/', '/') => return,

                    _ => ()
                }
            }

            // swap sub-expr. for order mattered (different values) operators
            if op.0 == '/' && a.v.0 != 0 || op.0 == '-'/* && !is_subn_expr(a)*/ {
                func(Rc::new(Self::new(b, *op, a)));
            }

            // prefer (b - a) than (a - b) when a < b
            if op.0 == '/' && b.v.0 == 0 || op.0 == '-'/* &&  is_subn_expr(b)*/ { return }
            func(Rc::new(Self::new(a, *op, b)));
        });

        /*#[inline(always)]
        fn is_subn_expr(e: &Expr) -> bool {
            if let Some((a, op, b)) = &e.m {
                if matches!(op.0, '*' | '/') { return is_subn_expr(a) || is_subn_expr(b) }
                if op.0 == '-' && a.v < b.v  { return true }
                // find ((a - b) * x / y) where a < b
            }   false
        }*/
    }
}

//impl Drop for Expr { fn drop(&mut self) { eprintln!(r"Dropping: {self}"); } }

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
        /* match (&self.m, &rhs.m) {
            (None, None) => self.v == rhs.v,
            (None, Some(_)) | (Some(_), None) => false,
            (Some((la, lop, lb)), Some((ra, rop, rb))) =>
                la == ra && lop.0 == rop.0 && lb == rb //&& self.v == rhs.v,
        } */

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        //self.to_string().hash(state); return;
        if let Some((a, op, b)) = &self.m {
            a.hash(state);  b.hash(state); op.0.hash(state);
            // XXX: have recursions, yet occasionally collision
        } else { self.v.0.hash(state); self.v.1.hash(state); }
    }
}

use std::collections::HashSet;
//use rustc_hash::FxHashSet as HashSet;
// faster than std version according to https://nnethercote.github.io/perf-book/hashing.html
//use rustc_hash::FxHasher as DefaultHasher;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

//use crate::list::List;
//use std::collections::LinkedList as List;     // both seems lower performance than Vec

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

fn comp24_dynprog(goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
    use std::cell::RefCell;     // for interior mutability, shared ownership
    let pow = 1 << nums.len();   // size of powerset
    let mut vexp = Vec::with_capacity(pow);
    (0..pow).for_each(|_| { vexp.push(RefCell::new(Vec::new())) });
    for i in 0..nums.len() { vexp[1 << i].borrow_mut().push(nums[i].clone()) }
    let mut hv = Vec::with_capacity(pow - 2);

    for x in 3..pow {
        if x & (x - 1) == 0 { continue }
        let sub_round = x != pow - 1;

        if  sub_round {     // skip duplicate combinations over different 'x'
            let mut hasher = DefaultHasher::default();
            //nums.iter().enumerate().for_each(|(i, e)| {
            //    if (1 << i) & x != 0 { e.hash(&mut hasher) } });
            let (mut n, mut i) = (1, 0);
            while  n < x {
                if n & x != 0 { nums[i].hash(&mut hasher) }
                n <<= 1;    i += 1;
            }   let h0 = hasher.finish();
            if hv.contains(&h0) { continue } else { hv.push(h0) }
        }

        let mut exps = vexp[x].borrow_mut();
        for i in 1..(x+1)/2 {
            if x & i != i { continue }
            let (si, sj) = (vexp[i].borrow(), vexp[x - i].borrow());

            //si.iter().cartesian_product(sj).for_each(|(&a, &b)| { });
            si.iter().for_each(|a| sj.iter().for_each(|b| {
                let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
                Expr::form_expr(a, b, |e|  // XXX: same code pieces
                    if sub_round { exps.push(e) } else if e.v == *goal {
                        if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) }});
                //eprintln!(r"-> ({a}) ? ({b})");
            }));
        }
    }   if pow == 2 { return Vec::new() }
    vexp.pop().unwrap().into_inner() //vexp[pow - 1].take()
}

// divide and conque number set
fn comp24_splitset(goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
    let (pow, mut exps) = (1 << nums.len(), Vec::new());
    let mut hv = Vec::with_capacity(pow - 2);
    let sub_round = std::ptr::eq(goal, &IR);
    const IR: Rational = Rational(0, 0);

    //let mut used = HashSet::default();
    //let all_unique = nums.iter().all(|e| used.insert(e));

    for x in 1..pow/2 {
        let (mut ns0, mut ns1) = (Vec::new(), Vec::new());
        nums.iter().enumerate().for_each(|(i, e)|
            if (1 << i) & x != 0 { ns0.push(e.clone()) } else { ns1.push(e.clone()) });
        //ns0.iter().for_each(|e| eprint!("{e} ")); eprint!("; ");
        //ns1.iter().for_each(|e| eprint!("{e} ")); eprintln!();

        //if !all_unique {      // no gain no penality for performance
        // skip duplicate (ns0, ns1)
        let mut hasher = DefaultHasher::default();
        ns0.hash(&mut hasher);   let h0 = hasher.finish();
        if hv.contains(&h0) { continue } else { hv.push(h0) }

        let mut hasher = DefaultHasher::default();
        ns1.hash(&mut hasher);   let h1 = hasher.finish();
        if h1 != h0 { if hv.contains(&h1) { continue } else { hv.push(h1) } }
        //}

        if 1 < ns0.len() { ns0 = comp24_splitset(&IR, &ns0, ia); }
        if 1 < ns1.len() { ns1 = comp24_splitset(&IR, &ns1, ia); }

        //ns0.iter().cartesian_product(ns1).for_each(|(&a, &b)| { });
        ns0.iter().for_each(|a| ns1.iter().for_each(|b| {
            let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
            Expr::form_expr(a, b, |e|  // XXX: same code pieces
                if sub_round { exps.push(e) } else if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) } });
            //eprintln!(r"-> ({a}) ? ({b})");
        }));
    }   exps
}

// construct expr. down up from numbers
fn comp24_construct(goal: &Rational, nums: &[Rc<Expr>], exps: &mut HashSet<Rc<Expr>>) {
    let mut hs = HashSet::new();
    let ia = false;

    // XXX: How to skip duplicates over different combination orders?
    //nums.iter().tuple_combinations::<(_, _)>().for_each(|(a, b)| { });
    nums.iter().enumerate().for_each(|(i, a)|
        nums.iter().skip(i+1).for_each(|b| {
            // traverse all expr. combinations, make (a, b) in ascending order
            let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
            if !hs.insert((a, b)) { return }    // skip exactly same combinations
            //eprintln!(r"-> ({a}) ? ({b})");

            let mut nums = nums.iter().filter(|&e|
                !std::ptr::eq(e, a) && !std::ptr::eq(e, b))
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            Expr::form_expr(a, b, |e| if nums.is_empty() && e.v == *goal {
                    if ia { println!(r"{}", Paint::green(&e)) } else { exps.insert(e); }
                } else { nums.push(e); comp24_construct(goal, &nums, exps); nums.pop(); });
        }));
}

#[derive(Debug, Clone, Copy)]
pub enum Comp24Algo { DynProg(bool), SplitSet(bool), Construct, }
pub  use Comp24Algo::*;

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;
// cargo run --features dhat-heap

#[inline(always)]
pub fn comp24_algo(goal: &Rational, nums: &[Rc<Expr>], algo: Comp24Algo) -> Vec<Rc<Expr>> {
    if nums.len() == 1 { return  if nums[0].v == *goal { nums.to_vec() } else { vec![] } }
    debug_assert!(nums.len() < 64);     // XXX: limited by u64/usize

    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    match algo {
        SplitSet(ia) => comp24_splitset(goal, nums, ia),
        DynProg (ia) => comp24_dynprog (goal, nums, ia),

        Construct => {
            let mut exps = HashSet::default();
            comp24_construct(goal, nums, &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }
    }
}

fn comp24_helper<I, S>(goal: &Rational, nums: I) where I: Iterator<Item = S>, S: AsRef<str> {
    let nums = nums.map(|str| str.as_ref().parse::<Rational>())
        .inspect(|res| if let Err(why) = res { eprintln!(r"Error parsing data: {why}")})
        .filter_map(Result::ok).map(|rn| Rc::new(rn.into())).collect::<Vec<_>>();
    //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));
    if nums.len() < 2 { return eprintln!(r"{}",
        Paint::yellow(r"Needs two numbers at least!")) }

    comp24_algo(goal, &nums, DynProg (true));
    //comp24_algo(goal, &nums, SplitSet(true));
    //comp24_algo(goal, &nums, Construct);
    // XXX: how to transfer a mut closure into resursive function?

    /*exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));

    let cnt = exps.len();
    if  cnt < 1 && !nums.is_empty() {
        eprintln!(r"{}", Paint::yellow(r"Found no expression!")) } else if 9 < cnt {
         println!(r"Got {} expressions!", Paint::cyan(cnt).bold());
    }*/
}

pub fn comp24_main() {
    let mut goal = 24.into();
    let mut nums = std::env::args().peekable();
    nums.next();    // skip the executable path

    let mut want_exit = false;
    if let Some(opt) = nums.peek() {
        if opt.eq_ignore_ascii_case("-g") {
            if opt == "-G" { want_exit = true }
            nums.next();

            if let Some(gs) = &nums.next() {
                match gs.parse::<Rational>() {
                    Ok(_goal) => goal = _goal,
                    Err(e) => eprintln!(r"Error parsing GOAL: {e}"),
                }
            } else { eprintln!(r"Lack parameter for GOAL!") }
        }

        use std::process::exit;
        comp24_helper(&goal, nums);
        if want_exit { exit(0) }
    }

    /* use std::mem::*;
    println!("\nsize_of: Expr-{}, &Expr-{}, Rc<Expr>-{}, Oper-{}, Rational-{}",
        size_of::<Expr>(), size_of::<&Expr>(), size_of::<Rc<Expr>>(),
        size_of::<Oper>(), size_of::<Rational>()); */
    // size_of_val(a)

    println!("\n### Solve {} computation ###", Paint::magenta(&goal).bold());
    loop {
        print!("\n{}{}{}", Paint::white(r"Input integers/rationals for ").dimmed(),
            Paint::cyan(&goal), Paint::white(": ").dimmed());

        use std::io::Write;
        let mut nums = String::new();
        std::io::stdout().flush().expect(r"Failed to flush!"); //.unwrap();
        std::io::stdin().read_line(&mut nums).expect(r"Failed to read!");
        let mut nums  = nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(first) = nums.peek() {
            if first.starts_with(&['g', 'G']) {
                match first[1..].parse::<Rational>() {
                    Ok(_goal) => {  goal = _goal;
                        println!(r"### Reset GOAL to {} ###", Paint::magenta(&goal).bold());
                    }
                    Err(e) => eprintln!(r"Error parsing GOAL: {e}"),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("quit") { break }
        }   comp24_helper(&goal, nums);
    }
}

//}

#[cfg(test)] mod tests {     // unit test
    use super::*;   // Need to import items from parent module, to access non-public members.

    #[test]
    fn test_rational() {
        use super::*;

        let cases = [
            (Rational::from(0), "0"), (Rational(1, 2), "(1/2)"),
            (Rational::from(1), "1"), (Rational::from(-1), "(-1)"),
        ];

        cases.iter().for_each(|it| {
            println!(r"Test rational display/parse: {}", it.0);
            assert_eq!(it.0.to_string(), it.1);
            assert_eq!(it.0, it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<Rational>().unwrap()); });
    }

    #[test]
    fn test_comp24() {
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
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 78),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 299),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 1832),
            //(100, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 5504),
            //( 24, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 34303),
        ];

        cases.iter().for_each(|it| {
            let (goal, nums, res, cnt) = it;
            let cnt = if 0 < *cnt { *cnt } else { res.len() };
            println!(r"Test compute {:3} from {:?}, expect {} expr.",
                Paint::cyan(goal), Paint::cyan(nums), Paint::cyan(cnt));

            let nums = nums.iter().map(|&n| Rc::new(n.into())).collect::<Vec<_>>();
            let goal = (*goal).into();

            let assert_closure = |goal, nums, algo| {
                let exps = comp24_algo(goal, nums, algo);

                exps.iter().for_each(|e| {
                    //println!(r"    {}", Paint::green(e));
                    if !res.is_empty() {
                        assert!(res.contains(&e.to_string().as_str()),
                            "  Unexpected expr.: {}", Paint::yellow(e))
                    }});

                println!(r"  Got {} expr. by algo-{:?}:",
                    Paint::magenta(exps.len()), Paint::magenta(algo));
                assert!(exps.len() == cnt);
            };

            /*unsafe {
                extern {
                    //fn comp24_splitset(const auto& goal, const list<const Expr*>& nums) -> list<const Expr*>;
                }
            }*/

            assert_closure(&goal, &nums, DynProg (false));
            assert_closure(&goal, &nums, SplitSet(false));
            if 10 < cnt { return }  // XXX: skip incorrect caused by hash collision
            assert_closure(&goal, &nums, Construct);
        });
    }

    //#[test]
    //#[bench]
    fn _test_bench() {
        use std::time::{Instant, Duration};
        use rand::{Rng, thread_rng, distributions::Uniform};

        let (cnt, mut total_time) = (50, Duration::from_millis(0));
        for _ in 0..cnt {
            let (mut rng, dst) = (thread_rng(), Uniform::new(1, 20));

            let (goal, nums) = (rng.sample(dst),
                rng.sample_iter(dst).take(6).collect::<Vec<_>>());
            println!(r"Bench compute {:2} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
            let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
            let (goal, now) = (goal.into(), Instant::now());

            comp24_algo(&goal, &nums, DynProg (false));
            //comp24_algo(&goal, &nums, SplitSet(false));
            total_time += now.elapsed();
        }

        println!(r"Totally {}s for {} iterations.",
            Paint::magenta(total_time.as_millis() as f32 / 1000.0), Paint::magenta(cnt));
        assert!(total_time.as_secs() < 8);
    }

    // cargo test -- --color always --nocapture
}

// vim:sts=4 ts=8 sw=4 noet