/****************************************************************
 * $ID: calc24.rs        四, 09  6 2022 18:09:34 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 一, 22  8 2022 15:28:09 +0800       by mhfan #
 ****************************************************************/

//pub mod calc24 {

//use std::io::prelude::*;

use yansi::Paint;   // Color, Style
//use itertools::Itertools;

//type Rational = (i32, i32);
#[cfg(not(feature = "num-rational"))] pub type Rational = RNum<i32>;
#[cfg(feature = "num-rational")] pub type Rational = num_rational::Ratio<i32>;

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary), derive(Clone, Copy))]
#[derive(Debug)] #[repr(C)] pub struct RNum<T>(T, T);   // { n: T, d: T };

use num_integer::Integer;
impl<T: Integer + Copy> RNum<T> {
    #![allow(dead_code)]

    #[inline] pub const fn numer(&self) -> &T { &self.0 }
    #[inline] pub const fn denom(&self) -> &T { &self.1 }
    #[inline] fn is_one (&self) -> bool { self.0 == self.1 }
    #[inline] fn is_zero(&self) -> bool { self.0 == T::zero() }
    #[inline] fn is_negative(&self) -> bool { self.0 * self.1 < T::zero() }
    //#[inline] fn is_positive(&self) -> bool { T::zero() < self.0 * self.1 }

    #[inline] pub const fn new_raw(numer: T, denom: T) -> Self { Self(numer, denom) }
    #[inline] pub fn new(numer: T, denom: T) -> Self {
        let mut rn = Self::new_raw(numer, denom);
        rn.reduce();    rn
    }

    /*pub */fn reduce(&mut self) -> &Self {
        #[inline] fn gcd<T: Integer + Copy>(mut a: T, mut b: T) -> T {
            // fast Euclid's algorithm for Greatest Common Denominator
            // Stein's algorithm (Binary GCD) support non-negative only
            while !b.is_zero() { a = a % b; core::mem::swap(&mut a, &mut b); } a //.abs()
        }

        let gcd = gcd(self.0, self.1);
        let (n, d) = (self.0 / gcd, self.1 / gcd);
        if T::zero() < d { self.0 = n; self.1 = d; } else {
            self.0 = T::zero() - n; self.1 = T::zero() - d;
        }   self
    }
}

use core::convert::From;
impl<T: Integer + Copy> From<T> for RNum<T> {
    fn from(n: T) -> Self { Self::new_raw(n, T::one()) }
}

use std::fmt::{Display,Formatter};
impl<T: Integer + Copy + Display> Display for RNum<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let srn = self; //.reduce();
        if  srn.1.is_zero() { write!(f, r"(INV)")? } else {
            let braket = srn.0 * srn.1 < T::zero() || !srn.1.is_one();
            if  braket { write!(f, r"(")? }     write!(f, r"{}", srn.0)?;
            if  !srn.1.is_one() { write!(f, r"/{}", srn.1)? }
            if  braket { write!(f, r")")? }
        }   Ok(())
    }
}

use core::str::FromStr;
impl<T: Integer + Copy + FromStr> FromStr for RNum<T> {
    type Err = T::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.splitn(2, '/');
        let n = FromStr::from_str(s.next().unwrap())?;  // XXX:
        let d = FromStr::from_str(s.next().unwrap_or("1"))?;
        Ok(Self::new_raw(n, d))
    }
}

use core::cmp::{Eq, /*Ord, */Ordering, PartialEq};
/* impl<T: Integer> Eq for RNum<T> { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl<T: Integer> std::cmp::Ord for RNum<T> {
    fn cmp(&self, rhs: &Self) -> Ordering { (self.0 * rhs.1).cmp(&(self.1 * rhs.0)) }
} */

impl<T: Integer + Copy> PartialOrd for RNum<T> {
    #[inline] fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        //if self.1 == 0 || rhs.1 == 0 { None } else { //Some(self.cmp(rhs))
            (self.0 * rhs.1).partial_cmp(&(self.1 * rhs.0))
    }
}

impl<T: Integer + Copy> PartialEq  for RNum<T> {
    #[inline] fn eq(&self, rhs: &Self) -> bool { self.partial_cmp(rhs) == Some(Ordering::Equal) }
}

/* impl<T: Integer + Copy> std::ops::Add for RNum<T> { //std::ops::{Add, Sub, Mul, Div}
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { todo!() }
} */

#[derive(/*Debug, */Clone, Copy)] struct Oper(u8);  // newtype idiom
//#[repr(C, u8)] enum Oper { Num, Add(u8), Sub(u8), Mul(u8), Div(u8), }
//type Oper = char;   // type alias

//#[derive(Debug)] enum Value { None, Valid, R(Rational) }
//type Value = Option<Rational>;

pub use std::rc::Rc;
//#[derive(Debug)] //#[repr(packed(4)/*, align(4)*/)]
pub struct Expr { v: Rational, m: Option<(Rc<Expr>, Rc<Expr>)>, op: Oper }
//pub struct Expr { v: Rational, a: *const Expr, b: *const Expr, op: Oper }
// a & b refer to left & right operands

/* impl Expr {
    #![allow(dead_code)]

    #[inline] fn is_one (&self) -> bool { self.op.0 == 0 && self.v.numer() == self.v.denom() }
    #[inline] fn is_zero(&self) -> bool { self.op.0 == 0 && self.v.numer() == &0 }
} */

//impl Drop for Expr { fn drop(&mut self) { eprintln!(r"Dropping: {self}"); } }

impl From<Rational> for Expr {
    #[inline] fn from(rn: Rational) -> Self { Self { v: rn/*.reduce()*/, m: None, op: Oper(0) } }
}

impl Display for Expr {   // XXX: Is it possible to reuse it for Debug trait?
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((a, b)) = &self.m {
            let braket = matches!(a.op.0, b'+' | b'-') &&
                matches!(self.op.0, b'*' | b'/');

            if  braket { write!(f, r"(")? }     write!(f, r"{a}")?;
            if  braket { write!(f, r")")? }     write!(f, r"{}", self.op.0 as char)?;

            let braket = self.op.0 == b'/' && matches!(b.op.0, b'*' | b'/') ||
                self.op.0 != b'+' && matches!(b.op.0, b'+' | b'-');

            if  braket { write!(f, r"(")? }     write!(f, r"{b}")?;
            if  braket { write!(f, r")")? }
        } else { write!(f, r"{}", self.v)? }    Ok(())
    }
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        let ord = self.v.partial_cmp(&rhs.v);
        if  ord != Some(Ordering::Equal) { return ord }

        match (&self.m, &rhs.m) {
            (None, None)    => Some(Ordering::Equal),
            (None, Some(_)) => Some(Ordering::Less),
            (Some(_), None) => Some(Ordering::Greater),

            (Some((la, lb)), Some((ra, rb))) => {
                let ord = self.op.0.partial_cmp(&rhs.op.0);
                if  ord != Some(Ordering::Equal) { return ord }
                let ord = la.partial_cmp(ra);   // recursive
                if  ord != Some(Ordering::Equal) { return ord }
                lb.partial_cmp(rb)   // recursive
            }
        }
    }
}

impl Eq for Expr { /*fn assert_receiver_is_total_eq(&self) { } */}
impl PartialEq for Expr {
    fn eq(&self, rhs: &Self) -> bool { //self.partial_cmp(rhs) == Some(Ordering::Equal)
        match (&self.m, &rhs.m) {
            (None, None) => self.v == rhs.v,
            (Some((la, lb)), Some((ra, rb))) =>
                self.op.0 == rhs.op.0 && la == ra && lb == rb,  // recursive
            _ => false, //(None, Some(_)) | (Some(_), None) => false,
        }   //self.v == rhs.v
    }
}

use std::hash::{Hash, Hasher};
impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        //self.to_string().hash(state); return;
        if let Some((a, b)) = &self.m {
            self.op.0.hash(state);  a.hash(state);  b.hash(state);  // recursive
        } else { self.v.numer().hash(state); self.v.denom().hash(state); }
    }
}

#[allow(dead_code)] fn hash_combine(lhs: u32, rhs: u32) -> u32 {
    //lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2))
    lhs ^ (rhs.wrapping_add(0x9e3779b9).wrapping_add(lhs.wrapping_shl(6))
                                       .wrapping_add(lhs.wrapping_shr(2)))
}

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

// several pruning rules to find inequivalent/unique expressions only
fn form_compose<F: FnMut(Rc<Expr>)>(a: &Rc<Expr>, b: &Rc<Expr>, is_final: bool, mut func: F) {
    let (nmd, dmn, dmd) = (a.v.numer() * b.v.denom(),
               a.v.denom() * b.v.numer(), a.v.denom() * b.v.denom());
    // ((a . b) . B) => (a . (b . B)    // XXX: check overflow and reduce?

    let op = Oper(b'*');
    // (A * (a * b)) => (a * (A * b)) if a < A
    // ((a / b) * B) => ((a * B) / b), (A * (a / b)) => ((A * a) / b)
    if a.op.0 != op.0 && a.op.0 != b'/' && b.op.0 != b'/' &&
        (!a.v.is_one() && !b.v.is_one() || is_final) &&
        (op.0 != b.op.0 || if let Some((ba, _)) = &b.m { a < ba } else { true }) {
        func(Rc::new(Expr { v: Rational::new_raw(a.v.numer() * b.v.numer(), dmd),
                            m: Some((a.clone(), b.clone())), op }));
    }

    let op = Oper(b'+');
    // (A + (a + b)) => (a + (A + b)) if a < A
    // ((a - b) + B) => ((a + B) - b), (A + (a - b)) => ((A + a) - b)
    if a.op.0 != op.0 && a.op.0 != b'-' && b.op.0 != b'-' &&
        (!a.v.is_zero() && !b.v.is_zero() || is_final) &&
        (op.0 != b.op.0 || if let Some((ba, _)) = &b.m { a < ba } else { true }) {
        func(Rc::new(Expr { v: Rational::new_raw(nmd + dmn, dmd),
                            m: Some((a.clone(), b.clone())), op }));
    }

    let op = Oper(b'-');
    // (B - (b - a)) => ((B + a) - b), x - 0 => x + 0?
    if a.op.0 != op.0 && op.0 != b.op.0 && !a.v.is_zero() {
        // FIXME: select (a - b) when goal < 0, better add condition in (a, b) ordering?
        func(Rc::new(Expr { v: Rational::new_raw(dmn - nmd, dmd),
                            m: Some((b.clone(), a.clone())), op }));
    }

    let op = Oper(b'/');    // order mattered
    // (A / (a / b)) => ((A * b) / a), x / 1 => x * 1, 0 / x => 0 * x?
    if a.op.0 != op.0 && op.0 != b.op.0 {
        if dmn != 0 && !b.v.is_one() && !a.v.is_zero() {
            func(Rc::new(Expr { v: Rational::new_raw(nmd, dmn),
                                m: Some((a.clone(), b.clone())), op }));
        }

        if nmd != 0 && !a.v.is_one() && !b.v.is_zero() {
            func(Rc::new(Expr { v: Rational::new_raw(dmn, nmd),
                                m: Some((b.clone(), a.clone())), op }));
        }
    }
}

//use crate::list::List;
//use std::collections::LinkedList as List;   // both seems lower performance than Vec

//use std::collections::{HashSet, hash_map::DefaultHasher};
use ahash::{AHashSet as HashSet, AHasher as DefaultHasher};
//use rustc_hash::{FxHashSet as HashSet, FxHasher as DefaultHasher};
// faster than std version according to https://nnethercote.github.io/perf-book/hashing.html

// traversely top-down divide the number set by dynamic programming
fn calc24_dynprog (goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
    use std::cell::RefCell;     // for interior mutability, shared ownership
    let pow = 1 << nums.len();   // size of powerset
    let mut vexp = Vec::with_capacity(pow);
    (0..pow).for_each(|_| { vexp.push(RefCell::new(Vec::new())) });
    for i in 0..nums.len() { vexp[1 << i].borrow_mut().push(nums[i].clone()) }
    let mut hv = Vec::with_capacity(pow - 2);

    for x in 3..pow {
        if x & (x - 1) == 0 { continue }
        let is_final = x == pow - 1;

        if !is_final {     // skip duplicate combinations over different 'x'
            let mut hasher = DefaultHasher::default();
            //nums.iter().enumerate().for_each(|(i, e)|     // no index access for list
            //    if (1 << i) & x != 0 { e.hash(&mut hasher) });
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
                let (a, b) = if b < a { (b, a) } else { (a, b) };
                form_compose(a, b, is_final, |e|
                    if !is_final { exps.push(e) } else if e.v == *goal {
                        if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) }});
                //eprintln!(r"-> ({a}) ? ({b})");
            }));
        }
    }

    if pow == 2 { return Vec::new() }
    vexp.pop().unwrap().into_inner() //vexp[pow - 1].take()
}

//#[async_recursion::async_recursion(?Send)] async
// traversely top-down divide the number set straightforward
fn calc24_splitset(goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
    //if nums.len() < 2 { return nums.to_vec() }
    let (pow, mut exps) = (1 << nums.len(), Vec::new());
    let mut hv = Vec::with_capacity(pow - 2);
    let is_final = !core::ptr::eq(goal, &IR);
    const IR: Rational = Rational::new_raw(0, 0);

    //let mut used = HashSet::default();
    //let all_unique = nums.iter().all(|e| used.insert(e));

    for x in 1..pow/2 {
        let (mut ns0, mut ns1) = (Vec::new(), Vec::new());
        nums.iter().enumerate().for_each(|(i, e)|
            if (1 << i) & x != 0 { ns0.push(e.clone()) } else { ns1.push(e.clone()) });
        //ns0.iter().for_each(|e| eprint!("{e} ")); eprint!("; ");
        //ns1.iter().for_each(|e| eprint!("{e} ")); eprintln!();

        //if !all_unique {  // no gain no penality for performance
        let mut hasher = DefaultHasher::default();
        ns0.hash(&mut hasher);   let h0 = hasher.finish();
        if hv.contains(&h0) { continue } else { hv.push(h0) }

        let mut hasher = DefaultHasher::default();
        ns1.hash(&mut hasher);   let h1 = hasher.finish();
        if h1 != h0 { if hv.contains(&h1) { continue } else { hv.push(h1) } }
        //}     // skip duplicate (ns0, ns1)

        if 1 < ns0.len() { ns0 = calc24_splitset(&IR, &ns0, ia); }
        if 1 < ns1.len() { ns1 = calc24_splitset(&IR, &ns1, ia); }
        //(ns0, ns1) = futures::join!(calc24_splitset(&IR, &ns0, ia),
        //                            calc24_splitset(&IR, &ns1, ia));

        //ns0.iter().cartesian_product(ns1).for_each(|(&a, &b)| { });
        ns0.iter().for_each(|a| ns1.iter().for_each(|b| {
            let (a, b) = if b < a { (b, a) } else { (a, b) };
            form_compose(a, b, is_final, |e|
                if !is_final { exps.push(e) } else if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) } });
            //eprintln!(r"-> ({a}) ? ({b})");
        }));
    }   exps
}

// traversely construct expr. inplace bottom-up from numbers
fn calc24_inplace<'a>(goal: &Rational, nums: &mut [Rc<Expr>],
    exps: &'a mut HashSet<Rc<Expr>>) -> &'a HashSet<Rc<Expr>> {
    let (n, mut i, ia) = (nums.len(), 0, false);
    let mut hv = Vec::with_capacity(n * (n - 1) / 2);

    while i < n {
        let (ta, mut j) = (nums[i].clone(), i + 1);
        while j < n {    let tb = nums[j].clone();
            let (a, b) = if tb < ta { (&tb, &ta) } else { (&ta, &tb) };

            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // in case duplicate numbers
            if hv.contains(&h0) { j += 1; continue } else { hv.push(h0) }
            //eprintln!(r"-> ({a}) ? ({b})");

            nums[j] = nums[n - 1].clone();
            form_compose(a, b, n == 2, |e|
                if n == 2 { if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(&e)) } else { exps.insert(e); }}
                } else { nums[i] = e; calc24_inplace(goal, &mut nums[..n-1], exps); });

            nums[j] = tb;   j += 1;
        }   nums[i] = ta;   i += 1;
    }   exps
}

// traversely construct expr. bottom-up from numbers straightforward
fn calc24_construct<'a>(goal: &Rational, nums: &[Rc<Expr>],
    exps: &'a mut HashSet<Rc<Expr>>) -> &'a HashSet<Rc<Expr>> {
    let (n, ia) = (nums.len(), false);  // got duplicates in interactive
    let mut hv = Vec::with_capacity(n * (n - 1) / 2);

    // XXX: How to skip duplicates over different combination orders?
    //nums.iter().tuple_combinations::<(_, _)>().for_each(|(a, b)| { });
    nums.iter().enumerate().for_each(|(i, a)|
        nums.iter().skip(i+1).for_each(|b| {
            // traverse all expr. combinations, make (a, b) in ascending order
            let (a, b) = if b < a { (b, a) } else { (a, b) };
            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // in case duplicate numbers
            if hv.contains(&h0) { return } else { hv.push(h0) }
            //eprintln!(r"-> ({a}) ? ({b})");

            let mut nums = nums.iter().filter(|&e|
                !core::ptr::eq(e, a) && !core::ptr::eq(e, b))
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            form_compose(a, b, nums.is_empty(), |e|
                if nums.is_empty() { if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(&e)) } else { exps.insert(e); }}
                } else { nums.push(e); calc24_construct(goal, &nums, exps); nums.pop(); });
        }));    exps
}

#[derive(Debug, Clone, Copy)] #[repr(C, u8)]
pub enum Calc24Algo { DynProg(bool), SplitSet(bool), Inplace, Construct, }
pub  use Calc24Algo::*;

// view dhat-heap.json in https://nnethercote.github.io/dh_view/dh_view.html
#[cfg(feature = "dhat-heap")] #[global_allocator] static ALLOC: dhat::Alloc = dhat::Alloc;
// cargo run --features dhat-heap   // memory profiling

#[inline] pub fn calc24_algo(goal: &Rational, nums: &[Rc<Expr>],
    algo: Calc24Algo) -> Vec<Rc<Expr>> {
    if nums.len() == 1 { return  if nums[0].v == *goal { nums.to_vec() } else { vec![] } }
    #[cfg(feature = "dhat-heap")] let _profiler = dhat::Profiler::new_heap();
    debug_assert!(nums.len() < core::mem::size_of::<usize>() * 8);

    match algo {    // TODO: closure: a. collect, b. print and count, c. stop on first found;
        DynProg (ia) => calc24_dynprog (goal, nums, ia),
        SplitSet(ia) => calc24_splitset(goal, nums, ia),
        //SplitSet(ia) => futures::executor::block_on(calc24_splitset(goal, nums, ia)),

        Inplace => {
            let mut exps = HashSet::default();
            calc24_inplace(goal, &mut nums.to_vec(), &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }

        Construct => {
            let mut exps = HashSet::default();
            calc24_construct(goal, nums, &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }
    }
}

#[cfg(not(tarpaulin_include))]
pub fn game24_cli() {
    fn game24_helper<I, S>(goal: &Rational, nums: I)
        where I: Iterator<Item = S>, S: AsRef<str> {    // XXX: how to use closure instead?
        let nums = nums.map(|str| str.as_ref().parse::<Rational>())
            .inspect(|res| match res {  // XXX: exit on error?
                Err(why) => eprintln!(r"Error parsing rational: {}", Paint::red(why)),
                Ok(rn) => if rn.denom() == &0 {
                    eprintln!(r"Invalid rational number: {}/{}", rn.numer(),
                    Paint::red(rn.denom())) }})
            .filter_map(Result::ok).map(|rn| Rc::new(rn.into())).collect::<Vec<_>>();
        //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));
        if  nums.len() < 2 { return eprintln!(r"{}",
            Paint::yellow(r"Needs two numbers at least!")) }

        let ia = true;
        let exps = calc24_algo(goal, &nums, DynProg (ia));
        //let exps = calc24_algo(goal, &nums, SplitSet(ia));
        //let exps = calc24_algo(goal, &nums, Inplace);
        //let exps = calc24_algo(goal, &nums, Construct);
        // XXX: how to transfer a mut closure into a resursive function?

        if ia { return }
        exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));
        let cnt = exps.len();
        if  cnt < 1 && !nums.is_empty() {
            eprintln!(r"{}", Paint::yellow(r"Found NO solution!")) } else if 5 < cnt {
             println!(r"Got {} solutions.", Paint::cyan(cnt).bold());
        }
    }

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

            game24_helper(&goal, nums);
            if want_exit { std::process::exit(0) }
        }
    }

    /* use core::mem::size_of;   // size_of_val(a)
    println!("\nsize_of: Expr-{}, &Expr-{}, Rc<Expr>-{}, Oper-{}, Rational-{}",
        size_of::<Expr>(), size_of::<&Expr>(), size_of::<Rc<Expr>>(),
        size_of::<Oper>(), size_of::<Rational>()); */

    println!("\n### Solve {} calculation ###", Paint::magenta(&goal).bold());
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
        }   game24_helper(&goal, nums);
    }
}

#[cfg(feature = "cc")] #[inline]
pub fn calc24_algo_c(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> usize {
    #[repr(C)] struct Calc24IO {
        algo: Calc24Algo, //ia: bool,
        goal: Rational, //nums: &[Rational],
        nums: *const Rational, ncnt: usize,

        ecnt: usize, //core::ffi::c_size_t,
        exps: *mut *const std::os::raw::c_char,
        //exps: *mut *const SharedPtr<Expr>,
        //exps: *mut *const Expr,
    }

    struct Cstr(*mut *const std::os::raw::c_char);
    impl Drop for Cstr { fn drop(&mut self) { todo!() } }

    let mut calc24 = Calc24IO {
        algo, goal: Rational::new_raw(*goal.numer(), *goal.denom()),
        //goal: unsafe { core::mem::transmute(goal) },
        nums: nums.as_ptr(), ncnt: nums.len(),
        ecnt: 0, exps: core::ptr::null_mut(),
    };

    // XXX: constraint according definition in C++
    debug_assert!(core::mem::size_of::<Rational>() == 8);
    //eprintln!("algo: {:?}, goal: {}, ncnt: {}", calc24.algo, calc24.goal, calc24.ncnt);
    debug_assert!(core::mem::size_of_val(&calc24.algo) == 2,
        "{}", core::any::type_name::<Calc24Algo>());

    extern "C" { fn calc24_algo(calc24: *mut Calc24IO); }

    //core::ptr::addr_of_mut!(calc24);
    unsafe { calc24_algo(&mut calc24);  // TODO:
        /* assert!(!calc24.exps.is_null());
        let exps = core::slice::from_raw_parts(calc24.exps, calc24.ecnt).iter().map(|es|
            std::ffi::CStr::from_ptr(*es).to_str().unwrap()).collect::<Vec<_>>(); */
    }   calc24.ecnt
}

#[cfg(feature = "cxx")] #[cxx::bridge] mod ffi_cxx {    // TODO: not works yet
    struct Rational { n: i32, d: i32 }
    #[repr(u8)] enum Oper { Num, Add, Sub, Mul, Div, }
    struct Expr { v: Rational, a: SharedPtr<Expr>, b: SharedPtr<Expr>, op: Oper }
    #[repr(u8)] enum Calc24Algo { DynProg, SplitSet, Inplace, Construct }

    extern "Rust" { }

    unsafe extern "C++" {
        include!("calc24.h");

        //type PtrE;// = cxx::SharedPtr<Expr>;

        /* CxxVector cannot hold SharePtr<_>
        fn calc24_dynprog (goal: &Rational, nums: &CxxVector<SharedPtr<Expr>>) ->
            UniquePtr<CxxVector<SharedPtr<Expr>>>;
        fn calc24_splitset(goal: &Rational, nums: &CxxVector<SharedPtr<Expr>>) ->
            UniquePtr<CxxVector<SharedPtr<Expr>>>; */
    }
}

//}

#[cfg(test)] mod tests {    // unit test
    use super::*;   // Need to import items from parent module, to access non-public members.

    #[test] fn parse_disp_rn() {
        let cases = [
            (RNum::from(0), "0"), (RNum::new_raw(1, 2), "(1/2)"),
            (RNum::from(1), "1"), (RNum::from(-1), "(-1)"),
        ];

        cases.iter().for_each(|it| {
            assert_eq!(it.0.to_string(), it.1, r"display {} != {}",
                Paint::red(&it.0), Paint::cyan(&it.1));
            assert_eq!(it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<RNum<i32>>().unwrap(),  it.0, r"parsing {} != {}",
                Paint::red(&it.1), Paint::cyan(&it.0));
        });
    }

    #[test] fn reduce_rn() {
        let cases = [
            (RNum::new(-1, -1), RNum::new_raw( 1, 1)),
            (RNum::new(-4, -2), RNum::new_raw( 2, 1)),
            (RNum::new( 6, -2), RNum::new_raw(-3, 1)),
            (RNum::new( 3,  2), RNum::new_raw( 3, 2)),
        ];

        cases.into_iter().for_each(|(a, b)| {
            assert!(a.numer() == b.numer() && a.denom() == b.denom(),
                "simplified rational: {a}");
        });
    }

    #[test] fn solve24() {
        let cases = [
            ( 24, vec![ 0], vec![], 0),
            ( 24, vec![24], vec!["24"], 0),
            ( 24, vec![ 8, 8, 8, 8], vec![], 0),
            ( 24, vec![ 8, 8, 3, 3], vec!["8/(3-8/3)"], 0),
            ( 24, vec![ 3, 3, 7, 7], vec!["(3/7+3)*7"], 0),
            ( 24, vec![ 5, 5, 5, 1], vec!["(5-1/5)*5"], 0),
            ( 24, vec![10, 9, 7, 7], vec!["10+(9-7)*7"], 0),
            ( 24, vec![24,24,24,24], vec!["(24-24)*24+24"], 0),
            (  5, vec![ 1, 2, 3], vec!["1*(2+3)", "2*3-1" ], 0),
            ( 24, vec![ 1, 2, 3, 4], vec!["1*2*3*4", "(1+3)*(2+4)", "4*(1+2+3)"], 0),
            (100, vec![13,14,15,16,17], vec!["16+(17-14)*(13+15)",
                                             "(17-13)*(14+15)-16"], 0),
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 47),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 113),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 847),
            //(100, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 3031),
            //( 24, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 14500),
        ];

        cases.into_iter().for_each(|it| {
            let (goal, nums, res, cnt) = it;
            let cnt = if 0 < cnt { cnt } else { res.len() };
            println!(r"Compute {:3} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
            let goal = goal.into();

            #[cfg(feature = "cc")]
            let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();

            #[cfg(feature = "cc")] {
                let assert_closure_c = |algo| {
                    let elen = calc24_algo_c(&goal, &nums, algo);
                    println!(r"  {} solutions by algo-Cxx{:?}",
                        Paint::green(elen), Paint::green(algo));
                    assert!(elen == cnt, r"Unexpect count by algo-Cxx{:?}: {} != {}",
                        Paint::magenta(algo), Paint::red(elen), Paint::cyan(cnt));
                };

                assert_closure_c(DynProg (false));
                assert_closure_c(SplitSet(false));
                if cnt < 100 { assert_closure_c(Inplace); }
            }

            let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
            let assert_closure = |algo| {
                let exps = calc24_algo(&goal, &nums, algo);

                exps.iter().for_each(|e| {
                    //println!(r"  {}", Paint::green(e));
                    if res.is_empty() { return }
                    assert!(res.contains(&e.to_string().as_str()),
                        r"Unexpect expr. by algo-{:?}: {}", Paint::magenta(algo), Paint::red(e));
                });

                println!(r"  {} solutions by algo-{:?}",
                    Paint::green(exps.len()), Paint::green(algo));
                assert!(exps.len() == cnt, r"Unexpect count by algo-{:?}: {} != {}",
                    Paint::magenta(algo), Paint::red(exps.len()), Paint::cyan(cnt));
            };

            assert_closure(DynProg (false));
            assert_closure(SplitSet(false));
            if 100 < cnt { return }     // XXX: regarding speed
            assert_closure(Inplace);
            assert_closure(Construct);

            #[cfg(feature = "cxx")] {
                use cxx::{/*CxxVector, */memory::SharedPtr};
                impl From<Expr> for ffi_cxx::Expr {
                    fn from(e: Expr) -> Self { Self { v: unsafe { core::mem::transmute(e.v) },
                        op: ffi_cxx::Oper::Num, a: SharedPtr::null(), b: SharedPtr::null() }
                    }
                }

                //let goal: Rational = unsafe { core::mem::transmute(goal) };
                //ffi_cxx::calc24_dynprog(&goal, &nums);    // FIXME:
            }
        });
    }

    #[cfg(feature = "cc")] /*#[test] */fn _solve24_c() {
        /*#[link(name = "calc24")] */extern "C" { fn test_24calc(); }
        unsafe { test_24calc(); }
    }

    #[cfg(not(tarpaulin_include))]
    /*#[test] #[bench] */fn _solve24_random() {
        use std::time::{Instant, Duration};
        use rand::{Rng, thread_rng, distributions::Uniform};

        let (cnt, mut total_time) = (50, Duration::from_millis(0));
        for _ in 0..cnt {
            let (mut rng, dst) = (thread_rng(), Uniform::new(1, 20));

            let (goal, nums) = (rng.sample(dst),
                rng.sample_iter(dst).take(6).collect::<Vec<_>>());
            println!(r"Compute {:2} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
            let nums = nums.into_iter().map(|n|
                Rc::new(Rational::from(n).into())).collect::<Vec<_>>();
            let (goal, now) = (goal.into(), Instant::now());

            calc24_algo(&goal, &nums, DynProg (false));
            //calc24_algo(&goal, &nums, SplitSet(false));
            //calc24_algo(&goal, &nums, Inplace);
            //calc24_algo(&goal, &nums, Construct);

            total_time += now.elapsed();
        }

        println!(r"Totally {}s for {} iterations.",
            Paint::magenta(total_time.as_millis() as f32 / 1000.0), Paint::magenta(cnt));
        assert!(total_time.as_secs() < 8);
    }

    // https://doc.rust-lang.org/nightly/rustc/instrument-coverage.html
    // RUSTFLAGS="-C instrument-coverage" cargo test    # XXX: didn't try yet
    // llvm-profdata merge -sparse default.profraw -o default.profdata
    // llvm-cov report --use-color --ignore-filename-regex='/.cargo/registry' \
    //      -instr-profile=default.profdata target/release/test-binary
    // llvm-cov show   --use-color --ignore-filename-regex='/.cargo/registry' \
    //      -instr-profile=default.profdata target/release/test-binary \
    //      -Xdemangler=rustfilt -show-line-counts-or-regions \
    //      -show-instantiations -name=add_quoted_string

    // cargo test -- --color always --nocapture
}

// vim:sts=4 ts=8 sw=4 noet
