/****************************************************************
 * $ID: calc24.rs        四, 09  6 2022 18:09:34 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 五, 09  9 2022 16:46:32 +0800       by mhfan #
 ****************************************************************/

//pub mod calc24 {

//use std::io::prelude::*;

use yansi::{Paint, Color};  // Style
//use itertools::Itertools;

//type Rational = (i32, i32);   // i32/i64/BigInt
#[cfg(not(feature = "num-rational"))] pub type Rational = RNum<i32>;
#[cfg(feature = "num-rational")] pub type Rational = num_rational::Ratio<i32>;

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Copy)] #[repr(C)] pub struct RNum<T>(T, T);   // { n: T, d: T };

use num_integer::Integer;
impl<T: Integer + Copy> RNum<T> {   #![allow(dead_code)]
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

use std::fmt::{Debug, Display, Formatter};
#[cfg(feature = "debug")] impl<T: Integer + Copy + Display> Debug for RNum<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

impl<T: Integer + Copy + Display> Display for RNum<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let srn = self; //.reduce();
        if  srn.1.is_zero() { write!(f, r"(INV)")? } else {
            let braket = srn.0 * srn.1 < T::zero() || !srn.1.is_one();
            if  braket { write!(f, r"(")? }     write!(f, r"{}", srn.0)?;
            if  !srn.1.is_one() { write!(f, r"/{}", srn.1)? }
            if  braket { write!(f, r")")? }
        }   Ok(())  // FIXME: add padding?
    }
}

use core::str::FromStr;
impl<T: Integer + Copy + FromStr> FromStr for RNum<T> {
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.splitn(2, '/');
        let n = FromStr::from_str(s.next().unwrap())?;  // XXX:
        let d = FromStr::from_str(s.next().unwrap_or("1"))?;
        Ok(Self::new_raw(n, d))
    }   type Err = T::Err;
}

use core::cmp::{Eq, Ord, Ordering, PartialEq};
impl<T: Integer + Copy>  Eq for RNum<T> { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl<T: Integer + Copy> Ord for RNum<T> {
    fn cmp(&self, rhs: &Self) -> Ordering { (self.0 * rhs.1).cmp(&(self.1 * rhs.0)) }
}

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
    fn add(self, rhs: Self) -> Self::Output { todo!() }
    type Output = Self;
} */

#[derive(/*Debug, */Clone, Copy, PartialEq)] //struct Oper(u8);  // newtype idiom
#[repr(u8/*, C*/)] enum Oper { Num, Add = b'+', Sub = b'-', Mul = b'*', Div = b'/', }
//type Oper = char;   // type alias     // XXX: '*' -> '×' ('\xD7'), '/' -> '÷' ('\xF7')

//#[derive(Debug)] enum Value { None, Valid, R(Rational) }
//type Value = Option<Rational>;

pub use std::rc::Rc;
//#[derive(Debug)] //#[repr(packed(4)/*, align(4)*/)]
pub struct Expr { v: Rational, m: Option<(Rc<Expr>, Rc<Expr>)>, op: Oper }
//pub struct Expr { v: Rational, a: *const Expr, b: *const Expr, op: Oper }
// a & b refer to left & right operands

/* impl Expr {  #![allow(dead_code)]
    #[inline] fn is_one (&self) -> bool { self.op.0 == 0 && self.v.numer() == self.v.denom() }
    #[inline] fn is_zero(&self) -> bool { self.op.0 == 0 && self.v.numer() == &0 }
} */

//impl Drop for Expr { fn drop(&mut self) { eprintln!(r"Dropping: {self}"); } }

impl From<Rational> for Expr {
    #[inline] fn from(rn: Rational) -> Self {
        Self { v: rn/*.reduce()*/, m: None, op: Oper::Num }
    }
}

#[cfg(feature = "debug")] impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((a, b)) = &self.m {
            if a.m.is_none() { write!(f, r"{a}")?; } else { write!(f, r"({a})")?; }
            write!(f, r"{}", self.op.0 as char)?;
            if b.m.is_none() { write!(f, r"{b}")?; } else { write!(f, r"({b})")?; }
        } else { write!(f, r"{}", self.v)? }    Ok(())
        //Display::fmt(self, f)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {  use Oper::*;
        if let Some((a, b)) = &self.m {
            let braket = matches!(a.op, Add | Sub) && matches!(self.op, Mul | Div);

            if  braket { write!(f, r"(")? }     write!(f, r"{a}")?;
            if  braket { write!(f, r")")? }     write!(f, r"{}", self.op as u8 as char)?;

            let braket = self.op == Div && matches!(b.op, Mul | Div) ||
                self.op != Add && matches!(b.op, Add | Sub);

            if  braket { write!(f, r"(")? }     write!(f, r"{b}")?;
            if  braket { write!(f, r")")? }
        } else { write!(f, r"{}", self.v)? }    Ok(())
    }
}

/* impl Ord for Expr {
    fn cmp(&self, other: &Self) -> Ordering { self.partial_cmp(other).unwrap() }
} */

impl PartialOrd for Expr {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        let ord = self.v.partial_cmp(&rhs.v);
        if  ord != Some(Ordering::Equal) { return ord }

        match (&self.m, &rhs.m) {
            (None, None)    => Some(Ordering::Equal),
            (None, Some(_)) => Some(Ordering::Less),
            (Some(_), None) => Some(Ordering::Greater),

            (Some((la, lb)), Some((ra, rb))) => {
                let ord = (self.op as u8).partial_cmp(&(rhs.op as u8));
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
                self.op == rhs.op && la == ra && lb == rb,  // recursive
            _ => false, //(None, Some(_)) | (Some(_), None) => false,
        }   //self.v == rhs.v
    }
}

use std::hash::{Hash, Hasher};
impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        //self.to_string().hash(state); return;
        if let Some((a, b)) = &self.m {
            (self.op as u8).hash(state);  a.hash(state);  b.hash(state);    // recursive
        } else { self.v.numer().hash(state); self.v.denom().hash(state); }
    }
}

#[allow(dead_code)] fn hash_combine(lhs: u32, rhs: u32) -> u32 {    // u64
    //lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2))
    lhs ^ (rhs.wrapping_add(0x9e3779b9).wrapping_add(lhs.wrapping_shl(6))
                                       .wrapping_add(lhs.wrapping_shr(2)))
}

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

// several pruning rules to find inequivalent/unique expressions only
fn form_compose<F>(a: &Rc<Expr>, b: &Rc<Expr>, is_final: bool, ngoal: bool,
    mut new_expr: F) -> Option<()> where F: FnMut(Rc<Expr>) -> Option<()> {
    #[cfg(feature = "debug")] eprintln!(r"({a:?}) ? ({b:?})");
    let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };

    // XXX: check overflow and reduce?
    let (nmd, dmn, dmd) = (a.v.numer() * b.v.denom(),
               a.v.denom() * b.v.numer(), a.v.denom() * b.v.denom());
    // ((A . B) . b) => (A . (B . b), kept right sub-tree only

    use Oper::*;
    let op = Mul;
    // ((A / B) * b) => ((A * b) / B), (a * (A / B)) => ((a * A) / B) if a != 1
    // (1 * x)  is only kept in final, (a * (A * B)) => (A * (a * B)) if A  < a
    if !(a.op == op || a.op == Div || (Div == b.op && !a.v.is_one()) ||
        (!is_final && (a.v.is_one() || b.v.is_one())) ||
        (op == b.op && if let Some((ba, _)) = &b.m {
            ba.partial_cmp(a) == Some(Ordering::Less) } else { false })) {
        new_expr(Rc::new(Expr { v: Rational::new_raw(a.v.numer() * b.v.numer(),
                    dmd), m: Some((a.clone(), b.clone())), op }))?;
    }

    let op = Add;
    // ((A - B) + b) => ((A + b) - B), (a + (A - B)) => ((a + A) - B) if a != 0
    // (0 + x)  is only kept in final, (a + (A + B)) => (A + (a + B)) if A  < a
    if !(a.op == op || a.op == Sub || (Sub == b.op && !a.v.is_zero()) ||
        (!is_final && (a.v.is_zero() || b.v.is_zero())) ||
        (op == b.op && if let Some((ba, _)) = &b.m {
            ba.partial_cmp(a) == Some(Ordering::Less) } else { false })) {
        new_expr(Rc::new(Expr { v: Rational::new_raw(nmd + dmn, dmd),
                                m: Some((a.clone(), b.clone())), op }))?;
    }

    #[inline] fn find_factor(av: &Rational, b: &Rc<Expr>, op: Oper) -> bool {
        b.op == op && if let Some((ba, bb)) = &b.m {
            //(if ba.m.is_none() { &ba.v == av } else { find_factor(av, ba, op) } ||
            // if bb.m.is_none() { &bb.v == av } else { find_factor(av, bb, op) })
            &ba.v == av || find_factor(av, ba, op) ||
            &bb.v == av || find_factor(av, bb, op)
        } else { false }
    }

    let op = Sub;   //  (b - (B - A)) => ((b + A) - B)
    // (x - 0) => (0 + x),    ((A + x) - x) is only kept in final
    if !(a.op == op || op == b.op || a.v.is_zero() ||
        (!is_final && find_factor(&a.v, b, Add))) {
        if ngoal {
            new_expr(Rc::new(Expr { v: Rational::new_raw(nmd - dmn, dmd),
                                    m: Some((a.clone(), b.clone())), op }))?;
        } else {
            new_expr(Rc::new(Expr { v: Rational::new_raw(dmn - nmd, dmd),
                                    m: Some((b.clone(), a.clone())), op }))?;
        }
    }

    let op = Div;   //  (a / (A / B)) => ((a * B) / A)
    // (x / 1) => (1 * x), (0 / x) => (0 * x), ((x * B) / x) => ((x + B) - x)
    if !(a.op == op || op == b.op) {
        if !(dmn == 0 || b.v.is_one() || a.v.is_zero() ||
            find_factor(&b.v, a, Mul)) {
            new_expr(Rc::new(Expr { v: Rational::new_raw(nmd, dmn),
                                    m: Some((a.clone(), b.clone())), op }))?;
        }

        if !(nmd == 0 || a.v.is_one() || b.v.is_zero() ||   // order mattered only if a != b
             nmd == dmn || find_factor(&a.v, b, Mul)) {
            new_expr(Rc::new(Expr { v: Rational::new_raw(dmn, nmd),
                                    m: Some((b.clone(), a.clone())), op }))?;
        }
    }   Some(())
}

//use crate::list::List;
//use std::collections::LinkedList as List;   // both seems lower performance than Vec

//use std::collections::{HashSet, hash_map::DefaultHasher};
use ahash::{AHashSet as HashSet, AHasher as DefaultHasher};
//use rustc_hash::{FxHashSet as HashSet, FxHasher as DefaultHasher};
// faster than std version according to https://nnethercote.github.io/perf-book/hashing.html

// traversely top-down divide the number set by dynamic programming
fn calc24_dynprog <F>(goal: &Rational, nums: &[Rc<Expr>], ngoal: bool,
    each_found: &mut F) -> Option<()> where F: FnMut(Rc<Expr>) -> Option<()> {
    use core::cell::RefCell;       // for interior mutability, shared ownership
    let n = nums.len();     let psn = 1 << n; // size of powerset
    let mut vexp = vec![RefCell::new(vec![]); psn];
    if 1 < n { for i in 0..n { vexp[1 << i].get_mut().push(nums[i].clone()) } }

    let mut hv = Vec::with_capacity(psn - 2);
    let get_hash = |x| {
        let mut hasher = DefaultHasher::default();
        //nums.iter().enumerate().for_each(|(i, e)| if (1 << i) & x != 0 {
        //    #[cfg(feature = "debug")] eprint!(r"{e} "); e.hash(&mut hasher) });

        let (mut n, mut i) = (1, 0);
        while n <= x { if n & x != 0 {
            #[cfg(feature = "debug")] eprint!(r"{} ", nums[i]);
            nums[i].hash(&mut hasher) }     n <<= 1;    i += 1;
        }   hasher.finish()
    };

    for x in 3..psn { if x & (x - 1) == 0 { continue }  // skip when (x == 2^n)
        let is_final = x == psn - 1;

        let mut exps = vexp[x].borrow_mut();
        for i in 1..(x+1)/2 { if x & i != i { continue }
            let (es0, es1) = (vexp[i].borrow(), vexp[x - i].borrow());
            #[cfg(feature = "debug")] eprintln!(r"{i:08b}{} | {:08b}{}",
                if es0.is_empty() {"X"} else {"="}, x - i, if es1.is_empty() {"X"} else {"="});

            let h0 = get_hash(i); if hv.contains(&h0) { // skip duplicate combinations
                #[cfg(feature = "debug")] eprintln!(r"~ dup"); continue
            } else { #[cfg(feature = "debug")] eprint!(r"~ "); hv.push(h0) }

            let h1 = get_hash(x - i); if h1 != h0 { if hv.contains(&h1) {
                #[cfg(feature = "debug")] eprintln!(r"dup"); continue
                } else { hv.push(h1) }
            }   #[cfg(feature = "debug")] eprintln!(r"pick");

            es0.iter().enumerate().try_for_each(|(i, a)|
                es1.iter().skip(if h1 != h0 { 0 } else { i }).try_for_each(|b|
                    form_compose(a, b, is_final, ngoal, |e| {
                        if !is_final { exps.push(e) } else if e.v == *goal { each_found(e)? }
                        Some(())
                    })))?;
        }   hv.clear();
    }   Some(())

    //vexp.pop().unwrap().into_inner() //vexp[psn - 1].take()
}

//#[async_recursion::async_recursion(?Send)] async
// traversely top-down divide the number set straightforward
fn calc24_splitset<F>(goal: &Rational, nums: &[Rc<Expr>], ngoal: bool,
    each_found: &mut F) -> Vec<Rc<Expr>> where F: FnMut(Rc<Expr>) -> Option<()> {
    let (psn, mut exps) = (1 << nums.len(), vec![]);
    const IR: Rational = Rational::new_raw(0, 0);
    let is_final = !core::ptr::eq(goal, &IR);
    //if nums.len() < 2 { return nums.to_vec() }

    let mut hv = Vec::with_capacity(psn - 2);
    let get_hash = |ns: &[_]| {
        let mut hasher = DefaultHasher::default();
        ns.hash(&mut hasher);   hasher.finish()
    };

    //let mut used = HashSet::new();
    //let all_unique = nums.iter().all(|e| used.insert(e));

    for x in 1..psn/2 {
        let (mut ns0, mut ns1) = (vec![], vec![]);
        nums.iter().enumerate().for_each(|(i, e)|
            if (1 << i) & x != 0 { ns0.push(e.clone()) } else { ns1.push(e.clone()) });
        #[cfg(feature = "debug")] eprint!(r"{:?} ~ {:?} ", ns0, ns1);

        //if !all_unique {  // skip duplicate (ns0, ns1)
        let h0 = get_hash(&ns0); if hv.contains(&h0) {
            #[cfg(feature = "debug")] eprintln!(r"dup"); continue
        } else { hv.push(h0) }

        let h1 = get_hash(&ns1); if h1 != h0 { if hv.contains(&h1) {
            #[cfg(feature = "debug")] eprintln!(r"dup"); continue
            } else { hv.push(h1) }
        }   #[cfg(feature = "debug")] eprintln!(r"pick");
        //}     // no gain no penality for performance

        if 1 < ns0.len() { ns0 = calc24_splitset(&IR, &ns0, ngoal, each_found); }
        if 1 < ns1.len() { ns1 = calc24_splitset(&IR, &ns1, ngoal, each_found); }
        //(ns0, ns1) = futures::join!(calc24_splitset(&IR, &ns0, ngoal, each_found),
        //                            calc24_splitset(&IR, &ns1, ngoal, each_found));

        //ns0.iter().cartesian_product(ns1).for_each(|(&a, &b)| { });
        if  ns0.iter().enumerate().try_for_each(|(i, a)|
            ns1.iter().skip(if h1 != h0 { 0 } else { i }).try_for_each(|b|
                form_compose(a, b, is_final, ngoal, |e| {
                    if !is_final { exps.push(e) } else if e.v == *goal { each_found(e)? }
                    Some(())
                }))).is_none() { break }
    }   exps
}

// traversely construct expr. inplace bottom-up from numbers
fn calc24_inplace<F>(goal: &Rational, nums: &mut [Rc<Expr>], ngoal: bool,
    each_found: &mut F) -> Option<()> where F: FnMut(Rc<Expr>) -> Option<()> {
    let (n, mut i) = (nums.len(), 0);
    let mut hv = Vec::with_capacity(n * (n - 1) / 2);

    // XXX: skip duplicates over different combination order, as well in symmetric style
    while i < n - 1 {   let (a, mut j) = (nums[i].clone(), i + 1);
        while j < n {   let b = nums[j].clone();
            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // unify duplicate numbers
            if hv.contains(&h0) { j += 1; continue } else { hv.push(h0) }

            nums[j] = nums[n - 1].clone();  // the last j is n - 1
            form_compose(&a, &b, n == 2, ngoal, |e| {
                if n == 2 { if e.v == *goal { each_found(e)? } } else {    nums[i] = e;
                    calc24_inplace(goal, &mut nums[..n-1], ngoal, each_found)?;
                }   Some(())
            })?; nums[j] = b;   j += 1;
        }        nums[i] = a;   i += 1;
    }   Some(())
}

// traversely construct expr. bottom-up from numbers straightforward
fn calc24_construct<F>(goal: &Rational, nums: &[Rc<Expr>], minj: usize, ngoal: bool,
    each_found: &mut F) -> Option<()> where F: FnMut(Rc<Expr>) -> Option<()> {
    let n = nums.len();
    let mut hv = Vec::with_capacity(n * (n - 1) / 2);

    // XXX: skip duplicates in symmetric style, e.g.: [1 1 5 5]
    //nums.iter().tuple_combinations::<(_, _)>().for_each(|(a, b)| { });
    nums.iter().enumerate().skip(minj).try_for_each(|(j, b)|
        nums.iter().take(j).try_for_each(|a| {

            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // unify duplicate numbers
            if hv.contains(&h0) { return Some(()) } else { hv.push(h0) }

            let mut nums = nums.iter().filter(|&e|
                !Rc::ptr_eq(e, a) && !Rc::ptr_eq(e, b)) // core::ptr::eq
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            form_compose(a, b, nums.is_empty(), ngoal, |e| {
                if  nums.is_empty() { if e.v == *goal { each_found(e)? } } else {
                    nums.push(e);
                    calc24_construct(goal, &nums, j - 1, ngoal, each_found)?;
                    nums.pop();
                }   Some(())
            })}))
}

#[derive(Debug, Clone, Copy)] #[repr(u8/*, C*/)]
pub enum Calc24Algo { DynProg, SplitSet, Inplace, Construct, }
pub  use Calc24Algo::*;

// view dhat-heap.json in https://nnethercote.github.io/dh_view/dh_view.html
#[cfg(feature = "dhat-heap")] #[global_allocator] static ALLOC: dhat::Alloc = dhat::Alloc;
// cargo run --features dhat-heap   // memory profiling

#[inline] pub fn calc24_coll (goal: &Rational, nums: &[Rational],
    algo: Calc24Algo) -> Vec<String> {
    let mut exps = vec![];
    calc24_algo(goal, nums, algo, &mut |e: Rc<Expr>| {
        exps.push(e.to_string());   Some(()) });    exps
}

/// ```
/// use inrust::calc24::*;
/// let nums = (1..=4).map(|n| n.into()).collect::<Vec<_>>();
/// assert_eq!(calc24_first(&24.into(), &nums, DynProg), "1*2*3*4".to_owned());
/// ```
#[inline] pub fn calc24_first(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> String {
    let mut sexp = String::new();
    calc24_algo(goal, nums, algo, &mut |e| {
        sexp = e.to_string(); None });     sexp
}

/// ```
/// use inrust::calc24::*;
/// let nums = (1..=4).map(|n| n.into()).collect::<Vec<_>>();
/// assert_eq!(calc24_print(&24.into(), &nums, DynProg), 3);
/// ```
#[inline] pub fn calc24_print(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> usize {
    let mut cnt = 0;
    calc24_algo(goal, nums, algo, &mut |e| {
        println!(r"{}", Paint::green(e)); cnt += 1; Some(()) });    cnt
}

#[inline] pub fn calc24_algo<F>(goal: &Rational, nums: &[Rational], algo: Calc24Algo,
    each_found: &mut F) where F: FnMut(Rc<Expr>) -> Option<()> {
    if nums.len() == 1 { return if nums[0] == *goal { each_found(Rc::new(nums[0].into())); } }
    #[cfg(feature = "dhat-heap")] let _profiler = dhat::Profiler::new_heap();
    debug_assert!(nums.len() < core::mem::size_of::<usize>() * 8,
        r"Required by algo. DynProg & SplitSet");

    let ngoal = goal.is_negative(); //goal < &0.into();
    let mut nums = nums.iter().map(|&rn|
        Rc::new(rn.into())).collect::<Vec<Rc<Expr>>>();
    //quicksort(nums, |a, b| a.v.partial_cmp(&b.v));    // XXX:
    nums.sort_unstable_by(|a, b| a.v.cmp(&b.v));
    // so don't needs order-independent hasher

    let mut hexp = HashSet::new();
    let mut hash_unify = |e: Rc<Expr>| {
        let mut hasher = DefaultHasher::default();
        e.hash(&mut hasher);
        if hexp.insert(hasher.finish()) { each_found(e) } else { Some(()) }
    };

    match algo {    // TODO: output/count all possible expr. forms?
        DynProg   => { calc24_dynprog  (goal, &nums, ngoal, each_found); }
        SplitSet  => { calc24_splitset (goal, &nums, ngoal, each_found); }
        //SplitSet  => { futures::executor::block_on(calc24_splitset(goal, nums, each_found)); }
        Inplace   => { calc24_inplace  (goal, &mut nums, ngoal, &mut hash_unify); }
        Construct => {
            calc24_construct(goal, &nums, 1, ngoal, &mut hash_unify);
        }
    }
}

/// ```
/// use inrust::calc24::*;
/// let expect = (458, 1362, 3017);
/// assert_eq!(game24_solvable(DynProg), expect);
/// ```
pub fn game24_solvable(algo: Calc24Algo) -> (usize, usize, usize) {
    let (pkm, goal) = (13, Rational::from(24));
    let mut cnt = (0, 0, 0);

    //let mut pks = (1..=pkm).collect::<Vec<_>>();
    //use rand::{thread_rng, seq::SliceRandom};
    //let mut rng = thread_rng();
    //pks.shuffle(&mut rng);

    // TODO: solvable for 4~6 cards?
    (1..=pkm).for_each(|a| (a..=pkm).for_each(|b|       // C^52_4 = 270725
    (b..=pkm).for_each(|c| (c..=pkm).for_each(|d| {     // C^(13+4-1)_4 = 1820
        let nums = [a, b, c, d].into_iter()
            .map(|n| n.into()).collect::<Vec<_>>();     // XXX: n -> pks[n - 1]
        let exps = calc24_coll(&goal, &nums, algo);

        if  exps.is_empty() { cnt.0 += 1; } else {
            cnt.1 += 1;       cnt.2 += exps.len();

            //nums.shuffle(&mut rng);
            nums.into_iter().for_each(|rn|
                print!(r" {:2}", Paint::cyan(rn.numer())));    print!(r":");
            exps.into_iter().for_each(|e| print!(r" {}", Paint::green(e)));
            println!();
        }
    }))));

    // "1362 sets with 3017 solutions, 458 sets unsolvable."
    eprintln!(r"{} sets with {} solutions, {} sets unsolvable.", Paint::green(cnt.1).bold(),
        Paint::magenta(cnt.2), Paint::yellow(cnt.0).bold());  cnt
}

#[cfg(not(tarpaulin_include))]
pub fn game24_poker(n: usize, algo: Calc24Algo) {   // n = 4~6?
    let court  = [ "T", "J", "Q", "K" ]; // ♠Spade, ♡Heart, ♢Diamond, ♣Club
    let suits = [ Color::Blue, Color::Red, Color::Magenta, Color::Cyan ];
    let mut poker= (0..52).collect::<Vec<_>>();

    use rand::{thread_rng, seq::SliceRandom};
    let mut rng = thread_rng();

    // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode
    // https://www.me.uk/cards/makeadeck.cgi, https://github.com/revk/SVG-playing-cards
    println!(r"{}", Paint::new(            // https://github.com/htdebeer/SVG-cards
        r"Classic 24-game with poker (T=10, J=11, Q=12, K=13, A=1)").dimmed());

    loop {  poker.shuffle(&mut rng);
        let mut rems = poker.as_mut_slice();
        while  !rems.is_empty() {   let pkns;
            (pkns, rems) = rems.partial_shuffle(&mut rng, n);
            let nums = pkns.iter().map(|pkn| {
                //let (num, sid) = ((pkn % 13) + 1, (pkn / 13)/* % 4 */);
                let (sid, mut num) = pkn.div_rem(&13);
                num += 1;   //sid %= 4;

                print!(r" {}", Paint::new(if num == 1 { String::from("A") }
                    else if num < 10 { num.to_string() } else { court[num - 10].to_owned() })
                    .bold().bg(suits[sid]));    (num as i32).into()
            }).collect::<Vec<_>>();     print!(r": ");

            let exps = calc24_coll(&24.into(), &nums, algo);
            if  exps.is_empty() { println!(r"{}", Paint::yellow("None")); continue }

            loop {  use std::io::Write;
                let mut es = String::new();
                std::io::stdout().flush().expect(r"Failed to flush!"); //.unwrap();
                std::io::stdin().read_line(&mut es).expect(r"Failed to read!");

                let es = es.trim_end();
                if  es.eq_ignore_ascii_case("N") {
                    print!(r"{}", Paint::new(r"Solution:").dimmed());
                    exps.iter().for_each(|e| print!(r" {}", Paint::green(e)));
                    println!();     break
                }

                if  es.eq_ignore_ascii_case("quit") { return }
                if let Ok(res) = mexe::eval(es) {
                    if 24 == (res + 0.5) as i32 {
                        print!(r"{} ", Paint::new(r"Correct!").bg(Color::Green));
                        exps.iter().for_each(|e| print!(r" {}", Paint::green(e)));
                        println!(); break
                    }
                } else { print!(r"{} ", Paint::new(r"Tryagain:").dimmed()); }
            }
        }   println!();
    }
}

#[cfg(not(tarpaulin_include))] pub fn game24_cli() {
    fn game24_helper<I, S>(goal: &Rational, nums: I, algo: Calc24Algo)
        where I: Iterator<Item = S>, S: AsRef<str> {    // XXX: use closure instead?
        let nums = nums.filter_map(|s| match s.as_ref().parse::<Rational>() {
                Err(why) => {
                    eprintln!(r"Error parsing rational: {}", Paint::red(why));   None
                }
                Ok(rn) => { if rn.denom() == &0 {
                    eprintln!(r"Invalid rational number: {}/{}",
                        rn.numer(), Paint::red(rn.denom())) }   Some(rn)
                }
            }).collect::<Vec<_>>();

        if  nums.len() < 2 { return eprintln!(r"{}",
            Paint::yellow(r"Require two numbers at least!")) }
        let cnt = calc24_print(goal, &nums, algo);

        if  cnt < 1 {
            eprintln!(r"{}", Paint::yellow(r"Found NO solution!")) } else if 5 < cnt {
            eprintln!(r"Got {} solutions.", Paint::cyan(cnt).bold());
        }
    }

    let (mut goal, mut algo) = (24.into(), DynProg);
    let mut nums = std::env::args().peekable();
    nums.next();    // skip the executable path

    let mut want_exit = false;
    if let Some(opt) = nums.peek() {
        let opt = opt.clone();
        if opt.eq("-A") {   nums.next();
            if let Some(gs) = nums.next() { match gs.parse::<u32>() {
                Ok(n) => algo = match n {
                    1 => SplitSet, 2 => Inplace, 3 => Construct, _ => DynProg,
                },
                Err(e) => eprintln!(r"Error parsing ALGO: {}", Paint::red(e)),
            } } else { eprintln!(r"Lack parameter for ALGO!") }
        }

        if opt.eq_ignore_ascii_case("-g") {
            if opt == "-G" { want_exit = true }
            nums.next();

            if let Some(gs) = nums.next() { match gs.parse::<Rational>() {
                Ok(_goal) => goal = _goal,
                Err(e) => eprintln!(r"Error parsing GOAL: {}", Paint::red(e)),
            } } else { eprintln!(r"Lack parameter for GOAL!") }

            if nums.len() < 1 && goal == 24.into() {    game24_solvable(algo);
            } else { game24_helper(&goal, nums, algo); }
            if want_exit { std::process::exit(0) }
        }
    }

    /* use core::mem::size_of;   // size_of_val(a)
    println!("\nsize_of: Expr-{}, &Expr-{}, Rc<Expr>-{}, Oper-{}, Rational-{}",
        size_of::<Expr>(), size_of::<&Expr>(), size_of::<Rc<Expr>>(),
        size_of::<Oper>(), size_of::<Rational>()); */

    println!("\n### Solve {} calculation ###", Paint::magenta(&goal).bold());
    loop {
        print!("\n{}{}{}", Paint::new(r"Input integers/rationals for ").dimmed(),
            Paint::cyan(&goal), Paint::new(": ").dimmed());

        use std::io::Write;
        let mut nums = String::new();
        std::io::stdout().flush().expect(r"Failed to flush!"); //.unwrap();
        std::io::stdin().read_line(&mut nums).expect(r"Failed to read!");
        let mut nums  = nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(&first) = nums.peek() {
            if first.starts_with(&['g', 'G']) {
                match first[1..].parse::<Rational>() {
                    Ok(_goal) => {  goal = _goal;
                        println!(r"### Reset GOAL to {} ###", Paint::magenta(&goal).bold());
                    }
                    Err(e) => eprintln!(r"Error parsing GOAL: {}", Paint::red(e)),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("poker") {
                game24_poker(4, algo);  nums.next();    continue;
            } else if first.eq_ignore_ascii_case("quit") { break }
        }       game24_helper(&goal, nums, algo);
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

    debug_assert!(core::mem::size_of::<Rational>() == 8);
    //eprintln!("algo: {:?}, goal: {}, ncnt: {}", calc24.algo, calc24.goal, calc24.ncnt);
    extern "C" { fn calc24_algo(calc24: *mut Calc24IO); }

    //core::ptr::addr_of_mut!(calc24);
    unsafe { calc24_algo(&mut calc24);  // XXX:
        if 0 < calc24.ecnt && !calc24.exps.is_null() {    //assert!(!calc24.exps.is_null());
            let _exps = core::slice::from_raw_parts(calc24.exps,
                calc24.ecnt).iter().map(|es|
                std::ffi::CStr::from_ptr(*es).to_str().unwrap()).collect::<Vec<_>>();
        }
    }   calc24.ecnt
}

#[cfg(feature = "cxx")] #[cxx::bridge] mod ffi_cxx {    // TODO: not works yet
    struct Rational { n: i32, d: i32 }
    #[repr(u8)] enum Oper { Num, Add = b'+', Sub = b'-', Mul = b'*', Div = b'/', }
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
            assert!(it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<RNum<i32>>().unwrap() == it.0, r"parsing {} != {}",
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
            ( 24, vec![ 1, 2, 4,12], vec![], 5),
            ( 24, vec![ 2, 4, 4,12], vec![], 5),
            ( 24, vec![ 8, 8, 3, 3], vec!["8/(3-8/3)"], 0),
            ( 24, vec![ 3, 3, 7, 7], vec!["(3/7+3)*7"], 0),
            ( 24, vec![ 5, 5, 5, 1], vec!["(5-1/5)*5"], 0),
            ( 24, vec![10, 9, 7, 7], vec!["10+(9-7)*7"], 0),
            ( 24, vec![12,12,13,13], vec!["12+12+13-13"], 0),
            ( 24, vec![24,24,24,24], vec!["(24-24)*24+24"], 0),
            (  5, vec![ 1, 2, 3   ], vec!["1*(2+3)", "2*3-1" ], 0),
            ( 24, vec![ 1, 1, 2, 6], vec!["2*(1+1)*6", "(1+1+2)*6"], 0),
            ( 24, vec![ 1, 1, 2,12], vec!["1+2*12-1", "12/(1-1/2)"], 0),
            ( 24, vec![ 5, 5, 1, 1], vec!["1*(5*5-1)", "(5-1)*(1+5)"], 0),
            ( 24, vec![ 1, 2, 3, 4], vec!["1*2*3*4", "(1+3)*(2+4)", "4*(1+2+3)"], 0),
            (100, vec![13,14,15,16,17], vec!["16+(17-14)*(13+15)", "(17-13)*(14+15)-16"], 0),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 111),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 727),
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 45),
        ];

        cases.into_iter().for_each(|it| {
            let (goal, nums, res, cnt) = it;
            let cnt = if 0 < cnt { cnt } else { res.len() };
            println!(r"Calculate {:3} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
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

                assert_closure_c(DynProg);
                assert_closure_c(SplitSet);
                assert_closure_c(Inplace);
                assert_closure_c(Construct);
            }

            let assert_closure = |algo| {
                let exps = calc24_coll(&goal, &nums, algo);

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

            assert_closure(DynProg);
            assert_closure(SplitSet);
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

            let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();
            let (goal, now) = (goal.into(), Instant::now());
            calc24_coll(&goal, &nums, DynProg); // XXX: other algo?

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
