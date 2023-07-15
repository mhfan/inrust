/****************************************************************
 * $ID: calc24.rs        四, 09  6 2022 18:09:34 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 一, 24 10 2022 10:10:08 +0800       by mhfan #
 ****************************************************************/

//pub mod calc24 {

//use std::io::prelude::*;

use yansi::{Paint, Color};  // Style
//use itertools::Itertools;

//type Rational = (i32, i32);   // i32/i64/i128
#[cfg(not(feature = "num-rational"))] pub type Rational = RNum<i32>;
#[cfg(feature = "num-rational")] pub type Rational = num_rational::Ratio<i32>;
#[cfg(feature = "num-rational")] use num_traits::{identities::{One, Zero}, sign::Signed};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
//#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Copy)] #[repr(C)] pub struct RNum<T>(T, T);   // { n: T, d: T };

use num_traits::PrimInt;    //use num_integer::Integer;     // for BigInt, somewhere `+ Copy'
impl<T: PrimInt> RNum<T> {   #![allow(dead_code)]
    #[inline] pub const fn numer(&self) -> &T { &self.0 }
    #[inline] pub const fn denom(&self) -> &T { &self.1 }
    #[inline] fn is_one (&self) -> bool { self.0 == self.1 }
    #[inline] fn is_zero(&self) -> bool { self.0 == T::zero() }
    #[inline] fn is_negative(&self) -> bool { self.0 * self.1 < T::zero() }
    //#[inline] fn is_positive(&self) -> bool { T::zero() < self.0 * self.1 }

    #[inline] pub const fn new_raw(n: T, d: T) -> Self { Self(n, d) }
    #[inline] pub fn new(num: T, den: T) -> Self { *Self::new_raw(num, den).reduce() }

    /*pub */fn reduce(&mut self) -> &Self {
        #[inline] fn gcd<T: PrimInt>(mut a: T, mut b: T) -> T {
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
impl<T: PrimInt> From<T> for RNum<T> {
    fn from(n: T) -> Self { Self::new_raw(n, T::one()) }
}

use std::fmt::{Debug, Display, Formatter, Result as fmtResult};
/*#[cfg(feature = "debug")] */impl<T: PrimInt + Display> Debug for RNum<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmtResult { Display::fmt(self, f) }
}

impl<T: PrimInt + Display> Display for RNum<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmtResult {
        let srn = self;     //srn.reduce();
        if  srn.1.is_zero() { write!(f, r"(INV)")? } else {
            let braket = srn.0 * srn.1 < T::zero() || !srn.1.is_one();
            if  braket { write!(f, r"(")? }     //write!(f, r"{}", srn.0)?;
            write!(f, "{:>width$}", srn.0, width = f.width().unwrap_or(0))?;
            if  !srn.1.is_one() { write!(f, r"/{}", srn.1)? }
            if  braket { write!(f, r")")? }
        }   Ok(())  // XXX: dynamic padding support
    }
}

use core::str::FromStr;
impl<T: PrimInt + FromStr> FromStr for RNum<T> {
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.splitn(2, '/');
        let n = s.next().unwrap_or("" ).parse::<T>()?;
        let d = s.next().unwrap_or("1").parse::<T>()?;
        Ok(Self::new_raw(n, d))
    }   type Err = T::Err;
}

use core::cmp::{Eq, Ord, Ordering, PartialEq};
impl<T: PrimInt> Ord for RNum<T> {
    fn cmp(&self, rhs: &Self) -> Ordering { (self.0 * rhs.1).cmp(&(self.1 * rhs.0))
        //let ord = (self.0 * rhs.1).cmp(&(self.1 * rhs.0));  // XXX:
        //if (T::zero() < self.1) ^ (T::zero() < rhs.1) { ord.reverse() } else { ord }
    }
}

impl<T: PrimInt> PartialOrd for RNum<T> {
    #[inline] fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        /*(self.1 == T::zero() || rhs.1 == T::zero()).then_some(..)*/Some(self.cmp(rhs))
        //(self.0 * rhs.1).partial_cmp(&(self.1 * rhs.0))
    }
}

impl<T: PrimInt>  Eq for RNum<T> { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl<T: PrimInt> PartialEq  for RNum<T> {
    #[inline] fn eq(&self, rhs: &Self) -> bool { self.cmp(rhs) == Ordering::Equal }
}

/* impl<T: PrimInt> std::ops::Add for RNum<T> { //std::ops::{Add, Sub, Mul, Div}
    fn add(self, rhs: Self) -> Self::Output { todo!() }     type Output = Self;
} */

#[derive(/*Debug, */Clone, Copy, PartialEq, Eq)]
#[repr(u8/*, C*/)] enum Oper { Num, Add = b'+', Sub = b'-', Mul = b'*', Div = b'/', }
//type Oper = char; // type alias   // XXX: '*' -> '×' ('\xD7'), '/' -> '÷' ('\xF7')
//struct Oper(u8);  // newtype idiom

//#[derive(Debug)] enum Value { None, Valid, R(Rational) }
//type Value = Option<Rational>;

use std::rc::Rc;
type RcExpr = Rc<Expr>;   //*const Expr;
//#[derive(/*Debug, */PartialEq, Eq, PartialOrd, Ord)] //#[repr(packed(4)/*, align(4)*/)]
pub struct Expr { v: Rational, m: Option<(RcExpr, RcExpr, Oper)> }
//pub struct Expr { v: Rational, a: *const Expr, b: *const Expr, op: Oper }  // XXX:
// a & b refer to left & right operands

impl Expr {     //#![allow(dead_code)]
    #[inline] pub fn value(&self) -> &Rational { &self.v }
    fn eval(a: Expr, b: Expr, ops: char) -> Result<Self, String> {
        let (an, ad) = (a.v.numer(), a.v.denom());
        let (bn, bd) = (b.v.numer(), b.v.denom());

        let op: Oper;   let v = match ops {
            '+' => { op = Oper::Add; Rational::new_raw(an * bd + ad * bn, ad * bd) }
            '-' => { op = Oper::Sub; Rational::new_raw(an * bd - ad * bn, ad * bd) }
            '*' | '×' => { op = Oper::Mul; Rational::new_raw(an * bn, ad * bd) }
            '/' | '÷' => { op = Oper::Div;  //assert_ne!(bn, &0);
                if *bn == 0 { return Err("Invalid divisor".to_owned()) }
                Rational::new_raw(an * bd, ad * bn)
            }   _ => return Err("Invalid operator".to_owned())  //unreachable!()
        };  Ok(Self { v, m: Some((Rc::new(a), Rc::new(b), op)) })
    }

    fn fmt(&self, f: &mut Formatter<'_>, dbg: bool, mdu: bool) -> fmtResult {
        if let Some((a, b, op)) = &self.m {
            let op = *op;   use Oper::*;
            let bracket = if dbg { a.m.is_some() } else {
                matches!(a.op(), Add | Sub) && matches!(op, Mul | Div)
            };  if bracket { write!(f, r"({a})")? } else { write!(f, r"{a}")? }

            if !mdu { write!(f, r"{}", op as u8 as char)? } else {  // XXX: add space around?
                write!(f, r" {} ", match op { Mul => '×', Div => '÷', _ => op as u8 as char })?
            }

            let bracket = if dbg { b.m.is_some() } else {
                op == Div && matches!(b.op(), Mul | Div) ||
                op != Add && matches!(b.op(), Add | Sub)
            };  if bracket { write!(f, r"({b})")? } else { write!(f, r"{b}")? }
        } else { write!(f, r"{}", self.v)? }    Ok(())
    }

    #[inline] fn op(&self) -> Oper { //self.op
        if let Some((.., op)) = &self.m { *op } else { Oper::Num }
    }

    //#[inline] fn is_zero(&self) -> bool { self.v.numer() == &0 }
    //#[inline] fn is_one (&self) -> bool { self.v.numer() == self.v.denom() }
}

//impl Default for Expr {
//    fn default() -> Self { Self { v: Rational::new_raw(0, 0), m: None } }
//}

//impl Drop for Expr { fn drop(&mut self) { eprintln!(r"Dropping: {self}"); } }

impl From<Rational> for Expr {
    #[inline] fn from(rn: Rational) -> Self { Self { v: rn, m: None } }
}

#[cfg(feature = "debug")] impl Debug for Expr {
    #[inline] fn fmt(&self, f: &mut Formatter<'_>) -> fmtResult { self.fmt(f, true, false) }
}

impl Display for Expr {     #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmtResult { self.fmt(f, false, false) }
}

//impl std::error::Error for ExprError {}     // convertable to Box<dyn Error>
#[derive(pest_derive::Parser)] #[grammar = "arith_expr.pest"] struct ArithExpr;

/// ```
/// # use inrust::calc24::{Expr, Rational};
/// let es = "((0 + 1 * 2 + 3) * 1 * 2 - (4 / (5/-6) / 8 + 7) - 9 + 10)"; // = 23/5
/// assert!(es.parse::<Expr>().is_ok_and(|e| e.value() == &Rational::new_raw(23, 5)));
/// ```
impl FromStr for Expr {
    fn from_str(s: &str) -> Result<Self, Self::Err> {   use pest::Parser;
        fn build_expr_ast(pair: pest::iterators::Pair<Rule>) -> Result<Expr, String> {
            let mut ex = Err("None".to_owned());
            let mut op = None;

            for pair in pair.into_inner() {
                let rule = pair.as_rule();  match rule {
                    Rule::integer | Rule::expr | Rule::sum | Rule::product | Rule::value => {
                        let e = if rule == Rule::integer {
                            pair.as_str().parse::<Rational>()
                                .map_err(|err| err.to_string())?.into()
                        } else { build_expr_ast(pair)? };

                        ex = if let Ok(a) = ex {
                             if let Some(vop) = op { op = None;  Expr::eval(a, e, vop)
                             } else { Err("No operator".to_owned()) }
                        } else { Ok(e) }
                    }

                    Rule::add | Rule::sub | Rule::mul | Rule::div =>
                        op = pair.as_str().chars().next(),
                    Rule::WHITESPACE | Rule::EOI => continue,
                }
            }   ex
        }

        //pest::state::<Rule, _>(s, |s| Ok(s)).unwrap();    // XXX:
        build_expr_ast(ArithExpr::parse(Rule::expr, s).map_err(|err|
            err.to_string())?.next().ok_or_else(|| "Empty".to_string())?)
    }   type Err = String;
}

impl PartialOrd for Expr {
    #[inline] fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> { Some(self.cmp(rhs)) }
}

impl Ord for Expr {
    fn cmp(&self, rhs: &Self) -> Ordering {
        let ord = self.v.cmp(&rhs.v);
        if  ord != Ordering::Equal { return ord }

        match (&self.m, &rhs.m) {
            (Some((la, lb, lop)),
             Some((ra, rb, rop))) => {
                let ord = (*lop as u8).cmp(&(*rop as u8));
                if  ord != Ordering::Equal { return ord }
                let ord = la.cmp(ra);   // recursive
                if  ord != Ordering::Equal { return ord }   lb.cmp(rb)  // recursive
            }   (None, None) => Ordering::Equal, //_ => unreachable!(),
            (Some(_) , None) => Ordering::Greater, (None, Some(_)) => Ordering::Less,
        }
    }
}

/// ```
/// # use inrust::calc24::Expr;
/// let (a, b) = ("(1 + 2) * 3 / 4 - 5", "0");
/// let (a, b) = (a.parse::<Expr>(), b.parse::<Expr>());
/// assert!(a == a && b == b && a != b);
/// ```
impl  Eq for Expr { /*fn assert_receiver_is_total_eq(&self) { } */}
impl PartialEq for Expr {
    fn eq(&self, rhs: &Self) -> bool { //self.cmp(rhs) == Ordering::Equal
        match (&self.m, &rhs.m) {
            (None, None) => self.v == rhs.v,
            (Some((la, lop, lb)),
             Some((ra, rop, rb))) =>
                lop == rop && la == ra && lb == rb,  // recursive
            _ => false, //(None, Some(_)) | (Some(_), None) => false,
        }   //self.v == rhs.v
    }
}

use std::hash::{Hash, Hasher};
impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {  //self.to_string().hash(state); return;
        if let Some((a, b, op)) = &self.m {
            (*op as u8).hash(state);  a.hash(state);  b.hash(state);    // recursive
        } else { self.v.numer().hash(state); self.v.denom().hash(state); }
    }
}

/// ```
/// # use inrust::calc24::hash_combine;
/// assert_eq!(hash_combine(0x12345678, 0x98765432), 0xda64d7f1);
/// ```
#[allow(dead_code)] pub fn hash_combine(lhs: u32, rhs: u32) -> u32 {    // u64
    //lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2))
    lhs ^ (rhs.wrapping_add(0x9e3779b9).wrapping_add(lhs.wrapping_shl(6))
                                       .wrapping_add(lhs.wrapping_shr(2)))
}

// context-free grammar, Chomsky type 2/3, Kleen Algebra
// TODO: Zero, One, Rule, Sum, Product, Star, Cross, ...

// several pruning rules to find inequivalent/unique expressions only
fn form_compose<F>(a: &RcExpr, b: &RcExpr, is_final: bool, ngoal: bool,
    mut new_expr: F) -> Option<()> where F: FnMut(Expr) -> Option<()> {
    #[cfg(feature = "debug")] eprintln!(r"({a:?}) ? ({b:?})");

    // XXX: check overflow and reduce?
    let (nmd, dmn, dmd) = (a.v.numer() * b.v.denom(),
               a.v.denom() * b.v.numer(), a.v.denom() * b.v.denom());
    // Commutativity (selecting a bias by lexicographical comparison)
    // ((A . B) . b) => (A . (B . b)), kept the right sub-tree only
    let (aop, bop) = (a.op(), b.op());   use Oper::*;

    #[inline] fn found_same(e: &Expr, v: &Rational, op: Oper) -> bool {
        if let Some((a, b, eop)) = &e.m {
            //(if a.m.is_none() { &a.v == v } else { found_same(a, v, op) } ||
            // if b.m.is_none() { &b.v == v } else { found_same(b, v, op) })
            *eop == op && (&a.v == v || &b.v == v ||
                found_same(a, v, op) || found_same(b, v, op))   // recursive
        } else { false }
    }

    struct  Cacher<T> where T: Fn() -> bool, { calc: T, v: Option<bool>, }
    impl<T> Cacher<T> where T: Fn() -> bool, {
        fn new(calc: T) -> Cacher<T> { Cacher { calc, v: None, } }

        fn get(&mut self) -> bool {
            match self.v {  Some(v) => v,
                None => { let v = (self.calc)(); self.v = Some(v); v }
            }   // memoization, lazy evaluation
        }
    }

    let mut subl_cmp = Cacher::new(||
        if let Some((ba, ..)) = &b.m { ba.cmp(a) == Ordering::Less } else { false });

    // ((A / B) * b) => ((A * b) / B) if b != 1,
    // (a * (A / B)) => ((a * A) / B) if a != 1, (1 * x) => kept in the final only,
    /* (a * (A * B)) => (A * (a * B)) if A  < a */  let op = Mul;
    if !(aop == op || (aop == Div   && !b.v.is_one())  || (Div == bop && !a.v.is_one()) ||
        (!is_final && (a.v.is_one()  || b.v.is_one() )) || (op == bop && subl_cmp.get())) {
        new_expr(Expr { v: Rational::new_raw(a.v.numer() * b.v.numer(), dmd),
                        m: Some((a.clone(), b.clone(), op)) })?;
    }

    // ((A - B) + b) => ((A + b) - B) if b != 0,
    // (a + (A - B)) => ((a + A) - B) if a != 0, (0 + x) => kept in the final only,
    /* (a + (A + B)) => (A + (a + B)) if A  < a */  let op = Add;
    if !(aop == op || (aop == Sub   && !b.v.is_zero()) || (Sub == bop && !a.v.is_zero()) ||
        (!is_final && (a.v.is_zero() || b.v.is_zero())) || (op == bop && subl_cmp.get())) {
        new_expr(Expr { v: Rational::new_raw(nmd + dmn, dmd),
                        m: Some((a.clone(), b.clone(), op)) })?;
    }

    // (b - (B - A)) => ((b + A) - B), (x - 0) => (0 + x),
    /* ((A + x) - x) => kept in the final only */   let op = Sub;
    if !(aop == op || op == bop || a.v.is_zero() ||
        (!is_final && found_same(b, &a.v, Add))) {  if ngoal {
            new_expr(Expr { v: Rational::new_raw(nmd - dmn, dmd),
                            m: Some((a.clone(), b.clone(), op)) })?;
        } else {    // Asymmetric select subtraction by judging sign of the target/goal
            new_expr(Expr { v: Rational::new_raw(dmn - nmd, dmd),
                            m: Some((b.clone(), a.clone(), op)) })?;
        }
    }

    // (a / (A / B)) => ((a * B) / A), (x / 1) => (1 * x), (0 / x) => (0 * x),
    /* ((x * B) / x) => ((x + B) - x) */    let op = Div;
    if !(aop == op || op == bop) {
        if !(dmn == 0 || b.v.is_one() || a.v.is_zero() || found_same(a, &b.v, Mul)) {
            new_expr(Expr { v: Rational::new_raw(nmd, dmn),
                            m: Some((a.clone(), b.clone(), op)) })?;
        }

        if !(nmd == 0 || a.v.is_one() || b.v.is_zero() ||   // order mattered only if a != b
             nmd == dmn || found_same(b, &a.v, Mul)) {
            new_expr(Expr { v: Rational::new_raw(dmn, nmd),
                            m: Some((b.clone(), a.clone(), op)) })?;
        }
    }   Some(())
}

//use crate::list::List;
//use std::collections::LinkedList as List;   // both seems lower performance than Vec

#[cfg(feature = "ahash")] use ahash::{AHashSet as HashSet, AHasher as DefaultHasher};
#[cfg(not(feature = "ahash"))] use std::collections::{HashSet, hash_map::DefaultHasher};
// 30+% faster than std version, refer to https://nnethercote.github.io/perf-book/hashing.html

// traversely top-down divide the number set by dynamic programming
fn calc24_dynprog <F>(goal: &Rational, nums: &[RcExpr], ngoal: bool,
    mut each_found: F) -> Option<()> where F: FnMut(Expr) -> Option<()> {
    use core::cell::RefCell;       // for interior mutability, shared ownership
    let n = nums.len();     let psn = 1 << n; // size of powerset
    let mut vexp = vec![RefCell::new(vec![]); psn];
    if 1 < n { for i in 0..n { vexp[1 << i].get_mut().push(nums[i].clone()) } }

    let mut hv = Vec::with_capacity(psn - 1);   // psn - 2
    let get_hash = |x| {
        let mut hasher = DefaultHasher::default();
        //nums.iter().enumerate().for_each(|(i, e)| if (1 << i) & x != 0 {
        //    #[cfg(feature = "debug")] eprint!(r"{e} "); e.hash(&mut hasher) });

        let (mut n, mut i) = (1, 0);
        while n <= x {  if n & x != 0 {  nums[i].hash(&mut hasher);
                #[cfg(feature = "debug")] eprint!(r"{} ", nums[i]);
            }   n <<= 1;    i += 1;
        }   hasher.finish()
    };

    for x in 3..psn {   // 0 is a placeholder, 1~2 both included in previous [1 << i]
        if x & (x - 1) == 0 { continue }    // skip when (x == 2^n)
        let is_final = x == psn - 1;

        let mut exps = vexp[x].borrow_mut();
        for i in 1..(x+1)/2 {   // exclude empty & full set pair
            if x & i != i { continue }  // split by bits, '0's vs '1's
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
                es1.iter().skip(if h1 != h0 { 0 } else { i }).try_for_each(|b| {
                    // skip duplicates by symmetric subset combinations, e.g.: [5 3], [5 3]
                    let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
                    form_compose(a, b, is_final, ngoal, |e| {
                        if !is_final { exps.push(Rc::new(e)) }
                        else if e.v == *goal { each_found(e)? }    Some(())
                    })
                }))?;
        }   hv.clear();
    }   Some(())

    //vexp.pop().unwrap().into_inner() //vexp[psn - 1].take()
}

//#[async_recursion::async_recursion(?Send)] async
// traversely top-down divide the number set straightforward
fn calc24_splitset<F>(goal: &Rational, nums: &[RcExpr], ngoal: bool,
    each_found: &mut F) -> Vec<RcExpr> where F: FnMut(Expr) -> Option<()> {
    let (psn, mut exps) = (1 << nums.len(), vec![]);
    const IR: Rational = Rational::new_raw(0, 0);
    let is_final = !core::ptr::eq(goal, &IR);
    //if nums.len() < 2 { return nums.to_vec() }

    let mut hv = Vec::with_capacity(psn - 1);   // psn - 2
    let get_hash = |ns: &[_]| {
        let mut hasher = DefaultHasher::default();
        ns.hash(&mut hasher);   hasher.finish()
    };

    //let mut used = HashSet::default();
    //let all_unique = nums.iter().all(|e| used.insert(e));

    for x in 1..psn/2 { // exclude empty & full set pair
        let (mut ns0, mut ns1) = (vec![], vec![]);
        nums.iter().enumerate().for_each(|(i, e)|   // split by bit 0/1 in 'x'
            if (1 << i) & x != 0 { ns0.push(e.clone()) } else { ns1.push(e.clone()) });
        #[cfg(feature = "debug")] eprint!(r"{:?} ~ {:?} ", ns0, ns1);

        //if !all_unique {  // skip duplicate (ns0, ns1)
        let h0 = get_hash(&ns0);    if hv.contains(&h0) {
            #[cfg(feature = "debug")] eprintln!(r"dup"); continue
        } else { hv.push(h0) }

        let h1 = get_hash(&ns1);    if h1 != h0 {   if hv.contains(&h1) {
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
            ns1.iter().skip(if h1 != h0 { 0 } else { i }).try_for_each(|b| {
                // skip duplicates by symmetric subset combinations, e.g.: [5 3], [5 3]
                let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
                form_compose(a, b, is_final, ngoal, |e| {
                    if !is_final { exps.push(Rc::new(e)) }
                    else if e.v == *goal { each_found(e)? }    Some(())
                })
            })).is_none() { break }
    }   exps
}

// traversely construct expr. inplace bottom-up from numbers
fn calc24_inplace<F>(goal: &Rational, nums: &mut [RcExpr], ngoal: bool,
    each_found: &mut F) -> Option<()> where F: FnMut(Expr) -> Option<()> {
    let n = nums.len();
    let mut hv = Vec::with_capacity(n * n / 2);     // n * (n - 1) / 2

    // XXX: skip duplicates over different combination order, as well in symmetric style
    for j in 1..n {     let b = nums[j].clone();
        nums[j] = nums[n - 1].clone();  // the last j is n - 1
        for i in 0..j { let a = nums[i].clone();

            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // unify duplicate numbers
            if hv.contains(&h0) { continue } else { hv.push(h0) }

            // XXX: compare expr. rather than value to avoid more duplicate combinations
            let (ta, tb) = if b < a { (&b, &a) } else { (&a, &b) };
            form_compose(ta, tb, n == 2, ngoal, |e| {
                if n == 2 { if e.v == *goal { each_found(e)? } } else { nums[i] = Rc::new(e);
                    calc24_inplace(goal, &mut nums[..n-1], ngoal, each_found)?;
                }   Some(())
            })?; nums[i] = a;
        }        nums[j] = b;
    }   Some(())
}

// traversely construct expr. bottom-up from numbers straightforward
fn calc24_construct<F>(goal: &Rational, nums: &[RcExpr], ngoal: bool,
    each_found: &mut F, minj: usize) -> Option<()> where F: FnMut(Expr) -> Option<()> {
    let n = nums.len();
    let mut hv = Vec::with_capacity(n * n / 2);     // n * (n - 1) / 2

    // XXX: skip duplicates in symmetric style, e.g.: [1 1 5 5]
    //nums.iter().tuple_combinations::<(_, _)>().for_each(|(a, b)| { });
    nums.iter().enumerate().skip(minj).try_for_each(|(j, b)|
        nums.iter().take(j).try_for_each(|a| {

            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();   // unify duplicate numbers
            if hv.contains(&h0) { return Some(()) } else { hv.push(h0) }

            use core::ptr::eq as ptr_eq;    // Rc::ptr_eq   // drop sub-expr.
            let mut nums = nums.iter().filter(|&e|
                !ptr_eq(e, a) && !ptr_eq(e, b)).cloned().collect::<Vec<_>>();

            let (a, b) = if b.v < a.v { (b, a) } else { (a, b) };
            form_compose(a, b, nums.is_empty(), ngoal, |e| {
                if  nums.is_empty() { if e.v == *goal { each_found(e)? } } else {
                    nums.push(Rc::new(e));
                    calc24_construct(goal, &nums, ngoal, each_found, j - 1)?;
                    nums.pop();
                }   Some(())
            })}))
}

#[derive(Debug, Clone, Copy)] #[repr(u8/*, C*/)]
pub enum Calc24Algo { DynProg, SplitSet, Inplace, Construct, }
pub  use Calc24Algo::*;

// view dhat-heap.json in https://nnethercote.github.io/dh_view/dh_view.html
#[cfg(feature = "dhat-heap")] #[global_allocator] static ALLOC: dhat::Alloc = dhat::Alloc;
// cargo run --features dhat-heap   // https://docs.rs/dhat/latest/dhat/

#[inline] pub fn calc24_coll (goal: &Rational, nums: &[Rational],
    algo: Calc24Algo) -> Vec<String> {
    let mut exps = vec![];
    calc24_algo(goal, nums, algo, |e| {
        exps.push(e.to_string());   Some(()) });    exps
}

/// ```
/// # use inrust::calc24::*;
/// let nums = (1..=4).map(|n| n.into()).collect::<Vec<_>>();
/// assert_eq!(calc24_first(&24.into(), &nums, DynProg), "1*2*3*4".to_owned());
/// assert_eq!(calc24_print(&24.into(), &nums, DynProg), 3);
/// ```
#[inline] pub fn calc24_first(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> String {
    let mut sexp = String::new();
    calc24_algo(goal, nums, algo, |e| {
        sexp = e.to_string();   None });    sexp
}

#[inline] pub fn calc24_print(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> usize {
    let mut cnt = 0;
    calc24_algo(goal, nums, algo, |e| {
        println!(r"{}", Paint::green(e)); cnt += 1; Some(()) });    cnt
}

#[inline] pub fn calc24_algo<F>(goal: &Rational, nums: &[Rational], algo: Calc24Algo,
    mut each_found: F) where F: FnMut(Expr) -> Option<()> {
    if 1 == nums.len() { return if nums[0] == *goal { each_found(nums[0].into()); } }
    #[cfg(feature = "dhat-heap")] let _profiler = dhat::Profiler::new_heap();
    debug_assert!(nums.len() < core::mem::size_of::<usize>() * 8,
        r"Required by algo. DynProg & SplitSet");

    let ngoal = goal.is_negative(); //goal < &0.into();
    let mut nums = nums.iter().map(|&rn|
        Rc::new(Expr::from(rn))).collect::<Vec<_>>();
    nums.sort_unstable_by(|a, b| a.v.cmp(&b.v));
    // so don't needs order-independent hasher  //quicksort(nums, |a, b| a.v < b.v);    // XXX:

    let mut hexp = HashSet::new();
    let mut hash_unify = |e: Expr| {
        let mut hasher = DefaultHasher::default();  e.hash(&mut hasher);
        if hexp.insert(hasher.finish()) { each_found(e) } else { Some(()) }
    };

    match algo {    // TODO: output/count all possible expr. forms?
        DynProg   => { calc24_dynprog  (goal, &nums, ngoal, &mut each_found); }
        SplitSet  => { calc24_splitset (goal, &nums, ngoal, &mut each_found);
            //futures::executor::block_on(calc24_splitset(goal, &nums, ngoal, &mut each_found));
        }
        Inplace   => { calc24_inplace  (goal, &mut nums, ngoal, &mut hash_unify); }
        Construct => {
            calc24_construct(goal, &nums, ngoal, &mut hash_unify, 1);
        }
    }
}

#[allow(dead_code)] #[inline] fn deck_traverse<F>(min: i32, max: i32, cnt: u8, mrpt: u8,
    nums: &mut Vec<i32>, solve: &mut F) where F: FnMut(&[i32]) {
    (min..=max).for_each(|x| {  let len = nums.len() as u8;
        if mrpt - 1 < len && nums.iter().fold(0u8, |acc, &n|
            if n == x { acc + 1 } else { acc }) == mrpt { return } else { nums.push(x) }

        if len + 1 == cnt { solve(nums); } else {
            deck_traverse(x, max, cnt, mrpt, nums, solve);
        }   nums.pop();
    });
}

/// ```
/// # use inrust::calc24::*;
/// // require absolute/complete path since Doc-tests run in a separate process
/// let (goal, silent, min) = (24.into(), true, 1);
/// assert_eq!(game24_solvable(&goal, min, 10, 5, false, DynProg), (37, 1955, 0));
/// //assert_eq!(game24_solvable(&goal, min, 13, 5, silent, DynProg), (81, 6094, 0));
/// //assert_eq!(game24_solvable(&goal, min, 10, 6, silent, DynProg), (3,  4902, 0));
/// //assert_eq!(game24_solvable(&goal, min, 13, 6, silent, DynProg), (3, 18392, 0));
/// //assert_eq!(game24_solvable(&goal, min, 10, 7, silent, DynProg), (0, 10890, 0));
/// assert_eq!(game24_solvable(&goal, min, 10, 4, false, DynProg), (149, 566, 1343));
/// for algo in [ DynProg, SplitSet, Inplace, Construct ] {
///     assert_eq!(game24_solvable(&goal, min, 13, 4, silent, algo), (458, 1362, 3017),
///         r"failed on algo-{algo:?}");
/// }
/// ```
pub fn game24_solvable(goal: &Rational, min: i32, max: i32, cnt: u8,
    silent: bool, algo: Calc24Algo) -> (u16, u16, u32) {
    let mut rcnt = (0, 0, 0);

    if 4 != cnt {    let mut nums = vec![];
        deck_traverse(min, max, cnt, 4, &mut nums, &mut |nums: &[i32]| {
            let nums = nums.iter().map(|&n| n.into()).collect::<Vec<_>>();
            let res = calc24_first(goal, &nums, algo);

            if  res.is_empty() { rcnt.0 += 1; } else {  rcnt.1 += 1;    if silent { return }
                nums.into_iter().for_each(|rn|
                    print!(r" {:2}", Paint::cyan(rn.numer())));     println!();
            }
        });         if silent { return rcnt }

        eprintln!(r"{} / {} sets solvable.", Paint::green(rcnt.1),
            rcnt.0 + rcnt.1);   return rcnt
    }

    //let mut pks = (min..=max).collect::<Vec<_>>();
    //let mut rng = rand::thread_rng();
    //use rand::seq::SliceRandom;
    //pks.shuffle(&mut rng);

    // C^52_4 = 270725, C^(13+4-1)_4 = 1820
    (min..=max).for_each(|a| (a..=max).for_each(|b|   // fast specialize
      (b..=max).for_each(|c| (c..=max).for_each(|d| {
        let nums = [a, b, c, d].iter().map(|&n|
            n.into()).collect::<Vec<_>>();     // XXX: n -> pks[n - 1]

        let exps = calc24_coll(goal, &nums, algo);
        if  exps.is_empty() { rcnt.0 += 1; } else {     rcnt.1 += 1;
            rcnt.2 += exps.len() as u32;

            if silent { return }    //nums.shuffle(&mut rng);
            nums.into_iter().for_each(|rn|
                print!(r" {:2}", Paint::cyan(rn.numer())));     print!(r":");
            exps.into_iter().for_each(|e|   // output solutions
                print!(r" {}", Paint::green(e)));               println!();
        }
    }))));

    if silent { return rcnt }
    eprintln!(r"{} / {} sets with {} solutions.", Paint::green(rcnt.1),
        rcnt.0 + rcnt.1, Paint::magenta(rcnt.2));   rcnt
}

#[cfg_attr(coverage_nightly, no_coverage)] //#[cfg(not(tarpaulin_include))]
pub fn game24_cards(goal: &Rational, cnt: u8, algo: Calc24Algo) {
    let court  = [ "T", "J", "Q", "K" ]; // ♠Spade, ♡Heart, ♢Diamond, ♣Club
    let suits = [ Color::Blue, Color::Red, Color::Magenta, Color::Cyan ];
    let (mut rng, mut spos, mut batch)= (rand::thread_rng(), 0, 0);
    let mut deck = (0..13*4u8).collect::<Vec<_>>();

    // https://en.wikipedia.org/wiki/Playing_cards_in_Unicode
    // https://www.me.uk/cards/makeadeck.cgi, https://github.com/revk/SVG-playing-cards
    println!(r"{}, target {goal}", Paint::new(  // https://github.com/htdebeer/SVG-cards
        r"24-game with cards (T=10, J=11, Q=12, K=13, A=1)").dimmed());

    loop {  use rand::seq::SliceRandom;
        if deck.len() < (spos + cnt) as usize { spos = 0; }
        if spos == 0 { deck.shuffle(&mut rng); }

        let nums = deck[spos as usize..].partial_shuffle(&mut rng,
            cnt as usize).0.iter().map(
            #[cfg_attr(coverage_nightly, no_coverage)] |num| {  // cards deck dealer
            let (num, sid) = ((num % 13) + 1, (num / 13)/* % 4 */);
            //let (sid, num) = num.div_rem(&13);  let num = num + 1;  //sid %= 4;

            print!(r" {}", Paint::new(match num { 1 => "A".to_owned(),    // String::from
                2..=9 => num.to_string(), _ => court[num as usize - 10].to_owned() })
                .bold().bg(suits[sid as usize]));   (num as i32).into()
        }).collect::<Vec<_>>();     spos += cnt;    print!(r": ");

        let exps = calc24_coll(goal, &nums, algo);
        if  exps.is_empty() { println!(r"{}", Paint::yellow("None")); continue }

        if 0 < batch {
            exps.iter().for_each(|e| print!(r" {}", Paint::black(e)));
            println!();     batch -= 1;     continue
        }

        loop {  use std::io::Write;     let mut es = String::new();
            std::io::stdout().flush().expect(r"Failed to flush!"); //.unwrap();
            std::io::stdin().read_line(&mut es).expect(r"Failed to read!");

            let es = es.trim_end();
            if  es.eq_ignore_ascii_case("N") || es.eq("?") {
                print!(r"{}", Paint::new(r"Solution:").dimmed());
                exps.iter().for_each(|e| print!(r" {}", Paint::green(e)));
                if let Ok(n) = es[1..].parse::<u16>() { batch = n; }
                println!();     break
            }

            if  es.eq_ignore_ascii_case("quit") { return }
            if  es.parse::<Expr>().is_ok_and(|e| e.value() == goal) {
                print!(r"{} ", Paint::new(r"Correct!").bg(Color::Green));
                exps.iter().for_each(|e| print!(r" {}", Paint::green(e)));
                println!();
            } else { print!(r"{} ", Paint::new(r"Tryagain:").dimmed()); }
        }       println!();
    }
}

#[cfg_attr(coverage_nightly, no_coverage)] //#[cfg(not(tarpaulin_include))]
pub fn game24_cli() {
    #[cfg_attr(coverage_nightly, no_coverage)]  // XXX:
    fn game24_helper<I, S>(goal: &Rational, nums: I, algo: Calc24Algo)
        where I: Iterator<Item = S>, S: AsRef<str> {    // XXX: use closure instead?
        let nums = nums.filter_map(
            #[cfg_attr(coverage_nightly, no_coverage)]  // XXX:
            |s| match s.as_ref().parse::<Rational>() {
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
    let  mut nums = std::env::args().peekable();
    nums.next();    // skip the executable path

    let mut want_exit = false;
    if  let Some(opt) = nums.peek() {
        let opt = opt.clone();
        if  opt.eq("-A") {   nums.next();
            if let Some(gs) = nums.next() { match gs.parse::<u32>() {
                Ok(n) => algo = match n {
                    1 => SplitSet, 2 => Inplace, 3 => Construct, _ => DynProg,
                },
                Err(e) => eprintln!(r"Error parsing ALGO: {}", Paint::red(e)),
            } } else { eprintln!(r"Lack parameter for ALGO!") }
        }
    }

    if  let Some(opt) = nums.peek() {
        let opt = opt.clone();
        if  opt.eq_ignore_ascii_case("-g") {
            if opt == "-G" { want_exit = true }
            nums.next();

            if let Some(gs) = nums.next() { match gs.parse::<Rational>() {
                Ok(_goal) => goal = _goal,
                Err(e) => eprintln!(r"Error parsing GOAL: {}", Paint::red(e)),
            } } else { eprintln!(r"Lack parameter for GOAL!") }

            if nums.len() < 1 {
                if goal == 0.into() { (0..=100).for_each(|n| println!("{n} {}",
                     game24_solvable(&n.into(), 1, 13, 4, true, algo).1));
                } else { // solvable for 4 cards dealed from a deck, traverse 0..=100 as target
                     game24_solvable(&goal, 1, 13, 4, false, algo);
                }
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
        let mut nums = nums.split_ascii_whitespace().peekable();
        //nums.trim().split(' ').filter(|s| !s.is_empty()).peekable();

        if let Some(&first) = nums.peek() {
            if first.starts_with(['g', 'G']) {
                match first[1..].parse::<Rational>() {
                    Ok(_goal) => {  goal = _goal;
                        println!(r"### Reset GOAL to {} ###", Paint::magenta(&goal).bold());
                    }
                    Err(e) => eprintln!(r"Error parsing GOAL: {}", Paint::red(e)),
                }   nums.next();
            } else if first.eq_ignore_ascii_case("poker") ||
                      first.eq_ignore_ascii_case("cards") {
                game24_cards(&goal, 4, algo);   nums.next();    continue;
            } else if first.eq_ignore_ascii_case("quit") { break }
        }       game24_helper(&goal, nums, algo);
    }
}

#[cfg(feature = "cc")] #[inline]
pub fn calc24_cffi(goal: &Rational, nums: &[Rational], algo: Calc24Algo) -> usize {
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
        algo, goal: *goal, //unsafe { core::mem::transmute(goal) },
        nums: nums.as_ptr(), ncnt: nums.len(),
        ecnt: 0,  exps: core::ptr::null_mut(),
    };

    //core::ptr::addr_of_mut!(calc24);
    debug_assert!(core::mem::size_of::<Rational>() == 8);
    //eprintln!("algo: {:?}, goal: {}, ncnt: {}", calc24.algo, calc24.goal, calc24.ncnt);

    extern "C" { fn calc24_cffi(calc24: *mut Calc24IO); }
    unsafe {   calc24_cffi(&mut calc24);  // XXX:

        if 0 < calc24.ecnt && !calc24.exps.is_null() {
            let _exps = core::slice::from_raw_parts(calc24.exps,
                calc24.ecnt).iter().map(|es| std::ffi::CStr::
                from_ptr(*es).to_str().unwrap()).collect::<Vec<_>>();
        }
    }   calc24.ecnt
}

#[cfg(feature = "cxx")] #[cxx::bridge] mod ffi_cxx {    // TODO: not works yet
    struct Rational { n: i32, d: i32 }
    #[repr(u8)] enum Oper { Num, Add = b'+', Sub = b'-', Mul = b'*', Div = b'/', }
    struct Expr { v: Rational, a: SharedPtr<Expr>, b: SharedPtr<Expr>, op: Oper }
    #[repr(u8)] enum Calc24Algo { DynProg, SplitSet, Inplace, Construct }

    extern "Rust" { }

    unsafe extern "C++" {   include!("calc24.h");
        fn calc24_coll(goal: &Rational, nums: &CxxVector<Rational>,
            algo: Calc24Algo) -> CxxVector<CxxString>;
    }
}

//}

#[cfg(test)] mod tests {    use super::*;   // unit test
    // Need to import items from parent module, to access non-public members.

    #[test] fn parse_disp_rn() {
        let cases = [
            (RNum::from(0), "0"), (RNum::new_raw(1, 2), "(1/2)"),
            (RNum::from(1), "1"), (RNum::from(-1), "(-1)"),
        ];

        cases.iter().for_each(|it| {
            assert_eq!(it.0.to_string(), it.1, r"display {} != {}",
                Paint::red(&it.0), Paint::cyan(&it.1));
            assert!(it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<RNum<i32>>().is_ok_and(|v| v == it.0),
                r"parsing {} != {}", Paint::red(&it.1), Paint::cyan(&it.0));
        });
    }

    #[test] fn reduce_rn() {
        let cases = [
            (RNum::new(-1, -1), RNum::new_raw( 1, 1)),
            (RNum::new(-4,  2), RNum::new_raw(-2, 1)),
            (RNum::new( 6, -2), RNum::new_raw(-3, 1)),
            (RNum::new( 3,  2), RNum::new_raw( 3, 2)),
            (RNum::new( 0,  2), RNum::new_raw( 0, 1)),
        ];

        cases.into_iter().for_each(|(a, b)| {
            assert!(a.numer() == b.numer() && a.denom() == b.denom(),
                "simplified rational: {a}");
        });
    }

    #[test] fn solve24() {
        let cases = [
            ( 24, vec![  ], vec![], 0),
            ( 24, vec![ 0], vec![], 0),
            ( 24, vec![24], vec!["24"], 0),
            ( 24, vec![ 8, 8, 8, 8], vec![], 0),
            ( 24, vec![ 1, 2, 4,12], vec![], 5),
            ( 24, vec![ 2, 4, 4,12], vec![], 5),
            ( -2, vec![ 1, 2, 3, 4], vec![], 11),
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
            let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();
            let goal = goal.into();

            #[cfg(feature = "cc")] let assert_closure_c = |algo| {
                    let elen = calc24_cffi(&goal, &nums, algo);
                    println!(r"  {} solutions by algo-Cxx{:?}",
                        Paint::green(elen), Paint::green(algo));
                    assert!(elen == cnt, r"Unexpect count by algo-Cxx{:?}: {} != {}",
                        Paint::magenta(algo), Paint::red(elen), Paint::cyan(cnt));
            };

            let assert_closure = |algo| {
                let exps = calc24_coll(&goal, &nums, algo);

                exps.iter().for_each(|e| {
                    //eprintln!(r"  {}", Paint::green(e));
                    if res.is_empty() { return }
                    assert!(res.contains(&e.to_string().as_str()),
                         r"Unexpect expr. by algo-{:?}: {}", Paint::magenta(algo), Paint::red(e));
                });

                println!(r"  {} solutions by algo-{:?}",
                    Paint::green(exps.len()), Paint::green(algo));
                assert!(exps.len() == cnt, r"Unexpect count by algo-{:?}: {} != {}",
                    Paint::magenta(algo), Paint::red(exps.len()), Paint::cyan(cnt));
            };

            for algo in [ DynProg, SplitSet, Inplace, Construct ] {
                #[cfg(feature = "cc")] assert_closure_c(algo);
                assert_closure(algo);
            }

            #[cfg(feature = "cxx")] {
                use cxx::{/*CxxVector, */memory::SharedPtr};
                impl From<Expr> for ffi_cxx::Expr {
                    fn from(e: Expr) -> Self { Self { v: unsafe { core::mem::transmute(e.v) },
                        op: ffi_cxx::Oper::Num, a: SharedPtr::null(), b: SharedPtr::null() }
                    }
                }

                let goal: Rational = unsafe { core::mem::transmute(goal) };
                let exps = ffi_cxx::calc24_coll(&goal, &nums, DynProg);     // FIXME:
            }
        });
    }

    #[test] fn test_deck_traverse() {   // for non-public function
        let (mut nums, mut cnt) = (vec![], 0);
        deck_traverse(1, 13, 5, 4, &mut nums, &mut |_| cnt += 1);
        assert_eq!(cnt,  6175);     cnt = 0;
        deck_traverse(1, 10, 6, 4, &mut nums, &mut |_| cnt += 1);
        assert_eq!(cnt,  4905);     cnt = 0;
        deck_traverse(1, 13, 6, 4, &mut nums, &mut |_| cnt += 1);
        assert_eq!(cnt, 18395);     cnt = 0;
        deck_traverse(1, 10, 7, 4, &mut nums, &mut |_| cnt += 1);
        assert_eq!(cnt, 10890);     //cnt = 0;
    }

    #[cfg(feature = "cc")] #[test] fn solve24_c() {
        /*#[link(name = "calc24")] */extern "C" { #[allow(dead_code)] fn test_24calc(); }
        unsafe { test_24calc(); }
    }

    #[cfg_attr(coverage_nightly, no_coverage)] //#[cfg(not(tarpaulin_include))]
     #[ignore] /*#[bench] */#[test] fn solve24_random() {
        let (cnt, mut total_time) = (50, std::time::Duration::from_millis(0));
        for _ in 0..cnt {   use rand::{Rng, distributions::Uniform};
            let mut rng = rand::thread_rng();
            let dst = Uniform::new(1, 20);

            let (goal, nums) = (rng.sample(dst),
                rng.sample_iter(dst).take(6).collect::<Vec<_>>());
            println!(r"Compute {:2} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));

            let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();
            let (goal, now) = (goal.into(), std::time::Instant::now());
            calc24_coll(&goal, &nums, DynProg); // XXX: other algo?
            total_time += now.elapsed();
        }

        println!(r"Totally {}s for {} iterations.",
            Paint::magenta(total_time.as_millis() as f32 / 1000.0), Paint::magenta(cnt));
        assert!(total_time.as_secs() < 8);
    }

    // cargo +nightly llvm-cov --include-ffi --doctests #--lcov --output-path lcov.info #nextest
    //      https://doc.rust-lang.org/stable/rustc/instrument-coverage.html
    //      https://github.com/taiki-e/cargo-llvm-cov
    // cargo t --doc && cargo nextest r && cargo bench  #--no-capture
    // cargo test -- --nocapture && cargo bench     # https://nexte.st/index.html
}

// vim:sts=4 ts=8 sw=4 noet
