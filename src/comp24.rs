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
use std::{fmt::{Display,Formatter}, cmp::{Eq, /*Ord, */Ordering, PartialEq}};
use core::convert::From;

use yansi::Paint;   // Color, Style
//use itertools::Itertools;

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Clone, Copy)] #[repr(C)] pub struct Rational(pub i32, pub i32);
//#[repr(C)] pub struct Rational { n: i32, d: i32 }
//type Rational = (i32, i32);

#[derive(/*Debug, */Clone, Copy)] struct Oper(u8);    // newtype idiom
//#[repr(C, u8)] enum Oper { Num, Add(u8), Sub(u8), Mul(u8), Div(u8), }
//type Oper = char;   // type alias

//#[derive(Debug)] enum Value { None, Valid, R(Rational) }
//type Value = Option<Rational>;

pub use std::rc::Rc;
//#[derive(Debug)] //#[repr(packed(4)/*, align(4)*/)]
pub struct Expr { pub v: Rational, m: Option<(Rc<Expr>, Rc<Expr>)>, op: Oper }

/* impl std::ops::Add for Rational {    //std::ops::{Add, Sub, Mul, Div}
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { todo!() }
} */

impl From<i32> for Rational { fn from(n: i32) -> Self { Self(n, 1) } }

impl Display for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let srn = self; //.simplify();
        if  srn.1 == 0 { write!(f, r"(INV)")? } else {
            let braket = srn.0 * srn.1 < 0 || srn.1 != 1;
            if  braket { write!(f, r"(")? }     write!(f, r"{}", srn.0)?;
            if  srn.1 != 1 { write!(f, r"/{}", srn.1)? }
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

/* impl std::cmp::Ord for Rational {
    fn cmp(&self, rhs: &Self) -> Ordering { (self.0 * rhs.1).cmp(&(self.1 * rhs.0)) }
} */

impl PartialOrd for Rational {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        if self.1 == 0 || rhs.1 == 0 { None } else { //Some(self.cmp(rhs))
            (self.0 * rhs.1).partial_cmp(&(self.1 * rhs.0))
        }
    }
}

//impl Eq for Rational { /*fn assert_receiver_is_total_eq(&self) { }*/ }
impl PartialEq for Rational {
    fn eq(&self, rhs: &Self) -> bool {
        self.partial_cmp(rhs) == Some(Ordering::Equal)
        //self.1 != 0 && rhs.1 != 0 && self.0 * rhs.1 == self.1 * rhs.0
    }
}

impl Rational {
    #[allow(dead_code)] fn simplify(&self) -> Self {
        fn gcd(a: i32, b: i32) -> i32 { // Greatest Common Denominator
            let (mut m, mut n) = (a, b);
            while m != 0 {  // Use Euclid's algorithm
                let temp = m;
                m = n % temp;
                n = temp;
            }   n //.abs()
        }

        let gcd = gcd(self.0, self.1);
        Self(self.0 / gcd, self.1 / gcd)  //*self
    }
}

impl Expr {
    #[allow(dead_code)] fn new(a: &Rc<Self>, b: &Rc<Self>, op: &Oper) -> Self {
        #[inline(always)] fn operate(a: &Expr, b: &Expr, op: &Oper) -> Rational {
            let mut val = Rational(0, 0);
            match op.0 {    // XXX: check overflow?
                b'+' => { val.0 = a.v.0 * b.v.1 + a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                b'-' => { val.0 = a.v.0 * b.v.1 - a.v.1 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                b'*' => { val.0 = a.v.0 * b.v.0;  val.1 = a.v.1 * b.v.1; }
                b'/' => if b.v.1 != 0 {
                          val.0 = a.v.0 * b.v.1;  val.1 = a.v.1 * b.v.0;
                }  else { val.1 = 0; }  // invalidation

                _ => unimplemented!("operator '{}'", op.0)
            }   val //.simplify()   // XXX: reduce probablity of future overflow
        }

        Self { v: operate(a, b, op), m: Some((Rc::clone(a), Rc::clone(b))), op: *op }
    }
}

fn form_expr<F: FnMut(Rc<Expr>)>(a: &Rc<Expr>, b: &Rc<Expr>, mut func: F) {
    let den = a.v.1 * b.v.1;

    // ((a . b) . B) => (a . (b . B)

    let op = Oper(b'*');
    // (A * (a * b)) => (a * (A * b)) if a < A
    // ((a / b) * B) => ((a * B) / b), (A * (a / b)) => ((A * a) / b)
    if a.op.0 != op.0 && a.op.0 != b'/' && b.op.0 != b'/' && !(op.0 == b.op.0 &&
        if let Some((ba, _)) = &b.m { ba.v < a.v } else { false }) {
        func(Rc::new(Expr { v: Rational(a.v.0 * b.v.0, den),
                            m: Some((a.clone(), b.clone())), op }));
    }

    let op = Oper(b'+');
    // (A + (a + b)) => (a + (A + b)) if a < A
    // ((a - b) + B) => ((a + B) - b), (A + (a - b)) => ((A + a) - b)
    if a.op.0 != op.0 && a.op.0 != b'-' && b.op.0 != b'-' && !(op.0 == b.op.0 &&
        if let Some((ba, _)) = &b.m { ba.v < a.v } else { false }) {
        func(Rc::new(Expr { v: Rational(a.v.0 * b.v.1 + a.v.1 * b.v.0, den),
                            m: Some((a.clone(), b.clone())), op }));
    }

    let op = Oper(b'-');
    // (A - (a - b)) => ((A + b) - a), x - 0 => x + 0?
    if a.op.0 != op.0 && op.0 != b.op.0 {
        let v = Rational(a.v.1 * b.v.0 - a.v.0 * b.v.1, den);
        //if a.v.0 != 0/* && !is_subn_expr(a)*/ { }
        func(Rc::new(Expr { v, m: Some((b.clone(), a.clone())), op }));

        //v.0 = -v.0; //if b.v.0 != 0/* && !is_subn_expr(b)*/ { }
        //func(Rc::new(Expr { v, m: Some((a.clone(), b.clone())), op }));
    }

    let op = Oper(b'/');
    // (A / (a / b)) => ((A * b) / a), x / 1 => x * 1, 0 / b => 0 * b?
    if a.op.0 != op.0 && op.0 != b.op.0 {
        let v = Rational(a.v.0 * b.v.1, a.v.1 * b.v.0);
        if v.1 != 0/* && b.v.0 != b.v.1 && a.v.0 != 0*/  {
            func(Rc::new(Expr { v, m: Some((a.clone(), b.clone())), op }));
        }

        let v = Rational(v.1, v.0);     //core::mem::swap(&mut v.0, &mut v.1);
        if v.1 != 0/* && a.v.0 != a.v.1 && b.v.0 != 0*/  {
            func(Rc::new(Expr { v, m: Some((b.clone(), a.clone())), op }));
        }
    }
}

fn _form_expr<F: FnMut(Rc<Expr>)>(a: &Rc<Expr>, b: &Rc<Expr>, mut func: F) {
    //const Add: Oper = Oper(b'+');  const Sub: Oper = Oper(b'-');
    //const Mul: Oper = Oper(b'*');  const Div: Oper = Oper(b'/');
    //[Oper::Add('+'), Oper::Sub('-'), Oper::Mul('*'), Oper::Div('/')]
    [Oper(b'+'), Oper(b'-'), Oper(b'*'), Oper(b'/')].iter().for_each(|op| {
        // keep human friendly expr. form ONLY
        if a.op.0 == op.0 { return }     // ((a . b) . B) => (a . (b . B))

        // ((a - b) + B) => ((a + B) - b), ((a / b) * B) => ((a * B) / b)
        //match (aop.0, op.0) { (b'-', b'+') | (b'/', b'*') => return, _ => () }
        if let (b'-', b'+') | (b'/', b'*') = (a.op.0, op.0) { return }

        if let Some((ba, _)) = &b.m {
            /* if op.0 == bop.0 {
                if  op.0 == b'-' || op.0 == b'/' { return }
                // (A + (a + b)) => (a + (A + b)) if a < A
                // (A * (a * b)) => (a * (A * b)) if a < A
                if (op.0 == b'+' || op.0 == b'*') && ba.v < a.v { return }
            }

            // (A + (a - b)) => ((A + a) - b), (A * (a / b)) => ((A * a) / b)
            // (A - (a - b)) => ((A + b) - a), (A / (a / b)) => ((A * b) / a)
            if let (b'+', b'-') | (b'*', b'/') = (op.0, bop.0) { return } */

            match (op.0, b.op.0) {
                // (A + (a + b)) => (a + (A + b)) if a < A
                // (A * (a * b)) => (a * (A * b)) if a < A
                (b'+', b'+') | (b'*', b'*') if ba.v < a.v => return,

                // (A + (a - b)) => ((A + a) - b), (A * (a / b)) => ((A * a) / b)
                // (A - (a - b)) => ((A + b) - a), (A / (a / b)) => ((A * b) / a)
                (b'+', b'-') | (b'*', b'/') | (b'-', b'-') | (b'/', b'/') => return,

                _ => ()
            }
        }

        match op.0 {    // x / 1 => x * 1, 0 / b => 0 * b; x - 0 => x + 0 ?
            b'/' => {   // swap sub-expr. for order mattered (different values) operators
                if a.v.0 != 0/* && a.v.0 != a.v.1 && b.v.0 != 0*/ {
                    func(Rc::new(Expr::new(b, a, op))) }
                if b.v.0 == 0 { return }
            }

            b'-' => {   // prefer (b - a) than (a - b) since a < b
                func(Rc::new(Expr::new(b, a, op))); //if a.v.0 != 0 && !is_subn_expr(a) { }
                return;                                  //if b.v.0 == 0 ||  is_subn_expr(b) { }
            }

            _ => ()
        }   func(Rc::new(Expr::new(a, b, op)));

        // swap sub-expr. for order mattered (different values) operators
        //if op.0 == b'/' &&  a.v.0 != 0/* && a.v.0 != a.v.1 && b.v.0 != 0*/ ||
        //   op.0 == b'-'/* &&  a.v.0 != 0 && !is_subn_expr(a))*/ {
        //    func(Rc::new(Expr::new(b, a, op)));
        //}

        // prefer (b - a) than (a - b) since a < b
        //if op.0 == b'/' && (b.v.0 == 0/* || b.v.0 == b.v.1 || a.v.0 == 0*/) ||
        //   op.0 == b'-'/* && (b.v.0 == 0 ||  is_subn_expr(b))*/ { return }
        //    func(Rc::new(Expr::new(a, b, op)));
    });

    /* #[inline(always)] fn is_subn_expr(e: &Expr) -> bool {
        if let Some((a, op, b)) = &e.m {    // recursive
            if matches!(op.0, '*' | '/') { return is_subn_expr(a) || is_subn_expr(b) }
            if op.0 == '-' && a.v < b.v  { return true }
            // find ((a - b) * x / y) where a < b
        }   false
    } */
}

//impl Drop for Expr { fn drop(&mut self) { eprintln!(r"Dropping: {self}"); } }

impl From<Rational> for Expr {
    fn from(r: Rational) -> Self { Self { v: r/*.simplify()*/, m: None, op: Oper(0) } }
}

impl From<i32> for Expr { fn from(n: i32) -> Self { Rational::from(n).into() } }

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
                let ord = lb.partial_cmp(rb);   // recursive
                if  ord != Some(Ordering::Equal) { return ord }   ord
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

fn _hash_combine(lhs: u32, rhs: u32) -> u32 {
    //lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2))
    lhs ^ (rhs.wrapping_add(0x9e3779b9).wrapping_add(lhs.wrapping_shl(6))
                                       .wrapping_add(lhs.wrapping_shr(2)))
}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        //self.to_string().hash(state); return;
        if let Some((a, b)) = &self.m {
            self.op.0.hash(state);  a.hash(state);  b.hash(state);  // recursive
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

fn comp24_dynprog (goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
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
            //nums.iter().enumerate().for_each(|(i, e)|     // no index access for list
            //    if (1 << i) & x != 0 { e.hash(&mut hasher) });
            let (mut n, mut i) = (1, 0);
            while  n < x {
                if n & x != 0 { nums[i].hash(&mut hasher) }
                n <<= 1;    i += 1;
            }   let h0 = hasher.finish();
            if hv.contains(&h0) { continue } else { hv.push(h0) }
        }

        // TODO: suitable concurrency for each vexp[x]?
        let mut exps = vexp[x].borrow_mut();
        for i in 1..(x+1)/2 {
            if x & i != i { continue }
            let (si, sj) = (vexp[i].borrow(), vexp[x - i].borrow());

            //si.iter().cartesian_product(sj).for_each(|(&a, &b)| { });
            si.iter().for_each(|a| sj.iter().for_each(|b| {
                let (a, b) = if b < a { (b, a) } else { (a, b) };
                form_expr(a, b, |e|
                    if sub_round { exps.push(e) } else if e.v == *goal {
                        if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) }});
                //eprintln!(r"-> ({a}) ? ({b})");
            }));
        }
    }

    if pow == 2 { return Vec::new() }
    vexp.pop().unwrap().into_inner() //vexp[pow - 1].take()
}

// divide and conque number set
fn comp24_splitset(goal: &Rational, nums: &[Rc<Expr>], ia: bool) -> Vec<Rc<Expr>> {
    let (pow, mut exps) = (1 << nums.len(), Vec::new());
    let mut hv = Vec::with_capacity(pow - 2);
    let sub_round = core::ptr::eq(goal, &IR);
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
            let (a, b) = if b < a { (b, a) } else { (a, b) };
            form_expr(a, b, |e|
                if sub_round { exps.push(e) } else if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(e)) } else { exps.push(e) } });
            //eprintln!(r"-> ({a}) ? ({b})");
        }));
    }   exps
}

// construct expr. inplace down up from numbers
fn comp24_inplace<'a>(goal: &Rational, nums: &mut [Rc<Expr>],
    exps: &'a mut HashSet<Rc<Expr>>) -> &'a HashSet<Rc<Expr>> {
    let (n, mut i, ia) = (nums.len(), 0, false);
    let mut hv = Vec::with_capacity(n * (n - 1) / 2);

    while i < n {
        let (ta, mut j) = (nums[i].clone(), i + 1);
        while j < n {    let tb = nums[j].clone();
            let (a, b) = if tb < ta { (&tb, &ta) } else { (&ta, &tb) };

            let mut hasher = DefaultHasher::default();
            a.hash(&mut hasher);    b.hash(&mut hasher);
            let h0 = hasher.finish();
            if hv.contains(&h0) { j += 1; continue } else { hv.push(h0) }
            //eprintln!(r"-> ({a}) ? ({b})");

            nums[j] = nums[n - 1].clone();
            form_expr(a, b, |e| if n == 2 { if e.v == *goal {
                    if ia { println!(r"{}", Paint::green(&e)) } else { exps.insert(e); }}
                } else { nums[i] = e; comp24_inplace(goal, &mut nums[..n-1], exps); });

            nums[j] = tb;   j += 1;
        }   nums[i] = ta;   i += 1;
    }   exps
}

fn comp24_construct<'a>(goal: &Rational, nums: &[Rc<Expr>],
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
            let h0 = hasher.finish();
            if hv.contains(&h0) { return } else { hv.push(h0) }
            //eprintln!(r"-> ({a}) ? ({b})");

            let mut nums = nums.iter().filter(|&e|
                !core::ptr::eq(e, a) && !core::ptr::eq(e, b))
                .cloned().collect::<Vec<_>>();  // drop sub-expr.

            form_expr(a, b, |e| if nums.is_empty() && e.v == *goal {
                    if ia { println!(r"{}", Paint::green(&e)) } else { exps.insert(e); }
                } else { nums.push(e); comp24_construct(goal, &nums, exps); nums.pop(); });
        }));    exps
}

#[derive(Debug, Clone, Copy)] #[repr(C, u8)]
pub enum Comp24Algo { DynProg(bool), SplitSet(bool), Inplace, Construct, }
pub  use Comp24Algo::*;

// view dhat-heap.json in https://nnethercote.github.io/dh_view/dh_view.html
#[cfg(feature = "dhat-heap")] #[global_allocator] static ALLOC: dhat::Alloc = dhat::Alloc;
// cargo run --features dhat-heap

#[inline] pub fn comp24_algo(goal: &Rational, nums: &[Rc<Expr>],
    algo: Comp24Algo) -> Vec<Rc<Expr>> {
    if nums.len() == 1 { return  if nums[0].v == *goal { nums.to_vec() } else { vec![] } }
    debug_assert!(nums.len() < core::mem::size_of::<usize>() * 8);

    #[cfg(feature = "dhat-heap")] let _profiler = dhat::Profiler::new_heap();

    match algo {
        SplitSet(ia) => comp24_splitset(goal, nums, ia),
        DynProg (ia) => comp24_dynprog (goal, nums, ia),

        Inplace => {
            let mut exps = HashSet::default();
            comp24_inplace(goal, &mut nums.to_vec(), &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }

        Construct => {
            let mut exps = HashSet::default();
            comp24_construct(goal, nums, &mut exps);
            exps.into_iter().collect::<Vec<_>>()
        }
    }
}

pub fn comp24_main() {
    fn comp24_helper<I, S>(goal: &Rational, nums: I)
        where I: Iterator<Item = S>, S: AsRef<str> {    // XXX: how to use closure instead?
        let nums = nums.map(|str| str.as_ref().parse::<Rational>())
            .inspect(|res| match res {  // XXX: exit on error?
                Err(why) => eprintln!(r"Error parsing rational: {}", Paint::red(why)),
                Ok(rn) => if rn.1 == 0 {
                    eprintln!(r"Invalid rational number: {}/{}", rn.0, Paint::red(rn.1)) }})
            .filter_map(Result::ok).map(|rn| Rc::new(rn.into())).collect::<Vec<_>>();
        //nums.sort_unstable_by(/* descending */|a, b| b.cmp(a));
        if  nums.len() < 2 { return eprintln!(r"{}",
            Paint::yellow(r"Needs two numbers at least!")) }

        // XXX: how to transfer a mut closure into resursive function?
        comp24_algo(goal, &nums, DynProg (true));
        //comp24_algo(goal, &nums, SplitSet(true));

        /* let exps = comp24_algo(goal, &nums, Inplace);
        //let exps = comp24_algo(goal, &nums, Construct);
        exps.iter().for_each(|e| println!(r"{}", Paint::green(e)));
        let cnt = exps.len();

        if  cnt < 1 && !nums.is_empty() {
            eprintln!(r"{}", Paint::yellow(r"Found no expression!")) } else if 9 < cnt {
            println!(r"Got {} expressions!", Paint::cyan(cnt).bold());
        } */
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

            comp24_helper(&goal, nums);
            if want_exit { std::process::exit(0) }
        }
    }

    /* use core::mem::size_of;   // size_of_val(a)
    println!("\nsize_of: Expr-{}, &Expr-{}, Rc<Expr>-{}, Oper-{}, Rational-{}",
        size_of::<Expr>(), size_of::<&Expr>(), size_of::<Rc<Expr>>(),
        size_of::<Oper>(), size_of::<Rational>()); */

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

#[cfg(feature = "cc")] #[inline]
pub fn comp24_algo_c(goal: &Rational, nums: &[Rational], algo: Comp24Algo) -> usize {
    #[repr(C)] struct Comp24 {
        algo: Comp24Algo, //ia: bool,
        goal: Rational, //nums: &[Rational],
        nums: *const Rational, ncnt: usize,

        ecnt: usize, //core::ffi::c_size_t,
        exps: *mut *const std::os::raw::c_char,
        //exps: *mut *const SharedPtr<Expr>,
        //exps: *mut *const Expr,
    }

    struct Cstr(*mut *const std::os::raw::c_char);
    impl Drop for Cstr { fn drop(&mut self) { todo!() } }

    let mut comp24 = Comp24 {
        algo, goal: Rational(goal.0, goal.1),
        //goal: unsafe { core::mem::transmute(goal) },
        nums: nums.as_ptr(), ncnt: nums.len(),
        ecnt: 0, exps: core::ptr::null_mut(),
    };

    //debug_assert!(core::mem::size_of::<bool>() == 1);
    //eprintln!("algo: {:?}, goal: {}, ncnt: {}", comp24.algo, comp24.goal, comp24.ncnt);
    debug_assert!(core::mem::size_of_val(&comp24.algo) == 2,
        "{}", std::any::type_name::<Comp24Algo>());

    extern "C" { fn comp24_algo(comp24: *mut Comp24); }

    //core::ptr::addr_of_mut!(comp24);
    unsafe { comp24_algo(&mut comp24);  // TODO:
        /* assert!(!comp24.exps.is_null());
        let exps = core::slice::from_raw_parts(comp24.exps, comp24.ecnt).iter().map(|es|
            std::ffi::CStr::from_ptr(*es).to_str().unwrap()).collect::<Vec<_>>(); */
    }   comp24.ecnt
}

#[cfg(feature = "cxx")] #[cxx::bridge] mod ffi_cxx {    // TODO:
    struct Rational { n: i32, d: i32 }
    #[repr(u8)] enum Oper { Num, Add, Sub, Mul, Div, }
    struct Expr { v: Rational, op: Oper, a: SharedPtr<Expr>, b: SharedPtr<Expr> }
    #[repr(u8)] enum Comp24Algo { DynProg, SplitSet, Inplace, Construct }

    extern "Rust" { }

    unsafe extern "C++" {
        include!("comp24.h");

        //type PtrE;// = cxx::SharedPtr<Expr>;

        /* CxxVector cannot hold SharePtr<_>
        fn comp24_dynprog (goal: &Rational, nums: &CxxVector<SharedPtr<Expr>>) ->
            UniquePtr<CxxVector<SharedPtr<Expr>>>;
        fn comp24_splitset(goal: &Rational, nums: &CxxVector<SharedPtr<Expr>>) ->
            UniquePtr<CxxVector<SharedPtr<Expr>>>; */
    }
}

//}

#[cfg(test)] mod tests {     // unit test
    use super::*;   // Need to import items from parent module, to access non-public members.

    #[test] fn parse_disp_rn() {
        let cases = [
            (Rational::from(0), "0"), (Rational(1, 2), "(1/2)"),
            (Rational::from(1), "1"), (Rational::from(-1), "(-1)"),
        ];

        cases.iter().for_each(|it| {
            assert_eq!(it.0.to_string(), it.1, r"display {} != {}",
                Paint::red(&it.0), Paint::cyan(&it.1));
            assert_eq!(it.1.trim_start_matches('(').trim_end_matches(')')
                .parse::<Rational>().unwrap(),  it.0, r"parsing {} != {}",
                Paint::red(&it.1), Paint::cyan(&it.0));
        });
    }

    #[test] fn simplify_rn() {
        let cases = [
            (Rational(-1, -1), Rational(1, 1)),
            (Rational(-4, -2), Rational(2, 1)),
            (Rational( 6,  2), Rational(3, 1)),
        ];

        cases.iter().for_each(|(a, b)| {
            let sa = a.simplify();
            assert!(sa.0 == b.0 && sa.1 == b.1, "simplified rational: {sa}");
        });
    }

    #[test] fn comp24() {
        let cases = [
            ( 24, vec![ 0], vec![], 0),
            ( 24, vec![24], vec!["24"], 0),
            ( 24, vec![ 8, 8, 8, 8], vec![], 0),
            ( 24, vec![ 8, 8, 3, 3], vec!["8/(3-8/3)"], 0),
            ( 24, vec![ 3, 3, 7, 7], vec!["(3/7+3)*7"], 0),
            ( 24, vec![ 5, 5, 5, 1], vec!["(5-1/5)*5"], 0),
            ( 24, vec![10, 9, 7, 7], vec!["10+(9-7)*7"], 0),
            ( 24, vec![ 1, 2, 3, 4], vec!["1*2*3*4", "2*3*4/1",
                                          "(1+3)*(2+4)", "4*(1+2+3)"], 0),
            ( 24, vec![24,24,24,24], vec!["(24-24)*24+24", "24-(24-24)*24", // XXX:
                                          "(24-24)/24+24", "24-(24-24)/24"], 0),
            (100, vec![13,14,15,16,17], vec!["16+(17-14)*(13+15)",
                                             "(17-13)*(14+15)-16"], 0),
            (  5, vec![ 1, 2, 3], vec!["1*(2+3)", "(2+3)/1", "2*3-1",
                                       "2+1*3", "2/1+3", "2+3/1", "1*2+3", ], 0),
            ( 24, vec![ 1, 2, 3, 4, 5], vec![], 78),
            (100, vec![ 1, 2, 3, 4, 5, 6], vec![], 299),
            ( 24, vec![ 1, 2, 3, 4, 5, 6], vec![], 1832),
            //(100, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 5504),
            //( 24, vec![ 1, 2, 3, 4, 5, 6, 7], vec![], 34301),
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
                    let elen = comp24_algo_c(&goal, &nums, algo);
                    println!(r"  Got {} expr. by algo-Cxx{:?}",
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
                let exps = comp24_algo(&goal, &nums, algo);

                exps.iter().for_each(|e| {
                    //println!(r"  {}", Paint::green(e));
                    if res.is_empty() { return }
                    assert!(res.contains(&e.to_string().as_str()),
                        r"Unexpect expr. by algo-{:?}: {}", Paint::magenta(algo), Paint::red(e));
                });

                println!(r"  Got {} expr. by algo-{:?}",
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
                //ffi_cxx::comp24_dynprog(&goal, &nums);    // FIXME:
            }
        });
    }

    #[cfg(feature = "cc")] /*#[test] */fn _comp24_c() {
        /*#[link(name = "comp24")] */extern "C" { fn test_comp24(); }
        unsafe { test_comp24(); }
    }

    /*#[test] #[bench] */fn _comp24_random() {
        use std::time::{Instant, Duration};
        use rand::{Rng, thread_rng, distributions::Uniform};

        let (cnt, mut total_time) = (50, Duration::from_millis(0));
        for _ in 0..cnt {
            let (mut rng, dst) = (thread_rng(), Uniform::new(1, 20));

            let (goal, nums) = (rng.sample(dst),
                rng.sample_iter(dst).take(6).collect::<Vec<_>>());
            println!(r"Compute {:2} from {:?}", Paint::cyan(goal), Paint::cyan(&nums));
            let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
            let (goal, now) = (goal.into(), Instant::now());

            comp24_algo(&goal, &nums, DynProg (false));
            //comp24_algo(&goal, &nums, SplitSet(false));
            //comp24_algo(&goal, &nums, Inplace);
            //comp24_algo(&goal, &nums, Construct);

            total_time += now.elapsed();
        }

        println!(r"Totally {}s for {} iterations.",
            Paint::magenta(total_time.as_millis() as f32 / 1000.0), Paint::magenta(cnt));
        assert!(total_time.as_secs() < 8);
    }

    // https://doc.rust-lang.org/nightly/rustc/instrument-coverage.html
    // RUSTFLAGS="-C instrument-coverage" cargo test
    // llvm-profdata merge -sparse default.profraw -o default.profdata
    // llvm-cov report --use-color --ignore-filename-regex='/.cargo/registry' \
    //      -instr-profile=default.profdata target/debug/examples/comp24
    // llvm-cov show   --use-color --ignore-filename-regex='/.cargo/registry' \
    //      -instr-profile=default.profdata target/debug/examples/comp24 \
    //      -Xdemangler=rustfilt -show-line-counts-or-regions \
    //      -show-instantiations -name=add_quoted_string

    // cargo test -- --color always --nocapture
}

// vim:sts=4 ts=8 sw=4 noet