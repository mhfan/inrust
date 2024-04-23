/****************************************************************
 * $ID: prime.rs  	Sun 21 Apr 2024 17:35:25+0800               *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2024 M.H.Fan, All rights reserved.             *
 ****************************************************************/

/** ```
    [ (0, 0), (1, 1), (4, 2), (5, 2), (7, 2), (8, 2), (9, 3), (10, 3), ].into_iter()
        .for_each(|(n, r)| assert!(inrust::prime::isqrt(n) == r, "isqrt(n) != {r})"));
``` */
pub fn isqrt(x: u64) -> u32 {   // XXX: to generalize?
    let (mut num, mut res) = (x, 0);
    // "bit" starts at the highest power of four <= the argument.
    //let  mut bit = 1 << ((32 - x.leading_zeros()) & !1); // assert!(x != 0);
    let  mut bit = 1 << (((std::mem::size_of::<u32>() as u32) << 3) - 2);
    // C/C++: 1 << (fls(x) & ~1) or 1 << ((32 - __builtin_clz(x)) & ~1)
    //while num < bit { bit >>= 2; }  // from the second-to-top bit

    while bit != 0 {
        if  num >= res + bit {
            num -= res + bit;
            res = (res >> 1) + bit;
        } else { res >>= 1; }
        bit >>= 2;
    }   res as u32
}

/** ```
    [ (1, false), (2, true), (3, true), (12, false), (5, true), (6, false) ].into_iter()
        .for_each(|(n, p)| assert!(inrust::prime::is_prime(n) == p, "({n}, {p})"));
``` */
pub fn is_prime(x: u64) -> bool {
    if 3 < x && x % 2 == 0 { return false }     let mut n = 3;
    while n * n <= x { if x % n == 0 { return false; } n += 2; }    1 < x
}

/** ```
    [ (1, vec![]), (2, vec![ (2, 1) ]), (6, vec![ (2, 1), (3, 1) ]),
        (60, vec![ (2, 2), (3, 1), (5, 1) ]) ].iter().for_each(|(x, pfv)| {
        let pfl = inrust::prime::prime_factor(*x);
        assert!(&pfl == pfv, "{x} {pfv:?} vs {pfl:?}");
    });
``` */
pub fn prime_factor(x: u64) -> Vec<(u32, u32)> {    assert!(x != 0);
    let (mut x, mut n, mut cnt, mut pfv) = (x, 3, 0, vec![]);

    // Handle factor 2 separately to allow for incrementing n by 2 later
    while x % 2 == 0 { x /= 2; cnt += 1; }
    if 0 < cnt {  pfv.push((2, cnt)); }

    while n * n <= x {  cnt = 0;    // Check only odd numbers starting from 3
        while x % n == 0 { x /= n; cnt += 1; }
        if 0 < cnt {  pfv.push((n as u32, cnt)); }  n += 2;
    }   if 1 < x   {  pfv.push((x as u32, 1)); }    pfv
}

//pub fn next_prime(x: u32) -> u32 { todo!() }
//pub fn find_prime(x: u64) -> Vec<u32> { todo!() }
//HashMap.entry(n).and_modify(|cnt| *cnt += 1).or_insert(1);

#[cfg_attr(coverage_nightly, coverage(off))] //#[cfg(not(tarpaulin_include))]
#[allow(dead_code)] #[cfg(feature = "cli")] pub fn factor_prime_cli() {
    println!("\n### Fractorization of prime ###");

    loop {  use std::io::Write;     let mut nstr = String::new();
        print!("\n{}", yansi::Paint::white("Input an arbitrary integer: ").dim());
        std::io::stdout().flush().expect("Failed to flush"); //.unwrap();
        std::io::stdin().read_line(&mut nstr).expect("Failed to read");

        let nstr = nstr.trim();
        if let Ok(num) = nstr.parse() {
            if num < 2 { println!("{num} (no prime factor)"); continue }
            let mut use_sep = false;    //print!("{num} = ");

            prime_factor(num).iter().for_each(|(p, n)| {
                if use_sep { print!(" * "); } else { use_sep = true; }  // interperse_with
                print!("{p}");  if 1 < *n { print!("^{n}"); }
            }); println!();
        } else if nstr.eq_ignore_ascii_case("quit") { break } else {
            eprintln!("Not a legal positive integer?");
        }
    }
}

