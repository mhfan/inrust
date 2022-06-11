
// https://nnethercote.github.io/perf-book/introduction.html

//#[macro_use]
//extern crate bencher;
//use bencher::Bencher;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n { 0 => 1, 1 => 1, n => fibonacci(n-1) + fibonacci(n-2), }
}

//fn bench_comp24(c: &mut Criterion) { }
fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(||
        fibonacci(black_box(20))));

    use hello_rust::comp24::*;
    /* let mut group = c.benchmark_group("comp24");
    group.bench_function("", |b| b.iter(|| {}))
    group.sample_size(10);
    group.finish(); */

    c.bench_function("comp24_splitset", |b| b.iter(|| {
        let nums = [1, 2, 3, 4, 5, 6];
        let nums = nums.iter().map(|&n|
            Rc::new(Expr { v: n.into(), m: None })).collect::<Vec<_>>();
        let _exps = compute_24_splitset(&nums).into_iter()
            .filter(|e| e.v == 24.into()).collect::<Vec<_>>();
    }));
}

criterion_group!(benches, criterion_benchmark);
criterion_main! (benches);
