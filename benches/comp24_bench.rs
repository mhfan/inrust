
// https://nnethercote.github.io/perf-book/introduction.html

// TODO: How to do memory profiling?

//#[macro_use]
//extern crate bencher;
//use bencher::Bencher;

use criterion::{criterion_group, criterion_main, Criterion};

//fn bench_comp24(c: &mut Criterion) { }
fn criterion_benchmark(c: &mut Criterion) {
    /* fn fibonacci(n: u64) -> u64 {
        match n { 0 => 1, 1 => 1, n => fibonacci(n-1) + fibonacci(n-2), }
    }

    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
    use criterion::black_box; */

    use hello_rust::comp24::*;
    let mut group = c.benchmark_group("comp24");
    group.sample_size(10);

    let (goal, nums) = (24, [1, 2, 3, 4, 5, 6].iter().map(|&n|
        Rc::new(Expr { v: n.into(), m: None })).collect::<Vec<_>>());

    group.bench_function("splitset", |b| b.iter(|| {
        let _exps = comp24_splitset(&nums).into_iter()
            .filter(|e| e.v == goal.into()).collect::<Vec<_>>();
    }));

    /* group.bench_function("construct", |b| b.iter(|| {
        let mut exps = HashSet::default();
        comp24_construct(&goal.into(), &nums, &mut exps);
        let _exps = exps.into_iter().collect::<Vec<_>>();
    })); */

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main! (benches);
