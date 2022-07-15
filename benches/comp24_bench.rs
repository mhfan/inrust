
// https://nnethercote.github.io/perf-book/introduction.html

// TODO: How to do memory profiling in macOS?

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

    /*use rand::{Rng, thread_rng, distributions::Uniform};
    let (mut rng, dst) = (thread_rng(), Uniform::new(1, 100));
    let (goal, nums) = (rng.sample(dst), rng.sample_iter(dst).take(6).collect::<Vec<_>>());
    */let (goal, nums) = (24, [1, 2, 3, 4, 5, 6, 7]);

    use yansi::Paint;
    println!("Benchmark compute {} from {:?} ", Paint::cyan(goal), Paint::cyan(nums));
    let (mut cnt, goal) = (0, goal.into());

    let nums = nums.iter().map(|&n| Rational::from(n)).collect::<Vec<_>>();
    let mut bench_cxx = |algo| {
        group.bench_function(format!("Cxx{:?}", algo), |b|
            b.iter(|| { cnt = comp24_algo_cxx(&goal, &nums, algo); }));
        if 0 < cnt { println!(r"Got {} expr.", Paint::magenta(cnt)) }
    };

    bench_cxx(DynProg (false));
    //bench_cxx(SplitSet(false));
    //bench_cxx(Inplace);

    let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
    let mut bench_closure = |algo| {
        group.bench_function(format!("{algo:?}"), |b|
            b.iter(|| { cnt = comp24_algo(&goal, &nums, algo).len(); }));
        if 0 < cnt { println!(r"Got {} expr.", Paint::magenta(cnt)) }
    };

    bench_closure(DynProg (false));
    //bench_closure(SplitSet(false));
    //bench_closure(Inplace);
    //bench_closure(Construct);

    group.finish();
}

// sudo cargo flamegraph --bench comp24_bench
criterion_group!(benches, criterion_benchmark);
criterion_main! (benches);
