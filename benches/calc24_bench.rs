
// https://nnethercote.github.io/perf-book/introduction.html

//#[macro_use]
//extern crate bencher;
//use bencher::Bencher;

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_24calc(c: &mut Criterion) {
    /* fn fibonacci(n: u64) -> u64 {
        match n { 0 => 1, 1 => 1, n => fibonacci(n-1) + fibonacci(n-2), }
    }

    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
    use criterion::black_box; */

    use inrust::calc24::*;
    let mut group = c.benchmark_group("calc24");
    group.sample_size(10);

    /*use rand::{Rng, thread_rng, distributions::Uniform};
    let (mut rng, dst) = (thread_rng(), Uniform::new(1, 100));
    let (goal, nums) = (rng.sample(dst), rng.sample_iter(dst).take(6).collect::<Vec<_>>());
    */let (goal, nums) = (24, [1, 2, 3, 4, 5, 6, 7]);

    use yansi::Paint;
    println!("Compute {} from {:?} ", Paint::cyan(goal), Paint::cyan(nums));
    let (mut cnt, goal) = (0, goal.into());

    #[cfg(feature = "cc")]
    let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();

    #[cfg(feature = "cc")] {
        let mut bench_closure_c = |algo| {
            group.bench_function(format!("Cxx{:?}", algo), |b|
                b.iter(|| { cnt = calc24_algo_c(&goal, &nums, algo); }));
            if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
        };

        bench_closure_c(DynProg (false));
        //bench_closure_c(SplitSet(false));
        //bench_closure_c(Inplace);
    }

    let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
    let mut bench_closure = |algo| {
        group.bench_function(format!("{algo:?}"), |b|
            b.iter(|| { cnt = calc24_algo(&goal, &nums, algo).len(); }));
        if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
    };

    bench_closure(DynProg (false));
    //bench_closure(SplitSet(false));
    //bench_closure(Inplace);
    //bench_closure(Construct);

    group.finish();
}

//criterion_group!(benches, bench_24calc);
use pprof::criterion::{PProfProfiler, Output};
criterion_group!{
    name = benches;
    config = Criterion::default()
        .with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_24calc
}

// sudo cargo flamegraph --bench comp24_bench
criterion_main!(benches);
