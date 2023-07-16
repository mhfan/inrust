
// https://nnethercote.github.io/perf-book/introduction.html

//#[macro_use]
//extern crate bencher;
//use bencher::Bencher;

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_24calc(c: &mut Criterion) {
    use inrust::{misc::fibonacci, calc24::*};
    let mut group = c.benchmark_group("calc24");
    group.sample_size(10);

    /*use rand::{Rng, distributions::Uniform};
    let (mut rng, dst) = (rand::thread_rng(), Uniform::new(1, 100));
    let (goal, nums) = (rng.sample(dst), rng.sample_iter(dst).take(6).collect::<Vec<_>>());
    */let (goal, nums) = (24, fibonacci().skip(3).take(7).collect::<Vec<i32>>());

    use yansi::Paint;
    println!("Compute {} from {:?} ", Paint::cyan(goal), Paint::cyan(&nums));
    let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();
    let (goal, mut cnt) = (goal.into(), 0);

    for algo in [ DynProg, Construct ] {    // XXX: SplitSet, Inplace,
        let mut bench_closure = |algo, cxx: &str| {
            group.bench_function(format!("{cxx}{algo:?}"), |b| b.iter(|| {
                if cxx.is_empty() { cnt = calc24_coll(&goal, &nums, algo).len(); } else {
                    #[cfg(feature = "cc")] { cnt = calc24_cffi(&goal, &nums, algo).len(); }
                }
            }));    if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
        };

        #[cfg(feature = "cc")] bench_closure(algo, "Cxx");
        bench_closure(algo, "");
    }   group.finish();
}

#[cfg(not(feature = "pprof"))] criterion_group!(benches, bench_24calc);

#[cfg(feature = "pprof")] use pprof::criterion::{PProfProfiler, Output};
#[cfg(feature = "pprof")] criterion_group!{     name = benches;
    config = Criterion::default()
        .with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_24calc
}   // https://github.com/tikv/pprof-rs

// sudo cargo flamegraph --bench calc24_bench   // https://github.com/flamegraph-rs/flamegraph
criterion_main!(benches);   // cargo bench --features="pprof" # dhat-heap

