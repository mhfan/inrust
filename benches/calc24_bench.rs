
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
    #[cfg(feature = "cc")] {
        let mut bench_closure_c = |algo| {
            group.bench_function(format!("Cxx{:?}", algo), |b|
                b.iter(|| { cnt = calc24_cffi(&goal, &nums, algo); }));
            if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
        };  bench_closure_c(algo);
    }

    let mut bench_closure = |algo| {
        group.bench_function(format!("{algo:?}"), |b| b.iter(|| {
            //cnt = calc24_coll(&goal, &nums, algo).len();  // got same performance
            let mut exps = vec![];  //cnt = 0;  // XXX: cnt += 1;
            calc24_algo(&goal, &nums, algo, |e| {
                exps.push(e);   Some(()) });    cnt = exps.len();
        }));
        if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
    };  bench_closure(algo);
  }

    group.finish();
}

#[cfg(not(feature = "pprof"))] criterion_group!(benches, bench_24calc);

#[cfg(feature = "pprof")] use pprof::criterion::{PProfProfiler, Output};
#[cfg(feature = "pprof")] criterion_group!{
    name = benches;
    config = Criterion::default()
        .with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_24calc
}

// sudo cargo flamegraph --bench comp24_bench
criterion_main!(benches);
