
// https://nnethercote.github.io/perf-book/introduction.html

//#[macro_use]
//extern crate bencher;
//use bencher::Bencher;

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_24calc(c: &mut Criterion) {
    use inrust::{fibonacci, calc24::*};
    let mut group = c.benchmark_group("calc24");
    group.sample_size(10);

    /*use rand::{Rng, thread_rng, distributions::Uniform};
    let (mut rng, dst) = (thread_rng(), Uniform::new(1, 100));
    let (goal, nums) = (rng.sample(dst), rng.sample_iter(dst).take(6).collect::<Vec<_>>());
    */let (goal, nums) = (24, fibonacci().skip(3).take(7).collect::<Vec<i32>>());

    use yansi::Paint;
    println!("Compute {} from {:?} ", Paint::cyan(goal), Paint::cyan(&nums));
    let nums = nums.into_iter().map(Rational::from).collect::<Vec<_>>();
    let (mut cnt, goal) = (0, goal.into());

    #[cfg(feature = "cc")] {
        let mut bench_closure_c = |algo| {
            group.bench_function(format!("Cxx{:?}", algo), |b|
                b.iter(|| { cnt = calc24_algo_c(&goal, &nums, algo); }));
            if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
        };

        bench_closure_c(DynProg);
        //bench_closure_c(SplitSet);
        //bench_closure_c(Inplace);
        //bench_closure_c(Construct);
    }

    let mut bench_closure = |algo| {
        group.bench_function(format!("{algo:?}"), |b| b.iter(|| {
            let mut exps = vec![];  //cnt = 0;  // XXX: cnt += 1;
            calc24_algo(&goal, &nums, algo, &mut |e| {
                exps.push(e);   Some(()) });    cnt = exps.len();
            //cnt = calc24_coll(&goal, &nums, algo).len();  // got same performance
        }));
        if 0 < cnt { println!(r"Got {} solutions.", Paint::magenta(cnt)) }
    };

    bench_closure(DynProg);
    //bench_closure(SplitSet);
    //bench_closure(Inplace);     // XXX: 6 times worse than Construct
    //bench_closure(Construct);

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
