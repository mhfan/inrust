
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

    /*use rand::{Rng, thread_rng, distributions::Uniform};
    let (mut rng, dst) = (thread_rng(), Uniform::new(1, 100));
    let (goal, nums) = (rng.sample(dst), rng.sample_iter(dst).take(6).collect::<Vec<_>>());
    */let (goal, nums) = (24, [1, 2, 3, 4, 5, 6]);

    println!("Benchmark compute {goal} from {nums:?} ");
    let nums = nums.into_iter().map(|n| Rc::new(n.into())).collect::<Vec<_>>();
    let goal = goal.into();

    let mut bench_closure = |algo| {
        group.bench_function(format!("{algo:?}"), |b| b.iter(|| {
            let _exps = comp24_algo(&goal, &nums, algo);
        }));
    };

    bench_closure(SplitSet(false));
    //bench_closure(DynProg);
    //bench_closure(Construct);

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main! (benches);
