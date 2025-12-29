use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use gcd::*;
use rand::distr::Uniform;
use rand::prelude::*;
use std::fmt::Debug;
use std::hint::black_box;

type GcdFn<I> = fn(I, I) -> u64;

/// Estimates the running time of a gcd subroutine on random pairs
/// of integers having the given probability distribution.
fn bench_gcd<I, D>(c: &mut Criterion, name: &str, gcd: GcdFn<I>, input_distr: &D)
where
  D: Distribution<I> + Debug,
{
  c.bench_with_input(
    BenchmarkId::new(name, format!("{input_distr:?}")),
    &input_distr,
    |b, _| {
      // Initialize a pseudorandom number generator with a constant seed
      // value, in order to pass exactly the same inputs to all the gcd
      // routines.
      let mut rng = SmallRng::seed_from_u64(2025);
      b.iter_batched(
        || (input_distr.sample(&mut rng), input_distr.sample(&mut rng)),
        |(u, v)| gcd(u, v),
        BatchSize::SmallInput,
      );
    },
  );
}

fn bench_unsigned_gcds(c: &mut Criterion) {
  let fns: [(&str, GcdFn<u64>); _] = [
    ("euclid", euclid),
    ("binary_stein", binary_stein),
    ("binary_bonzini", binary_bonzini),
    ("binary_brent", binary_brent),
    ("harris", harris),
  ];
  // Test the gcd subroutines on pairs of integers that are uniformly
  // distributed in intervals of the form $[2^x,2^y)$, with $x<y$.
  let bit_len_ranges = [0..u64::BITS, 0..10];
  for bit_len in bit_len_ranges {
    let min_input = 1 << bit_len.start; // $2^x$.
    let max_input = u64::MAX >> (u64::BITS - bit_len.end); // $2^y-1$.
    let input_distr = Uniform::new_inclusive(min_input, max_input).unwrap();
    for (fn_name, fn_) in fns {
      bench_gcd(c, fn_name, fn_, &input_distr);
    }
  }
}

fn bench_signed_gcds(c: &mut Criterion) {
  let fns: [(&str, GcdFn<i64>); _] = [("binary_brent_kung", binary_brent_kung)];
  // Test the signed gcd subroutines on pairs of integers that are
  // uniformly distributed in intervals of the form $[-2^x,2^x)$.
  let bit_lens = [i64::BITS - 1, 10];
  for bit_len in bit_lens {
    let max_input = (u64::MAX >> (u64::BITS - bit_len)) as i64; // $2^x-1$.
    let min_input = -max_input - 1; // $-2^x$.
    let input_distr = Uniform::new_inclusive(min_input, max_input).unwrap();
    for (fn_name, fn_) in fns {
      bench_gcd(c, fn_name, fn_, &input_distr);
    }
  }
}

fn bench_even_even_reduction(c: &mut Criterion) {
  pub fn or(mut u: u64, mut v: u64) -> (u32, u64, u64) {
    unsafe { core::hint::assert_unchecked(u > 0 && v > 0) };
    let k = (u | v).trailing_zeros();
    u >>= u.trailing_zeros();
    v >>= v.trailing_zeros();
    (k, u, v)
  }

  pub fn min(mut u: u64, mut v: u64) -> (u32, u64, u64) {
    unsafe { core::hint::assert_unchecked(u > 0 && v > 0) };
    let (k_u, k_v) = (u.trailing_zeros(), v.trailing_zeros());
    u >>= k_u;
    v >>= k_v;
    let k = k_u.min(k_v);
    (k, u, v)
  }

  c.bench_function("or", |b| {
    b.iter(|| or(black_box(1), black_box(2)));
  });
  c.bench_function("min", |b| {
    b.iter(|| min(black_box(1), black_box(2)));
  });
}

criterion_group!(
  benches,
  bench_unsigned_gcds,
  bench_signed_gcds,
  bench_even_even_reduction
);
criterion_main!(benches);
