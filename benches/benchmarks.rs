use criterion::{BatchSize, Bencher, BenchmarkId, Criterion, criterion_group, criterion_main};
use gcd::{binary_brent, binary_stein, euclid, harris};
use rand::distr::Uniform;
use rand::prelude::*;
use std::hint::black_box;

type GcdFn = fn(u64, u64) -> u64;

/// Estimates the running time of a gcd subroutine on random pairs of
/// integers having the given probability distribution.
fn bench_gcd<D>(b: &mut Bencher, gcd: GcdFn, input_distr: &D)
where
  D: Distribution<u64>,
{
  // Initialize a pseudorandom number generator with a constant seed
  // value, in order to pass exactly the same inputs to all the gcd
  // routines.
  let mut rng = SmallRng::seed_from_u64(2025);
  b.iter_batched(
    || (input_distr.sample(&mut rng), input_distr.sample(&mut rng)),
    |(u, v)| gcd(u, v),
    BatchSize::SmallInput,
  );
}

fn bench_gcds(c: &mut Criterion) {
  let gcd_fns: [(&str, GcdFn); _] = [
    ("euclid", euclid),
    ("binary_stein", binary_stein),
    ("binary_stein2", binary_stein2),
    ("binary_lemire", binary_lemire),
    ("binary_brent", binary_brent),
    ("harris", harris),
  ];
  // Test the gcd subroutines on pairs of integers that are uniformly
  // distributed in intervals of the form $[2^x,2^y)$, with $x<y$.
  //let bit_len_ranges = [0..u64::BITS, 0..10];
  let bit_len_ranges = [0..u64::BITS - 1];
  for bit_len in bit_len_ranges {
    let min_input = 1 << bit_len.start; // $2^x$.
    let max_input = u64::MAX >> (u64::BITS - bit_len.end); // $2^y-1$.
    let input_distrib = Uniform::new_inclusive(min_input, max_input).unwrap();

    for (fn_name, fn_) in gcd_fns {
      c.bench_with_input(
        BenchmarkId::new(fn_name, format!("{bit_len:?}")),
        &input_distrib,
        |b, input_distrib| {
          bench_gcd(b, fn_, input_distrib);
        },
      );
    }
  }
}

fn binary_lemire(u: u64, v: u64) -> u64 {
  let mut u = u as i64;
  let mut v = v as i64;
  if u == 0 {
    return v.unsigned_abs();
  }
  if v == 0 {
    return u.unsigned_abs();
  }
  let (mut k_u, k_v) = (u.trailing_zeros(), v.trailing_zeros());
  v >>= k_v;
  let k = k_u.min(k_v);
  loop {
    u >>= k_u;
    let diff = v - u;
    k_u = diff.trailing_zeros();
    v = u.min(v);
    u = diff.abs();
    if u == 0 {
      return (v << k) as u64;
    }
  }
}

pub fn binary_stein2(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  let k = (u | v).trailing_zeros();
  u >>= u.trailing_zeros();
  loop {
    v >>= v.trailing_zeros();
    if u > v {
      (u, v) = (v, u);
    }
    v -= u;
    if v == 0 {
      return u << k;
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

criterion_group!(benches, bench_gcds, bench_even_even_reduction);
criterion_main!(benches);
