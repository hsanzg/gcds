// The following doc comment is kept in sync with the `README.md` file.
// Please run `cargo sync-readme` after modifying the comment contents.
//! This crate implements several algorithms for finding the greatest
//! common divisor of two single-precision numbers.
//!
//! The _greatest common divisor_ $\gcd(u,v)$ of two integers $u$ and $v$,
//! not both zero, is the largest integer that evenly divides them both.
//! This definition does not apply when $u$ and $v$ are both zero, since
//! every number divides zero; for convenience, all the algorithms adhere
//! to the convention that $\gcd(0,0)=0$.
#![cfg_attr(not(test), no_std)]

/// Computes the greatest common divisor of $u$ and $v$ using the modern
/// version of the Euclidean algorithm, as described in Algorithm 4.5.2A
/// of _TAOCP_.
///
/// # Examples
/// ```
/// use gcd::euclid;
///
/// assert_eq!(euclid(0, 0), 0);
/// assert_eq!(euclid(2, 0), 2);
/// assert_eq!(euclid(1, 1), 1);
/// assert_eq!(euclid(1, 13), 1);
/// assert_eq!(euclid(1769, 551), 29);
/// assert_eq!(euclid(7000, 4400), 200);
/// assert_eq!(euclid(40902, 24140), 34);
/// assert_eq!(euclid(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(euclid(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed integers.
/// assert_eq!(euclid((-9i64).unsigned_abs(), 3), 3);
/// ```
#[must_use]
pub const fn euclid(mut u: u64, mut v: u64) -> u64 {
  // If $v=0$, we have $\gcd(u,0)=u$.
  while v != 0 {
    // Note that $\gcd(u,v)=\gcd(v,u\bmod v)$, because
    // 1. there is an integer $q$ such that $u\bmod v=u-qv$,
    // 2. any number that divides $u$ and $v$ also divides $u-qv$, and
    // 3. any number that divides $v$ and $u-qv$ also divides $u$.
    (u, v) = (v, u % v);
  }
  u
}

/// Computes the greatest common divisor of $u$ and $v$ using the binary
/// gcd algorithm of J. Stein [["Computational Problems Associated with Racah Algebra,"][stein]
/// _J. Comp. Phys._ **1** (1967), 397--405].
///
/// A summary of what was known up to 1999 about the average running time
/// of this method appears in R. P. Brent's [_"Further analysis of the Binary Euclidean algorithm,"_][brent]
/// Technical Report PRG TR-7--99 (Oxford Univ. Computing Laboratory, 1999).
/// See also Section 4.5.2 of _TAOCP_.
///
/// # Examples
/// ```
/// use gcd::binary_stein;
///
/// assert_eq!(binary_stein(0, 0), 0);
/// assert_eq!(binary_stein(0, 3), 3);
/// assert_eq!(binary_stein(1, 1), 1);
/// assert_eq!(binary_stein(5, 1), 1);
/// assert_eq!(binary_stein(114, 551), 19);
/// assert_eq!(binary_stein(1992, 581), 83);
/// assert_eq!(binary_stein(51041, 18017), 43);
/// assert_eq!(binary_stein(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(binary_stein(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed numbers.
/// assert_eq!(binary_stein(36, (-48i64).unsigned_abs()), 12);
/// ```
///
/// [stein]: https://doi.org/10.1016/0021-9991(67)90047-2
/// [brent]: https://maths-people.anu.edu.au/~brent/pd/rpb183tr.pdf
#[must_use]
pub fn binary_stein(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  // If $u$ and $v$ are both even, then $\gcd(u,v)=2\gcd(u/2,v/2)$.
  // It follows by induction that $\gcd(u,v)=2^k\gcd(u/2^k,v/2^k)$,
  // where $2^k$ is a common divisor of $u$ and $v$. Also, if $u$
  // is even and $v$ is odd, then $\gcd(u,v)=\gcd(u/2,v)$. More
  // generally, $\gcd(u,v)=\gcd(u/2^{k_u},v)$ if $u$ is a multiple
  // of $2^{k_u}$ and $v$ is odd. Combine these results to prove
  // that $\gcd(u,v)=2^k\gcd(u/2^{k_u},v/2^{k_v})$, whenever $u$
  // is a multiple of $2^{k_u}$, $v$ is a multiple of $2^{k_v}$,
  // and $k=\min(k_u,k_v)$.
  let (k_u, k_v) = (u.trailing_zeros(), v.trailing_zeros());
  // SAFETY: Since $u$ and $v$ are nonzero, $k_u$ and $k_v$ are
  //         less than `u64::BITS`.
  u >>= k_u;
  v >>= k_v;
  let k = k_u.min(k_v);
  loop {
    // At the beginning of each iteration of this loop, we have
    // the invariant condition that both $u$ and $v$ are odd.
    // Ensure that $u\le v$; note that $\gcd(u,v)=\gcd(v,u)$.
    if u > v {
      (u, v) = (v, u);
    }
    // As in the Euclidean algorithm, $\gcd(u,v)=\gcd(u,v-u)$.
    v -= u;
    if v == 0 {
      return u << k; // Terminate with $u\cdot2^k$.
    }
    // Now $v$ is even, and $u$ remains odd. Therefore we can apply the
    // identity $\gcd(u,v)=\gcd(u,v/2^{k_v})$ again. After this step, the
    // assertion that $u$ and $v$ are both odd at the start of the next
    // iteration is true.
    // SAFETY: $v$ is nonzero, so it has at least one 1 bit.
    v >>= v.trailing_zeros();
  }
}

/// Computes the greatest common divisor of $u$ and $v$ using an alternative
/// formulation of the binary gcd algorithm proposed by R. P. Brent
/// [[_"Further analysis of the Binary Euclidean algorithm,"_][brent]
/// Technical Report PRG TR-7--99 (Oxford Univ. Computing Laboratory, 1999),
/// Section 5].
///
/// # Examples
/// ```
/// use gcd::binary_brent;
///
/// assert_eq!(binary_brent(0, 0), 0);
/// assert_eq!(binary_brent(0, 4), 4);
/// assert_eq!(binary_brent(1, 1), 1);
/// assert_eq!(binary_brent(1, 7), 1);
/// assert_eq!(binary_brent(306, 5049), 153);
/// assert_eq!(binary_brent(7684, 3400), 68);
/// assert_eq!(binary_brent(68825, 10150), 25);
/// assert_eq!(binary_brent(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(binary_brent(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed integers.
/// assert_eq!(
///   binary_brent((-10i64).unsigned_abs(), (-5i64).unsigned_abs()),
///   5
/// );
/// ```
///
/// [brent]: https://maths-people.anu.edu.au/~brent/pd/rpb183tr.pdf
pub fn binary_brent(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  // A proof of correctness of this algorithm looks almost identical to
  // that in `binary_stein`, the original version of the binary method.
  // First recall that $\gcd(u,v)=2^k\gcd(u/2^{k_u},v/2^{k_v})$, where
  // $2^{k_u}$ and $2^{k_v}$ are the greatest powers of 2 that divide
  // $u$ and $v$, respectively, and $k=\min(k_u,k_v)$. (The integers
  // $k_u$ and $k_v$ are sometimes known as the _dyadic valuations_
  // of $u$ and $v$, respectively.)
  let (k_u, k_v) = (u.trailing_zeros(), v.trailing_zeros());
  // SAFETY: Since $u$ and $v$ are nonzero, $k_u$ and $k_v$ are
  //         less than `u64::BITS`.
  u >>= k_u;
  v >>= k_v;
  let k = k_u.min(k_v);
  // Ensure that $u\le v$ on entry to R. P. Brent's Algorithm V.
  // todo: check if moving this swap before the trailing zero computation
  //  results in a measurable speedup.
  if u > v {
    (u, v) = (v, u);
  }
  while u != v {
    while u < v {
      // Note: This inner loop satisfies the invariant condition that
      // $u$ and $v$ are both odd at the beginning of each iteration.
      // Apply the identity $\gcd(u,v)=\gcd(u,v-u)$.
      v -= u;
      // Now $u$ is odd and $v$ is even; we can use the fact that
      // $\gcd(u,v)=\gcd(u,v/2^{k_v})$, where $2^{k_v}$ divides $v$.
      // SAFETY: $v$ is nonzero, because it was greater than $u$ before
      //         the subtraction step.
      v >>= v.trailing_zeros();
      // At this point $v$ is odd, as required by the invariant.
    }
    (u, v) = (v, u);
  }
  // We have $\gcd(u,v)=u$; terminate with $u\cdot2^k$.
  u << k
}

/// Computes the greatest common divisor of $u$ and $v$ using a cross
/// between [Euclid's algorithm](euclid) and the [binary gcd algorithm]
/// proposed by V. C. Harris \[_The Fibonacci Quarterly_ **8** (1970),
/// [102--103][harris]].
///
/// See Section 4.5.2 of _TAOCP_ for a short discussion of this method.
///
/// # Examples
/// ```
/// use gcd::harris;
///
/// assert_eq!(harris(0, 0), 0);
/// assert_eq!(harris(0, 3), 3);
/// assert_eq!(harris(1, 1), 1);
/// assert_eq!(harris(1, 4), 1);
/// assert_eq!(harris(45, 165), 15);
/// assert_eq!(harris(6119, 2175), 29);
/// assert_eq!(harris(69336, 82818), 1926);
/// assert_eq!(harris(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(harris(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed integers.
/// assert_eq!(harris(18, (-27i64).unsigned_abs()), 9);
/// ```
///
/// [binary gcd algorithm]: binary_stein
/// [harris]: https://www.fq.math.ca/Scanned/8-1/harris1.pdf
#[must_use]
pub fn harris(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  // Like the binary gcd algorithm, the main loop of this scheme assumes
  // that $u$ and $v$ are both odd at the beginning of each iteration.
  // Apply the familiar identity $\gcd(u,v)=2^k\gcd(u/2^{k_u},v/2^{k_v})$,
  // where $k_u$ and $k_v$ are the dyadic valuations of $u$ and $v$,
  // and $k=\min(k_u,k_v)$. After this step, $u$ and $v$ become odd.
  let (k_u, k_v) = (u.trailing_zeros(), v.trailing_zeros());
  u >>= k_u;
  v >>= k_v;
  let k = k_u.min(k_v);
  // This scheme also requires that $0<v\le u$ upon entry to the main
  // loop. Obviously $\gcd(u,v)=\gcd(v,u)$.
  if u < v {
    (u, v) = (v, u);
  }
  loop {
    // The comment in `euclid` shows that $\gcd(u,v)=\gcd(v,u\bmod v)$,
    // so we may replace $u$ by its remainder modulo $v$.
    (u, v) = (v, u % v);
    if v == 0 {
      // Clearly $\gcd(u,0)=u$, and the answer is $u\cdot2^k$.
      return u << k;
    }
    // That was the "Euclidean" part of the algorithm; now let's turn
    // to the "binary" part. Since $0<v<u$ and $u$ is odd, either $v$
    // or $u-v$ is a positive even integer less than $u$. Now observe
    // that $\gcd(u,u-v)=\gcd(u,(u-v)\bmod u)=\gcd(u,v)$. Therefore
    // we can always replace $v$ by an even integer in $(0,u)$ that
    // has the same gcd with $u$.
    if v % 2 == 1 {
      v = u - v;
    }
    // SAFETY: See the previous comment.
    unsafe { core::hint::assert_unchecked(v > 0) };
    // At this point $u$ is odd and $v$ is even. If $k_v$ denotes the
    // dyadic valuation of $v$, then $\gcd(u,v)=2^{k_v}\gcd(u,v/2^{k_v})$.
    // Note that this step makes $v$ odd and preserves the inequality
    // $0<v\le u$.
    v >>= v.trailing_zeros();
  }
}

#[must_use]
pub fn binary_brent_kung(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  // It can be shown that this loop runs for $\le 2+2\lg\max(u,v)$ iterations.

  todo!()
}

#[cfg(test)]
mod tests {
  use super::*;

  fn test_methods<I>(cases: I)
  where
    I: Iterator<Item = ((u64, u64), u64)>,
  {
    const METHODS: [fn(u64, u64) -> u64; 4] = [euclid, binary_stein, binary_brent, harris];
    for ((u, v), expected) in cases {
      for method in METHODS {
        assert_eq!(method(u, v), expected);
      }
    }
  }

  #[test]
  fn small_numbers() {
    test_methods(
      [
        ((0, 0), 0),
        ((0, 1), 1),
        ((0, u64::MAX), u64::MAX),
        ((1, 2), 1),
        ((1, 5), 1),
        ((1, u64::MAX), 1),
        ((2, 4), 2),
        ((3, 8), 1),
        ((4, 8), 4),
        ((12, 54), 6),
        ((30, 70), 10),
        ((76, 95), 19),
        ((64, 128), 64),
        ((119, 544), 17),
        ((233, 377), 1),
        ((610, 2584), 2),
        ((512, 1024), 512),
        ((1989, 3003), 39),
        ((2166, 6099), 57),
        ((5046, 8004), 174),
        ((1 << 11, 1 << 13), 1 << 11),
      ]
      .into_iter(),
    );
  }

  #[test]
  fn random_pairs() {
    use rand::prelude::*;
    let rng = SmallRng::seed_from_u64(2025);
    let pairs = rng
      .random_iter::<u128>()
      .take(10_000_000)
      .map(|x| (x as u64, (x >> u64::BITS) as u64));
    test_methods(pairs.map(|(u, v)| {
      let gcd = euclid(u, v);
      ((u, v), gcd)
    }));
  }
}
