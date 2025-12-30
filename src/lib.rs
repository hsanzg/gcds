// The following doc comment is kept in sync with the `README.md` file.
// Please run `cargo sync-readme` after modifying its contents.
//! This crate implements several algorithms for finding the greatest
//! common divisor of two single-precision numbers.
//!
//! The _greatest common divisor_ $\gcd(u,v)$ of two integers $u$ and $v$,
//! not both zero, is the largest integer that evenly divides them both.
//! This definition does not apply when $u$ and $v$ are both zero, since
//! every number divides zero; for convenience, all the algorithms adhere
//! to the convention that $\gcd(0,0)=0$.

/// Computes the greatest common divisor of $u$ and $v$ using the modern
/// version of the Euclidean algorithm, as described in Algorithm 4.5.2A
/// of _TAOCP_.
///
/// # Examples
/// ```
/// use gcds::euclid;
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
/// use gcds::binary_stein;
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
  let k = (u | v).trailing_zeros();
  // SAFETY: Since $u$ and $v$ are nonzero, $k_u$ and $k_v$ are
  //         less than `u64::BITS`.
  u >>= u.trailing_zeros();
  v >>= v.trailing_zeros();
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

/// Computes the greatest common divisor of $u$ and $v$ using an optimized
/// variant of the [binary gcd algorithm] proposed by P. Bonzini, and studied
/// by D. Lemire [["Greatest common divisor, the extended Euclidean algorithm, and speed!"][lemire]
/// (April 2024)].
///
/// # Examples
/// ```
/// use gcds::binary_bonzini;
///
/// assert_eq!(binary_bonzini(0, 0), 0);
/// assert_eq!(binary_bonzini(2, 0), 2);
/// assert_eq!(binary_bonzini(1, 1), 1);
/// assert_eq!(binary_bonzini(1, 4), 1);
/// assert_eq!(binary_bonzini(792, 252), 36);
/// assert_eq!(binary_bonzini(954, 5883), 159);
/// assert_eq!(binary_bonzini(14003, 63194), 19);
/// assert_eq!(binary_bonzini(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(binary_bonzini(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed numbers.
/// assert_eq!(binary_bonzini((-8i64).unsigned_abs(), 76), 4);
/// ```
///
/// [binary gcd algorithm]: binary_stein
/// [lemire]: https://lemire.me/blog/2024/04/13/greatest-common-divisor-the-extended-euclidean-algorithm-and-speed/
pub fn binary_bonzini(mut u: u64, mut v: u64) -> u64 {
  if u == 0 {
    return v;
  }
  if v == 0 {
    return u;
  }
  // As in the original binary gcd algorithm, we begin by applying the
  // formula $\gcd(u,v)=2^k\gcd(u/2^{k_u},v/2^{k_v})$, where $2^{k_u}$
  // and $2^{k_v}$ are the largest powers of 2 dividing $u$ and $v$,
  // respectively, and $k=\min(k_u,k_v)$. The only difference is that
  // the assignment "$v\gets v/2^{k_v}$" appears within the main loop,
  // consolidated with the same operation appearing at the end of the
  // original version of the loop.
  let k = (u | v).trailing_zeros();
  u >>= u.trailing_zeros();
  let mut k_v = v.trailing_zeros();
  loop {
    v >>= k_v;
    // In essence, the updating rule of the binary gcd algorithm is
    // $(u,v)\gets(\min(u,v),|u-v|)$. (As we have already observed,
    // this transformation leaves $\gcd(u,v)$ unchanged.) Perhaps
    // the most obvious way to find the new value of $v$ is to use
    // `u.abs_diff(v)` or the equivalent sequence of operations in
    // `binary_stein`. Here we start by computing $u-v$ instead:
    let (diff, neg_diff) = u.overflowing_sub(v);
    // Why? In the first place, the termination condition $|u-v|=0$
    // of the original algorithm holds if and only if $u-v=0$. The
    // latter quantity is easier to compute on most architectures.
    if diff == 0 {
      return u << k;
    }
    // In the second place, $|u-v|$ and $u-v$ have the same dyadic
    // valuation $k_v$ (equivalently, the greatest power of $2$
    // that divides each of them is the same, $2^{k_v}$). So we
    // can compute $k_v$ directly from $u-v$, without having to
    // wait for the result of $|u-v|$ to become available.
    k_v = diff.trailing_zeros();
    u = u.min(v);
    // Actually compute $|u-v|$ from `diff` and `neg_diff`. Note
    // that a smart compiler will lower the required conditional
    // branch to a `cmov` instruction on x86 and a `cneg` on ARM,
    // much like what it would produce for `u.abs_diff(v)`.
    v = if neg_diff { diff.wrapping_neg() } else { diff };
    // After this operation, we recover the invariant condition that
    // $u$ is odd and $v$ is even. The next iteration will reduce $v$
    // by applying the identity $\gcd(u,v)=2^{k_v}\gcd(u,v/2^{k_v})$.
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
/// use gcds::binary_brent;
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
  // or the _ruler functions_ of $u$ and $v$, respectively.)
  let k = (u | v).trailing_zeros();
  // SAFETY: Since $u$ and $v$ are nonzero, $k_u$ and $k_v$ are
  //         less than `u64::BITS`.
  u >>= u.trailing_zeros();
  v >>= v.trailing_zeros();
  // Ensure that $u\le v$ on entry to R. P. Brent's Algorithm V.
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

/// Computes the greatest common divisor of $u$ and $v$ using the systolic
/// variant of the binary gcd algorithm by R. P. Brent and H. T. Kung [_IEEE
/// Symposium on Computer Arithmetic_ **7** (1985), [118--125][systolic]].
///
/// Exercise 4.5.2.40 of _TAOCP_ studies the worst-case running time of
/// this method.
///
/// # Examples
/// ```
/// use gcds::binary_brent_kung;
///
/// assert_eq!(binary_brent_kung(0, 0), 0);
/// assert_eq!(binary_brent_kung(-3, 0), 3);
/// assert_eq!(binary_brent_kung(1, 1), 1);
/// assert_eq!(binary_brent_kung(1, -6), 1);
/// assert_eq!(binary_brent_kung(-45, -63), 9);
/// assert_eq!(binary_brent_kung(4899, 690), 69);
/// assert_eq!(binary_brent_kung(-4515, 9765), 105);
/// assert_eq!(binary_brent_kung(75850, 20213), 41);
/// assert_eq!(binary_brent_kung(i64::MAX - 1, i64::MAX), 1);
/// assert_eq!(binary_brent_kung(i64::MAX, i64::MAX), i64::MAX as u64);
/// assert_eq!(binary_brent_kung(i64::MAX, -i64::MAX), i64::MAX as u64);
/// ```
///
/// [systolic]: https://maths-people.anu.edu.au/brent/pd/rpb077i.pdf
#[must_use]
pub fn binary_brent_kung(mut u: i64, mut v: i64) -> u64 {
  if u == 0 {
    return v.unsigned_abs();
  }
  // This variant of the binary gcd algorithm avoids the need to test
  // the sign of $u-v$ by maintaining (loose) upper bounds $|u|\le2^p$
  // and $|v|\le2^q$, and replacing the test ``$u>v$'' by the weaker
  // ``$p>q$.'' The important thing is that if $u$ and $v$ are $n$-bit
  // numbers, then $p$ and $q$ fit in at most $\floor{\lg n}+1$ bits.
  // Thus it is easier to test the sign of $p-q$ than of $u-v$. Also,
  // since no other step of the algorithm involves the variables $p$
  // and $q$, we can work directly with their difference. R. Brent and
  // H. T. Kung exploited these ideas to implement the new algorithm
  // on a _systolic array_, a collection of primitive data processing
  // units that work in parallel and communicate with their neighbors.

  // It should be noted that the original binary algorithm performs
  // at most $n+1$ iterations of its main loop (see exercise 4.5.2.37
  // of _TAOCP_), whereas its systolic counterpart might need up to
  // $2n+2$ (see exercise 4.5.2.40). Thus there is a tradeoff between
  // the number of iterations and their individual speed. (Of course
  // this tradeoff applies only when the test ``$p>q$'' is performed
  // efficiently; since the present routine operates on full computer
  // words, it is actually significantly slower than `binary_stein`.
  // We will content ourselves with this unoptimized implementation,
  // because it illustrates the salient features of the systolic
  // algorithm and the properties of the $\gcd$ function that it
  // relies on.)

  // Ensure that $u$ is odd by using the by-now-familiar identity
  // $\gcd(u,v)=2^k\gcd(u/2^k_u,v/2^k_v)$, where $k_u$ and $k_v$
  // are the dyadic valuations of $u$ and $v$, and $k=\min(k_u,k_v)$.
  // Unlike the other gcd methods, this routine accepts _signed_
  // integers as input. Rust works with two's complement notation,
  // so `x.trailing_zeros()` gives the value of $k_x$ whenever $x$
  // is a nonzero integer; the case $x=v=0$ is handled below.
  let (k_u, mut k_v) = (u.trailing_zeros(), v.trailing_zeros());
  u >>= k_u;
  let k = k_u.min(k_v);

  // Variable $d$ stores the difference between the upper bounds $p$
  // and $q$ on $\lg|u|$ and $\lg|v|$, respectively. We have $p=q=n$
  // upon entry to the algorithm, and $p=n-k_u$ after dividing $u$ by
  // $2^{k_u}$. If $u$ and $v$ are expected to have wildly different
  // orders of magnitude, it is advantageous to initialize $d$ with
  // the exact difference $\ceil{\lg|u|}-\ceil{\lg|v|}$, but that
  // expression is more difficult to evaluate on a systolic array.
  let mut d = -(k_u as i32);
  while v != 0 {
    // Each iteration of this loop begins with $u$ odd and $v$ even.
    v >>= k_v;
    d += k_v as i32;
    // Swap $u\leftrightarrow v$ if the bound on $|u|$ is larger
    // than the bound on $|v|$.
    if d > 0 {
      (u, v) = (v, u);
      d = -d;
    }
    // At this point both $u$ and $v$ are odd, and it is likely that
    // $|u|\le|v|$. Unfortunately the latter condition is not strong
    // enough to guarantee that setting $v\gets v-u$ now (as in the
    // original binary algorithm) will make the algorithm converge.
    // Consider what happens if $u=-1$ and $v=1$, for example. One
    // solution suitable for use in a systolic array is to replace
    // $v$ by whichever of $w=(u+v)/2$ or $z=(u-v)/2$ is even. (Note
    // that $w$ and $z$ have different parity, because $z=w-v$ and
    // $v$ is odd.) To show that $\gcd(u,v)=\gcd(u,w)=\gcd(u,z)$,
    // observe that any (odd) common divisor of $u$ and $v$ is a
    // divisor of both $u+v$ and $u-v$, and hence of $w$ and $z$;
    // conversely, any common divisor of $u$ and $w$ (or $u$ and
    // $z$) is odd and must divide both $u$ and $v$. It remains to
    // prove that the algorithm always terminates: By the triangle
    // inequality and the fact that $d\le0$ (i.e., $p\le q$) after
    // the previous step, $w$ and $z$ are at most $(2^p+2^q)/2\le2^q$
    // in absolute value. The new value of $v$ is even, so the next
    // iteration of this loop will decrease $q$ by at least 1; it
    // follows by induction that $v$ eventually becomes zero.

    // Compute the average of $u$ and $v$ truncated towards zero,
    // using a popular formula from the book _Hacker's Delight_ by
    // H.~S.~Warren, Jr., 2nd edition (2012), Section 2.5. Since
    // $u$ and $v$ are odd, the correction term $(w\gg63)\&(u\oplus v)$
    // is zero; thus this is slightly faster than the built-in
    // `i64::midpoint` method.
    let w = (u & v) + ((u ^ v) >> 1);
    if w % 2 == 0 {
      v = w;
    } else {
      v = w - v; // $z$.
    }
    k_v = v.trailing_zeros();
  }
  // Now $v=0$, so the algorithm terminates with $|u|2^k$.
  u.unsigned_abs() << k
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
/// use gcds::harris;
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
  let k = (u | v).trailing_zeros();
  u >>= u.trailing_zeros();
  v >>= v.trailing_zeros();
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

#[cfg(test)]
mod tests {
  use super::*;

  fn test_methods<I>(cases: I)
  where
    I: IntoIterator<Item = ((u64, u64), u64)>,
  {
    let unsigned_methods: [fn(u64, u64) -> u64; _] =
      [euclid, binary_stein, binary_bonzini, binary_brent, harris];
    let signed_methods: [fn(i64, i64) -> u64; _] = [binary_brent_kung];
    for ((u, v), expected) in cases {
      for method in unsigned_methods {
        assert_eq!(method(u, v), expected, "gcd({u}, {v})");
      }
      let Ok(u) = u.try_into() else { continue };
      let Ok(v) = v.try_into() else { continue };
      for method in signed_methods {
        assert_eq!(method(u, v), expected, "gcd({u}, {v})");
      }
    }
  }

  #[test]
  fn small_numbers() {
    test_methods([
      ((0, 0), 0),
      ((0, 1), 1),
      ((1, 2), 1),
      ((1, 5), 1),
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
    ]);
  }

  #[test]
  fn mersenne_numbers() {
    // Use the fact that $\gcd(2^u-1,2^v-1)=2^{\gcd(u,v)}-1$
    // for nonnegative integers $u$ and $v$.
    let exps = 0..u64::BITS;
    test_methods(exps.clone().zip(exps).map(|(u, v)| {
      let gcd_u_v = euclid(u as u64, v as u64);
      (((1 << u) - 1, (1 << v) - 1), (1 << gcd_u_v) - 1)
    }));
  }

  #[test]
  fn extreme_cases() {
    const MAX_SIGNED: u64 = i64::MAX as u64;
    test_methods([
      ((0, MAX_SIGNED), MAX_SIGNED),
      ((0, u64::MAX), u64::MAX),
      ((1, MAX_SIGNED), 1),
      ((1, u64::MAX), 1),
      ((MAX_SIGNED, MAX_SIGNED - 2), 1),
      ((u64::MAX, u64::MAX - 2), 1),
      ((MAX_SIGNED, MAX_SIGNED), MAX_SIGNED),
      ((u64::MAX, u64::MAX), u64::MAX),
    ]);
  }

  #[test]
  fn random_nonnegative_pairs() {
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
