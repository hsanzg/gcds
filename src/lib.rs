// The following doc comment is kept in sync with the `README.md` file.
// Please run `cargo sync-readme` after modifying the comment contents.
//! This crate implements several algorithms for finding the greatest
//! common divisor of two single-precision numbers.
//!
//! The _greatest common divisor_ $\gcd(u,v)$ of two integers $u$ and $v$,
//! not both zero, is the largest integer that evenly divides them both.
//! (By convention we let $\gcd(0,0)=0$.)
//#![no_std]

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

#[must_use]
pub const fn binary_stein(mut u: u64, mut v: u64) -> u64 {
  todo!()
}

/// Computes the greatest common divisor of $u$ and $v$ using the binary
/// gcd algorithm of R. P. Brent [[_"Further analysis of the Binary Euclidean algorithm,"_][brent]
/// Technical Report PRG TR-7-99 (Oxford Univ. Computing Laboratory, 1999)].
///
/// # Examples
/// ```
/// use gcd::binary_brent;
///
/// assert_eq!(binary_brent(0, 0), 0);
/// assert_eq!(binary_brent(0, 3), 3);
/// assert_eq!(binary_brent(1, 1), 1);
/// assert_eq!(binary_brent(5, 1), 1);
/// assert_eq!(binary_brent(114, 551), 19);
/// assert_eq!(binary_brent(1992, 581), 83);
/// assert_eq!(binary_brent(51041, 18017), 43);
/// assert_eq!(binary_brent(u64::MAX, u64::MAX - 1), 1);
/// assert_eq!(binary_brent(u64::MAX, u64::MAX), u64::MAX);
///
/// // Find the gcd of two signed numbers.
/// assert_eq!(binary_brent(36, (-48i64).unsigned_abs()), 12);
/// ```
///
/// [brent]: https://maths-people.anu.edu.au/~brent/pd/rpb183tr.pdf
#[must_use]
pub fn binary_brent(mut u: u64, mut v: u64) -> u64 {
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

#[must_use]
pub const fn harris(mut u: u64, mut v: u64) -> u64 {
  todo!()
}

#[must_use]
pub fn binary_brent_kung(mut u: u64, mut v: u64) -> u64 {
  todo!()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn gcd() {
    let test_pairs = [
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
    ];
    let methods = [euclid, binary_brent];
    for ((u, v), expected) in test_pairs {
      for method in methods {
        assert_eq!(method(u, v), expected);
        assert_eq!(method(v, u), expected);
      }
    }
  }

  #[test]
  fn check_binary() {
    let gcd = binary_brent(40902, 24140);
    println!("gcd={gcd}");
  }
}
