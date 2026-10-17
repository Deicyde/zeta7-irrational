---
article_id: af_4a2ec29b35052df331a4836a
declaration: theorem
origin: background
not_ready: true
---

# Prime number theorem

The prime number theorem in the `θ(x) ~ x` form with partial
summation over primes, as needed to turn the local exponents
into the continuum integrals of the prime-sum bound. The pinned
Mathlib checkout has only Chebyshev upper and lower bounds
(`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge`), whose
constants do not give the exact limit constants the final
inequality needs.

This node is not ready because it needs a dependency-strategy
decision first: adopt or port the external PrimeNumberTheoremAnd
project, formalize the Wiener-Ikehara route, or restructure the
prime-sum argument to work with explicit Chebyshev bounds. That
decision is the largest open planning item in the roadmap.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Proposition 5.4.
