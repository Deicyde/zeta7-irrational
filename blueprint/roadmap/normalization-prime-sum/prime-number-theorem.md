---
article_id: af_4a2ec29b35052df331a4836a
declaration: theorem
origin: background
---

# Prime number theorem

The prime number theorem in the `θ(x) ~ x` form, with the
partial-summation step that turns it into prime Riemann sums:
for `0 < a < b` and a piecewise continuous weight `G` with
finitely many breakpoints on `[a, b]`,
`X^{-1} ∑_{aX < p ≤ bX} G(p/X) log p → ∫_a^b G(y) dy` as
`X → ∞`. Proposition 5.4 uses the plain form in the middle prime
range and the Riemann-sum form for the inner and outer integrals.

The asymptotic comes from the pinned PrimeNumberTheoremAnd
dependency (rev `c39a751`): `chebyshev_asymptotic : θ ~[atTop] id`
in `PrimeNumberTheoremAnd/Consequences.lean`, stated for Mathlib's
`Chebyshev.theta`. The partial-summation step is project work;
Mathlib's Abel summation (`sum_mul_eq_sub_integral_mul`) handles
each smooth piece of the weight. No ZetaSeven module imports
PrimeNumberTheoremAnd yet. The pinned Mathlib alone has only the
Chebyshev bounds `Chebyshev.theta_le_log4_mul_x` and
`Chebyshev.theta_ge`, too weak for the exact limit constants.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Proposition 5.4.
