---
article_id: af_1323c9eb0db11af5ed48fd33
---

# Normalization and the prime sum

This chapter turns the local valuations into a global integrality
statement and a global growth bound. The explicit rational factor
m_K,M clears exactly the denominators the local estimates predict,
making Q_K,M an integer polynomial. Its logarithmic growth is then
bounded by a prime sum whose continuum limit splits into inner and
outer limiting integrals plus a tail integral with an explicit periodic
expansion.

The resulting prime-sum bound gives the arithmetic half of the final
exponent: `lim sup K^-2 log m_K,M <= A_M`. The exact rational margins
at the two cutoffs `M = 200` and `M = 100000`, evaluated through the
192-piece inner integral and the outer integrand tables, are what the
assembly chapter combines with the analytic bound. The paper's outer
integral (122) does not survive recomputation: with the recomputed
value `A_M + U` is positive at both cutoffs, so the final margins
cannot be proved as stated and the v1 route to the main theorem does
not close. The source notes record this (open question 5, errata 8-9),
and what to do about the margins is the user's decision.

## Normalization

- [Normalization and integrality](normalization-integrality.md) — the factor and integer coefficients.

## Continuum limits

- [Inner limiting functions](inner-limiting.md) — the inner continuum limit.
- [Outer limiting functions](outer-limiting.md) — the outer continuum limit.
- [Tail integral bound](tail-integral.md) — the periodic tail estimate.

## Exact certificates

- [Exact inner integral](exact-inner-integral.md) — the rational value of (121), through 131 affine pieces (erratum 12).
- [Exact outer integral](exact-outer-integral.md) — the 11-piece rational value, recomputed (erratum 9).

## Main estimate

- [Prime-sum bound](prime-sum-bound.md) — the arithmetic growth bound, with the constants `A_0`, `B_0`, `A_M`.
- [Final rational margins](final-margins.md) — the cutoff constants and the -19000 margin, which fails with the recomputed outer integral.

## Background

- [Prime number theorem](prime-number-theorem.md) — exact prime asymptotics via PrimeNumberTheoremAnd.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Sections 5.1-5.5 and the exact-integral appendix,
  Proposition 5.1 through Proposition 5.4.
