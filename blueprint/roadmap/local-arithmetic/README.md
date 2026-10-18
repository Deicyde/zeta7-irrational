---
article_id: af_39cc603be5dddc97d2cc885b
---

# Local arithmetic estimates

This chapter controls the denominators of the determinant one prime at
a time. An auxiliary functional tau_X reproduces mu_X through a
pullback identity, and its p-adic completion to the Tate algebra lets
each local determinant valuation be bounded with X kept indeterminate,
so one estimate covers every coefficient. A distribution formula by
residue class handles large primes, while a separate small-prime bound
plus an integer-valued change of basis covers the rest.

The payoff is two determinant valuations: an inner-range estimate from
a basis with prescribed vanishing at the pole classes, and an
outer-range estimate that isolates the residue terms from a polynomial
correction via a rank lemma. Together they feed the normalization
factor of the next chapter.

The paper's outer-range proof defers its basis, weights, and weight
count to the zeta(5) predecessor, and its claim (53) that the
corrected matrix is integral is false as written. The outer range is
therefore assembled from reconstructed steps: the rank decomposition,
a class basis adapted to the residue classes, weighted entry
valuations in that basis, a Gauss-valuation form of the rank lemma,
and the weight count that yields the exponent (59).

## Local functional

- [Tau pullback identity](tau-pullback.md) — the auxiliary functional and pullback.
- [Reflection and difference identities](reflection-difference.md) — the two functional identities.
- [P-adic completion](completion.md) — extension to the Tate algebra.
- [Distribution formula](distribution-formula.md) — averaging over residue classes.

## Estimates

- [Small-prime estimate](small-prime-estimate.md) — the crude global bound and integer-valued basis.
- [Inner range estimate](inner-estimate.md) — determinant valuations in the inner range.

## Outer range

- [Outer range data](outer-range-data.md) — class counts, the outer-range hypothesis, the rank correction, the weights, and the exponent (59).
- [Outer moment integrality](outer-moment-integrality.md) — the polynomial moments are integral below `3p - 4`.
- [Outer rank decomposition](outer-rank-decomposition.md) — the low-rank correction.
- [Large-prime integrality](large-prime-integrality.md) — the determinant is integral above `K`.
- [Outer class basis](outer-class-basis.md) — the unimodular basis adapted to residue classes.
- [Outer entry valuations](outer-entry-valuations.md) — weighted valuations of the class Gram matrix.
- [Rank lemma](rank-lemma.md) — determinant bound under a low-rank correction.
- [Gauss-valuation rank lemma](gauss-rank-lemma.md) — the same bound for polynomial entries.
- [Outer weight sum](outer-weight-sum.md) — the weight count giving the exponent.
- [Outer range estimate](outer-estimate.md) — determinant valuations in the outer range.

## Background

- [Von Staudt-Clausen theorem](von-staudt-clausen.md) — upstream Bernoulli denominators.
- [Bernoulli multiplication formula](bernoulli-multiplication.md) — distribution over residue classes.
- [Integer-valued polynomial estimates](integer-valued-estimates.md) — predecessor-adapted bounds.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Sections 3.1-3.5 and 4.1-4.2, Lemmas 3.1-3.8 and
  Propositions 4.4-4.6. The bridged outer-range nodes reconstruct
  the steps the paper defers to its zeta(5) predecessor [5].
