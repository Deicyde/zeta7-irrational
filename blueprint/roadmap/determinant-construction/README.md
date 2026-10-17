---
article_id: af_ba33a6c5e3ae7ac76585c672
---

# Determinant construction

This chapter builds the polynomials whose values at zeta(7) drive the
irrationality proof. For parameters `K = 40n`, `N = 3n`, `h = 37n`, a
rational functional mu_X on rational functions with simple poles among
the negative integer squares feeds an `h x h` Hankel-type matrix G_K(X);
its determinant Delta_K(X), after the explicit scalar normalization S_K
and the rational factor m_K,M, becomes the integer polynomial Q_K,M.

Two facts proved here shape everything downstream. The degree
calculation shows Delta_K has degree exactly h with an explicit
nonzero leading coefficient, so Q_K,M is genuinely of growing degree.
The positive integral representation identifies mu at X = zeta(7) with
integration against an explicit positive weight, which makes
G_K(zeta(7)) a positive definite Gram matrix and hence forces
Q_K,M(zeta(7)) > 0. The chapter's contract is the main-estimates
statement: integrality, degree, positivity, and the two decay bounds.

## Definitions

- [Functional mu](functional-mu.md) — parameters and the functional.
- [Matrix and determinant](matrix-determinant.md) — the matrix and its normalizations.

## Main results

- [Degree lemma](degree-lemma.md) — exact degree and leading coefficient.
- [Positive integral representation](positive-integral-representation.md) — the weight and Gram positivity.

## Background

- [Vandermonde determinant](vandermonde-det.md) — upstream matrix identity.
- [Euler formula for even zeta values](euler-even-zeta.md) — even moments.
- [Hermite integral for Hurwitz zeta](hermite-hurwitz.md) — pole evaluation.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Sections 2.1-2.6, Definition 2.1 through Theorem 2.5.
