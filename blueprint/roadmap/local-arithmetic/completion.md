---
article_id: af_022a4d1c16225498b0b3eb00
declaration: theorem
origin: cited
---

# P-adic completion

Extend `τ` to the Tate algebra with norm bound `‖τ‖ ≤ p`, and
extend `τ_X` to the completed space with principal parts so that
the completed functional sends the normalized series
`∑ p^j U_j / T` into `ℤ_p[X]`.

The proof bounds the Bernoulli coefficients via von
Staudt-Clausen, decomposes each quotient by polynomial division
with `p`-unit denominators from the incongruence hypothesis, and
treats the `j = 0` term by the degree bound `p+4` and the `j ≥ 1`
terms by absorbing one lost `p`-power into `p^j`. The Tate-algebra
and Gauss-norm infrastructure is project work; no Tate algebra was
found in the pinned Mathlib checkout.

## Depends on

- [Tau pullback identity](tau-pullback.md)

## Proof depends on

- [Von Staudt-Clausen theorem](von-staudt-clausen.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 3.3, Lemmas 3.4-3.5, equations (32)-(33).
