---
article_id: af_c332421df16f169adfc697b3
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZetaSeven.hurwitzZeta7_eq_hermite_integral ZetaSeven.integrableOn_hermite_integrand ZetaSeven.summable_hurwitzZeta7 ZetaSeven.hurwitzZeta7
---

# Hermite integral for Hurwitz zeta

Hermite's integral formula for the Hurwitz zeta function at `s = 7`
(DLMF 25.11.29), used to evaluate the pole integrals against the
weight. No matching statement was found in the pinned Mathlib
checkout, so this is project work: either prove the `s = 7` instance
directly or bridge from a general Hurwitz-zeta integral if one is
located during the Mathlib audit.
The Lean statement is for real `a > 0`, with
`ζ(7, a) = ∑_{n ≥ 0} (n + a)^{-7}`, which is the case Proposition 2.4
uses (`a = j` a positive integer); the paper states it for `Re a > 0`.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Proposition 2.4, equation (19).
