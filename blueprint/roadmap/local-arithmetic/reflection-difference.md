---
article_id: af_50ee1de0b9f751e16ee0e8e3
declaration: theorem
origin: cited
---

# Reflection and difference identities

The functional `τ_X` satisfies the reflection identity
`τ_X(g(-1-x)) = -τ_X(g(x))` and the difference identity
`τ_X(g(x+1) - g(x)) = g^{(6)}(0)/720`, the latter extended to
rational functions with simple integer poles regular at zero.

Both proofs reduce to monomials plus Bernoulli-polynomial endpoint
values (`B_n(1) = B_n` for `n ≠ 1`, with the `k = 6` case computed
directly). The pinned Mathlib checkout has adjacent endpoint
identities for `bernoulliFun`
(`bernoulliFun_endpoints_eq_of_ne_one`, `bernoulliFun_eval_one`);
bridging them to the polynomial form over `ℚ` is part of this node.

## Depends on

- [Tau pullback identity](tau-pullback.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 3.2, Lemmas 3.2-3.3, equations (29)-(31).
