---
article_id: af_50ee1de0b9f751e16ee0e8e3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.tau_reflection ZetaSeven.tau_difference ZetaSeven.tauPoly_reflection ZetaSeven.tauPoly_difference ZetaSeven.bernoulliL_X_add_one_pow_sub ZetaSeven.bernoulliL_comp_X_add_one_sub ZetaSeven.bernoulli_eval_one_eq ZetaSeven.bernoulliL_X_add_one_pow_eq_eval_one ZetaSeven.tauFunctional_reflect ZetaSeven.tauFunctional_difference ZetaSeven.ratFuncReflect ZetaSeven.ratFuncShift ZetaSeven.ratFuncReflect_algebraMap ZetaSeven.ratFuncShift_algebraMap ZetaSeven.reflectPoles ZetaSeven.shiftPoles ZetaSeven.ratFuncReflect_tauRatFunc ZetaSeven.ratFuncShift_tauRatFunc ZetaSeven.laurent_tauRatFunc_coeff_six ZetaSeven.laurent_iterate_derivative_six_coeff_zero
---

# Reflection and difference identities

The functional `τ_X` satisfies the reflection identity
`τ_X(g(-1-x)) = -τ_X(g(x))` and the difference identity
`τ_X(g(x+1) - g(x)) = g^{(6)}(0)/720`, the latter extended to
rational functions with simple integer poles regular at zero.
The Lean statement reads `g^{(6)}(0)` as the constant coefficient of
the sixth derivative of the Laurent expansion of `g` at zero, which is
the same number when `g` is regular at zero, and drops that hypothesis
because a pole `1/x` contributes zero to both sides.

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
