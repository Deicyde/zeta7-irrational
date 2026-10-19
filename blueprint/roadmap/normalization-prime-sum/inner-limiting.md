---
article_id: af_e49fc36fca2bd5d52dd8dcd4
declaration: def
origin: cited
statement: formalized
lean: ZetaSeven.innerGamma ZetaSeven.innerN ZetaSeven.innerR ZetaSeven.gammaIn_approx ZetaSeven.padicValRat_SK_approx ZetaSeven.innerJ ZetaSeven.gammaIntegrand ZetaSeven.ellLim ZetaSeven.bLim ZetaSeven.TLim ZetaSeven.sLim ZetaSeven.qLim ZetaSeven.nPlus ZetaSeven.gammaIntegrand_intervalIntegrable ZetaSeven.ell_eq_ellLim ZetaSeven.padicValRat_SK ZetaSeven.innerJ_sum_bounds
---

# Inner limiting functions

Define the continuum-limit functions `Γ`, `N`, and `R = -Γ - N`
in the variable `x = K/p`, and prove the uniform approximations
`γ^in_p = pΓ(K/p) + O_M(1)` and `v_p(S_K) = pN(K/p) + O_M(1)`
in the inner range.
The Lean definitions are total in `x` and `z`; the approximations
use them only at `x = K/p` with `3 ≤ x < M`.

The proof matches grid counts to interval lengths for the
weight sums and applies the Legendre formula with the `J`
correction for the factorial contribution.

## Depends on

- [Inner range estimate](../local-arithmetic/inner-estimate.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 5.2, equations (64)-(70).
