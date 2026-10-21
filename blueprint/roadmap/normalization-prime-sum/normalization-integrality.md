---
article_id: af_a256539d38585e17f839fc5d
declaration: theorem
origin: cited
lean: ZetaSeven.normalization_integrality ZetaSeven.padicValRat_QKM_nonneg ZetaSeven.padicValRat_SK_legendre ZetaSeven.mKM_pos ZetaSeven.outerRange_of_K_lt_three_mul ZetaSeven.padicValRat_mKM ZetaSeven.padicValRat_SK_of_lt ZetaSeven.innerExtraRows_spec ZetaSeven.QKM_eq ZetaSeven.LpKM_of_le ZetaSeven.LpKM_of_inner ZetaSeven.LpKM_of_outer ZetaSeven.LpKM ZetaSeven.mKM ZetaSeven.QKM ZetaSeven.innerExtraRows
---

# Normalization and integrality

Define the branch exponents `L_p(K,M)` from the inner exponent
`γ^in_p`, the outer exponent `γ^out_p` of the outer range data
((59) for `K/3 < p ≤ K`, and `0` for `p > K`), and the crude
bound, the positive rational normalization factor `m_{K,M}` as the
product of `p^{-L_p}` over `p ≤ 2h`, and the final polynomial
`Q_{K,M} = m_{K,M} F_K`. Then `Q_{K,M}` has integer coefficients.

The proof checks `v_p(Q_{K,M}) ≥ 0` prime by prime: each of
the three branches cancels by construction against its local
estimate, and primes above `2h` are units throughout. In the outer
branch `3p > K`, a prime `p ≤ K` satisfies (52) because
`K ≥ 200M^2 ≥ 320000`, so the outer range estimate gives
`v^G_p(Δ_K) ≥ γ^out_p`; a prime `K < p ≤ 2h` has `γ^out_p = 0`,
and the large-prime clause of the outer range estimate gives
`v^G_p(Δ_K) ≥ 0`. The Legendre-formula expression for `v_p(S_K)`
is part of this node.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)
- [Inner range estimate](../local-arithmetic/inner-estimate.md)
- [Outer range data](../local-arithmetic/outer-range-data.md)
- [Small-prime estimate](../local-arithmetic/small-prime-estimate.md)

## Proof depends on

- [Outer range estimate](../local-arithmetic/outer-estimate.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 5.1, Proposition 5.1, equations (60)-(63), and the first
  sentence of Section 5.1, which puts `γ^out_p = 0` for `p > K`.
