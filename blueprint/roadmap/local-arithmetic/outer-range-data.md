---
article_id: af_d6d819b199888798d6232c46
declaration: def
origin: cited
statement: formalized
lean: ZetaSeven.OuterRange ZetaSeven.rankCorr ZetaSeven.classDelta ZetaSeven.outerWeight ZetaSeven.outerWeightDbl ZetaSeven.classV ZetaSeven.classU ZetaSeven.classT ZetaSeven.gammaOut ZetaSeven.gammaOut_of_lt_two_mul ZetaSeven.gammaOut_of_two_mul_le ZetaSeven.gammaOut_of_K_lt ZetaSeven.rankCorr_cast ZetaSeven.outerWeightDbl_eq_two_mul ZetaSeven.classV_eq_mod
---

# Outer range data

Fix a prime `p`, and take the half-range `m` and the class counts
`ℓ_A(a)` from the local range data. For `1 ≤ a ≤ m` define the
class indicator `δ_a = 1` if `a ≤ N`, `δ_a = 0` otherwise. The
outer-range hypothesis (52) is the conjunction of `p ≥ 11`,
`K/3 < p ≤ K`, `p^2 > 2K`, and `7N ≤ 2p - 2`. The rank correction
(54) is `r_p = min(h, max(0, K + 6N - 3p + 4))`.

The outer weights (56): for a class `1 ≤ a ≤ m`, with
`ℓ = ℓ_K(a)` and `δ = δ_a`, and for `0 ≤ i < ℓ - δ`, put
`w^out_{a,i} = min(0, i + 4δ - (ℓ + 6)/2)` if `i < ℓ - 2` and
`w^out_{a,i} = 0` if `i ≥ ℓ - 2`.

Finally, (58) puts `v = K - p⌊K/p⌋`, `u = max(0, N + v - p + 1)`,
and `t_p = min(N, v) + u`. The outer exponent `γ^out_p` is defined
for every prime `p > K/3`, in two ranges. For `K/3 < p ≤ K` it is
(59):
`γ^out_p = -9(K - p) + 8t_p - 1 - min(r_p, p - 1 - N + u)` when
`K < 2p`, and
`γ^out_p = -9(K - p) + 3 + 16N + 7t_p - min(r_p, p + u)` when
`K ≥ 2p`; the outer estimates use this range under (52). For
`p > K` it is `γ^out_p = 0`. For `p ≤ K/3`, which the source
leaves unspecified, the formalization uses the `K ≥ 2p` formula.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)
- [Local range data](local-range-data.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, equations (52), (54), (56), and (58)-(59);
  Section 5.1, first sentence ("For `p > K`, put `γ^out_p = 0`"),
  for the value above `K`, which the normalization (60) and the
  outer limiting functions use.
