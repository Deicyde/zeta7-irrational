---
article_id: af_114fe5c7d5b4070a0cc154ea
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZetaSeven.outer_weight_sum ZetaSeven.outer_weight_sum_rat ZetaSeven.OuterRange.outer_weight_sum_eq_of_lt_two_mul ZetaSeven.OuterRange.outer_weight_sum_eq_of_two_mul_le ZetaSeven.OuterRange.sum_outerFamWeightDbl_of_lt_two_mul ZetaSeven.OuterRange.card_zero_outerFamWeightDbl_of_lt_two_mul ZetaSeven.OuterRange.sum_outerFamWeightDbl_of_two_mul_le ZetaSeven.OuterRange.card_zero_outerFamWeightDbl_of_two_mul_le ZetaSeven.OuterRange.three_mul_N_lt ZetaSeven.OuterRange.ell_N_eq_classDelta ZetaSeven.OuterRange.ell_K_eq ZetaSeven.OuterRange.ell_K_le_six ZetaSeven.OuterRange.sum_ell_K_sub_two ZetaSeven.sum_outerWeightDbl_delta_zero ZetaSeven.card_zero_outerWeightDbl_delta_zero ZetaSeven.sum_outerWeightDbl_delta_one ZetaSeven.card_zero_outerWeightDbl_delta_one
---

# Outer weight sum

Let `p` satisfy the outer-range hypothesis (52). Take from the
outer range data the rank correction `r_p` and the outer exponent
`γ^out_p`, and let `w` be the outer weight family (the outer
weights (56) on the class pairs and the zero-class weights on the
zero-class pairs). Let `z` be the number of zero weights in the
family.
Then `2 ∑ w - min(r_p, z) ≥ γ^out_p`.

The proof counts by classes. Under (52), `N < p/3`, so the only
`j ≤ N` in class `a` is `a` itself when `δ = 1`, and
`ℓ_K(a) ≤ 6`. A class with `δ = 0` has all weights below
`ℓ - 2` negative, contributing `-9(ℓ - 2)` to `2∑w` and two
zeros. A class with `δ = 1` contributes `0, -1, -2, -4, -6` for
`ℓ = 2, …, 6`, and `1, 1, 2, 2, 3` zeros. Since
`∑_a (ℓ_K(a) - 2) = K - ⌊K/p⌋ - (p - 1)`, and for `a ≤ N` the
count `ℓ_K(a)` is the base value (2 when `K < 2p`, 4 when
`K ≥ 2p`) plus one if `a ≤ v` and one more if `a ≥ p - v`, one
gets `2∑w = -9(K - p) + 8t_p - 1` and `z = p - 1 - N + u` when
`K < 2p`, and `2∑w = -9(K - p) + 6 + 16N + 7t_p` and `z = p + u`
when `K ≥ 2p`. So the bound holds with equality when `K < 2p`
and with a margin of 3 when `K ≥ 2p`. The formalization proves the
closed form of `ℓ_K(a)` for every class `1 ≤ a ≤ m`.

## Depends on

- [Outer range data](outer-range-data.md)
- [Outer weight family](outer-weight-family.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.3, equations (56)-(59), and the sentence "Applying
  Lemma 4.5 to the weights (56) and summing over classes yields
  `γ^out_p`" at the end of the second paragraph of the proof of
  Proposition 4.6. The paper gives (59) through
  removed-class costs (57) without the derivation; this statement
  is reconstructed by this project, because the paper defers the
  weight count to its zeta(5) predecessor [5].
