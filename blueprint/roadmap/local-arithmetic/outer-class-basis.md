---
article_id: af_8d3f5d5d03fde3635f1c4e3f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZetaSeven.outer_class_basis ZetaSeven.OuterRange.card_outerIdx_eq_hDim ZetaSeven.OuterRange.natDegree_outerRow_lt ZetaSeven.OuterRange.outerRow_unimodular ZetaSeven.OuterRange.card_outerClassSet_of_ne_zero ZetaSeven.OuterRange.card_outerClassSet_zero ZetaSeven.OuterRange.card_outerClassSet ZetaSeven.OuterRange.sum_card_outerClassSet ZetaSeven.OuterRange.card_filter_outerClassSet_add_two ZetaSeven.OuterRange.natDegree_outerQ ZetaSeven.OuterRange.natDegree_outerRowPoly ZetaSeven.map_outerClassPoly ZetaSeven.map_outerHighPoly ZetaSeven.map_outerCofactor ZetaSeven.OuterRange.map_outerQ ZetaSeven.OuterRange.map_outerRowPoly ZetaSeven.OuterRange.linearIndependent_map_outerRow ZetaSeven.OuterRange.det_map_outerRow_ne_zero
---

# Outer class basis

Let `p` satisfy the outer-range hypothesis (52). The outer class
rows are exactly `h` integer polynomials of degree less than `h`,
and the integer matrix `U` expressing them in the monomial basis
`1, t, …, t^{h-1}` has `det U` prime to `p`; so they form a
`ℤ_p`-unimodular basis of the polynomials of degree less than `h`.

The proof: under (52), `N < p/3`, so for `1 ≤ c ≤ m` the only
`j ≤ N` congruent to `±c` modulo `p` is `c` itself when `δ_c = 1`,
which gives `|S_c| = ℓ_K(c) - δ_c`, and `|S_0| = ⌊K/p⌋`. So the
rows at the class pairs `(c, i)` and the zero-class pairs `(0, i)`
number `∑_{0 ≤ c ≤ m} |S_c|`; every `j ∈ (N, K]` lies in exactly
one `S_c`, so this is `K - N = h`. The elements of `S_c` at most
`p` are `p - c` and, when `δ_c = 0`, `c`, so `E_c` has degree
`ℓ_K(c) - 2`, and `deg P_c q_{c,i} = h - |S_c| + i < h`, and
likewise `deg P_0 t^i < h`. Modulo `p`, `F_c ≡ (t + c^2)^{|S_c|}`
and `E_c ≡ (t + c^2)^{ℓ - 2}`, so the class-`c` rows reduce to
`∏_{d ≠ c} (t + d^2)^{|S_d|} · (t + c^2)^i`. The factors `t + d^2`,
`0 ≤ d ≤ m`, are pairwise coprime in `𝔽_p[t]`, and in the Chinese
remainder decomposition of `𝔽_p[t]_{<h}` by their powers the
reduced rows are triangular with unit diagonal, hence an
`𝔽_p`-basis.

## Depends on

- [Outer range data](outer-range-data.md)
- [Outer class rows](outer-class-rows.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, proof of Proposition 4.6: "Together with the
  zero-class rows, these form a `ℤ_p`-unimodular basis." The paper
  gives no proof; this statement and its proof are reconstructed
  by this project, because the paper defers the basis to its
  zeta(5) predecessor [5].
