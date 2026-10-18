---
article_id: af_ad1ec8a1c04c5d41f0121260
declaration: lemma
origin: bridged
---

# Gauss-valuation rank lemma

Let `A` be an `h × h` matrix with entries in `ℚ[X]` and `L` an
`h × h` matrix with entries in `ℚ`. Write `v^G_p` for the minimum
of the `p`-adic valuations of the coefficients of a polynomial,
with `v^G_p(0) = +∞`. Suppose `v^G_p(A_{ij}) ≥ w_i + w_j` for
nonpositive half-integers `w_i`, that `L` is `p`-integral with
`rank_ℚ L ≤ r`, and that exactly `z` of the weights are zero.
Then `v^G_p det(A + p^{-1} L) ≥ 2 ∑_i w_i - min(r, z)`.

The proof reduces to the rational rank lemma coefficient by
coefficient. Write row `i` of `A + p^{-1} L` as
`(A_{0,i} + p^{-1} L_i) + ∑_{k ≥ 1} X^k A_{k,i}`, where `A_k` is
the matrix of `X^k`-coefficients of `A`, and expand the
determinant multilinearly in the rows. For each choice
`f(i) ∈ {0, 1, 2, …}` of a summand in every row, the term is
`X^{∑ f(i)} det(B_f + p^{-1} L_f)`, where row `i` of `B_f` is row
`i` of `A_{f(i)}` and `L_f` is `L` with the rows having `f(i) ≥ 1`
replaced by zero. Each `B_f` satisfies
`v_p((B_f)_{ij}) ≥ w_i + w_j` and each `L_f` is `p`-integral of
rank at most `r`, so the rational rank lemma bounds every term,
and hence every coefficient of the determinant, below by
`2 ∑_i w_i - min(r, z)`.

## Depends on

None. Self-contained linear algebra.

## Proof depends on

- [Rank lemma](rank-lemma.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.2, Lemma 4.5, last sentence ("The same assertion
  holds for the Gauss valuation of polynomial entries"). The paper
  gives no proof or precise form of this extension; this statement
  is reconstructed by this project, because the paper defers the
  outer-range argument that uses it to its zeta(5) predecessor [5].
