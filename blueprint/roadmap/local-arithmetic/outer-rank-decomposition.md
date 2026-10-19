---
article_id: af_99b09565a05d0763806d1c5f
declaration: theorem
origin: cited
---

# Outer rank decomposition

Let `p` be prime, take the matrices `A` and `L` of the outer
modified functional, and the rank correction `r_p` (54) of the
outer range data. Then `G_K = A + p^{-1} L`, `L` is an integer
matrix, and `rank_ℚ L ≤ r_p`.
Nothing is claimed about the integrality of `A`: the paper's (53)
asserts it, but it fails in the monomial basis, and the outer
estimate uses a weighted bound in the class basis instead.

The proof: `μ_X` and `μ_0` take the same values on the simple
poles, and `μ_X(t^e) = μ_0(t^e) + c_e/p` on monomials, so applying
both to `P_{ij} + ∑_a ρ_{ij,a}/(t + a^2)` gives
`G_K = A + p^{-1} L` entry by entry. Since `D_K` is monic in
`ℤ[t]`, the quotient `P_{ij}` has integer coefficients and degree
at most `i + j + 8N - K`; the `c_e` are integers, so `L` is an
integer matrix, and `L_{ij} = 0` when
`i + j < T = K - 8N + 3p - 4`, because `c_e = 0` for `e < 3p - 4`.
Row `i` of `L` vanishes when `i ≤ T - h`, so at most
`min(h, max(0, 2h - T))` rows are nonzero, and
`2h - T = K + 6N - 3p + 4` because `h = 37K/40`, `N = 3K/40`.
The proof uses nothing about the size of the moments `μ(t^e)`.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)
- [Outer range data](outer-range-data.md)
- [Outer modified functional](outer-modified-functional.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.1, equations (53)-(54) and the rank count between
  them. The statement drops (53)'s claim that `A` is integral at
  every prime, which is false as written (source-map erratum 1),
  makes explicit the integrality of `L` that Lemma 4.5 needs, and
  states it for every prime, since the decomposition and the rank
  count use nothing from (52).
