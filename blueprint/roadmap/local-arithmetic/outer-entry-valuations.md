---
article_id: af_3bb165f2f6c999e3be14ab74
declaration: theorem
origin: bridged
---

# Outer entry valuations

Let `p` satisfy the outer-range hypothesis (52), take the class
rows and zero-class rows of the outer class basis, and let `μ_0`
be the modified functional of the rank decomposition. For two rows
`r`, `s` put `A'_{rs} = μ_0(r(t) s(t) D_N(t)^7 / D_tail(t))`, a
polynomial of degree at most one in `X`, where
`D_tail = D_K/D_N`. Give the class row `P_c q_{c,i}` the outer
weight `w^out_{c,i}` (56) and the zero-class row `P_0 t^i` the
zero-class weight `w^out_{0,i}`, both from the outer range data.
Then every entry satisfies `v^G_p(A'_{rs}) ≥ w_r + w_s`.

The proof: for rows of different classes, `r s` is divisible by
`D_tail`, so `A'_{rs}` is `μ_0` of an integer polynomial and is
`p`-integral. For two rows of class `c`, with `ℓ = ℓ_K(c)` and
`δ = δ_c`, the poles are the
`-j^2` with `j ∈ S_c`, the factor `P_c(-j^2)` is a `p`-unit, and
each factor `j'^2 - j^2` of the derivative of `F_c` has
valuation exactly one because `j + j' ≤ 2K < p^2`. If either row
index is at least `ℓ - 2`, the factor `E_c` cancels the poles
with `j > p`; the remaining poles `c` (when `δ = 0`) and `p - c`
have `p`-integral pole values that are congruent modulo `p`, and
their residues have `p`-integral sum, so the entry is
`p`-integral. If both indices `i`, `j` are below `ℓ - 2`, the
residue at `j' ∈ S_c` has valuation at least
`(i + j) + 7δ - (ℓ - δ - 1)`, from `(t + c^2)^{i+j}`, from the
factor `t + c^2` of `D_N` when `δ = 1`, and from the derivative
of `F_c`; the pole value `j'^6 (X - H^(7)_{j'}) + 1/(2j') - 1/6`
has valuation at least `-7`, so the entry has valuation at least
`i + j + 8δ - ℓ - 6 ≥ w^out_{c,i} + w^out_{c,j}`. For two
zero-class rows, the poles are `-(kp)^2` with `1 ≤ k ≤ ⌊K/p⌋`,
the pole values have valuation at least `-1`, and the residues
of `P_0 t^{i+j} D_N^7 / F_0` have valuation at least `2(i + j)`
when `K < 2p` and `2(i + j) - 2` when `K ≥ 2p`, so these entries
have valuation at least `2(i + j) - 1`, respectively
`2(i + j) - 3`, which the zero-class weights allow.

## Depends on

- [Outer range data](outer-range-data.md)
- [Outer class basis](outer-class-basis.md)
- [Outer rank decomposition](outer-rank-decomposition.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, equation (56) and the proof of Proposition 4.6.
  The paper states the residue bound `i + j + 8δ - ℓ - 6` and
  the outer weights, but not the zero-class weights; this
  statement is reconstructed by this project, because the paper
  defers the weighted bound to its zeta(5) predecessor [5].
