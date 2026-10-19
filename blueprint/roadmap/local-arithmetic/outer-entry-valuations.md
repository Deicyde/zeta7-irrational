---
article_id: af_3bb165f2f6c999e3be14ab74
declaration: theorem
origin: bridged
---

# Outer entry valuations

Let `p` satisfy the outer-range hypothesis (52), take the outer
class rows and the modified functional `μ_0` of the outer modified
functional, and give each row the weight `w_r` of its index in the
outer weight family: the outer weight `w^out_{c,i}` (56) to the
class row `P_c q_{c,i}`, and the zero-class weight `w^out_{0,i}` to
the zero-class row `P_0 t^i`. For two rows `r`, `s` put
`A'_{rs} = μ_0(r(t) s(t) D_N(t)^7 / D_tail(t))`, a polynomial of
degree at most one in `X`, where `D_tail = D_K/D_N`. Then every
entry satisfies `v^G_p(A'_{rs}) ≥ w_r + w_s`.

The proof: by the outer moment integrality, `μ_0` is `p`-integral
on monomials, since `c_e = 0` and `μ(t^e)` is `p`-integral for
`e < 3p - 4`, while for larger `e` the number `p μ(t^e)` is
`p`-integral and congruent to `c_e` modulo `p`; so `μ_0` of an
integer polynomial is `p`-integral. For rows of different classes,
`r s` is divisible by `D_tail`, so `A'_{rs}` is `μ_0` of an integer
polynomial and is `p`-integral. For two rows of class `c`, with
`ℓ = ℓ_K(c)` and `δ = δ_c`, the poles are the `-b^2` with
`b ∈ S_c`, a set of `ℓ - δ` elements under (52); the factor
`P_c(-b^2)` is a `p`-unit, and each factor `b'^2 - b^2` of the
derivative of `F_c` has valuation exactly one because
`b + b' ≤ 2K < p^2`. If either row index is at least `ℓ - 2`, the
factor `E_c` cancels the poles with `b > p`, which leaves an
integer polynomial over `t + (p - c)^2` when `δ = 1` and over
`(t + c^2)(t + (p - c)^2)` when `δ = 0`. A lone pole `p - c` has
a `p`-integral residue and pole value, and the pair `c`, `p - c`
contributes a `p`-integral amount by the paired-pole congruence,
so the entry is `p`-integral. If both row indices `i`, `j`
are below `ℓ - 2`, the residue at `b ∈ S_c` has valuation at
least `(i + j) + 7δ - (ℓ - δ - 1)`, from `(t + c^2)^{i+j}`, from
the factor `t + c^2` of `D_N` when `δ = 1`, and from the
derivative of `F_c`; the pole value
`b^6 (X - H^(7)_b) + 1/(2b) - 1/6` has valuation at least `-7`,
and the polynomial part is `p`-integral, so the entry has
valuation at least `min(0, i + j + 8δ - ℓ - 6)`, which is at least
`w^out_{c,i} + w^out_{c,j}` because
`min(0, x) + min(0, y) ≤ min(0, x + y)`. For two zero-class rows,
the poles are `-(kp)^2` with `1 ≤ k ≤ ⌊K/p⌋`, the pole values have
valuation at least `-1`, and the residues of
`P_0 t^{i+j} D_N^7 / F_0` have valuation at least `2(i + j)` when
`K < 2p` and `2(i + j) - 2` when `K ≥ 2p`, so these entries have
valuation at least `min(0, 2(i + j) - 1)`, respectively
`min(0, 2(i + j) - 3)`, which is at least the sum of the two
zero-class weights. Every weight is at most `0`, so the
`p`-integral entries also satisfy `v^G_p(A'_{rs}) ≥ w_r + w_s`.

## Depends on

- [Outer range data](outer-range-data.md)
- [Outer class rows](outer-class-rows.md)
- [Outer weight family](outer-weight-family.md)
- [Outer modified functional](outer-modified-functional.md)

## Proof depends on

- [Outer moment integrality](outer-moment-integrality.md)
- [Paired-pole congruence](paired-pole-congruence.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, equation (56) and the proof of Proposition 4.6.
  The paper states the residue bound `i + j + 8δ - ℓ - 6` and
  the outer weights, but not the zero-class weights, which the
  outer weight family reconstructs; this statement is reconstructed
  by this project, because the paper defers the weighted bound to
  its zeta(5) predecessor [5].
