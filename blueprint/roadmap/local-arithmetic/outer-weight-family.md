---
article_id: af_d2c5f969d1b551fbd6d91119
declaration: def
origin: bridged
---

# Outer weight family

Fix a prime `p`, and take `m` and the class counts `ℓ_K(c)` of the
local range data, and the class indicators `δ_c` and the outer
weights `w^out_{c,i}` (56) from the outer range data. The
zero-class weights are `w^out_{0,0} = -1/2` when `K < 2p`,
`w^out_{0,0} = -3/2` when `K ≥ 2p`, and `w^out_{0,i} = 0` for
`i ≥ 1`.

The outer weight family is indexed by the class pairs `(c, i)`
with `1 ≤ c ≤ m` and `0 ≤ i < ℓ_K(c) - δ_c`, and by the zero-class
pairs `(0, i)` with `0 ≤ i < ⌊K/p⌋`. It gives the class pair
`(c, i)` the outer weight `w^out_{c,i}` and the zero-class pair
`(0, i)` the zero-class weight `w^out_{0,i}`.

Remarks, which the consuming theorems discharge where they use
them: under the outer-range hypothesis (52), `K/3 < p ≤ K`, so
`⌊K/p⌋` is 1 when `K < 2p` and 2 when `K ≥ 2p`, and the zero class
carries the weight `-1/2`, respectively the weights `-3/2, 0`.
Every weight is a nonpositive half-integer: the outer range
estimate needs this to apply the Gauss-valuation rank lemma, and
the outer entry valuations use that the weights are at most `0`.

## Depends on

- [Outer range data](outer-range-data.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, equation (56), and the proof of Proposition 4.6,
  which applies Lemma 4.5 "to the weights (56)". The paper gives no
  weights for the zero-class rows; the zero-class weights and this
  indexing are reconstructed by this project, because the paper
  defers the basis to its zeta(5) predecessor [5]. The zero-class
  weights were found by computation and checked with the outer
  entry valuations.
