---
article_id: af_114fe5c7d5b4070a0cc154ea
declaration: theorem
origin: bridged
---

# Outer weight sum

Assume (52) and put `m = (p-1)/2`. For each class `1 ≤ a ≤ m`
with `ℓ = ℓ_K(a)` and `δ = 1_{a ≤ N}`, take the `ℓ - δ` outer
weights (56), `w^out_{a,i} = min(0, i + 4δ - (ℓ + 6)/2)` for
`i < ℓ - 2` and `0` for `ℓ - 2 ≤ i < ℓ - δ`; add the zero-class
weight `-1/2` when `K < 2p`, or the two zero-class weights `-3/2`
and `0` when `K ≥ 2p`. This gives `h` weights. Let `z` be the
number of zero weights, `r_p = min(h, max(0, K + 6N - 3p + 4))`,
`v = K - p⌊K/p⌋`, `u = max(0, N + v - p + 1)`,
`t_p = min(N, v) + u`, and let `γ^out_p` be given by (59):
`-9(K - p) + 8t_p - 1 - min(r_p, p - 1 - N + u)` when `K < 2p`,
and `-9(K - p) + 3 + 16N + 7t_p - min(r_p, p + u)` when `K ≥ 2p`.
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
and with a margin of 3 when `K ≥ 2p`.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.3, equations (56)-(59), and the last sentence of
  the proof of Proposition 4.6. The paper gives (59) through
  removed-class costs (57) without the derivation; this statement
  is reconstructed by this project, because the paper defers the
  weight count to its zeta(5) predecessor [5].
