---
article_id: af_d6d819b199888798d6232c46
declaration: def
origin: cited
---

# Outer range data

Fix a prime `p` and put `m = (p-1)/2`. For `A ≥ 0` and
`1 ≤ a ≤ m` define the class count (43)
`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ a or j ≡ -a (mod p)}`, and the class
indicator `δ_a = 1` if `a ≤ N`, `δ_a = 0` otherwise. The
outer-range hypothesis (52) is the conjunction of `p ≥ 11`,
`K/3 < p ≤ K`, `p^2 > 2K`, and `7N ≤ 2p - 2`. The rank correction
(54) is `r_p = min(h, max(0, K + 6N - 3p + 4))`.

The outer weights (56): for a class `1 ≤ a ≤ m`, with
`ℓ = ℓ_K(a)` and `δ = δ_a`, and for `0 ≤ i < ℓ - δ`, put
`w^out_{a,i} = min(0, i + 4δ - (ℓ + 6)/2)` if `i < ℓ - 2` and
`w^out_{a,i} = 0` if `i ≥ ℓ - 2`.

Finally, (58) puts `v = K - p⌊K/p⌋`, `u = max(0, N + v - p + 1)`,
and `t_p = min(N, v) + u`, and (59) defines the outer exponent
`γ^out_p = -9(K - p) + 8t_p - 1 - min(r_p, p - 1 - N + u)` when
`K < 2p` and
`γ^out_p = -9(K - p) + 3 + 16N + 7t_p - min(r_p, p + u)` when
`K ≥ 2p`.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4, equations (42)-(43) (the half-range `m` and the class
  counts), and Section 4.2, equations (52), (54), (56), and
  (58)-(59).
