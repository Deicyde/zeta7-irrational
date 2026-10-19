---
article_id: af_fb6217ebdc3cf0e17db2a538
declaration: def
origin: bridged
---

# Outer class rows

Fix a prime `p`, and take `m` and the class counts `ℓ_K(c)` of the
local range data, the class indicators `δ_c` of the outer range
data, and the index set of the outer weight family. For
`0 ≤ c ≤ m` let `S_c = {N < j ≤ K : j ≡ ±c (mod p)}`, so `S_0` is
the set of multiples of `p` in `(N, K]`,
`F_c(t) = ∏_{j ∈ S_c} (t + j^2)`, and
`P_c = ∏_{0 ≤ d ≤ m, d ≠ c} F_d`. For `1 ≤ c ≤ m` write
`ℓ = ℓ_K(c)` and `δ = δ_c`, and put
`E_c(t) = ∏_{j ∈ S_c, j > p} (t + j^2)` and
`q_{c,i} = (t + c^2)^i` for `0 ≤ i < ℓ - 2`,
`q_{c,i} = E_c(t) (t + c^2)^{i - (ℓ - 2)}` for `ℓ - 2 ≤ i < ℓ - δ`.
The outer class rows are the integer polynomials indexed by the
outer weight family: the class row `P_c q_{c,i}` at the class pair
`(c, i)`, and the zero-class row `P_0 t^i` at the zero-class pair
`(0, i)`.

## Depends on

- [Outer range data](outer-range-data.md)
- [Outer weight family](outer-weight-family.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, proof of Proposition 4.6, which defines `q_{a,i}`
  and `E_a` and uses the rows `P_a q_{a,i}` and the zero-class
  rows without defining `P_a` or the zero-class rows. The
  definitions of `S_c`, `F_c`, `P_c`, and the zero-class rows are
  reconstructed by this project, because the paper defers the
  basis to its zeta(5) predecessor [5].
