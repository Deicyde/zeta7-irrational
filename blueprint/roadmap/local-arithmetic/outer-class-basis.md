---
article_id: af_8d3f5d5d03fde3635f1c4e3f
declaration: theorem
origin: bridged
---

# Outer class basis

Let `p` satisfy the outer-range hypothesis (52), and take `m` and
the class counts `ℓ_K(c)` of the local range data and the class
indicators `δ_c` from the outer range data. For `0 ≤ c ≤ m` let
`S_c = {N < j ≤ K : j ≡ ±c (mod p)}`, so `S_0` is the set of
multiples of `p` in `(N, K]`, and `F_c(t) = ∏_{j ∈ S_c} (t + j^2)`.
For `1 ≤ c ≤ m` write `ℓ = ℓ_K(c)` and `δ = δ_c`, so
`|S_c| = ℓ - δ`; put
`E_c(t) = ∏_{j ∈ S_c, j > p} (t + j^2)`, of degree `ℓ - 2`,
`P_c = ∏_{0 ≤ d ≤ m, d ≠ c} F_d`, and
`q_{c,i} = (t + c^2)^i` for `0 ≤ i < ℓ - 2`,
`q_{c,i} = E_c(t) (t + c^2)^{i - (ℓ - 2)}` for `ℓ - 2 ≤ i < ℓ - δ`.
The class rows are `P_c q_{c,i}` for `1 ≤ c ≤ m`, `0 ≤ i < ℓ - δ`,
and the zero-class rows are `P_0 t^i` for `0 ≤ i < |S_0|`.
These are exactly `h` integer polynomials of degree less than
`h`, and the integer matrix `U` expressing them in the monomial
basis `1, t, …, t^{h-1}` has `det U` prime to `p`; so they form a
`ℤ_p`-unimodular basis of the polynomials of degree less than `h`.
Under (52), `N < p` and `K/3 < p ≤ K`, so `|S_0| = ⌊K/p⌋`, which is
1 when `K < 2p` and 2 otherwise.

The proof: every `j ∈ (N, K]` lies in exactly one `S_c`, so the
row count is `K - N = h`, and `deg P_c q_{c,i} = h - |S_c| + i < h`.
Modulo `p`, `F_c ≡ (t + c^2)^{|S_c|}` and
`E_c ≡ (t + c^2)^{ℓ - 2}`, so the class-`c` rows reduce to
`∏_{d ≠ c} (t + d^2)^{|S_d|} · (t + c^2)^i`. The factors `t + d^2`,
`0 ≤ d ≤ m`, are pairwise coprime in `𝔽_p[t]`, and in the Chinese
remainder decomposition of `𝔽_p[t]_{<h}` by their powers the
reduced rows are triangular with unit diagonal, hence an
`𝔽_p`-basis.

## Depends on

- [Outer range data](outer-range-data.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, proof of Proposition 4.6 (the rows `P_a q_{a,i}`).
  The paper uses `P_a` and the zero-class rows without defining
  them; this statement is reconstructed by this project, because
  the paper defers the basis to its zeta(5) predecessor [5]. The
  weights on these rows are the outer weight family.
