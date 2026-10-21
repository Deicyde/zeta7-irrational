---
article_id: af_27b2cb3a6dbebdde2b7696d7
declaration: theorem
origin: cited
---

# Prime-sum bound

Put `A_0 = 9928298118277006344769/7535670527041937280000` (87),
`B_0 = A_0 + I_out + ∫_3^20 R(x)/x^3 dx` (88), where `I_out` is the
outer integral (73) of the outer limiting functions (its value is
`453803/288000`, not the printed (122); source-map errata 8-9), and
`A_M = B_0 + 9λ/M - 11549/(720M^2) + 44/M^3` (89); these
definitions belong to this node. Then for each fixed
`M ∈ 40ℤ_{>0}`, with `K = 40n`,
`lim sup_{n→∞} K^{-2} log m_{K,M} ≤ A_M`: for every `ε > 0`,
`K^{-2} log m_{K,M} ≤ A_M + ε` for all large `n`.

The proof combines four prime ranges: the small primes
`p ≤ √(5K)`, whose contribution is `o(K^2)`; the crude range
`√(5K) < p ≤ K/M`, which contributes `8λ/M`; the inner range
`K/M < p ≤ K/3`, through (70) and the prime number theorem; and
the outer range `K/3 < p ≤ 2h`. It then splits the inner integral
at `20`, bounds `∫_20^M` through `∫_20^∞` and the tail bound (86),
which is where `40 ∣ M` is used, and uses
`∫_20^∞ R(x)/x^3 dx ≤ A_0`, which follows from (85) at `T = 20`
(source-map erratum 14).

In the outer range `K/3 < p ≤ 2h` the proof first establishes
`-γ^out_p = K g(p/K) + O(1)` uniformly, with `g` from the outer
limiting functions (bounded arithmetic in (54), (58), and (59),
and `γ^out_p = 0` for `p > K`), and `-v_p(S_K) = K s(p/K) + O(1)`,
with `s` the scalar term of (73), from (62) since `p^2 > 2h` and
`N < p`; so `L_p = v_p(S_K) + γ^out_p` is `-K` times the integrand
of (73) at `y = p/K`, up to `O(1)`. The Riemann-sum form of the
prime number theorem needs the inner weight to have finitely many
discontinuities on each bounded interval: `R` jumps only where
`cx` is an integer for some `c ∈ {2, 2α, 2H, 2λ}`.

## Depends on

- [Normalization and integrality](normalization-integrality.md)
- [Inner limiting functions](inner-limiting.md)
- [Outer limiting functions](outer-limiting.md)
- [Tail integral bound](tail-integral.md)

## Proof depends on

- [Prime number theorem](prime-number-theorem.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 5.5, Proposition 5.4, equations (87)-(90).
- [Source-map erratum 14](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  `A_0` bounds the tail integral; it is not equal to it.
