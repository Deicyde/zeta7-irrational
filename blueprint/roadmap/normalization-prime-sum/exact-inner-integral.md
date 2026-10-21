---
article_id: af_d3b3fd1eb0800824df8ce97c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.innerIntegral_value ZetaSeven.intervalIntegrable_innerR_div_cube ZetaSeven.innerRPieces ZetaSeven.innerR_eq_of_mem_innerRPieces ZetaSeven.integral_gammaIntegrand_of_le ZetaSeven.integral_gammaIntegrand_of_ge ZetaSeven.innerR_eq_of_le ZetaSeven.innerR_eq_of_ge ZetaSeven.innerR_jump_4 ZetaSeven.innerR_jump_5 ZetaSeven.innerR_jump_6 ZetaSeven.innerR_jump_7 ZetaSeven.innerR_jump_8 ZetaSeven.innerR_jump_9 ZetaSeven.innerR_jump_10 ZetaSeven.innerR_jump_11 ZetaSeven.innerR_jump_12 ZetaSeven.innerR_jump_13 ZetaSeven.innerR_jump_40_3 ZetaSeven.innerR_jump_14 ZetaSeven.innerR_jump_15 ZetaSeven.innerR_jump_16 ZetaSeven.innerR_jump_17 ZetaSeven.innerR_jump_18 ZetaSeven.innerR_jump_19 ZetaSeven.innerR_at_twenty
---

# Exact inner integral

The exact rational value of the bounded inner integral
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`,
through the 192 affine pieces of Tables 2-4, with `R` affine on
the interior of each piece.

The proof strategy is certificate-checking, not recomputation:
write the `z`-integral of (66) in closed form, so that `R` is
affine between consecutive points where `cx` is an integer for
some `c ∈ {1, 2, α, 2α, 2H, 2λ, 1 - α, 1 + α, 9/20}`: there the floors
`⌊x⌋`, `⌊2x⌋`, `⌊αx⌋`, `⌊2αx⌋`, `⌊2Hx⌋`, `⌊2λx⌋`, the order of
`d({x})` and `d({αx})` (which flips where `(1 ± α)x` is an integer),
and the branch of `(s - n_+)_+` (which, with the floors fixed,
flips only where `(9/20)x` is an integer) are all constant. Then check for each piece that `R`
equals the listed affine function on its interior, and sum the
exact contributions. Only 131 of the 192 pieces are distinct, and `R`
jumps at `x = 4, …, 19`, `40/3`, and `20` (source-map erratum 12),
so the per-piece identities hold on open intervals.

## Depends on

- [Inner limiting functions](inner-limiting.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.1, equations (120)-(121), Tables 2-4.
- [Source-map erratum 12](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  the closed intervals of Tables 2-4 and the redundant cut points.
