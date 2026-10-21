---
article_id: af_d3b3fd1eb0800824df8ce97c
declaration: theorem
origin: cited
---

# Exact inner integral

The exact rational value of the bounded inner integral
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`,
through the 192 affine pieces of Tables 2-4, with `R` affine on
the interior of each piece.

The proof strategy is certificate-checking, not recomputation:
write the `z`-integral of (66) in closed form, so that `R` is
affine wherever the floors `⌊x⌋`, `⌊2x⌋`, `⌊αx⌋`, `⌊2αx⌋`, `⌊2Hx⌋`,
`⌊2λx⌋` and the branch of `(s - n_+)_+` are constant; check for
each piece that they are constant on its interior and that `R`
equals the listed affine function there; and sum the exact
contributions. Only 131 of the 192 pieces are distinct, and `R`
jumps at `x = 4, …, 19`, `40/3`, and `20` (source-map erratum 12),
so the per-piece identities hold on open intervals.

## Depends on

- [Inner limiting functions](inner-limiting.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.1, equations (120)-(121), Tables 2-4.
- [Source-map erratum 12](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  the closed intervals of Tables 2-4 and the redundant cut points.
