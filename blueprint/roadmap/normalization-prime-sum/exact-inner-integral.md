---
declaration: theorem
origin: cited
---

# Exact inner integral

The exact rational value of the bounded inner integral
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`,
through the 192 affine pieces of Tables 2-4.

The proof strategy is certificate-checking, not recomputation:
verify for each piece that the branch choices are constant on
the interval, that `R` equals the listed affine function (by
evaluating the fractional-part formula at the two interior
sample points), and that the summed contributions equal the
claimed rational. Each check is decidable rational arithmetic;
the node is large but mechanical.

## Depends on

- [Inner limiting functions](inner-limiting.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.1, equations (120)-(121), Tables 2-4.
