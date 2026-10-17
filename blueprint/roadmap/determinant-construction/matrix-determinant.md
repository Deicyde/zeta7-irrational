---
article_id: af_e88b0fbd91b69906b8727a64
declaration: def
origin: cited
statement: formalized
lean: ZetaSeven.Dtail ZetaSeven.Rnum ZetaSeven.polyPart ZetaSeven.resCoeff ZetaSeven.poleCoeffs ZetaSeven.Gentry ZetaSeven.Gmat ZetaSeven.DeltaK ZetaSeven.SK ZetaSeven.FK
---

# Matrix and determinant

Define the `h × h` Hankel-type matrix `G_K(X)` whose `(i,j)` entry
applies `μ_X` to `D_N(t)^8 t^{i+j} / D_K(t)`, its determinant
`Δ_K(X)`, the factorial scalar `S_K`, and the normalized determinant
`F_K = S_K Δ_K`. The fully normalized polynomial `Q_{K,M} = m_{K,M} F_K`
is defined with the normalization factor, since `m_{K,M}` comes from
the prime-sum chapter.

## Depends on

- [Functional mu](functional-mu.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 2.3, equations (7)-(8).
