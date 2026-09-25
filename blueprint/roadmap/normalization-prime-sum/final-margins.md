---
declaration: theorem
origin: cited
---

# Final rational margins

The exact rational values of `A_0`, `B_0`, `A_200`, and
`A_100000` from the evaluated integrals and the tail bound,
with the strict margin inequalities. In particular this node
proves `A_200 + U < -95/8`, i.e. `1600(A_200 + U) < -19000`,
which is the approved `-19000` target and goes beyond the
paper's proved `(118)` (`A_200 + U < -11`).

The proof is exact rational arithmetic from the certified
tables: the exact values leave margin `~0.118`, so the
certificate is expected to close by cross-multiplication of
explicit integers. If the tables fail to check, this node is
where the project learns it.

## Depends on

- [Exact inner integral](exact-inner-integral.md)
- [Exact outer integral](exact-outer-integral.md)
- [Tail integral bound](tail-integral.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.3 and Section B.1, equations (118)-(119).
