---
article_id: af_8db86a9b06c6d0d8bd08f4e0
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

The planned proof is exact rational arithmetic from the
certified tables, by cross-multiplication of explicit integers.
With the recomputed outer integral the inequality fails:
`A_200 + U ≈ +4.86`, so the node cannot be proved as stated.

## Depends on

- [Exact inner integral](exact-inner-integral.md)
- [Exact outer integral](exact-outer-integral.md)
- [Tail integral bound](tail-integral.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.3 and Section B.1, equations (118)-(119).
- [Open question 5](../../sources/zeta7-preprint.md#open-source-questions):
  with the recomputed outer integral (erratum 9) the inequality
  fails, so this node cannot be proved as stated; what to do about
  its statement is the user's decision.
