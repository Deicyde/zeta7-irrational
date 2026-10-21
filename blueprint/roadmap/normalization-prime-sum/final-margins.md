---
article_id: af_8db86a9b06c6d0d8bd08f4e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.final_margins_fail ZetaSeven.primeSumB0_value ZetaSeven.primeSumA_two_hundred_add_U ZetaSeven.primeSumB0_lt_primeSumA ZetaSeven.primeSumA_add_U_pos ZetaSeven.primeSumB0_add_U_pos ZetaSeven.primeSumB0_approx ZetaSeven.primeSumA_two_hundred_add_U_approx ZetaSeven.primeSumA_numerator_pos
---

# Final rational margins

The constants of the prime-sum bound are explicit rationals, and the
paper's final margin fails at every cutoff. With `A_0`, `B_0`, and
`A_M` as defined in the prime-sum bound, (87)-(89), and `U = 44/25`
the constant of the real bound (Proposition 6.3):
`B_0 = 166929451792375913959739/54488694580149392640000`, about
`3.0636`; `A_200 + U = 6626902387705935050696033/1362217364503734816000000`,
about `4.8648`; and `A_M > B_0` for every integer `M > 0`. In
particular, since `B_0 + U > 0`, `A_M + U > 0` for every integer
`M > 0`, so the margin `A_200 + U < -95/8` (that is,
`1600(A_200 + U) < -19000`), the paper's (118), `A_200 + U < -11`,
and its (119), `A_100000 + U < -12`, all fail.

The proof substitutes the exact outer integral `453803/288000` and
the exact inner integral
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`
into (88), and (89) then gives `A_200`. For `M > 0`,
`A_M - B_0 = (9λM^2 - 11549M/720 + 44)/M^3` with `λ = 37/40`, and
the numerator is positive for every real `M`: its leading
coefficient `9λ = 333/40` is positive and its discriminant
`(11549/720)^2 - 4·(333/40)·44 = -626180279/518400` is negative.

## Depends on

- [Prime-sum bound](prime-sum-bound.md)
- [Real bound](../real-bound/real-bound.md)

## Proof depends on

- [Exact inner integral](exact-inner-integral.md)
- [Exact outer integral](exact-outer-integral.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.3 and Section B.1, equations (118)-(119),
  where the paper claims the margin, and Table 5 with (122), the
  printed outer integral.
- [Source-map errata 8-9](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  the exact outer integral `453803/288000` replaces the printed (122).
- [Open question 5](../../sources/zeta7-preprint.md#open-source-questions):
  this node records, with exact arithmetic, the failure of the
  paper's final step.
