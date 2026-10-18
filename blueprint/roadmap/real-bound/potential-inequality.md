---
article_id: af_e89f81eb6698385b44db7c19
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.two_mul_Ulog_compMeasure_sub_Vfield_le ZetaSeven.Jfield_eq ZetaSeven.Vfield_eq ZetaSeven.Vfield_zero ZetaSeven.qMinus ZetaSeven.qPlus ZetaSeven.pi_add_arctan_sub_qMinus_neg ZetaSeven.pi_add_arctan_sub_qPlus_pos ZetaSeven.exists_Vfield_min_between ZetaSeven.Vstar ZetaSeven.Vstar_le_Vfield ZetaSeven.Ulog_compMeasure_monotoneOn ZetaSeven.potBound ZetaSeven.two_mul_Ulog_sub_Vfield_le_potBound ZetaSeven.tailPoint ZetaSeven.potBreak ZetaSeven.potBreak_strictMono ZetaSeven.potBreak_zero_last ZetaSeven.potBound_potBreak_lt ZetaSeven.two_mul_Ulog_sub_Vfield_le_of_two_le ZetaSeven.tail_bound_lt
---

# Potential inequality

The potential bound `2U_ρ(t) - V(t) ≤ -5.45` for all `t ≥ 0`:
the closed form of `V`, its unique minimum located between
the consecutive rationals `q_-` and `q_+`, the interval
certificate `B(l,r) < -5.45` over the partition with the
subdivided tail interval, and the asymptotic bound past 2.
In Lean the closed forms of `J_a` and `V` are proved for every
real `a` and every `t ≥ 0` (the arctangent terms vanish at
`t = 0`), which specializes to the stated case `a > 0`, `t > 0`.

The proof strategy is certificate-checking with the elementary
enclosures: each interval's bound is a finite rational
computation, and the worst reported bounds carry positive
margin.

## Depends on

- [Comparison measure](comparison-measure.md)
- [Elementary enclosures](elementary-enclosures.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  comparison-measure appendix A.3, equations (113)-(116).
