---
article_id: af_6fce3535eea6444de11b31d8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.Ilog_compMeasure ZetaSeven.energy_norm_bound ZetaSeven.cStar ZetaSeven.cStar_bounds ZetaSeven.Ilog_compMeasure_eq_sum_sum ZetaSeven.integrable_log_abs_sub_prod_compMeasure ZetaSeven.integral_log_abs_sub_prod_arcsineMeasure ZetaSeven.integrable_log_abs_sub_prod_arcsineMeasure ZetaSeven.sum_sum_mul_min
---

# Energy and norm constant

The energy evaluation `I(ρ)` from the nesting formula, the
direct evaluation of `C*`, and the combined bound
`λM_0 - I(ρ) + C* ≤ U = 44/25`.

The proof evaluates the finite rational sums for the energy
and `C*` and checks the final inequality by exact arithmetic.
Table 1 lists the intervals in decreasing order, so the nesting
formula is recorded with the tail sums `T_j = c_j + ⋯ + c_16` in
place of the source's prefix sums `S_j = c_1 + ⋯ + c_j`, which
would give the value `-3.1433…` printed in A.4 instead of the
energy `I(ρ) ≈ -1.9482`; the bound holds with the true value.

## Depends on

- [Comparison measure](comparison-measure.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  comparison-measure appendix A.4, equations (95)-(96), (110).
