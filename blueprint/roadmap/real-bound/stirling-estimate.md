---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZetaSeven.Stirling.log_factorial_upper ZetaSeven.Stirling.log_factorial_lower ZetaSeven.Stirling.sum_integral_compare ZetaSeven.Stirling.stirling_106 ZetaSeven.Stirling.SK ZetaSeven.Stirling.log_SK ZetaSeven.Stirling.four_log_two_lam_add_log_four_le ZetaSeven.Stirling.stirling_107
---

# Stirling factorial estimate

The Stirling-type upper bound for `log S_K` with the exact
quadratic-log coefficient and the `C*` constant, as needed for
the `K^2 log K` cancellation. Record the precise factorial
bounds required (including the `(2i)!` sums) during the
Mathlib audit; prove from project lemmas what is missing
upstream.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in Section 6.6, equations (106)-(107).
