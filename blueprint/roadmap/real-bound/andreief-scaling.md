---
article_id: af_097a2632bc5a05da96c9262c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.aeval_DeltaK_zeta_le_scaled ZetaSeven.aeval_DeltaK_zeta_eq_andreief ZetaSeven.w7_le ZetaSeven.riemann_sum_log_bound ZetaSeven.integrable_andreief_integrand ZetaSeven.integrable_scaled_integrand ZetaSeven.integrableOn_residual_density
---

# Andreief scaling

The determinant at `ζ(7)` rewritten by Andreief's identity as
a multiple integral, bounded by the elementary weight estimate
and the Riemann-sum comparison, then scaled to the energy form
with the external field and the integrable residual density.
In Lean, (101) and (104) are stated for every `n`, the case `n = 0`
(an empty determinant, both sides equal to `1`) being trivial.

## Depends on

- [Positive integral representation](../determinant-construction/positive-integral-representation.md)

## Proof depends on

- [Andreief identity](andreief-identity.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.5, equations (101)-(104).
