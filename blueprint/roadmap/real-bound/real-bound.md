---
article_id: af_86ae9ab95a54586118a282f5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.real_bound ZetaSeven.log_aeval_DeltaK_zeta_le ZetaSeven.log_SK_le ZetaSeven.SK_cast_eq ZetaSeven.scaled_integral_le ZetaSeven.integral_residual_density_le
---

# Real bound

For every `K = 40n` with `n ≥ 1`, `F_K(ζ(7))` is positive with
`log F_K(ζ(7)) ≤ UK^2 + 24K log K + 220K` for `U = 44/25`.

The proof takes logarithms of the scaled integral, cancels
the `K^2 log K` terms between the determinant estimate and
the Stirling bound for `S_K`, and applies the energy-norm
constant bound for the remaining quadratic coefficient.

## Depends on

- [Configuration energy bound](configuration-bound.md)
- [Andreief scaling](andreief-scaling.md)
- [Energy and norm constant](energy-computation.md)

## Proof depends on

- [Stirling factorial estimate](stirling-estimate.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.6, Proposition 6.3, equations (105)-(108).
