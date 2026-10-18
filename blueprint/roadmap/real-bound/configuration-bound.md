---
article_id: af_628271880f5a353f0020ba51
declaration: theorem
origin: cited
---

# Configuration energy bound

For every configuration of `h` points, the discrete logarithmic
energy with the external field satisfies the general bound with
main term `(λM_0 - I(ρ))K^2`, after circle regularization and
retaining the integrable `√t/K` factor for the unbounded domain.

The proof applies the zero-mass lemma to the circle-regularized
empirical measure minus the comparison measure, bounds the
regularization error by the arcsine mass estimate and the
circle-average identity, and checks the retained-factor
inequality on `[0,2]` and past 2 by elementary bounds.
The paper's bound (99) past 2 is false as printed (with the
coefficient `13/10` it fails for `t > 3.53`, e.g. at `t = 4`); the
correct bound is
`2U_ρ(t) - V(t) ≤ (29/20) log t + 8α^3/t - 2π√t` for
`t ≥ 2`, proved in the potential-inequality node, and with it
the retained-factor inequality (98) still holds, since after
adding `√t/K` the right side is decreasing on `[2,∞)` and its
value at `t = 2` is below `M_0 + √2/K` for `K ≥ 2`.

## Depends on

- [Zero-mass logarithmic energy](zero-mass-energy.md)
- [Comparison measure](comparison-measure.md)

## Proof depends on

- [Potential inequality](potential-inequality.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.4, equations (97)-(100).
