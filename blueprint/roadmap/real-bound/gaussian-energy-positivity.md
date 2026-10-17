---
article_id: af_752c6d73fd566eeef16b170a
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.ZeroMassEnergy.signed_gaussJ_nonneg ZetaSeven.ZeroMassEnergy.gaussian_pointwise
---

# Gaussian energy positivity

For finite positive measures `μ`, `ρ` on `ℂ` and `s > 0`, the
Gaussian-regularized signed interaction
`J(s) = J(μ,μ;s) - J(μ,ρ;s) - J(ρ,μ;s) + J(ρ,ρ;s)` is
nonnegative, where `J(μ,ρ;s) = ∫∫ e^{-s|z-w|²} dμ(z)dρ(w)`.
Applied to the Jordan parts of a signed measure, this is the
paper's `J(s) ≥ 0`.

The proof completes the square pointwise, rewriting the Gaussian
kernel as a scaled convolution of shifted Gaussians, then applies
Fubini to exhibit `J(s)` as a nonnegative square integral of
profile differences. The interchange is justified by the bounded
kernel and the finiteness of the measures.

## Depends on

None. Self-contained measure theory.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.3, proof of Lemma 6.2 (Gaussian regularization).
