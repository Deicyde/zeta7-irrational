---
article_id: af_777d2a6506e15243904e0cf5
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.ZeroMassEnergy.zero_mass_energy_nonpos
---

# Zero-mass logarithmic energy

A compactly supported signed Borel measure of total mass zero
with integrable logarithmic kernel has nonpositive energy
`I(ν) ≤ 0`.

The proof regularizes with the Gaussian kernel (completing the
square plus Fubini gives a nonnegative square integral),
represents the logarithm as an improper `s`-integral, uses the
mass-zero condition to drop the constant term, and passes to
the limit by dominated convergence.

## Depends on

None. The statement needs no other article.

## Proof depends on

- [Gaussian energy positivity](gaussian-energy-positivity.md)
- [Truncated logarithm energy](truncated-log-energy.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.3, Lemma 6.2.
