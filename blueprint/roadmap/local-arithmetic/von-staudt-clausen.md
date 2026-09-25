---
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: Bernoulli.vonStaudt_clausen
---

# Von Staudt-Clausen theorem

The denominator of `B_{2k}` is squarefree with prime divisors `p`
exactly those with `(p-1) ∣ 2k`. This is upstream as
`Bernoulli.vonStaudt_clausen` in the pinned Mathlib checkout
(`Mathlib/NumberTheory/Bernoulli.lean`), verified by inspection.
The valuation corollaries the completion proof needs
(`v_p(κ_d) ≥ -1`, integrality for `d ≤ p+4`) are short derivations
from it and live in the completion node's proof.

## Depends on

None. Upstream result.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in Lemma 3.4 and the outer-range integrality argument.
