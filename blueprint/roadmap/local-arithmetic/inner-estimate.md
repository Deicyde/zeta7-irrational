---
article_id: af_2ecf5c546c9083afd41c375f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.inner_estimate ZetaSeven.eBasis_unimodular ZetaSeven.bA_lt_allocT ZetaSeven.alloc_eq ZetaSeven.card_eIdx ZetaSeven.eBasis_natDegree_lt ZetaSeven.exists_extraRows ZetaSeven.ell_le_ell_add_one ZetaSeven.tauExt_subst_norm_le ZetaSeven.normSqLe_gram ZetaSeven.comparison ZetaSeven.InnerRange ZetaSeven.L0 ZetaSeven.bA ZetaSeven.allocTotal ZetaSeven.allocT ZetaSeven.allocE ZetaSeven.ExtraRows ZetaSeven.allocZ ZetaSeven.allocL ZetaSeven.eBasis ZetaSeven.eIdx ZetaSeven.weight2 ZetaSeven.gammaIn ZetaSeven.ClassDeg ZetaSeven.pfNum ZetaSeven.NormSqLe ZetaSeven.muTail
---

# Inner range estimate

In the inner range `K/M < p ≤ K/3`, the determinant valuation
bound `v^G_p(Δ_K) ≥ γ^in_p`, with the dimension allocation, the
unimodular `E`-basis, and the half-weights defined as stated.

The proof establishes the residue valuations per source class
from the distribution formula, then checks the four comparison
cases (diagonal, cross-class, outside, zero class), using the
tie-breaking margins where the worst cases would otherwise
overlap.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)
- [Local range data](local-range-data.md)
- [Distribution formula](distribution-formula.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.1, Proposition 4.4, equations (44)-(51), with the
  definitions (42)-(43) shared through the local range data.
