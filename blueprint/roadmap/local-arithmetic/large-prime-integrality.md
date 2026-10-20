---
article_id: af_7ddab937d5a5d3746ee93f05
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZetaSeven.large_prime_integrality ZetaSeven.Gentry_mem_pIntPoly ZetaSeven.muFunctional_polyPart_mem_pIntPoly ZetaSeven.resCoeff_mem_pInt_of_unpaired ZetaSeven.resCoeff_pair_mem_pIntPoly ZetaSeven.exists_intCast_eq_coeff_polyPart ZetaSeven.natDegree_polyPart_le
---

# Large-prime integrality

For every prime `p > K`, each entry
`G_K(i,j) = μ_X(D_N^8 t^{i+j}/D_K)` has `p`-integral coefficients
as a polynomial in `X`.

The proof: write `R = D_N^7 t^{i+j}` and
`D_tail = D_K/D_N = ∏_{N<b≤K} (t + b^2)`. The polynomial part of
`R/D_tail` has integer coefficients and degree at most
`7N + h - 2 < 3p - 4`, so its `μ`-value is `p`-integral by the
outer moment integrality. Every pole `-a^2` has
`N < a ≤ K < p`, so the pole value
`μ_X(1/(t + a^2)) = a^6 (X - H^(7)_a) + 1/(2a) - 1/6` is
`p`-integral. A factor `b^2 - a^2` of `D_tail'(-a^2)` is divisible
by `p` only for `b = p - a`, so the residue at an unpaired pole is
`p`-integral. A pair `a`, `p - a` both in `(N, K]` contributes a
`p`-integral amount by the paired-pole congruence, applied with
`S = {N < b ≤ K}` and `Q = R`, although each of its two residues
can have valuation `-1`.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)

## Proof depends on

- [Outer moment integrality](outer-moment-integrality.md)
- [Paired-pole congruence](paired-pole-congruence.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, Proposition 4.6 (the case `p > K`). The paper's
  two-sentence proof treats every residue as `p`-integral, which
  fails for the paired poles `a`, `p - a`; this statement and
  proof are reconstructed by this project, because the paper
  defers the outer-range argument to its zeta(5) predecessor [5].
  It is labeled bridged, not cited, because the outer range
  estimate is the cited target for Proposition 4.6 and owns its
  determinant bound `v^G_p(Δ_K) ≥ 0` for `p > K`, while the
  entrywise statement and the paired proof here are the project's.
- [Source-map erratum 7](../../sources/zeta7-preprint.md#errata-found-during-formalization)
  records the paired-pole finding.
