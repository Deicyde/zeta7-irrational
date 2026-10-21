---
article_id: af_d1535c272118e0129003b67c
declaration: theorem
origin: cited
lean: ZetaSeven.small_prime_tau_bound ZetaSeven.FK_small_prime_bound ZetaSeven.FK_eq_det_fBasis ZetaSeven.det_transMat ZetaSeven.qPoly_comp_neg_sq ZetaSeven.Dpoly_comp_neg_sq ZetaSeven.fPoly_comp_neg_sq_intValued ZetaSeven.transMat_isLowerTriangular ZetaSeven.fPoly_eq_transMat_sum ZetaSeven.small_prime_tau_rep_exists ZetaSeven.fBasis_muRep_exists ZetaSeven.muRatFunc_inj ZetaSeven.Wpoly ZetaSeven.qPoly ZetaSeven.fPoly ZetaSeven.transMat ZetaSeven.muRatFunc
---

# Small-prime estimate

For integer-valued `A` of degree `d`, the valuation bound
`v^G_p(τ_X(g)) ≥ -8⌊log_p max(2K,d+1)⌋ - v_p(720)` for the
weighted product `g`, plus the integer-valued basis change to
the `f_i` basis with its triangular transition determinant,
yielding the crude global bound
`v^G_p(F_K) ≥ -8h⌊log_p(5K)⌋ - h v_p(720)` at every prime.
The global bound is stated for every `n ≥ 0`; at the degenerate
`n = 0` (`h = K = 0`, `F_K = 1`) it holds trivially, and for
`n ≥ 1` it is exactly (41).

The proof bounds residues by Legendre's formula, controls the
polynomial part on and off the root balls, applies `τ` to the
polynomial part, and bounds pole contributions by harmonic
denominators. The binomial identities making `q_i(-x^2)` and
`f_i(-x^2)` integer-valued are part of this node. The constant
8 in (37) absorbs the per-term constant 6, since
`⌊log_p(d+1)⌋ ≤ ⌊log_p max(2K,d+1)⌋`, so the proof needs no
sharp constant-5 cancellation lemma; that sharpening is out of
scope by design, and no separate node is planned for it.

## Depends on

- [Tau pullback identity](tau-pullback.md)
- [Matrix and determinant](../determinant-construction/matrix-determinant.md)

## Proof depends on

- [Integer-valued polynomial estimates](integer-valued-estimates.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 3.5, Lemma 3.8, equations (37)-(41).
