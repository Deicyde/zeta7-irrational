# ZetaSeven: a Lean audit of "Zeta 7 is Irrational"

This repository formalizes Prince Anand's preprint "Zeta 7 is Irrational"
([Zenodo 22920911](https://zenodo.org/records/22920911)) in Lean 4 (with Mathlib and
PrimeNumberTheoremAnd), as a [blueprint](blueprint/README.md) of statements linked to Lean
code, built with [AutoformBot](https://github.com/facebookresearch/autoform-bot).

It is an audit, not a proof. **It does not show that ζ(7) is irrational**, which remains
open. The paper's argument fails at its last numerical step, and the repository proves
that failure in Lean. Work has stopped.

## What was achieved

- 50 of the blueprint's 55 statements and definitions are formalized (39 theorems with
  complete proofs, 11 definitions); 3 more are Mathlib results. CI builds everything and
  allows only the standard axioms. This covers the construction and its positivity, the
  p-adic estimates (Propositions 4.4 and 4.6), integrality (5.1), the prime-sum bound (5.4,
  with the recomputed integral below), the real bound (6.3) and the paper's exact integrals.
- The paper's printed outer integral (122) is wrong, as a
  [reader report](https://github.com/gmDevi/zeta-7-21-lean/issues/1) found and an
  [independent audit](https://carlostoledo.co/reports/zeta7-anand.html) confirmed.
  Recomputed from the paper's definitions it is 453803/288000
  (`ZetaSeven.outerIntegral_value`; errata 8 and 9 discuss the reading). The paper's (118)
  claims A₂₀₀ + U < −11; the corrected value is about +4.86, and the argument needs a
  negative one. `ZetaSeven.primeSumA_add_u_pos` proves A_M + U > 0 for every integer
  cutoff M ≥ 1, and [`ZetaSeven.final_margins_fail`](ZetaSeven/FinalMargins.lean) proves
  that (118) and (119) fail, so Theorems 1.1 and 1.2 do not follow.
- The [source map](blueprint/sources/zeta7-preprint.md) records 14 errata; as far as the
  formalization has checked, only this one (erratum 9) breaks the argument.

## What was not achieved

- Theorems 1.1 and 1.2 are not formalized (`not_ready`: no known proof route). Corollary
  1.3 and the rest of Appendix B were deferred.
- The failure does not look like a matter of loose constants. Exact computations for
  n ≤ 9 (K = 40n), not in this repository, find that even the smallest integer
  normalization of the paper's determinant has a value at ζ(7) of roughly exp(0.9K²): it
  grows instead of decaying, though finitely many sizes do not prove the asymptotic rate.
  The audit's values for n ≤ 3 agree, and the author's note on the Zenodo record
  (2026-10-17) says: "There is an error in the argument in its current state,the data
  tables have few wrong entries. There also seems to be an exponential growth instead of
  a decay."

The [blueprint site](https://deicyde.github.io/zeta7-irrational/) shows the status of every
statement.
