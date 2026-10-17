---
article_id: af_ab893e2a96025b15c7aadf47
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: hasSum_zeta_nat
---

# Euler formula for even zeta values

Euler's formula `ζ(2e+2) = (-1)^e B_{2e+2} (2π)^{2e+2} / (2(2e+2)!)`
for every `e ≥ 0`, used to evaluate the even moments of the weight.
This is upstream as `hasSum_zeta_nat` in the pinned Mathlib checkout
(`Mathlib/NumberTheory/ZetaValues.lean`), verified by inspection:
with `k = e+1` its value equals the formula above. The `tsum`
equation and the rearrangement are short derivations and live in
the positive-integral-representation node's proof.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Proposition 2.4, equation (18).
