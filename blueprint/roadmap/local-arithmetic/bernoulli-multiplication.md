---
article_id: af_e48b505715ce896769de30d8
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZetaSeven.bernoulli_mul ZetaSeven.bernoulli_mul_zpow
---

# Bernoulli multiplication formula

The Bernoulli multiplication formula
`∑_{a=0}^{p-1} B_n(x + a/p) = p^{1-n} B_n(px)` in the polynomial
form over `ℚ` needed for the distribution formula. The pinned
Mathlib checkout has the real-valued `bernoulliFun_mul`; lifting
that identity to Bernoulli polynomials over `ℚ` is part of this
node.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Lemma 3.7 (DLMF 24.4.18).
