---
article_id: af_d1535c272118e0129003b67c
declaration: theorem
origin: cited
---

# Small-prime estimate

For integer-valued `A` of degree `d`, the valuation bound
`v^G_p(τ_X(g)) ≥ -8⌊log_p max(2K,d+1)⌋ - v_p(720)` for the
weighted product `g`, plus the integer-valued basis change to
the `f_i` basis with its triangular transition determinant,
yielding the crude global bound
`v^G_p(F_K) ≥ -8h⌊log_p(5K)⌋ - h v_p(720)` at every prime.

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

## Proof depends on

- [Integer-valued polynomial estimates](integer-valued-estimates.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 3.5, Lemma 3.8, equations (37)-(41).
