---
article_id: af_426ee1f8522ffe7c192def45
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZetaSeven.muPole_paired_congruence ZetaSeven.paired_residues ZetaSeven.poleResidue ZetaSeven.H7_reflect_congruence ZetaSeven.pInt ZetaSeven.pIntPoly
---

# Paired-pole congruence

Let `p ≥ 7` be prime, let `1 ≤ a ≤ (p-1)/2`, and put `a' = p - a`.
Write `π_b = μ_X(1/(t + b^2)) = b^6 (X - H^(7)_b) + 1/(2b) - 1/6`
for the pole values of the functional `μ_X`.

1. The pole values `π_a` and `π_{a'}` have `p`-integral
   coefficients and are congruent modulo `p`, coefficientwise.
2. Let `S` be a finite set of positive integers that contains `a`
   and `a'` and no other integer congruent to `±a` modulo `p`, put
   `T(t) = ∏_{b ∈ S} (t + b^2)`, and let `Q` be a polynomial with
   `p`-integral rational coefficients. The residues
   `ρ_b = Q(-b^2)/T'(-b^2)` of `Q/T` at `t = -a^2` and
   `t = -a'^2` satisfy `v_p(ρ_a) ≥ -1` and `v_p(ρ_{a'}) ≥ -1`, both
   with equality when `Q(-a^2)` is a `p`-unit, while `ρ_a + ρ_{a'}`
   is `p`-integral. Consequently `ρ_a π_a + ρ_{a'} π_{a'}` has
   `p`-integral coefficients.

The Lean statement takes `S` to be a finite set of natural numbers, so
it also allows `0 ∈ S`, and for a set of positive integers it is the
second part as stated.

The proof of the first part, whose key input is the congruence
`H^(7)_{a'} ≡ H^(7)_{a-1} (mod p)`: since `1 ≤ a, a' < p` and
`p ∤ 6`, every denominator in `π_a` and `π_{a'}` is prime to `p`.
Because `p - 1` does not divide `7`, the power sum
`∑_{v=1}^{p-1} v^{-7} ≡ ∑_{v ∈ 𝔽_p^×} v^7` vanishes modulo `p`, so
`H^(7)_{p-a} ≡ -∑_{w=1}^{a-1} (p - w)^{-7} ≡ H^(7)_{a-1} (mod p)`.
Hence `π_{a'} ≡ a^6 (X - H^(7)_{a-1}) - 1/(2a) - 1/6 (mod p)`,
and `π_a` equals the same expression because
`H^(7)_a = H^(7)_{a-1} + a^{-7}`.

The proof of the second part: `T'(-a^2) = ∏_{b ∈ S, b ≠ a} (b^2 - a^2)`.
The factor `b = a'` is `(a' - a)(a' + a) = p (p - 2a)` with
`1 ≤ p - 2a < p`, and every other factor is a `p`-unit because
`b ≢ ±a (mod p)`. So `ρ_a = x_a / (p (p - 2a))` and, in the same
way, `ρ_{a'} = -x_{a'} / (p (p - 2a))`, where
`x_b = Q(-b^2) / ∏_{c ∈ S, c ≠ a, a'} (c^2 - b^2)` is `p`-integral
with `v_p(x_a) = v_p(Q(-a^2))`. Since `a'^2 ≡ a^2 (mod p)`, also
`x_a ≡ x_{a'} (mod p)`, so
`ρ_a + ρ_{a'} = (x_a - x_{a'}) / (p (p - 2a))` is `p`-integral.
Finally
`ρ_a π_a + ρ_{a'} π_{a'} = ρ_a (π_a - π_{a'}) + (ρ_a + ρ_{a'}) π_{a'}`,
and both terms are `p`-integral by the first part.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, proof of Proposition 4.6: the sentence "the two
  remaining pole values at `a` and `p − a` are integral and
  congruent modulo `p`", and the case `p > K`, whose residues the
  paper treats as `p`-integral one by one. The paper gives no
  proof of the congruence and does not pair the residues; this
  statement is reconstructed by this project, because the paper
  defers the outer-range argument to its zeta(5) predecessor [5].
  It is labeled bridged, not cited, because the source asserts the
  congruence in passing and never states the pairing; large-prime
  integrality and the outer entry valuations both use it.
- [Source-map erratum 7](../../sources/zeta7-preprint.md#errata-found-during-formalization)
  records the paired-pole finding.
