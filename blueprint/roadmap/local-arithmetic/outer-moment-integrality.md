---
article_id: af_ce5a6926482dde7b0796b669
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.outer_moment_integrality ZetaSeven.muMonomial_padicValRat_ge ZetaSeven.muMonomial_padicValRat_nonneg ZetaSeven.muFunctional_X_pow ZetaSeven.muMonomial_eq_kappa ZetaSeven.dvd_descFactorial_of_sub_one_dvd ZetaSeven.norm_muMonomial_le ZetaSeven.norm_muMonomial_le_one ZetaSeven.norm_muMonomial_eq
---

# Outer moment integrality

Let `p ≥ 7` be prime. For every `e ≥ 0` the polynomial moment
`μ(t^e) = μ_X(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)(2e+6)(2e+7)/720`
satisfies `v_p(μ(t^e)) ≥ -1`, and `v_p(μ(t^e)) ≥ 0` when
`e < 3p - 4`.

The proof: by (5) and (24), `μ(t^e) = (-1)^e κ_{2e+7}`, and
Lemma 3.4 gives `v_p(κ_d) ≥ -1` for every `d`, hence the first
bound. For the second, `v_p(720) = 0` because `p ≥ 7`, and the
other factors are integers. Von Staudt-Clausen gives
`v_p(B_{2e+2}) ≥ 0` unless `(p-1) ∣ 2e+2`, and then
`v_p(B_{2e+2}) = -1`. If `2e+2 = k(p-1)`, the condition
`e < 3p - 4` means `2e + 2 < 6(p - 1)`, so `1 ≤ k ≤ 5`, and the
factor `2e+2+k = kp` among `2e+3, …, 2e+7` cancels the
denominator.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Proof depends on

- [P-adic completion](completion.md)
- [Von Staudt-Clausen theorem](von-staudt-clausen.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 3.3, Lemma 3.4, with (24), for `v_p(μ(t^e)) ≥ -1`
  through `μ(t^e) = (-1)^e κ_{2e+7}` (the monomial case of the
  proof of Lemma 3.1); Section 4.2.1, first paragraph, for the
  moment formula and its `p`-integrality for `e < 3p - 4`. The
  paper relies on the first bound when it chooses
  `c_e ≡ p μ(t^e)` in the next paragraph.
