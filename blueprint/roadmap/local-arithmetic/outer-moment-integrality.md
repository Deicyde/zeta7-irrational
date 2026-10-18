---
article_id: af_ce5a6926482dde7b0796b669
declaration: theorem
origin: cited
---

# Outer moment integrality

Let `p ≥ 7` be prime. For every `e ≥ 0` the polynomial moment
`μ(t^e) = μ_X(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)(2e+6)(2e+7)/720`
satisfies `v_p(μ(t^e)) ≥ -1`, and `v_p(μ(t^e)) ≥ 0` when
`e < 3p - 4`.

The proof: `v_p(720) = 0` because `p ≥ 7`, and the other factors
are integers. Von Staudt-Clausen gives `v_p(B_{2e+2}) ≥ -1`, with
`v_p(B_{2e+2}) ≥ 0` unless `(p-1) ∣ 2e+2`. If `2e+2 = k(p-1)`,
the condition `e < 3p - 4` means `2e + 2 < 6(p - 1)`, so
`1 ≤ k ≤ 5`, and the factor `2e+2+k = kp` among
`2e+3, …, 2e+7` cancels the denominator.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Proof depends on

- [Von Staudt-Clausen theorem](von-staudt-clausen.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.1, first paragraph (the moment formula and its
  `p`-integrality for `e < 3p - 4`). The bound `v_p ≥ -1` for all
  `e` is the von Staudt-Clausen step the paper relies on when it
  chooses `c_e ≡ p μ(t^e)` in the next paragraph.
