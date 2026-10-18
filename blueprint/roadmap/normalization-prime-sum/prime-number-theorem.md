---
article_id: af_4a2ec29b35052df331a4836a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZetaSeven.theta_isEquivalent_id ZetaSeven.tendsto_primeRiemannSum ZetaSeven.tendsto_primeRiemannSum_of_theta
---

# Prime number theorem

The prime number theorem in the `θ(x) ~ x` form, with the
partial-summation step that turns it into prime Riemann sums:
for `0 < a < b` and a bounded weight `G` on `[a, b]` that is
continuous except at finitely many points,
`X^{-1} ∑_{aX < p ≤ bX} G(p/X) log p → ∫_a^b G(y) dy` as
`X → ∞`. Proposition 5.4 needs only `θ(x) ≤ (1 + o(1))x` in the
middle prime range. It uses the Riemann-sum form with `X = K` in
the inner range, with `G(y) = y R(1/y)` on `[1/M, 1/3]` (so the
limit is `∫_3^M R(x) x^{-3} dx` under `x = 1/y`), and in the outer
range, with the outer integrand on `[1/3, 2λ]`. The `O(1)` errors
in the local exponents need only `θ(x) = O(x)`.

The asymptotic comes from the pinned PrimeNumberTheoremAnd
dependency (rev `c39a751`): `chebyshev_asymptotic : θ ~[atTop] id`
in `PrimeNumberTheoremAnd/Consequences.lean`, stated for Mathlib's
`Chebyshev.theta`. The partial-summation step is project work. The paper's weights are
polynomial or rational on each of finitely many closed pieces,
where Mathlib's Abel summation `sum_mul_eq_sub_sub_integral_mul`
(for `0 ≤ a ≤ b`) applies; a general weight can instead be
sandwiched between step functions. The pinned Mathlib has no
asymptotic for `θ`, only explicit bounds such as
`Chebyshev.theta_le_log4_mul_x` and `Chebyshev.theta_ge`. These fix
`θ` only up to constant factors, so they cannot give the exact
limits that define `A_M` in (88)-(90).

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Proposition 5.4.
