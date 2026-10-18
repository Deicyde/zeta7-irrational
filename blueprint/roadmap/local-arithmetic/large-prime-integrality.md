---
article_id: af_7ddab937d5a5d3746ee93f05
declaration: theorem
origin: bridged
---

# Large-prime integrality

For every prime `p > K`, each entry
`G_K(i,j) = μ_X(D_N^8 t^{i+j}/D_K)` has `p`-integral coefficients
as a polynomial in `X`; hence `Δ_K` has `p`-integral coefficients,
that is, `v^G_p(Δ_K) ≥ 0`.

The proof: write `R = D_N^7 t^{i+j}` and
`D_tail = D_K/D_N = ∏_{N<b≤K} (t + b^2)`. The polynomial part of
`R/D_tail` has integer coefficients and degree at most
`7N + h - 2 < 3p - 4`, so its `μ`-value is `p`-integral by the
moment bound. Every pole `-a^2` has `N < a ≤ K < p`, so the pole
value `μ_X(1/(t + a^2)) = a^6 (X - H^(7)_a) + 1/(2a) - 1/6` is
`p`-integral. A factor `b^2 - a^2` of `D_tail'(-a^2)` is divisible
by `p` only for `b = p - a`, and then exactly once, so the
residue at an unpaired pole is `p`-integral. For a pair `a`,
`p - a` both in `(N, K]`, put
`x_a = R(-a^2) / ∏_{b ≠ a, p-a} (b^2 - a^2)`; the two residues
sum to `(x_a - x_{p-a}) / (p (p - 2a))`, which is `p`-integral
because `x_a ≡ x_{p-a} (mod p)`, and the two pole values are
congruent modulo `p` because
`H^(7)_{p-a} ≡ H^(7)_{a-1} (mod p)`, a consequence of
`∑_{v=1}^{p-1} v^{-7} ≡ 0 (mod p)`. So the pair contributes a
`p`-integral amount, each residue having valuation at least `-1`.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)

## Proof depends on

- [Outer moments and rank decomposition](outer-rank-decomposition.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, Proposition 4.6 (the case `p > K`). The paper's
  two-sentence proof treats every residue as `p`-integral, which
  fails for the paired poles `a`, `p - a`; this statement and
  proof are reconstructed by this project, because the paper
  defers the outer-range argument to its zeta(5) predecessor [5].
