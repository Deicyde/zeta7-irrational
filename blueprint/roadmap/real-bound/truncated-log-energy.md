---
article_id: af_98b7f178584866bd888afef9
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.ZeroMassEnergy.pair_truncEnergy_eq ZetaSeven.ZeroMassEnergy.logTrunc_le_abs_log ZetaSeven.ZeroMassEnergy.tendsto_logTrunc_seq
---

# Truncated logarithm energy

For `0 < a ≤ b` and `r > 0`, let
`L_{a,b}(r) = ½∫_a^b (e^{-s} - e^{-sr²})/s ds`. Then:

- the truncated pair energy of finite measures is the
  `s`-integral `∫∫ L_{a,b}(|z-w|) dμdρ = ½∫_a^b (e^{-s}μ(ℂ)ρ(ℂ) - J(μ,ρ;s))/s ds`
  by Fubini, so the signed combination is a nonpositive
  `s`-integral once the Gaussian positivity applies and the
  mass terms cancel at mass zero;
- domination: `|L_{a,b}(r)| ≤ |log r|`;
- convergence: `L_{a_n,b_n}(r) → log r` along the explicit
  truncation sequences `a_n = 1/(n+2) → 0` and
  `b_n = n+2 → ∞`.

Domination holds because the integrand has a fixed sign in
each regime `r > 1` and `r < 1` (vanishing at `r = 1`); the
limit is the improper-integral value.

## Depends on

None. Self-contained analysis.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 6.3, proof of Lemma 6.2 (truncated logarithm).
