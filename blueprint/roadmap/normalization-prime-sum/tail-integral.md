---
article_id: af_8b96ff34fa9b4145b548e6bf
declaration: theorem
origin: cited
---

# Tail integral bound

Write `R(x) = xF(x) + Q(x)` with the periodic coefficient
`F(x) = 6λ + 2λ{x} - 16λ{αx}` (81) and the bounded remainder `Q`
of (82), whose `∫_0^{1/2} B(z)^2 dz` term has the coefficient `16`
(source-map erratum 11); bound `Q` between `-1/2` and `27/8`; and
prove, for every `M ∈ 40ℤ_{>0}`, the tail estimate
`∫_M^∞ R(x)/x^3 dx ≥ -λ/M + 11549/(720M^2) - 44/M^3`
by double integration by parts against the explicit periodic
primitives `P` and `C` with `|C| < 22`.

The hypothesis `M ∈ 40ℤ_{>0}` is the paper's: it makes
`P(M) = C(M) = 0`, and it cannot be dropped: the estimate fails at
every `M ≡ 20 (mod 40)`, for example at `M = 20`, `60`, and `100`. For the lower bound on `Q`, the
termwise bounds give only `-5/8`; the bound `-1/2` follows from
`|∫_0^{1/2} A(z)B(z) dz| ≤ ∫_0^{1/2} B(z)^2 dz` by (78)-(79), which
gives `16∫B^2 - 4∫AB ≥ 0` and so `Q ≥ -1/8`.

## Depends on

- [Inner limiting functions](inner-limiting.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 5.4, equations (74)-(86).
- [Source-map erratum 11](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  the coefficient `16` in (82) and the argument for (83).
