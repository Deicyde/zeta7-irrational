---
article_id: af_7332d2b33bf74a81accda2b8
declaration: def
origin: cited
---

# Outer limiting functions

Work in the variable `y = p/K`, which runs over `(1/3, 2λ)` in the
outer range, with `α = 3/40` and `λ = 37/40`. For `1/3 < y ≤ 1`
put `k = ⌊1/y⌋`, `v = 1 - ky`, `u = max(0, α + v - y)`,
`t = min(α, v) + u`, and `r = min(λ, max(0, 1 + 6α - 3y))`, and
define

- `g(y) = 9(1 - y) - 8t + min(r, y - α + u)` for `1/2 < y ≤ 1`,
- `g(y) = 9(1 - y) - 16α - 7t + min(r, y + u)` for `1/3 < y ≤ 1/2`,
- `g(y) = 0` for `1 < y < 2λ`.

This is the outer exponent of the outer range data scaled by `K`,
with `p = yK`, `N = αK`, `h = λK` in (54), (58), and (59), and
`0` for `y > 1`, where `γ^out_p = 0`: the prime-sum bound proves
that `g(y)` is the limit of `-γ^out_p/K` as `K → ∞` with
`p/K → y`, in the uniform form it uses.

Define the outer limiting function `R_0(y) = g(y) + d(y)`, where
`d` is the zero-weight correction (72)
`d(y) = (1 + 6α - 3y - (1 + 2α - 3y)_+)_+ · 1_{(1/3,1/2)}(y)`,
and the outer integral (73)
`I_out = ∫_{1/3}^{2λ} (R_0(y) - d(y) - 2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+) dy`.
Its integrand is `g(y)` plus the scalar term
`-2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+`, which is the continuum limit
of `-v_p(S_K)/K`.

## Depends on

- [Outer range data](../local-arithmetic/outer-range-data.md)
- [Matrix and determinant](../determinant-construction/matrix-determinant.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 5.3, Definition 5.3, equations (71)-(73), and the last
  sentence of Section 5.3; Section 5.1, first sentence, for
  `γ^out_p = 0` when `p > K`. The definition `R_0 = g + d` follows
  the last sentence of Section 5.3 and the outer-range step of the
  proof of Proposition 5.4, which both use
  `R_0 - d = lim -γ^out_p/K`, and not (71), which sets
  `R_0 = lim -γ^out_p/K`. The proof of Proposition 5.4 (its `L_p`
  identity) uses the first reading; under (71) that proof is off by
  the integral of `d`, `3/100`, and (90) would then rest on the
  slack in `A_0`. The explicit formula for `g` is derived by this
  project by scaling (54), (58), and (59).
- [Source-map erratum 8](../../sources/zeta7-preprint.md#errata-found-during-formalization)
  records the conflict, and
  [open question 5](../../sources/zeta7-preprint.md#open-source-questions)
  the outer integral it affects.
