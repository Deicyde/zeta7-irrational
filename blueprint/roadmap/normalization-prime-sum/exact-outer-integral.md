---
article_id: af_5501e328f0f561b7f427a60e
declaration: theorem
origin: cited
---

# Exact outer integral

The outer integral of the outer limiting functions has the exact
rational value `I_out = 453803/288000 ≈ 1.5757049`. Its integrand
`T(y) = g(y) - 2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+` is affine,
`T(y) = b + cy`, on the interior of each of the following 11
pieces of `[1/3, 37/20]` (it jumps at `y = 1/2` and `y = 1`, where
`⌊1/y⌋` does, which does not change the integral):

| `y`-interval | `b` | `c` |
| --- | --- | --- |
| `[1/3, 43/120]` | `51/8` | `-5` |
| `[43/120, 29/80]` | `513/40` | `-23` |
| `[29/80, 37/100]` | `571/40` | `-27` |
| `[37/100, 37/80]` | `497/40` | `-22` |
| `[37/80, 29/60]` | `41/10` | `-4` |
| `[29/60, 1/2]` | `53/20` | `-1` |
| `[1/2, 43/80]` | `7/2` | `1` |
| `[43/80, 37/60]` | `121/10` | `-15` |
| `[37/60, 37/40]` | `41/4` | `-12` |
| `[37/40, 1]` | `1` | `-2` |
| `[1, 37/20]` | `37/20` | `-1` |

The proof strategy is the same certificate check as the inner
integral: verify for each piece that the branch choices in `g`
and the floors in the scalar term are constant on its interior,
that `T` equals the listed affine function there, and that the
eleven contributions `b(y_1 - y_0) + c(y_1^2 - y_0^2)/2` sum to
`453803/288000`. Each check is decidable rational arithmetic.

## Depends on

- [Outer limiting functions](outer-limiting.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  exact-integral appendix A.2, equation (122), Table 5.
- [Zeta 7 preprint source map, errata](../../sources/zeta7-preprint.md#errata-found-during-formalization):
  the value and the pieces that this node proves are recomputed
  exactly from (54), (58), (59), (72), and (73), with
  `γ^out_p = 0` for `p > K` and `R_0` as in erratum 8, in place of
  the printed `-11002997/720000` and the nine pieces of Table 5,
  which do not follow from the paper's definitions; recorded in
  erratum 9.
