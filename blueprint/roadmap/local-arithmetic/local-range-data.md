---
article_id: af_6eb0c47ae4938b428ae5fb50
declaration: def
origin: cited
statement: formalized
lean: ZetaSeven.mHalf ZetaSeven.mN ZetaSeven.mK ZetaSeven.ell ZetaSeven.card_filter_dvd_sub ZetaSeven.ell_eq_add ZetaSeven.ell_eq_count ZetaSeven.sum_ell
---

# Local range data

For a prime `p` put (42) `m = (p-1)/2`, `m_N = ⌊N/p⌋`, and
`m_K = ⌊K/p⌋`, and for `A ≥ 0` and `1 ≤ a ≤ m` define the class
count (43)
`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ a or j ≡ -a (mod p)}`.
These are shared by the inner and outer ranges. For odd `p` and
`1 ≤ c ≤ m`, writing `A + 1 = qp + s` with `0 ≤ s < p`, the class
count is `ℓ_A(c) = 2q + [c < s] + [p - c < s]`, and
`∑_{a=1}^{m} ℓ_A(a) = A - ⌊A/p⌋`, because every `j ≤ A` prime to `p`
lies in exactly one class `±a`; these counting identities are
elementary.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4, opening paragraph, equations (42)-(43).
