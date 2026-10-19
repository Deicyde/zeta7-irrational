---
article_id: af_67346953e303bdfb5e41a80d
declaration: def
origin: cited
---

# Outer modified functional

Fix a prime `p`, and write `μ(t^e) = μ_X(t^e)` for the polynomial
moments of the functional `μ_X`. Put `c_e = 0` for `e < 3p - 4`.
For `e ≥ 3p - 4` let `c_e ∈ {0, …, p - 1}` be the representative
of `p μ(t^e)` modulo `p`: writing `p μ(t^e) = u/v` in lowest terms,
`c_e ≡ u v^{-1} (mod p)` when `p ∤ v`, and `c_e = 0` when `p ∣ v`.
The modified functional `μ_0` is the functional defined like `μ_X`,
with the values `μ_0(t^e) = μ(t^e) - c_e/p` on monomials and the
values of `μ_X` on the simple poles `1/(t + a^2)`. For
`0 ≤ i, j < h` let `P_{ij}` be the polynomial part of
`D_N(t)^8 t^{i+j} / D_K(t)`, so that
`D_N^8 t^{i+j}/D_K = P_{ij}(t) + ∑_{N<a≤K} ρ_{ij,a}/(t + a^2)`, and
define the `h × h` matrices `A_{ij} = μ_0(D_N^8 t^{i+j}/D_K)` and
`L_{ij} = ∑_e c_e [t^e] P_{ij}`.

Remark, which the consuming theorems discharge where they use it:
for `p ≥ 7` the outer moment integrality gives `v_p(μ(t^e)) ≥ -1`
for every `e`, and `v_p(μ(t^e)) ≥ 0` for `e < 3p - 4`, so `p ∣ v`
never happens, `p μ(t^e) ≡ c_e (mod p)`, and every `μ_0(t^e)` is
`p`-integral. That is what the choice of
`c_e` in (53) is for.

## Depends on

- [Functional mu](../determinant-construction/functional-mu.md)
- [Matrix and determinant](../determinant-construction/matrix-determinant.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.1, second paragraph: "Choose `c_e ∈ ℤ_p` with
  `c_e ≡ p µ(t^e) (mod p)`, taking `c_e = 0` for `e < 3p − 4`.
  Replace each polynomial moment by `µ_0(t^e) = µ(t^e) − c_e/p`
  and leave the simple-pole values unchanged", and (53), which
  names `A` and `L`. The representative in `{0, …, p - 1}`, its
  value when `p` divides the denominator, and the explicit
  formula for `L` are this project's precise form of that
  paragraph.
