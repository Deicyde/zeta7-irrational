---
article_id: af_99b09565a05d0763806d1c5f
declaration: theorem
origin: bridged
---

# Outer rank decomposition

Let `p ≥ 7` be prime and write `μ(t^e) = μ_X(t^e)` for the
polynomial moments. Let `c_e ∈ {0, …, p-1}` be the residue of
`p μ(t^e)` modulo `p` (a `p`-integral number, by the outer moment
integrality) when `e ≥ 3p - 4`, and `c_e = 0` when `e < 3p - 4`.
Let `μ_0` be the functional defined like `μ_X`, with the
`p`-integral values
`μ_0(t^e) = μ(t^e) - c_e/p` on monomials and the values of `μ_X`
on the simple poles `1/(t + a^2)`. Write
`D_N(t)^8 t^{i+j} / D_K(t) = P_{ij}(t) + ∑_{N<a≤K} ρ_{ij,a}/(t + a^2)`
with `P_{ij} ∈ ℤ[t]`. Then `G_K = A + p^{-1} L`, where
`A_{ij} = μ_0(D_N^8 t^{i+j}/D_K)` and `L_{ij} = ∑_e c_e [t^e] P_{ij}`,
and `L` is an integer matrix with `rank_ℚ L ≤ r_p`, the rank
correction (54) of the outer range data.
Nothing is claimed about the integrality of `A`: the paper's (53)
asserts it, but it fails in the monomial basis, and the outer
estimate uses a weighted bound in the class basis instead.

The proof: by the outer moment integrality, `μ(t^e)` is
`p`-integral for `e < 3p - 4`, and `p μ(t^e) ≡ c_e (mod p)` for
`e ≥ 3p - 4`, so every `μ_0(t^e)` is `p`-integral. On monomials
`μ = μ_0 + c_e/p`, so linearity gives `G_K = A + p^{-1} L`. Since
`D_K` is monic in `ℤ[t]`, the quotient `P_{ij}` has integer
coefficients and degree `i + j + 8N - K`, so `L_{ij} = 0` when
`i + j < T = K - 8N + 3p - 4`. Row `i` of `L` vanishes when
`i ≤ T - h`, so at most `max(0, 2h - T)` rows are nonzero, and
`2h - T = K + 6N - 3p + 4` because `h = 37K/40`, `N = 3K/40`.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)
- [Outer range data](outer-range-data.md)

## Proof depends on

- [Outer moment integrality](outer-moment-integrality.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2.1, equations (53)-(54). The choice of `c_e` and the
  rank count are in the paper; the statement drops (53)'s false
  integrality claim for `A` and is otherwise reconstructed by
  this project, because the paper defers the use of the
  decomposition to its zeta(5) predecessor [5].
