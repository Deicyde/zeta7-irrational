---
article_id: af_f6d7fb0e399a74224e96827b
declaration: theorem
origin: cited
---

# Outer range estimate

Let `p` be a prime satisfying the outer-range hypothesis (52) of
the outer range data, and let `γ^out_p` be the outer exponent (59)
defined there. Then `v^G_p(Δ_K) ≥ γ^out_p`. Also
`v^G_p(Δ_K) ≥ 0` for every prime `p > K`: this second clause of
Proposition 4.6 is the conclusion of the large-prime integrality
node, restated here unchanged so that this node mirrors the cited
proposition.

The second clause is the large-prime integrality itself. Under
(52), the rank decomposition writes `G_K = A + p^{-1} L` with the
modified functional `μ_0` and an integral `L` of rank at most
`r_p`. Let
`U` be the integer matrix of the outer class basis in the
monomial basis; `det U` is prime to `p`, and
`U G_K U^T = A' + p^{-1} U L U^T`, where
`A'_{rs} = μ_0(r s D_N^7 / D_tail)` and `U L U^T` is integral of
rank at most `r_p`. The entry valuations give
`v^G_p(A'_{rs}) ≥ w_r + w_s` with the outer weight family on the
class rows and the zero-class rows, the Gauss-valuation rank
lemma gives `v^G_p det(U G_K U^T) ≥ 2∑w - min(r_p, z)`, and the
weight sum bounds this below by `γ^out_p`. Since
`det(U G_K U^T) = (det U)^2 Δ_K` with `det U` a `p`-unit, the
bound holds for `Δ_K`. The paper's (53) also asserts that `A` is
integral at every prime; that is false in the monomial basis
(pole values `j^6 H^(7)_j` with `p < j ≤ K`, `p ∤ j`, can have
valuation `-7`), and the argument above uses only the weighted
bound in the class basis.

## Depends on

- [Matrix and determinant](../determinant-construction/matrix-determinant.md)
- [Outer range data](outer-range-data.md)

## Proof depends on

- [Outer rank decomposition](outer-rank-decomposition.md)
- [Large-prime integrality](large-prime-integrality.md)
- [Outer class basis](outer-class-basis.md)
- [Outer entry valuations](outer-entry-valuations.md)
- [Gauss-valuation rank lemma](gauss-rank-lemma.md)
- [Outer weight sum](outer-weight-sum.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 4.2, Proposition 4.6, equations (52)-(59). The proof
  sketch follows the route that proves the proposition; the
  paper's proof defers the basis, the zero-class weights, and the
  derivation of (59) to its zeta(5) predecessor [5].
