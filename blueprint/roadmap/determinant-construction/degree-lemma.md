---
article_id: af_0ea96162bc1c1b4a1a49923e
declaration: theorem
origin: cited
---

# Degree lemma

For every `K` in `40ℤ_{>0}`, the determinant `Δ_K(X)` is a
polynomial of degree exactly `h`, with the explicit nonzero leading
coefficient `(-1)^{h(h-1)/2} ∏_{j=N+1}^K j^6 D_N(-j^2)^7`.

The proof writes each entry as affine in `X`, so `G_K(X) = A + XB`,
factors the coefficient matrix as `B = V diag(γ) Vᵀ` with Vandermonde
`V`, and computes `det B` from the Vandermonde determinant and the
derivative identity for the tail divisor.

## Depends on

- [Matrix and determinant](matrix-determinant.md)

## Proof depends on

- [Vandermonde determinant](vandermonde-det.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 2.4, Lemma 2.3, equations (10)-(15).
