---
article_id: af_c5cb1ea5c1492a72ec91e5ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZetaSeven.aeval_muFunctional_zeta_eq_integral ZetaSeven.integrableOn_muIntegrand ZetaSeven.posDef_Gmat_zeta ZetaSeven.normalized_FK_zeta_pos ZetaSeven.aeval_FK_zeta_pos ZetaSeven.aeval_DeltaK_zeta_pos ZetaSeven.w7 ZetaSeven.w7_pos ZetaSeven.integral_moment_w7 ZetaSeven.integral_pole_w7 ZetaSeven.Rnum_eq_partialFractions ZetaSeven.aeval_polyPart_add_poleCoeffs ZetaSeven.Dpoly_K_eq_mul_Dtail ZetaSeven.poleCoeffs_apply_zero
---

# Positive integral representation

At `X = ζ(7)` the functional becomes integration against the
explicit positive weight `w_7`: for every rational function in the
domain, `μ_{ζ(7)}(R) = ∫_0^∞ R(y^2) w_7(y) dy`.
Consequently `G_K(ζ(7))` is a positive definite Gram matrix and
`Q_{K,M}(ζ(7)) > 0` whenever the normalization is positive.
In Lean these hold for every `n` (the matrix is empty when `n = 0`),
and since `m_{K,M}` is defined only in a later chapter, the last claim
is stated for an arbitrary positive factor `m`.

The proof checks the identity on monomials (even moments via the
Euler formula) and on simple poles (six integrations by parts plus
the Hermite/Hurwitz identity and the recurrence
`ζ(7,j) = ζ(7) - H^(7)_j + j^{-7}`), then extends by linearity.
Positivity follows because the quadratic form is an integral of a
nonnegative, almost-everywhere-positive integrand.

## Depends on

- [Functional mu](functional-mu.md)
- [Matrix and determinant](matrix-determinant.md)

## Proof depends on

- [Euler formula for even zeta values](euler-even-zeta.md)
- [Hermite integral for Hurwitz zeta](hermite-hurwitz.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Section 2.5, Proposition 2.4, equations (16)-(19).
