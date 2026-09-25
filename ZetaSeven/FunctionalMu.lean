import Mathlib

/-!
# Functional μ (paper Section 2.1-2.2, equations (3)-(6))

Parameters `K N h α λ H`, divisor polynomials `D_m`, partial sums `H⁷`,
and the `ℚ`-linear functional `μ_X` given by its values (5)-(6) on
monomials and on simple poles `1/(t + j²)`.

The functional is defined on the partial-fraction decomposition
`(P, c)` (polynomial part plus finitely supported pole coefficients);
existence/uniqueness of the decomposition for a given rational function
is a later bridge lemma, not part of this definition node.
-/

namespace ZetaSeven

open Polynomial Finset

/-- Equation (3): `K = 40n`. -/
def K (n : ℕ) : ℕ := 40 * n

/-- Equation (3): `N = 3n`. -/
def N (n : ℕ) : ℕ := 3 * n

/-- Equation (3): `h = 37n`, the matrix size. -/
def hDim (n : ℕ) : ℕ := 37 * n

/-- Equation (3): `α = 3/40`. -/
def alpha : ℚ := 3 / 40

/-- Equation (3): `λ = 37/40`. -/
def lam : ℚ := 37 / 40

/-- Equation (3): `H = 1 + 3α = 49/40`. -/
def bigH : ℚ := 49 / 40

/-- Equation (4): `D_m(t) = ∏_{j=1}^m (t + j²)`, with `D_0 = 1`. -/
noncomputable def Dpoly (m : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.range m, (X + C (((j : ℚ) + 1) ^ 2))

/-- Partial sums `H⁷_j = ∑_{v=1}^j v⁻⁷` for `j ≥ 1`, and `H⁷_0 = 0`. -/
def H7 (j : ℕ) : ℚ :=
  ∑ v ∈ Finset.range j, 1 / ((v : ℚ) + 1) ^ 7

/-- Equation (5): `μ_X(t^e)`, independent of `X`.
Uses Mathlib's `bernoulli` (same `B₁ = -1/2` convention as the paper). -/
def muMonomial (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2)
    * ((2 * (e : ℚ) + 3) * (2 * (e : ℚ) + 4) * (2 * (e : ℚ) + 5)
      * (2 * (e : ℚ) + 6) * (2 * (e : ℚ) + 7)) / 720

/-- Equation (6): `μ_X(1/(t + j²)) = j⁶(X - H⁷_j) + 1/(2j) - 1/6`,
affine in `X` (here `X` is the polynomial variable). -/
noncomputable def muPole (j : ℕ) : Polynomial ℚ :=
  C (j : ℚ) ^ 6 * (X - C (H7 j)) + C (1 / (2 * (j : ℚ)) - 1 / 6)

/-- Definition 2.1: the `ℚ`-linear functional `μ_X`, evaluated on the
partial-fraction data `(P, c)` by linearity from (5)-(6). -/
noncomputable def muFunctional (p : Polynomial ℚ) (c : ℕ →₀ ℚ) : Polynomial ℚ :=
  p.sum (fun e a => C a * C (muMonomial e))
    + c.sum (fun j a => C a * muPole j)

end ZetaSeven
