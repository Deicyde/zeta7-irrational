import ZetaSeven.FunctionalMu

/-!
# Matrix and determinant (paper Section 2.3, equations (7)-(8))

The `h × h` matrix `G_K(X)`, its determinant `Δ_K(X)`, the factorial
scalar `S_K`, and the normalized determinant `F_K = S_K Δ_K`.

The `(i,j)` entry applies `μ_X` to `D_N(t)⁸ t^{i+j} / D_K(t)`.
Following the proof of Lemma 2.3, the entry is computed from the
polynomial part (Euclidean division by the tail divisor) and the
simple-pole residues, which is exactly the partial-fraction data
`muFunctional` consumes. The fully normalized `Q_{K,M} = m_{K,M} F_K`
is not defined here: `m_{K,M}` comes from the prime-sum chapter.
-/

namespace ZetaSeven

open Polynomial Finset

/-- Tail divisor `D_tail = D_K / D_N = ∏_{j=N+1}^K (t + j²)`
(Lemma 2.3 proof). -/
noncomputable def Dtail (n : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.Icc (N n + 1) (K n), (X + C ((j : ℚ) ^ 2))

/-- Numerator `D_N⁷ · t^{i+j}` of `R_{ij} = D_N⁸ t^{i+j} / D_K`
after canceling one `D_N` against `D_K` (Lemma 2.3 proof). -/
noncomputable def Rnum (n i j : ℕ) : Polynomial ℚ := Dpoly (N n) ^ 7 * X ^ (i + j)

/-- Polynomial part of `R_{ij}` via Euclidean division by `D_tail`. -/
noncomputable def polyPart (n i j : ℕ) : Polynomial ℚ := (Rnum n i j).div (Dtail n)

/-- Residue of `R_{ij}` at `t = -a²`, i.e. the partial-fraction
coefficient of `1/(t + a²)` (Lemma 2.3 proof). -/
noncomputable def resCoeff (n i j a : ℕ) : ℚ :=
  (Rnum n i j).eval (-(a : ℚ) ^ 2)
    / (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)

/-- Pole coefficients of `R_{ij}`, supported on `N < a ≤ K`. -/
noncomputable def poleCoeffs (n i j : ℕ) : ℕ →₀ ℚ :=
  ∑ a ∈ Finset.Icc (N n + 1) (K n), Finsupp.single a (resCoeff n i j a)

/-- Equation (7): the `(i,j)` entry `μ_X(D_N⁸ t^{i+j} / D_K)` of `G_K`. -/
noncomputable def Gentry (n i j : ℕ) : Polynomial ℚ :=
  muFunctional (polyPart n i j) (poleCoeffs n i j)

/-- Equation (7): the `h × h` matrix `G_K(X)`. -/
noncomputable def Gmat (n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) (Polynomial ℚ) :=
  Matrix.of fun i j => Gentry n i.val j.val

/-- Equation (7): `Δ_K(X) = det G_K(X)`. -/
noncomputable def DeltaK (n : ℕ) : Polynomial ℚ := (Gmat n).det

/-- Equation (8): `S_K = (K!)²ʰ 4^{h-1} / ((N!)¹⁶ʰ ∏_{i=1}^{h-1} ((2i)!)²)`. -/
def SK (n : ℕ) : ℚ :=
  (Nat.factorial (K n) : ℚ) ^ (2 * hDim n) * 4 ^ (hDim n - 1)
    / ((Nat.factorial (N n) : ℚ) ^ (16 * hDim n)
      * ∏ i ∈ Finset.Icc 1 (hDim n - 1), (Nat.factorial (2 * i) : ℚ) ^ 2)

/-- Equation (8): the normalized determinant `F_K = S_K Δ_K`. -/
noncomputable def FK (n : ℕ) : Polynomial ℚ := C (SK n) * DeltaK n

end ZetaSeven
