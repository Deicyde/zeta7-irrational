import Mathlib.RingTheory.PowerSeries.Basic
import ZetaSeven.RankLemma

/-!
# Gauss-valuation rank lemma (Lemma 4.5, last sentence)

Prince Anand, "Zeta 7 is Irrational", Section 4.2.2, Lemma 4.5: after the rank
lemma (55) the paper adds "The same assertion holds for the Gauss valuation of
polynomial entries". This file proves that extension: for `h × h` matrices `A`
over `ℚ[X]` and `L` over `ℚ`, if `v^G_p(A_{ij}) ≥ w_i + w_j` for nonpositive
half-integer weights, `L` is `p`-integral of rank at most `r`, and exactly `z`
weights are zero, then `v^G_p det(A + p⁻¹ L) ≥ 2 ∑ w_i - min(r, z)`, where
`v^G_p` is the minimum of the `p`-adic valuations of the coefficients.

As in `ZetaSeven.rank_lemma`, the weights are doubled integers (`w i` is twice
the paper's weight). The Gauss valuation is stated coefficientwise with
`padicValRat`; see the docstring of `ZetaSeven.gauss_rank_lemma`.

Proof (following the project's article): expanding the Leibniz formula column by
column, the `X^k`-coefficient of `det(A + p⁻¹ L)` is the sum, over all splittings
`l` of `k` among the columns, of `det(B_l + p⁻¹ L_l)`, where column `j` of `B_l`
is the `X^{l j}`-coefficient of column `j` of `A` and `L_l` is `L` with the
columns having `l j ≠ 0` replaced by zero (`ZetaSeven.coeff_det_eq_sum`,
`ZetaSeven.coeffMatrix_add_smul_map`). Each `B_l` satisfies the entry bounds and
each `L_l = L * D` is `p`-integral of rank at most `rank L`, so the rational rank
lemma bounds every term, and the ultrametric inequality bounds the sum.
-/

open Polynomial Finset

namespace ZetaSeven

variable {h : ℕ}

/-! ## Coefficients of a determinant over `ℚ[X]` -/

/-- Coefficients of a finite product of polynomials: the `X^k`-coefficient of
`∏ i ∈ s, f i` is the sum, over all ways `l` to split `k` among the factors, of
`∏ i ∈ s, (f i).coeff (l i)`. -/
theorem coeff_prod_eq_sum_finsuppAntidiag {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℚ[X]) (k : ℕ) :
    (∏ i ∈ s, f i).coeff k = ∑ l ∈ s.finsuppAntidiag k, ∏ i ∈ s, (f i).coeff (l i) := by
  calc (∏ i ∈ s, f i).coeff k
      = PowerSeries.coeff k (coeToPowerSeries.ringHom (∏ i ∈ s, f i)) := by
        rw [coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    _ = PowerSeries.coeff k (∏ i ∈ s, coeToPowerSeries.ringHom (f i)) := by
        rw [map_prod]
    _ = ∑ l ∈ s.finsuppAntidiag k,
          ∏ i ∈ s, PowerSeries.coeff (l i) (coeToPowerSeries.ringHom (f i)) :=
        PowerSeries.coeff_prod _ k s
    _ = ∑ l ∈ s.finsuppAntidiag k, ∏ i ∈ s, (f i).coeff (l i) := by
        simp only [coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]

/-- Multilinear expansion of a determinant over `ℚ[X]` by `X`-degree, column by
column: the `X^k`-coefficient of `det M` is the sum, over all splittings `l` of
`k` among the columns, of the determinant of the rational matrix whose column
`j` is the `X^{l j}`-coefficient of column `j` of `M`. -/
theorem coeff_det_eq_sum (M : Matrix (Fin h) (Fin h) ℚ[X]) (k : ℕ) :
    M.det.coeff k = ∑ l ∈ (univ : Finset (Fin h)).finsuppAntidiag k,
      (Matrix.of fun i j => (M i j).coeff (l j)).det := by
  simp only [Matrix.det_apply', finsetSum_coeff, ← C_eq_intCast, coeff_C_mul,
    coeff_prod_eq_sum_finsuppAntidiag, Finset.mul_sum, Matrix.of_apply]
  exact Finset.sum_comm

/-- The coefficient matrices of `A + c L` (with `L` rational, hence constant):
taking the `X^{l j}`-coefficient in column `j` gives `B_l + c L_l`, where `B_l`
takes the same coefficients of `A` and `L_l` is `L` with the columns having
`l j ≠ 0` replaced by zero. -/
theorem coeffMatrix_add_smul_map (A : Matrix (Fin h) (Fin h) ℚ[X])
    (L : Matrix (Fin h) (Fin h) ℚ) (c : ℚ) (l : Fin h →₀ ℕ) :
    (Matrix.of fun i j => ((A + (c • L).map C) i j).coeff (l j)) =
      Matrix.of (fun i j => (A i j).coeff (l j)) +
        c • Matrix.of (fun i j => if l j = 0 then L i j else 0) := by
  ext i j
  by_cases hl : l j = 0 <;> simp [hl, coeff_C]

/-- Zeroing some columns of `L` does not increase its rank: the result is
`L * D` for a diagonal `0/1` matrix `D`. -/
theorem rank_of_ite_le (L : Matrix (Fin h) (Fin h) ℚ) (l : Fin h →₀ ℕ) :
    (Matrix.of fun i j => if l j = 0 then L i j else 0).rank ≤ L.rank := by
  have hmul : (Matrix.of fun i j => if l j = 0 then L i j else 0) =
      L * Matrix.diagonal (fun j => if l j = 0 then (1 : ℚ) else 0) := by
    ext i j
    by_cases hl : l j = 0 <;> simp [Matrix.mul_diagonal, hl]
  rw [hmul]
  exact Matrix.rank_mul_le_left _ _

/-! ## The Gauss-valuation rank lemma -/

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric bound for a finite sum: if every term has `p`-adic valuation at
least `c ≤ 0`, so does the sum (a zero sum has the junk valuation `0 ≥ c`). -/
theorem le_padicValRat_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {c : ℤ} (hc : c ≤ 0)
    (hall : ∀ i ∈ s, c ≤ padicValRat p (f i)) : c ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  by_cases h0 : ∑ i ∈ s, f i = 0
  · rw [h0, padicValRat.zero]
    exact hc
  · have h2 := val_two_sum (p := p) s f (2 * c) (fun i hi => by linarith [hall i hi]) h0
    linarith

/-- **Gauss-valuation rank lemma** (Lemma 4.5, last sentence). Let `A` be an
`h × h` matrix over `ℚ[X]` and `L` an `h × h` matrix over `ℚ`. Suppose
`v^G_p(A i j) ≥ w_i + w_j` for nonpositive half-integer weights, `L` is
`p`-integral with `rank L ≤ r`, and exactly `z` weights are zero. Then
`v^G_p det(A + p⁻¹ L) ≥ 2 ∑ w_i - min(r, z)`.

Conventions. As in `ZetaSeven.rank_lemma`, `w i` is twice the paper's weight,
so the hypothesis reads `w i + w j ≤ 2 v_p` and the bound `∑ w i - min r z`.
The Gauss valuation `v^G_p` (minimum of the `p`-adic valuations of the
coefficients, `v^G_p(0) = +∞`) is stated coefficientwise: `v^G_p(P) ≥ b` is
written `∀ k, b ≤ padicValRat p (P.coeff k)`. Since `padicValRat p 0 = 0` and
every bound here is nonpositive (the weights are `≤ 0`), the zero coefficients
impose nothing, so both the hypothesis `hA` and the conclusion (for every `k`)
are exactly the paper's statements. The matrix `p⁻¹ L` enters as the constant
polynomial matrix `((p : ℚ)⁻¹ • L).map C`. -/
theorem gauss_rank_lemma {r z : ℕ}
    (w : Fin h → ℤ) (A : Matrix (Fin h) (Fin h) ℚ[X]) (L : Matrix (Fin h) (Fin h) ℚ)
    (hw0 : ∀ i, w i ≤ 0)
    (hz : (Finset.univ.filter (fun i => w i = 0)).card = z)
    (hA : ∀ i j k, w i + w j ≤ 2 * padicValRat p ((A i j).coeff k))
    (hL : ∀ i j, 0 ≤ padicValRat p (L i j))
    (hr : Matrix.rank L ≤ r) (k : ℕ) :
    ∑ i, w i - ↑(min r z) ≤
      padicValRat p ((A + ((p : ℚ)⁻¹ • L).map C).det.coeff k) := by
  have hsum0 : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => hw0 i
  have hmin0 : (0 : ℤ) ≤ ((min r z : ℕ) : ℤ) := Nat.cast_nonneg _
  rw [coeff_det_eq_sum]
  refine le_padicValRat_sum _ _ (by linarith) fun l _ => ?_
  rw [coeffMatrix_add_smul_map]
  refine rank_lemma w (Matrix.of fun i j => (A i j).coeff (l j))
    (Matrix.of fun i j => if l j = 0 then L i j else 0) hw0 hz (fun i j => ?_)
    (fun i j => ?_) ((rank_of_ite_le L l).trans hr)
  · simp only [Matrix.of_apply]
    exact hA i j (l j)
  · simp only [Matrix.of_apply]
    split_ifs
    · exact hL i j
    · simp

end ZetaSeven
