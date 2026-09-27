import Mathlib

/-!
# Andreief's integration identity for moment determinants

Paper: Prince Anand, *Zeta 7 is Irrational*, preprint v1, Section 6.5, equation (101).

`andreief_integral` proves Andreief's identity: the determinant of the matrix of
mixed-moment integrals `∫ φᵢ ψⱼ dμ` equals `1 / n!` times the `n`-fold product
integral of the product of the two pointwise determinants. The proof expands both
determinants (Leibniz formula) and integrates term by term, using Fubini on finite
product spaces (`MeasureTheory.integral_fintype_prod_eq_prod`).

`andreief_moment_det` specializes to moment matrices (`φᵢ = ψᵢ = X^i`), where both
determinants become transposes of Vandermonde determinants, giving the
squared-Vandermonde form; `andreief_moment_det_prod` unfolds it to the explicit
double product over `i < j`.
-/

open MeasureTheory

namespace ZetaSeven.Andreief

/-- The square of a permutation sign, as a real number, is `1`. -/
theorem sign_sq_eq_one {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    ((τ.sign : ℤ) : ℝ) * ((τ.sign : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or τ.sign with h | h <;> simp [h]

/-- Determinant as a double signed sum over two independent permutations. -/
theorem sum_sign_mul_prod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∑ τ : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n),
      ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ) * ∏ i, M (τ i) (ρ i)
      = (Nat.factorial n : ℝ) * M.det := by
  have hprod : ∀ τ ρ : Equiv.Perm (Fin n),
      ∏ i, M (τ i) (ρ i) = ∏ i, M i ((ρ * τ⁻¹) i) := by
    intro τ ρ
    calc ∏ i, M (τ i) (ρ i)
        = ∏ i, (fun j => M j ((ρ * τ⁻¹) j)) (τ i) := by
          refine Finset.prod_congr rfl fun i _ => by simp
      _ = ∏ i, M i ((ρ * τ⁻¹) i) :=
          Equiv.prod_comp (↑τ : Fin n ≃ Fin n) (fun j => M j ((ρ * τ⁻¹) j))
  calc
    ∑ τ : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n),
          ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ) * ∏ i, M (τ i) (ρ i)
        = ∑ τ : Equiv.Perm (Fin n), ((τ.sign : ℤ) : ℝ) * ∑ ρ : Equiv.Perm (Fin n),
            ((ρ.sign : ℤ) : ℝ) * ∏ i, M (τ i) (ρ i) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ _ => mul_assoc _ _ _
    _ = ∑ τ : Equiv.Perm (Fin n), ((τ.sign : ℤ) : ℝ) * ∑ π : Equiv.Perm (Fin n),
            (((π * τ).sign : ℤ) : ℝ) * ∏ i, M i (π i) := by
          refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
          refine Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ fun ρ => ?_
          simp_rw [Equiv.coe_mulRight]
          have hsign : (ρ * τ⁻¹) * τ = ρ := by group
          rw [hsign, hprod τ ρ]
    _ = ∑ τ : Equiv.Perm (Fin n),
            ((τ.sign : ℤ) : ℝ)
              * ((Matrix.transpose M).det * ((τ.sign : ℤ) : ℝ)) := by
          refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
          have hsign2 : ∀ π : Equiv.Perm (Fin n), ((((π * τ).sign : ℤ)) : ℝ)
              = ((π.sign : ℤ) : ℝ) * ((τ.sign : ℤ) : ℝ) := by
            intro π
            rw [Equiv.Perm.sign_mul]
            simp only [Units.val_mul, Int.cast_mul]
          simp_rw [hsign2]
          rw [show (∑ π : Equiv.Perm (Fin n), ((π.sign : ℤ) : ℝ) * ((τ.sign : ℤ) : ℝ)
              * ∏ i, M i (π i))
              = (∑ π : Equiv.Perm (Fin n), ((π.sign : ℤ) : ℝ) * ∏ i, M i (π i))
              * ((τ.sign : ℤ) : ℝ) from by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun π _ => mul_right_comm _ _ _]
          congr 1
          rw [Matrix.det_apply']
          refine Finset.sum_congr rfl fun π _ => congrArg _ ?_
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Matrix.transpose_apply]
    _ = (Nat.factorial n : ℝ) * M.det := by
          simp_rw [show ∀ τ : Equiv.Perm (Fin n),
            ((τ.sign : ℤ) : ℝ) * ((Matrix.transpose M).det * ((τ.sign : ℤ) : ℝ))
              = (Matrix.transpose M).det from fun τ => by
            rw [← mul_assoc, mul_comm ((τ.sign : ℤ) : ℝ) (Matrix.transpose M).det,
              mul_assoc, sign_sq_eq_one τ, mul_one]]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul, Matrix.det_transpose]

/-- **Andreief's identity** (paper Section 6.5, eq. (101)): the determinant of the
matrix of mixed-moment integrals equals `1 / n!` times the `n`-fold product
integral of the product of the two pointwise determinants. -/
theorem andreief_integral {n : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [MeasureTheory.SigmaFinite μ] (φ ψ : Fin n → X → ℝ)
    (hint : ∀ i j, Integrable (fun x => φ i x * ψ j x) μ) :
    (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det
      = (Nat.factorial n : ℝ)⁻¹ * ∫ x, (Matrix.of fun i j => φ i (x j)).det
          * (Matrix.of fun i j => ψ i (x j)).det ∂(Measure.pi fun _ : Fin n => μ) := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ with hM
  have hint2 : ∀ τ ρ : Equiv.Perm (Fin n), Integrable
      (fun x : Fin n → X => ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ)
        * ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)))
      (Measure.pi fun _ : Fin n => μ) := by
    intro τ ρ
    have hbase : Integrable (fun x : Fin n → X => ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)))
        (Measure.pi fun _ : Fin n => μ) :=
      MeasureTheory.Integrable.fintype_prod
        (f := fun i x => φ (τ i) x * ψ (ρ i) x) (fun i => hint (τ i) (ρ i))
    exact hbase.const_mul (((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ))
  have hmain : (∫ x, (Matrix.of fun i j => φ i (x j)).det
        * (Matrix.of fun i j => ψ i (x j)).det ∂(Measure.pi fun _ : Fin n => μ))
      = (Nat.factorial n : ℝ) * M.det := by
    have hpoint : ∀ x : Fin n → X, (Matrix.of fun i j => φ i (x j)).det
          * (Matrix.of fun i j => ψ i (x j)).det
          = ∑ τ : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n),
            ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ)
              * ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)) := by
      intro x
      rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [Matrix.of_apply, Finset.prod_mul_distrib]
      ring
    simp_rw [hpoint]
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun τ _ => MeasureTheory.integrable_finsetSum Finset.univ (fun ρ _ => hint2 τ ρ))]
    simp_rw [MeasureTheory.integral_finsetSum Finset.univ (fun ρ _ => hint2 _ ρ)]
    have heval : ∀ τ ρ : Equiv.Perm (Fin n),
        (∫ x : Fin n → X, ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ)
          * ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)) ∂(Measure.pi fun _ : Fin n => μ))
        = ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ) * ∏ i, M (τ i) (ρ i) := by
      intro τ ρ
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_fintype_prod_eq_prod (fun i x => φ (τ i) x * ψ (ρ i) x)]
      simp only [hM, Matrix.of_apply]
    simp_rw [heval]
    exact sum_sign_mul_prod M
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [hmain, inv_mul_cancel_left₀ hfact]

/-- Specialization to moment matrices: with `φᵢ = ψᵢ = X^i`, both pointwise
determinants are transposes of Vandermonde determinants, giving the
squared-Vandermonde form. -/
theorem andreief_moment_det {n : ℕ} (μ : Measure ℝ) [MeasureTheory.SigmaFinite μ]
    (hint : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ ((i : ℕ) + (j : ℕ))) μ) :
    (Matrix.of fun i j : Fin n => ∫ x, x ^ ((i : ℕ) + (j : ℕ)) ∂μ).det
      = (Nat.factorial n : ℝ)⁻¹ * ∫ x : Fin n → ℝ,
          ((Matrix.vandermonde x).det ^ 2) ∂(Measure.pi fun _ : Fin n => μ) := by
  have hint' : ∀ i j : Fin n,
      Integrable (fun x : ℝ => (x ^ (i : ℕ)) * (x ^ (j : ℕ))) μ := by
    intro i j
    simpa [pow_add] using hint i j
  have hmain := andreief_integral μ (fun i (x : ℝ) => x ^ (i : ℕ))
    (fun i (x : ℝ) => x ^ (i : ℕ)) hint'
  have hmat : (Matrix.of fun i j : Fin n => ∫ x : ℝ, (x ^ (i : ℕ)) * (x ^ (j : ℕ)) ∂μ)
      = Matrix.of fun i j : Fin n => ∫ x : ℝ, x ^ ((i : ℕ) + (j : ℕ)) ∂μ := by
    ext i j
    simp only [Matrix.of_apply]
    congr 1
    ext x
    rw [pow_add]
  have hvand : ∀ x : Fin n → ℝ, (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ)).det
      = (Matrix.vandermonde x).det := by
    intro x
    have h : (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ))
        = Matrix.transpose (Matrix.vandermonde x) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [h, Matrix.det_transpose]
  have hsq : ∀ x : Fin n → ℝ, (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ)).det
        * (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ)).det
        = (Matrix.vandermonde x).det ^ 2 := by
    intro x
    rw [hvand x, pow_two]
  have hRHS : (∫ x : Fin n → ℝ, (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ)).det
        * (Matrix.of fun (i j : Fin n) => (x j) ^ (i : ℕ)).det
        ∂(Measure.pi fun _ : Fin n => μ))
      = ∫ x : Fin n → ℝ, (Matrix.vandermonde x).det ^ 2
        ∂(Measure.pi fun _ : Fin n => μ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    exact hsq x
  rw [← hmat, ← hRHS]
  exact hmain

/-- Explicit double-product form of the squared Vandermonde factor. -/
theorem andreief_moment_det_prod {n : ℕ} (μ : Measure ℝ) [MeasureTheory.SigmaFinite μ]
    (hint : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ ((i : ℕ) + (j : ℕ))) μ) :
    (Matrix.of fun i j : Fin n => ∫ x, x ^ ((i : ℕ) + (j : ℕ)) ∂μ).det
      = (Nat.factorial n : ℝ)⁻¹ * ∫ x : Fin n → ℝ,
          ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2)
          ∂(Measure.pi fun _ : Fin n => μ) := by
  rw [andreief_moment_det μ hint]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  rw [Matrix.det_vandermonde]

end ZetaSeven.Andreief
