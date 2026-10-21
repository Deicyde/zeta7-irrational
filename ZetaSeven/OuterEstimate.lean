import ZetaSeven.GaussRankLemma
import ZetaSeven.LargePrimeIntegrality
import ZetaSeven.OuterClassBasis
import ZetaSeven.OuterEntryValuations
import ZetaSeven.OuterRankDecomposition
import ZetaSeven.OuterWeightSum

/-!
# Outer range estimate (paper Section 4.2, Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2, Proposition 4.6: under the outer-range
hypothesis (52), `v^G_p(Δ_K) ≥ γ^out_p`, and `v^G_p(Δ_K) ≥ 0` for every prime `p > K`.
As in `ZetaSeven.inner_estimate`, the Gauss valuation `v^G_p` is stated coefficientwise with
`padicValRat`.

* `outer_estimate`: under (52), every nonzero coefficient of `Δ_K(X)` has `p`-adic valuation
  at least `γ^out_p` (`ZetaSeven.gammaOut`).
* `outer_estimate_of_K_lt`: for a prime `p > K`, every coefficient of `Δ_K(X)` is `p`-integral,
  since `Δ_K = det G_K` lies in the subring `pIntPoly p` with every entry of `G_K`
  (`DeltaK_mem_pIntPoly`, from `ZetaSeven.Gentry_mem_pIntPoly`).

The proof of the first clause follows the article's assembly. For an enumeration `e` of the
outer class rows, let `U` be the matrix of their coefficients in the monomial basis
(`outerUmat`; `det U` is an integer prime to `p` by `ZetaSeven.outer_class_basis`). Then

* `U G_K Uᵀ = A' + p⁻¹ (U L Uᵀ)` (`OuterRange.gram_eq`), with `A'_{rs} = μ_0(r s D_N⁷/D_tail)`
  the modified Gram matrix `ZetaSeven.outerAprime` in the class basis
  (`OuterRange.outerAprime_reindex_eq`), by the rank decomposition `G_K = A + p⁻¹ L`
  (`ZetaSeven.Gmat_eq_outerAmat_add`) and the linearity of `μ_0(·/D_tail)`
  (`muZeroTail_add`, `muZeroTail_smul`, `OuterRange.outerAprime_eq_sum`);
* `U L Uᵀ` is `p`-integral (`outerUmat_mul_outerLmat_integral`) of rank at most `r_p`
  (`rank_outerUmat_mul_outerLmat_le`);
* `det(U G_K Uᵀ) = (det U)² Δ_K` (`det_outerUmat_gram`).

The entry valuations (`ZetaSeven.outer_entry_valuations_dbl`), the Gauss-valuation rank lemma
(`ZetaSeven.gauss_rank_lemma`) and the weight sum (`ZetaSeven.outer_weight_sum`) then bound
`v^G_p det(U G_K Uᵀ)` below by `γ^out_p`, and `det U` is a `p`-unit.
-/

namespace ZetaSeven

open Polynomial Finset
open scoped Matrix

/-! ## Large primes -/

/-- The determinant of a matrix whose entries lie in a subring lies in the subring. -/
private theorem outer_det_mem_of_entries_mem {R : Type*} [CommRing R] (S : Subring R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (hM : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

/-- For a prime `p > K`, `Δ_K = det G_K` has `p`-integral coefficients, since every entry of
`G_K` does (`ZetaSeven.Gentry_mem_pIntPoly`). -/
theorem DeltaK_mem_pIntPoly {n p : ℕ} [Fact p.Prime] (hpK : K n < p) :
    DeltaK n ∈ pIntPoly p := by
  unfold DeltaK
  refine outer_det_mem_of_entries_mem _ (Gmat n) fun i j => ?_
  simp only [Gmat, Matrix.of_apply]
  exact Gentry_mem_pIntPoly hpK i.isLt j.isLt

/-- **Outer estimate**, case `p > K` (Proposition 4.6, second sentence). For every prime
`p > K`, `v^G_p(Δ_K) ≥ 0`: every coefficient of `Δ_K(X)` has `p`-adic valuation at least `0`
(for the coefficient `0` this is Lean's `padicValRat p 0 = 0`). -/
theorem outer_estimate_of_K_lt {n p : ℕ} [Fact p.Prime] (hpK : K n < p) (k : ℕ) :
    0 ≤ padicValRat p ((DeltaK n).coeff k) :=
  mem_pInt_iff_padicValRat.mp (mem_pIntPoly.mp (DeltaK_mem_pIntPoly hpK) k)

/-! ## Linearity of `μ_0(·/D_tail)` -/

private theorem outer_muZeroFunctional_add (p : ℕ) (P₁ P₂ : ℚ[X]) (c₁ c₂ : ℕ →₀ ℚ) :
    muZeroFunctional p (P₁ + P₂) (c₁ + c₂) =
      muZeroFunctional p P₁ c₁ + muZeroFunctional p P₂ c₂ := by
  unfold muZeroFunctional
  rw [Polynomial.sum_add_index _ _ _ (fun i => by simp) (fun a b₁ b₂ => by rw [C_add, add_mul]),
    Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by rw [C_add, add_mul])]
  ring

private theorem outer_muZeroFunctional_smul (p : ℕ) (r : ℚ) (P : ℚ[X]) (c : ℕ →₀ ℚ) :
    muZeroFunctional p (r • P) (r • c) = C r * muZeroFunctional p P c := by
  unfold muZeroFunctional
  rw [Polynomial.sum_smul_index _ _ _ (fun i => by simp),
    Finsupp.sum_smul_index' (fun i => by simp)]
  simp only [Polynomial.sum_def, Finsupp.sum, mul_add, Finset.mul_sum, smul_eq_mul, C_mul,
    mul_assoc]

private theorem outer_div_Dtail (n : ℕ) (Q : ℚ[X]) : Q.div (Dtail n) = Q /ₘ Dtail n :=
  (divByMonic_eq_div Q (OuterEntry.monic_Dtail n)).symm

/-- `μ_0(·/D_tail)` is additive. -/
theorem muZeroTail_add (p n : ℕ) (Q₁ Q₂ : ℚ[X]) :
    muZeroTail p n (Q₁ + Q₂) = muZeroTail p n Q₁ + muZeroTail p n Q₂ := by
  unfold muZeroTail outerTailPoles outerTailRes
  rw [← outer_muZeroFunctional_add]
  congr 1
  · rw [outer_div_Dtail, outer_div_Dtail, outer_div_Dtail, add_divByMonic]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finsupp.single_add, eval_add, add_div]

/-- `μ_0(·/D_tail)` is homogeneous over `ℚ`. -/
theorem muZeroTail_smul (p n : ℕ) (r : ℚ) (Q : ℚ[X]) :
    muZeroTail p n (r • Q) = C r * muZeroTail p n Q := by
  unfold muZeroTail outerTailPoles outerTailRes
  rw [← outer_muZeroFunctional_smul]
  congr 1
  · rw [outer_div_Dtail, outer_div_Dtail, smul_divByMonic]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.smul_single, eval_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc]

/-- `μ_0(·/D_tail)` as a `ℚ`-linear map. -/
private noncomputable def outerMuZeroTailLin (p n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := muZeroTail p n
  map_add' := muZeroTail_add p n
  map_smul' r Q := by rw [muZeroTail_smul, RingHom.id_apply, smul_eq_C_mul]

/-! ## The class basis matrix `U` and the bilinearity of `A'` -/

/-- For an enumeration `e` of the outer class rows (`ZetaSeven.outerRow`, indexed by
`ZetaSeven.outerIdx`), the matrix `U` of their coefficients in the monomial basis
`1, t, …, t^{h-1}`: row `k` holds the coefficients of the row `e⁻¹(k)`. The entries are
integers, read in `ℚ`; `outerUmat_det` identifies `det U` with the determinant of the integer
matrix of `ZetaSeven.outer_class_basis`. -/
noncomputable def outerUmat (n p : ℕ) (e : outerIdx n p ≃ Fin (hDim n)) :
    Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun k l => ((outerRow n p (e.symm k)).coeff l : ℚ)

/-- `det U` is the determinant of the integer matrix of `ZetaSeven.outer_class_basis`. -/
theorem outerUmat_det {n p : ℕ} (e : outerIdx n p ≃ Fin (hDim n)) :
    (outerUmat n p e).det =
      ((Matrix.of fun k l : Fin (hDim n) => (outerRow n p (e.symm k)).coeff l).det : ℚ) := by
  rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1

/-- Under (52), every outer class row, read in `ℚ[X]`, is `∑_{i<h} U_{r,i} t^i`. -/
theorem OuterRange.map_outerRow_eq_sum {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (ρ : outerIdx n p) :
    (outerRow n p ρ).map (Int.castRingHom ℚ)
      = ∑ i : Fin (hDim n), C (((outerRow n p ρ).coeff i : ℤ) : ℚ) * X ^ (i : ℕ) := by
  have hdeg : ((outerRow n p ρ).map (Int.castRingHom ℚ)).natDegree < hDim n :=
    natDegree_map_le.trans_lt (hR.natDegree_outerRow_lt ρ)
  conv_lhs => rw [as_sum_range_C_mul_X_pow' _ hdeg]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => C (((outerRow n p ρ).map (Int.castRingHom ℚ)).coeff i) * X ^ i)]
  simp only [coeff_map, eq_intCast]

/-- Bilinearity: under (52), the entry `A'_{rs} = μ_0(r s D_N⁷/D_tail)` of the modified Gram
matrix in the class basis is `∑_{i,j<h} U_{r,i} U_{s,j} A_{ij}`, where
`A_{ij} = μ_0(D_N⁷ t^{i+j}/D_tail)` are the entries of (53) (`ZetaSeven.outerAentry`). -/
theorem OuterRange.outerAprime_eq_sum {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (ρ σ : outerIdx n p) :
    outerAprime p n ρ σ = ∑ i : Fin (hDim n), ∑ j : Fin (hDim n),
      C (((outerRow n p ρ).coeff i : ℚ) * ((outerRow n p σ).coeff j : ℚ))
        * outerAentry p n i j := by
  have h : (outerRow n p ρ * outerRow n p σ).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7
      = ∑ i : Fin (hDim n), ∑ j : Fin (hDim n),
          (((outerRow n p ρ).coeff i : ℚ) * ((outerRow n p σ).coeff j : ℚ)) • Rnum n i j := by
    rw [Polynomial.map_mul, hR.map_outerRow_eq_sum ρ, hR.map_outerRow_eq_sum σ,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, Rnum, C_mul]
    ring
  show muZeroTail p n ((outerRow n p ρ * outerRow n p σ).map (Int.castRingHom ℚ)
    * Dpoly (N n) ^ 7) = _
  rw [h]
  change outerMuZeroTailLin p n _ = _
  simp only [map_sum, map_smul]
  simp only [smul_eq_C_mul]
  rfl

/-- Under (52), the modified Gram matrix `A'` in the class basis, reindexed by `e`, is
`U A Uᵀ`, with `A` the matrix of (53) (`ZetaSeven.outerAmat`). -/
theorem OuterRange.outerAprime_reindex_eq {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (e : outerIdx n p ≃ Fin (hDim n)) :
    (Matrix.of fun k l : Fin (hDim n) => outerAprime p n (e.symm k) (e.symm l))
      = (outerUmat n p e).map C * outerAmat p n * ((outerUmat n p e).map C)ᵀ := by
  refine Matrix.ext fun k l => ?_
  rw [Matrix.of_apply, hR.outerAprime_eq_sum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, outerUmat,
    Matrix.of_apply, outerAmat, Finset.sum_mul]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_mul]
  ring

/-- `(c • M).map C = c • M.map C` for a rational matrix `M`. -/
private theorem outer_map_C_smul {m l : Type*} (c : ℚ) (M : Matrix m l ℚ) :
    (c • M).map (C : ℚ →+* ℚ[X]) = c • M.map (C : ℚ →+* ℚ[X]) :=
  Matrix.map_smul _ c (fun a => (smul_C c a).symm) M

/-- Under (52), `U G_K Uᵀ = A' + p⁻¹ (U L Uᵀ)`, with `A'` the modified Gram matrix in the
class basis reindexed by `e` and `L` the integer matrix of (53) (`ZetaSeven.outerLmat`), from
`G_K = A + p⁻¹ L` (`ZetaSeven.Gmat_eq_outerAmat_add`). -/
theorem OuterRange.outerUmat_gram_eq {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (e : outerIdx n p ≃ Fin (hDim n)) :
    (outerUmat n p e).map C * Gmat n * ((outerUmat n p e).map C)ᵀ
      = (Matrix.of fun k l : Fin (hDim n) => outerAprime p n (e.symm k) (e.symm l))
        + ((p : ℚ)⁻¹ • (outerUmat n p e * outerLmat p n * (outerUmat n p e)ᵀ)).map C := by
  rw [Gmat_eq_outerAmat_add p n, Matrix.mul_add, Matrix.add_mul, hR.outerAprime_reindex_eq e,
    add_right_inj, Matrix.mul_smul, Matrix.smul_mul, outer_map_C_smul, Matrix.map_mul,
    Matrix.map_mul, Matrix.transpose_map]

/-- `det(U G_K Uᵀ) = (det U)² Δ_K`. -/
theorem det_outerUmat_gram {n p : ℕ} (e : outerIdx n p ≃ Fin (hDim n)) :
    ((outerUmat n p e).map C * Gmat n * ((outerUmat n p e).map C)ᵀ).det
      = C ((outerUmat n p e).det ^ 2) * DeltaK n := by
  have hC : ((outerUmat n p e).map C).det = C (outerUmat n p e).det :=
    (RingHom.map_det C (outerUmat n p e)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, DeltaK, hC, C_pow]
  ring

/-! ## The matrix `U L Uᵀ` -/

private theorem outer_mul_apply_mem_pInt {p : ℕ} [Fact p.Prime] {m l o : Type*} [Fintype l]
    (A : Matrix m l ℚ) (B : Matrix l o ℚ) (hA : ∀ a b, A a b ∈ pInt p)
    (hB : ∀ a b, B a b ∈ pInt p) (i : m) (j : o) : (A * B) i j ∈ pInt p := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

/-- `U L Uᵀ` is `p`-integral: its entries are integers, since `U` and `L`
(`ZetaSeven.exists_outerLmat_eq_map_intCast`) are integer matrices. -/
theorem outerUmat_mul_outerLmat_integral {n p : ℕ} [Fact p.Prime]
    (e : outerIdx n p ≃ Fin (hDim n)) (i j : Fin (hDim n)) :
    0 ≤ padicValRat p ((outerUmat n p e * outerLmat p n * (outerUmat n p e)ᵀ) i j) := by
  obtain ⟨L, hL⟩ := exists_outerLmat_eq_map_intCast p n
  have hU : ∀ a b, outerUmat n p e a b ∈ pInt p := fun a b => by
    simp only [outerUmat, Matrix.of_apply]
    exact intCast_mem _ _
  have hLm : ∀ a b, outerLmat p n a b ∈ pInt p := fun a b => by
    rw [hL, Matrix.map_apply]
    exact intCast_mem _ _
  exact mem_pInt_iff_padicValRat.mp (outer_mul_apply_mem_pInt _ _
    (fun a b => outer_mul_apply_mem_pInt _ _ hU hLm a b) (fun a b => hU b a) i j)

/-- `rank(U L Uᵀ) ≤ rank L ≤ r_p` (`ZetaSeven.rank_outerLmat_le`). -/
theorem rank_outerUmat_mul_outerLmat_le {n p : ℕ} (e : outerIdx n p ≃ Fin (hDim n)) :
    (outerUmat n p e * outerLmat p n * (outerUmat n p e)ᵀ).rank ≤ rankCorr n p :=
  (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (rank_outerLmat_le p n))

/-! ## The outer estimate -/

/-- **Outer estimate** (Proposition 4.6, first sentence). Let `p` be a prime satisfying the
outer-range hypothesis (52). Then `v^G_p(Δ_K) ≥ γ^out_p`: every nonzero coefficient of
`Δ_K(X)` has `p`-adic valuation at least the outer exponent `γ^out_p` (`ZetaSeven.gammaOut`). -/
theorem outer_estimate {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p) (k : ℕ)
    (hk : (DeltaK n).coeff k ≠ 0) : gammaOut n p ≤ padicValRat p ((DeltaK n).coeff k) := by
  obtain ⟨e⟩ : Nonempty (outerIdx n p ≃ Fin (hDim n)) :=
    ⟨Fintype.equivFinOfCardEq hR.card_outerIdx_eq_hDim⟩
  have hsum : ∑ i : Fin (hDim n), outerFamWeightDbl n p (e.symm i).1 (e.symm i).2
      = ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2 :=
    Equiv.sum_comp e.symm (fun ρ : outerIdx n p => outerFamWeightDbl n p ρ.1 ρ.2)
  have hcard : (univ.filter fun i : Fin (hDim n) =>
        outerFamWeightDbl n p (e.symm i).1 (e.symm i).2 = 0).card
      = (univ.filter fun ρ : outerIdx n p => outerFamWeightDbl n p ρ.1 ρ.2 = 0).card :=
    Finset.card_equiv e.symm fun i => by simp
  have hgauss := gauss_rank_lemma (p := p) (r := rankCorr n p)
    (fun i => outerFamWeightDbl n p (e.symm i).1 (e.symm i).2)
    (Matrix.of fun i j => outerAprime p n (e.symm i) (e.symm j))
    (outerUmat n p e * outerLmat p n * (outerUmat n p e)ᵀ)
    (fun i => outerFamWeightDbl_nonpos n p _ _) hcard
    (fun i j l => outer_entry_valuations_dbl hR (e.symm i) (e.symm j) l)
    (outerUmat_mul_outerLmat_integral e) (rank_outerUmat_mul_outerLmat_le e) k
  rw [← hR.outerUmat_gram_eq e, det_outerUmat_gram e, coeff_C_mul, outerUmat_det] at hgauss
  obtain ⟨hd0, hdv⟩ :=
    intCast_ne_zero_and_padicValRat_eq_zero (p := p) (hR.outerRow_unimodular e)
  rw [padicValRat.mul (pow_ne_zero 2 hd0) hk, padicValRat.pow, hdv, mul_zero, zero_add]
    at hgauss
  have hw := outer_weight_sum hR
  rw [← hsum] at hw
  exact hw.trans hgauss

end ZetaSeven
