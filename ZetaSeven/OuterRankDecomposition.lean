import ZetaSeven.OuterModifiedFunctional
import ZetaSeven.OuterRangeData

/-!
# Outer rank decomposition (paper Section 4.2.1, equations (53)-(54))

Prince Anand, "Zeta 7 is Irrational", Section 4.2.1, equation (53) and the rank count
leading to (54). With the corrections `c_e`, the modified functional `μ_0` and the matrices
`A` (`ZetaSeven.outerAmat`) and `L` (`ZetaSeven.outerLmat`) of the outer modified
functional, and the rank correction `r_p` (`ZetaSeven.rankCorr`) of the outer range data:

* `G_K = A + p⁻¹ L` (`Gmat_eq_outerAmat_add`), entry by entry
  (`Gentry_eq_outerAentry_add`), since `μ_X(t^e) = μ_0(t^e) + c_e/p` on monomials and the
  two functionals agree on the simple poles;
* `L` is an integer matrix (`exists_outerLmat_eq_map_intCast`), since `D_K` is monic in
  `ℤ[t]`, so the polynomial part `P_{ij}` has integer coefficients (`polyPart_eq_map`);
* `rank_ℚ L ≤ r_p` (`rank_outerLmat_le`): `[t^e] P_{ij} ≠ 0` forces
  `e ≤ i + j + 8N - K` (`le_of_mem_support_polyPart`), and `c_e = 0` for `e < 3p - 4`, so
  `L_{ij} = 0` for `i + j < T = K - 8N + 3p - 4` (`outerLentry_eq_zero`), row `i` of `L`
  vanishes for `i ≤ T - h` (`outerLmat_row_eq_zero`), and at most
  `min(h, max(0, 2h - T)) = r_p` rows are nonzero (`nonzero_rows_outerLmat_le`,
  `two_hDim_sub_threshold`).

The paper's (53) also asserts that `A` is integral at every prime; that is false in the
monomial basis (source-map erratum 1), and nothing is claimed about it here. The
statements hold for every natural number `p`; the source takes `p` prime.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The polynomial part over `ℤ` -/

/-- `D_m` over `ℤ`: `∏_{j=1}^m (t + j²)`. -/
noncomputable def DpolyZ (m : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range m, (X + C (((j : ℤ) + 1) ^ 2))

/-- The tail divisor `D_tail = D_K/D_N = ∏_{N<j≤K} (t + j²)` over `ℤ`. -/
noncomputable def DtailZ (n : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Icc (N n + 1) (K n), (X + C ((j : ℤ) ^ 2))

/-- The numerator `D_N⁷ t^{i+j}` over `ℤ`. -/
noncomputable def RnumZ (n i j : ℕ) : Polynomial ℤ := DpolyZ (N n) ^ 7 * X ^ (i + j)

theorem map_DpolyZ (m : ℕ) : (DpolyZ m).map (Int.castRingHom ℚ) = Dpoly m := by
  simp [DpolyZ, Dpoly, Polynomial.map_prod]

theorem map_DtailZ (n : ℕ) : (DtailZ n).map (Int.castRingHom ℚ) = Dtail n := by
  simp [DtailZ, Dtail, Polynomial.map_prod]

theorem map_RnumZ (n i j : ℕ) : (RnumZ n i j).map (Int.castRingHom ℚ) = Rnum n i j := by
  simp [RnumZ, Rnum, map_DpolyZ]

theorem monic_DtailZ (n : ℕ) : (DtailZ n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- The polynomial part `P_{ij}` of `D_N⁸ t^{i+j}/D_K` is the image of the integer
polynomial `D_N⁷ t^{i+j} /ₘ D_tail`, so it has integer coefficients. -/
theorem polyPart_eq_map (n i j : ℕ) :
    polyPart n i j = (RnumZ n i j /ₘ DtailZ n).map (Int.castRingHom ℚ) := by
  have hm : (Dtail n).Monic := by
    rw [← map_DtailZ]
    exact (monic_DtailZ n).map _
  rw [Polynomial.map_divByMonic _ (monic_DtailZ n), map_RnumZ, map_DtailZ]
  exact (divByMonic_eq_div _ hm).symm

theorem natDegree_DpolyZ_le (m : ℕ) : (DpolyZ m).natDegree ≤ m := by
  unfold DpolyZ
  refine (natDegree_prod_le _ _).trans ?_
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    le_refl]

theorem natDegree_RnumZ_le (n i j : ℕ) : (RnumZ n i j).natDegree ≤ 7 * N n + (i + j) := by
  unfold RnumZ
  have h1 : (DpolyZ (N n) ^ 7).natDegree ≤ 7 * N n :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 7 (natDegree_DpolyZ_le _))
  have h2 : (X ^ (i + j) : Polynomial ℤ).natDegree ≤ i + j := natDegree_X_pow_le _
  exact natDegree_mul_le.trans (Nat.add_le_add h1 h2)

/-- `deg D_tail = K - N`. -/
theorem natDegree_DtailZ (n : ℕ) : (DtailZ n).natDegree = K n - N n := by
  unfold DtailZ
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

/-- The degree bound for the polynomial part: `[t^e] P_{ij} ≠ 0` forces
`e ≤ i + j + 8N - K`. -/
theorem le_of_mem_support_polyPart {n i j e : ℕ} (he : e ∈ (polyPart n i j).support) :
    e + K n ≤ i + j + 8 * N n := by
  rw [polyPart_eq_map, support_map_of_injective _ (Int.castRingHom ℚ).injective_int] at he
  have hne : RnumZ n i j /ₘ DtailZ n ≠ 0 := by
    rintro h
    rw [h, support_zero] at he
    exact Finset.notMem_empty e he
  have hdeg : (DtailZ n).natDegree ≤ (RnumZ n i j).natDegree := by
    by_contra hlt
    exact hne ((divByMonic_eq_zero_iff (monic_DtailZ n)).mpr (degree_lt_degree (not_le.mp hlt)))
  have h1 := le_natDegree_of_mem_supp e he
  rw [natDegree_divByMonic _ (monic_DtailZ n)] at h1
  have h2 := natDegree_RnumZ_le n i j
  have h3 := natDegree_DtailZ n
  have hNK : N n ≤ K n := by unfold N K; omega
  omega

/-! ## The decomposition `G_K = A + p⁻¹ L` -/

/-- On a polynomial `P`, `μ_X(P) = μ_0(P) + p⁻¹ ∑_e c_e [t^e] P`, since
`μ_X(t^e) = μ_0(t^e) + c_e/p`. -/
private theorem polySum_eq_muZero_add (p : ℕ) (P : ℚ[X]) :
    P.sum (fun e a => C a * C (muMonomial e)) =
      P.sum (fun e a => C a * C (muZeroMonomial p e)) +
        C ((p : ℚ)⁻¹ * P.sum fun e a => (outerCe p e : ℚ) * a) := by
  simp only [Polynomial.sum_def, Finset.mul_sum, map_sum, ← Finset.sum_add_distrib, ← C_mul,
    ← C_add]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [muZeroMonomial]
  congr 1
  ring

/-- (53) entry by entry: `G_K(i,j) = A_{ij} + p⁻¹ L_{ij}`. -/
theorem Gentry_eq_outerAentry_add (p n i j : ℕ) :
    Gentry n i j = outerAentry p n i j + C ((p : ℚ)⁻¹ * outerLentry p n i j) := by
  rw [Gentry, outerAentry, muFunctional, muZeroFunctional, outerLentry,
    polySum_eq_muZero_add p]
  ring

/-- (53): `G_K = A + p⁻¹ L`, with the rational matrix `L` lifted to `ℚ[X]` by `C`. -/
theorem Gmat_eq_outerAmat_add (p n : ℕ) :
    Gmat n = outerAmat p n + (p : ℚ)⁻¹ • (outerLmat p n).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [Gmat, outerAmat, outerLmat, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.of_apply, smul_C, smul_eq_mul]
  exact Gentry_eq_outerAentry_add p n i j

/-! ## `L` is an integer matrix -/

/-- `L_{ij} = ∑_e c_e [t^e] P_{ij}` is the integer `∑_e c_e [t^e] (D_N⁷ t^{i+j} /ₘ D_tail)`. -/
theorem outerLentry_eq_intCast (p n i j : ℕ) :
    outerLentry p n i j =
      (((RnumZ n i j /ₘ DtailZ n).sum fun e a => (outerCe p e : ℤ) * a : ℤ) : ℚ) := by
  rw [outerLentry, polyPart_eq_map, Polynomial.sum_def, Polynomial.sum_def,
    support_map_of_injective _ (Int.castRingHom ℚ).injective_int, Int.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [coeff_map, eq_intCast, Int.cast_mul, Int.cast_natCast]

/-- `L` is an integer matrix. -/
theorem exists_outerLmat_eq_map_intCast (p n : ℕ) :
    ∃ L : Matrix (Fin (hDim n)) (Fin (hDim n)) ℤ, outerLmat p n = L.map (Int.cast : ℤ → ℚ) := by
  refine ⟨Matrix.of fun i j =>
    (RnumZ n (i : ℕ) (j : ℕ) /ₘ DtailZ n).sum fun e a => (outerCe p e : ℤ) * a, ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [outerLmat, Matrix.map_apply, Matrix.of_apply]
  exact outerLentry_eq_intCast p n i j

/-! ## The rank bound (54) -/

/-- (54) arithmetic: with `T = K - 8N + 3p - 4` and `h = 37K/40`, `N = 3K/40`,
`2h - T = K + 6N - 3p + 4`. -/
theorem two_hDim_sub_threshold (n p : ℕ) :
    2 * (hDim n : ℤ) - ((K n : ℤ) - 8 * N n + 3 * p - 4) = K n + 6 * N n - 3 * p + 4 := by
  simp only [hDim, K, N]
  push_cast
  ring

/-- `L_{ij} = 0` when `i + j < T = K - 8N + 3p - 4`: every `e` with `[t^e] P_{ij} ≠ 0` has
`e ≤ i + j + 8N - K < 3p - 4`, where `c_e = 0`. -/
theorem outerLentry_eq_zero {p n i j : ℕ}
    (h : (i : ℤ) + j < (K n : ℤ) - 8 * N n + 3 * p - 4) : outerLentry p n i j = 0 := by
  rw [outerLentry, Polynomial.sum_def]
  refine Finset.sum_eq_zero fun e he => ?_
  have h1 := le_of_mem_support_polyPart he
  have he' : e < 3 * p - 4 := by omega
  rw [outerCe_of_lt he', Nat.cast_zero, zero_mul]

/-- Row `i` of `L` vanishes when `i ≤ T - h`, i.e. `i + h ≤ T`. -/
theorem outerLmat_row_eq_zero {p n : ℕ} (i : Fin (hDim n))
    (h : ((i : ℕ) : ℤ) + hDim n ≤ (K n : ℤ) - 8 * N n + 3 * p - 4) : outerLmat p n i = 0 := by
  funext j
  have hj := j.isLt
  simp only [outerLmat, Matrix.of_apply, Pi.zero_apply]
  exact outerLentry_eq_zero (by omega)

/-- At most `min(h, max(0, 2h - T)) = r_p` rows of `L` are nonzero: the rows `i ≤ T - h`
vanish, and at most `r_p` indices `0 ≤ i < h` satisfy `i > T - h`. -/
theorem nonzero_rows_outerLmat_le (p n : ℕ) :
    ∃ S : Finset (Fin (hDim n)), S.card ≤ rankCorr n p ∧ ∀ i ∉ S, outerLmat p n i = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = Int.toNat ((K n : ℤ) - 8 * N n + 3 * p - 4 - hDim n + 1) :=
    ⟨_, rfl⟩
  refine ⟨Finset.univ.filter fun i : Fin (hDim n) => a ≤ (i : ℕ), ?_, fun i hi => ?_⟩
  · have hmaps : Set.MapsTo (fun i : Fin (hDim n) => (i : ℕ))
        (Finset.univ.filter fun i : Fin (hDim n) => a ≤ (i : ℕ)) (Finset.Ico a (hDim n)) := by
      intro i hi
      exact Finset.mem_coe.2
        (Finset.mem_Ico.2 ⟨(Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2, i.isLt⟩)
    have h1 := Finset.card_le_card_of_injOn _ hmaps Fin.val_injective.injOn
    rw [Nat.card_Ico] at h1
    have hK : K n = 40 * n := rfl
    have hN : N n = 3 * n := rfl
    have hh : hDim n = 37 * n := rfl
    unfold rankCorr
    omega
  · have hlt : ¬ a ≤ (i : ℕ) := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    exact outerLmat_row_eq_zero i (by omega)

/-- A rational matrix whose rows outside `S` vanish has rank at most `|S|`. -/
private theorem rank_le_card_of_row_eq_zero {m : Type*} [Fintype m] {k : ℕ}
    (A : Matrix m (Fin k) ℚ) (S : Finset m) (hS : ∀ i ∉ S, A i = 0) : A.rank ≤ S.card := by
  have hle : Submodule.span ℚ (Set.range A.row) ≤
      Submodule.span ℚ (Set.range fun i : S => A i) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ S
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Matrix.row_apply', hS i hi]
      exact Submodule.zero_mem _
  rw [Matrix.rank_eq_finrank_span_row]
  refine (Submodule.finrank_mono hle).trans ((finrank_range_le_card (R := ℚ) _).trans ?_)
  exact (Fintype.card_coe _).le

/-- (54): `rank_ℚ L ≤ r_p`. -/
theorem rank_outerLmat_le (p n : ℕ) : (outerLmat p n).rank ≤ rankCorr n p := by
  obtain ⟨S, hS, hrow⟩ := nonzero_rows_outerLmat_le p n
  exact (rank_le_card_of_row_eq_zero _ S hrow).trans hS

/-- Section 4.2.1, (53)-(54): `G_K = A + p⁻¹ L` with `L` lifted to `ℚ[X]` by `C`, `L` is an
integer matrix, and `rank_ℚ L ≤ r_p`. Stated for every natural number `p`; the source
takes `p` prime. -/
theorem outer_rank_decomposition (p n : ℕ) :
    Gmat n = outerAmat p n + (p : ℚ)⁻¹ • (outerLmat p n).map C ∧
      (∃ L : Matrix (Fin (hDim n)) (Fin (hDim n)) ℤ,
        outerLmat p n = L.map (Int.cast : ℤ → ℚ)) ∧
      (outerLmat p n).rank ≤ rankCorr n p :=
  ⟨Gmat_eq_outerAmat_add p n, exists_outerLmat_eq_map_intCast p n, rank_outerLmat_le p n⟩

end ZetaSeven
