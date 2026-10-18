import ZetaSeven.ExternalField

/-!
# Comparison measure (paper Lemma 6.1; Appendix A.1, Table 1, equation (109))

The comparison measure `ρ = Σ_{j=1}^{16} c_j ω_{[0,L_j]}` of Lemma 6.1: a sum of sixteen
arcsine components on the nested intervals `[0, L_j]` of Table 1, where `ω_{[0,L]}` is the
probability measure on `(0, L)` with density `1 / (π √(t (L - t)))`.

Table 1 lists the integers `10^12 L_j` and `10^12 c_j`; they are recorded verbatim and scaled
by `10^12`. The facts the paper reads off the table are proved here: the weights sum to
`λ = 37/40`, so `ρ` has total mass `37/40` (each arcsine component has mass one); the
intervals are nested, `0 < L_16 < ⋯ < L_1 < 2`; and every length `L_j` exceeds `1/225`.

Equation (109), the closed form of the potential `U_{ω_{[0,L]}}(t)` (`ZetaSeven.Ulog`) for
`t ≥ 0`, is recorded as a definition, together with its weighted sum over Table 1. Its
identification with the integral potential is proved where it is used.
-/

namespace ZetaSeven

open MeasureTheory

/-- Appendix A.1, Table 1: the integers `10^12 L_j` for `j = 1, …, 16` (at index `j - 1`). -/
def tableLNum : Fin 16 → ℕ :=
  ![870000000000, 800000000000, 700000000000, 600000000000,
    500000000000, 400000000000, 300000000000, 250000000000,
    200000000000, 150000000000, 120000000000, 100000000000,
    80000000000, 60000000000, 40000000000, 20000000000]

/-- Appendix A.1, Table 1: the integers `10^12 c_j` for `j = 1, …, 16` (at index `j - 1`). -/
def tableCNum : Fin 16 → ℕ :=
  ![100000000000, 80000000000, 60000000000, 50000000000,
    50000000000, 50000000000, 50000000000, 50000000000,
    50000000000, 50000000000, 50000000000, 50000000000,
    50000000000, 50000000000, 15000000000, 120000000000]

/-- Appendix A.1, Table 1: the endpoint `L_j` of the `j`-th interval `[0, L_j]`. -/
noncomputable def compEndpoint (j : Fin 16) : ℝ := (tableLNum j : ℝ) / 10 ^ 12

/-- Appendix A.1, Table 1: the weight `c_j` of the `j`-th arcsine component. -/
noncomputable def compWeight (j : Fin 16) : ℝ := (tableCNum j : ℝ) / 10 ^ 12

/-- Appendix A.1: the density `1 / (π √((t - 0)(L - t)))` of the unit arcsine measure
`ω_{[0,L]}` on `(0, L)`. -/
noncomputable def arcsineDensity (L t : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (t * (L - t)))

/-- Appendix A.1: the unit arcsine measure `ω_{[0,L]}`, the measure on `(0, L)` with density
`1 / (π √(t (L - t)))`. For `L > 0` it is a probability measure
(`isProbabilityMeasure_arcsineMeasure`). -/
noncomputable def arcsineMeasure (L : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo 0 L)).withDensity fun t => ENNReal.ofReal (arcsineDensity L t)

/-- Lemma 6.1 and Appendix A.1: the comparison measure `ρ = Σ_{j=1}^{16} c_j ω_{[0,L_j]}`. -/
noncomputable def compMeasure : Measure ℝ :=
  ∑ j : Fin 16, ENNReal.ofReal (compWeight j) • arcsineMeasure (compEndpoint j)

/-- Equation (109): the closed form of the potential `U_{ω_{[0,L]}}(t)` for `t ≥ 0`, namely
`log (L/4)` for `0 ≤ t ≤ L` and `log ((t - L/2 + √(t (t - L))) / 2)` for `t > L`. -/
noncomputable def arcsinePotential (L t : ℝ) : ℝ :=
  if t ≤ L then Real.log (L / 4) else Real.log ((t - L / 2 + Real.sqrt (t * (t - L))) / 2)

/-- Equation (109) summed over Table 1: the closed form `Σ_j c_j U_{ω_{[0,L_j]}}(t)` used to
evaluate the potential `U_ρ(t)` for `t ≥ 0`. -/
noncomputable def compPotential (t : ℝ) : ℝ :=
  ∑ j : Fin 16, compWeight j * arcsinePotential (compEndpoint j) t

/-! ### Table 1 -/

/-- Table 1: every weight `c_j` is positive. -/
theorem compWeight_pos (j : Fin 16) : 0 < compWeight j := by
  first
    | (fin_cases j <;> norm_num [compWeight, tableCNum]); done; trace "ALT wpos: fin_cases"
    | (exact div_pos (Nat.cast_pos.2 (by fin_cases j <;> simp [tableCNum])) (by positivity));
        trace "ALT wpos: div_pos"

/-- Table 1: the weights sum to `λ = 37/40`. -/
theorem sum_compWeight : ∑ j, compWeight j = 37 / 40 := by
  first
    | (norm_num [Fin.sum_univ_succ, compWeight, tableCNum]; done; trace "ALT sum: norm_num")
    | (simp [Fin.sum_univ_succ, compWeight, tableCNum]; norm_num; done;
        trace "ALT sum: simp norm_num")
    | (simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, compWeight, tableCNum,
          Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num; done;
        trace "ALT sum: simp only norm_num")

/-- Table 1: every interval `[0, L_j]` is longer than `1/225`. -/
theorem one_div_225_lt_compEndpoint (j : Fin 16) : 1 / 225 < compEndpoint j := by
  first
    | (fin_cases j <;> norm_num [compEndpoint, tableLNum]); done; trace "ALT len: fin_cases"
    | (fin_cases j <;> simp [compEndpoint, tableLNum] <;> norm_num); done;
        trace "ALT len: fin_cases simp"

/-- Table 1: every endpoint `L_j` is positive. -/
theorem compEndpoint_pos (j : Fin 16) : 0 < compEndpoint j :=
  lt_trans (by norm_num) (one_div_225_lt_compEndpoint j)

/-- Table 1: every endpoint `L_j` is less than `2`. -/
theorem compEndpoint_lt_two (j : Fin 16) : compEndpoint j < 2 := by
  first
    | (fin_cases j <;> norm_num [compEndpoint, tableLNum]); done; trace "ALT two: fin_cases"
    | (fin_cases j <;> simp [compEndpoint, tableLNum] <;> norm_num); done;
        trace "ALT two: fin_cases simp"

/-- Table 1: the intervals are nested, `L_16 < L_15 < ⋯ < L_1`. -/
theorem compEndpoint_strictAnti : StrictAnti compEndpoint := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  first
    | (fin_cases i <;> norm_num [compEndpoint, tableLNum]); done; trace "ALT anti: fin_cases"
    | (fin_cases i <;> simp [compEndpoint, tableLNum] <;> norm_num); done;
        trace "ALT anti: fin_cases simp"

/-! ### The unit arcsine measure -/

theorem arcsineDensity_nonneg (L t : ℝ) : 0 ≤ arcsineDensity L t := by
  unfold arcsineDensity
  positivity

/-- Appendix A.1: `ω_{[0,L]}` has total mass one. The density has antiderivative
`arcsin (2t/L - 1) / π` on `(0, L)`, which increases from `-1/2` to `1/2`. -/
theorem arcsineMeasure_univ {L : ℝ} (hL : 0 < L) : arcsineMeasure L Set.univ = 1 := by
  have hL0 : L ≠ 0 := hL.ne'
  have hcont : ContinuousOn (fun t : ℝ => Real.arcsin (2 * t / L - 1) / Real.pi)
      (Set.Icc 0 L) := by
    first
      | (fun_prop; trace "ALT hcont: fun_prop")
      | (exact (by continuity : Continuous fun t : ℝ =>
            Real.arcsin (2 * t / L - 1) / Real.pi).continuousOn;
          trace "ALT hcont: continuity")
  have hderiv : ∀ t ∈ Set.Ioo 0 L, HasDerivAt
      (fun s : ℝ => Real.arcsin (2 * s / L - 1) / Real.pi) (arcsineDensity L t) t := by
    intro t ht
    have hpos : 0 < t * (L - t) := mul_pos ht.1 (sub_pos.2 ht.2)
    have hs : Real.sqrt (t * (L - t)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hgt : 0 < 2 * t / L := div_pos (mul_pos two_pos ht.1) hL
    have hlt : 2 * t / L < 2 := by
      rw [div_lt_iff₀ hL]
      linarith [ht.2]
    have hlin : HasDerivAt (fun s : ℝ => 2 * s / L - 1) (2 * 1 / L) t :=
      (((hasDerivAt_id' t).const_mul 2).div_const L).sub_const 1
    have h := ((Real.hasDerivAt_arcsin (by linarith : -1 < 2 * t / L - 1).ne'
      (by linarith : 2 * t / L - 1 < 1).ne).comp t hlin).div_const Real.pi
    refine h.congr_deriv ?_
    have hsq : 1 - (2 * t / L - 1) ^ 2 = (2 * Real.sqrt (t * (L - t)) / L) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hpos.le]
      first
        | (linear_combination (-4 * t / L) * mul_inv_cancel₀ hL0;
            trace "ALT hsq: linear_combination")
        | (field_simp; ring1; trace "ALT hsq: field_simp ring1")
        | (field_simp; done; trace "ALT hsq: field_simp")
    have hroot : Real.sqrt (1 - (2 * t / L - 1) ^ 2) = 2 * Real.sqrt (t * (L - t)) / L := by
      rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hL.le)]
    rw [hroot]
    show _ = 1 / (Real.pi * Real.sqrt (t * (L - t)))
    first
      | (rw [one_div_div];
          linear_combination (Real.sqrt (t * (L - t)))⁻¹ * Real.pi⁻¹ * mul_inv_cancel₀ hL0;
          trace "ALT final: linear_combination")
      | (field_simp; done; trace "ALT final: field_simp")
      | (field_simp; ring1; trace "ALT final: field_simp ring1")
  have hint : IntegrableOn (arcsineDensity L) (Set.Ioc 0 L) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv
      fun t _ => arcsineDensity_nonneg L t
  have hval : ∫ t in (0 : ℝ)..L, arcsineDensity L t = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL.le hcont hderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2 hint)]
    have h1 : 2 * L / L - 1 = 1 := by
      rw [mul_div_assoc, div_self hL0]
      norm_num
    have h0 : 2 * (0 : ℝ) / L - 1 = -1 := by norm_num
    simp only [h1, h0, Real.arcsin_one, Real.arcsin_neg_one]
    first
      | (rw [div_sub_div_same, sub_neg_eq_add, add_halves, div_self Real.pi_ne_zero];
          trace "ALT val: rw")
      | (field_simp; ring1; trace "ALT val: field_simp ring1")
      | (field_simp; done; trace "ALT val: field_simp")
  rw [arcsineMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Set.Ioo_subset_Ioc_self)
      (ae_of_all _ (arcsineDensity_nonneg L)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL.le, hval,
    ENNReal.ofReal_one]

/-- Appendix A.1: for `L > 0`, `ω_{[0,L]}` is a probability measure. -/
theorem isProbabilityMeasure_arcsineMeasure {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (arcsineMeasure L) :=
  ⟨arcsineMeasure_univ hL⟩

/-! ### Total mass of the comparison measure -/

/-- Lemma 6.1: the comparison measure has total mass `λ = 37/40`. -/
theorem compMeasure_univ : compMeasure Set.univ = ENNReal.ofReal (37 / 40) := by
  rw [compMeasure, Measure.finsetSum_apply, ← sum_compWeight,
    ENNReal.ofReal_sum_of_nonneg fun j _ => (compWeight_pos j).le]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, arcsineMeasure_univ (compEndpoint_pos j), smul_eq_mul, mul_one]

instance isFiniteMeasure_compMeasure : IsFiniteMeasure compMeasure :=
  ⟨by rw [compMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

end ZetaSeven
