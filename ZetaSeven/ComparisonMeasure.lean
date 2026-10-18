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
`t ≥ 0`, is proved here (`Ulog_arcsineMeasure`), together with its weighted sum over Table 1
(`Ulog_compMeasure`) and the integrability of `u ↦ log |t - u|` that the Bochner integral needs.
As in the paper, the proof substitutes `u = L (1 + cos θ) / 2`, which carries `ω_{[0,L]}` to
`dθ / π` on `(0, π)`. Writing `t - L/2 = (L/4) (w + w⁻¹)` and `z = e^{iθ}` factors
`|t - u| = (L/4) |z - w| |z - w̄| / |w|`, and the circle average
`circleAverage_log_norm_sub_const_eq_posLog` (the standard interval formula) evaluates the
`θ`-integral; `w = e^{iφ}` for `0 ≤ t ≤ L` and `w > 1` real for `t > L`.
-/

namespace ZetaSeven

open MeasureTheory
open scoped ComplexConjugate

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
  fin_cases j <;> norm_num [compWeight, tableCNum]

/-- Table 1: the weights sum to `λ = 37/40`. -/
theorem sum_compWeight : ∑ j, compWeight j = 37 / 40 := by
  norm_num [Fin.sum_univ_succ, compWeight, tableCNum]

/-- Table 1: every interval `[0, L_j]` is longer than `1/225`. -/
theorem one_div_225_lt_compEndpoint (j : Fin 16) : 1 / 225 < compEndpoint j := by
  fin_cases j <;> norm_num [compEndpoint, tableLNum]

/-- Table 1: every endpoint `L_j` is positive. -/
theorem compEndpoint_pos (j : Fin 16) : 0 < compEndpoint j :=
  lt_trans (by norm_num) (one_div_225_lt_compEndpoint j)

/-- Table 1: every endpoint `L_j` is less than `2`. -/
theorem compEndpoint_lt_two (j : Fin 16) : compEndpoint j < 2 := by
  fin_cases j <;> norm_num [compEndpoint, tableLNum]

/-- Table 1: the intervals are nested, `L_16 < L_15 < ⋯ < L_1`. -/
theorem compEndpoint_strictAnti : StrictAnti compEndpoint := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> norm_num [compEndpoint, tableLNum]

/-! ### The unit arcsine measure -/

/-- The arcsine density is nonnegative. -/
theorem arcsineDensity_nonneg (L t : ℝ) : 0 ≤ arcsineDensity L t := by
  unfold arcsineDensity
  positivity

/-- Appendix A.1: `ω_{[0,L]}` has total mass one. The density has antiderivative
`arcsin (2t/L - 1) / π` on `(0, L)`, which increases from `-1/2` to `1/2`. -/
theorem arcsineMeasure_univ {L : ℝ} (hL : 0 < L) : arcsineMeasure L Set.univ = 1 := by
  have hL0 : L ≠ 0 := hL.ne'
  have hcont : ContinuousOn (fun t : ℝ => Real.arcsin (2 * t / L - 1) / Real.pi)
      (Set.Icc 0 L) := by fun_prop
  have hderiv : ∀ t ∈ Set.Ioo 0 L, HasDerivAt
      (fun s : ℝ => Real.arcsin (2 * s / L - 1) / Real.pi) (arcsineDensity L t) t := by
    intro t ht
    have hpos : 0 < t * (L - t) := mul_pos ht.1 (sub_pos.2 ht.2)
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
      linear_combination (-4 * t / L) * mul_inv_cancel₀ hL0
    have hroot : Real.sqrt (1 - (2 * t / L - 1) ^ 2) = 2 * Real.sqrt (t * (L - t)) / L := by
      rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hL.le)]
    rw [hroot]
    show _ = 1 / (Real.pi * Real.sqrt (t * (L - t)))
    rw [one_div_div]
    linear_combination (Real.sqrt (t * (L - t)))⁻¹ * Real.pi⁻¹ * mul_inv_cancel₀ hL0
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
    rw [div_sub_div_same, sub_neg_eq_add, add_halves, div_self Real.pi_ne_zero]
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

/-- Lemma 6.1: `ρ` is supported in `(0, 2)`, since `ω_{[0,L_j]}` lives on `(0, L_j)` and every
`L_j < 2`. -/
theorem compMeasure_compl_Ioo : compMeasure (Set.Ioo 0 2)ᶜ = 0 := by
  rw [compMeasure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  have hac := withDensity_absolutelyContinuous (volume.restrict (Set.Ioo 0 (compEndpoint j)))
    (fun t => ENNReal.ofReal (arcsineDensity (compEndpoint j) t))
  refine mul_eq_zero_of_right _ (hac ?_)
  rw [Measure.restrict_apply' measurableSet_Ioo]
  have hempty : (Set.Ioo (0 : ℝ) 2)ᶜ ∩ Set.Ioo 0 (compEndpoint j) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx =>
      hx.1 ⟨hx.2.1, hx.2.2.trans (compEndpoint_lt_two j)⟩
  rw [hempty, measure_empty]

/-! ### Equation (109): change of variables `u = L (1 + cos θ) / 2` -/

/-- The arcsine density is measurable. -/
theorem measurable_arcsineDensity (L : ℝ) : Measurable (arcsineDensity L) := by
  show Measurable fun t => 1 / (Real.pi * Real.sqrt (t * (L - t)))
  fun_prop

/-- The substitution `θ ↦ L (1 + cos θ) / 2` has derivative `-L sin θ / 2`. -/
theorem hasDerivAt_arcsineParam (L θ : ℝ) :
    HasDerivAt (fun θ : ℝ => L * (1 + Real.cos θ) / 2) (L * -Real.sin θ / 2) θ :=
  (((Real.hasDerivAt_cos θ).const_add 1).const_mul L).div_const 2

/-- The substitution `θ ↦ L (1 + cos θ) / 2` is injective on `(0, π)`. -/
theorem injOn_arcsineParam {L : ℝ} (hL : 0 < L) :
    Set.InjOn (fun θ : ℝ => L * (1 + Real.cos θ) / 2) (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have h : L * (1 + Real.cos x) / 2 = L * (1 + Real.cos y) / 2 := hxy
  have hc : L * (Real.cos x - Real.cos y) = 0 := by linear_combination 2 * h
  have hc' : Real.cos x = Real.cos y := by
    rcases mul_eq_zero.1 hc with h' | h'
    · exact absurd h' hL.ne'
    · linarith
  exact Real.injOn_cos ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hc'

/-- The substitution `θ ↦ L (1 + cos θ) / 2` maps `(0, π)` onto `(0, L)`. -/
theorem image_arcsineParam {L : ℝ} (hL : 0 < L) :
    (fun θ : ℝ => L * (1 + Real.cos θ) / 2) '' Set.Ioo 0 Real.pi = Set.Ioo 0 L := by
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have h1 : Real.cos θ < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
      rwa [Real.cos_zero] at h
    have h2 : -1 < Real.cos θ := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
      rwa [Real.cos_pi] at h
    have h3 := mul_pos hL (by linarith : (0 : ℝ) < 1 + Real.cos θ)
    have h4 := mul_pos hL (by linarith : (0 : ℝ) < 1 - Real.cos θ)
    show 0 < L * (1 + Real.cos θ) / 2 ∧ L * (1 + Real.cos θ) / 2 < L
    constructor
    · linarith [h3]
    · linarith [h4]
  · rintro ⟨h0, h1⟩
    have hx : 0 < 2 * u / L := div_pos (mul_pos two_pos h0) hL
    have hx' : 2 * u / L < 2 := (div_lt_iff₀ hL).2 (by linarith)
    refine ⟨Real.arccos (2 * u / L - 1),
      ⟨Real.arccos_pos.2 (by linarith [hx']), Real.arccos_lt_pi.2 (by linarith [hx])⟩, ?_⟩
    have hcos : Real.cos (Real.arccos (2 * u / L - 1)) = 2 * u / L - 1 :=
      Real.cos_arccos (by linarith [hx]) (by linarith [hx'])
    show L * (1 + Real.cos (Real.arccos (2 * u / L - 1))) / 2 = u
    rw [hcos]
    have hLinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
    linear_combination u * hLinv

/-- Under `u = L (1 + cos θ) / 2`, the Jacobian `L sin θ / 2` times the arcsine density is
`1 / π` on `(0, π)`. -/
theorem abs_deriv_mul_arcsineDensity {L θ : ℝ} (hL : 0 < L) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    |L * -Real.sin θ / 2| * arcsineDensity L (L * (1 + Real.cos θ) / 2) = Real.pi⁻¹ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hpos : 0 < L * Real.sin θ / 2 := div_pos (mul_pos hL hs) two_pos
  have habs : |L * -Real.sin θ / 2| = L * Real.sin θ / 2 := by
    rw [show L * -Real.sin θ / 2 = -(L * Real.sin θ / 2) by ring, abs_neg, abs_of_pos hpos]
  have hsq : L * (1 + Real.cos θ) / 2 * (L - L * (1 + Real.cos θ) / 2) =
      (L * Real.sin θ / 2) ^ 2 := by
    linear_combination (-(L ^ 2) / 4) * Real.sin_sq_add_cos_sq θ
  have hroot : Real.sqrt (L * (1 + Real.cos θ) / 2 * (L - L * (1 + Real.cos θ) / 2)) =
      L * Real.sin θ / 2 := by
    rw [hsq, Real.sqrt_sq hpos.le]
  rw [arcsineDensity, hroot, habs, one_div, mul_inv, ← mul_assoc,
    mul_comm (L * Real.sin θ / 2) Real.pi⁻¹, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]

/-- The Jacobian identity in the form the change of variables produces. -/
theorem arcsine_jacobian {L θ : ℝ} (hL : 0 < L) (hθ : θ ∈ Set.Ioo 0 Real.pi) (y : ℝ) :
    |L * -Real.sin θ / 2| •
        ((ENNReal.ofReal (arcsineDensity L (L * (1 + Real.cos θ) / 2))).toReal • y) =
      Real.pi⁻¹ * y := by
  rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal (arcsineDensity_nonneg _ _), ← mul_assoc,
    abs_deriv_mul_arcsineDensity hL hθ]

/-- Appendix A.1: the substitution `u = L (1 + cos θ) / 2` carries `ω_{[0,L]}` to `dθ / π` on
`(0, π)`. No integrability is assumed: both sides vanish together when `F` is not integrable. -/
theorem integral_arcsineMeasure {L : ℝ} (hL : 0 < L) (F : ℝ → ℝ) :
    ∫ u, F u ∂(arcsineMeasure L) =
      Real.pi⁻¹ * ∫ θ in Set.Ioo 0 Real.pi, F (L * (1 + Real.cos θ) / 2) := by
  rw [arcsineMeasure, integral_withDensity_eq_integral_toReal_smul
      (measurable_arcsineDensity L).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) F,
    ← image_arcsineParam hL,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun θ _ => (hasDerivAt_arcsineParam L θ).hasDerivWithinAt) (injOn_arcsineParam hL),
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ => arcsine_jacobian hL hθ _

/-- Integrability transfers along the substitution `u = L (1 + cos θ) / 2`. -/
theorem integrable_arcsineMeasure_of_integrableOn {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hF : IntegrableOn (fun θ => F (L * (1 + Real.cos θ) / 2)) (Set.Ioo 0 Real.pi)) :
    Integrable F (arcsineMeasure L) := by
  rw [arcsineMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_arcsineDensity L).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : IntegrableOn (fun u => (ENNReal.ofReal (arcsineDensity L u)).toReal • F u)
      ((fun θ : ℝ => L * (1 + Real.cos θ) / 2) '' Set.Ioo 0 Real.pi) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun θ _ => (hasDerivAt_arcsineParam L θ).hasDerivWithinAt) (injOn_arcsineParam hL)]
    exact IntegrableOn.congr_fun (Integrable.const_mul hF Real.pi⁻¹)
      (fun θ hθ => (arcsine_jacobian hL hθ _).symm) measurableSet_Ioo
  rw [image_arcsineParam hL] at h
  exact h

/-! ### Equation (109): the `θ`-integral through a circle average -/

/-- On the unit circle, `z z̄ = 1`. -/
theorem unitCircle_mul_conj_self (θ : ℝ) : circleMap 0 1 θ * conj (circleMap 0 1 θ) = 1 := by
  rw [Complex.mul_conj', norm_circleMap_zero, abs_one]
  norm_num

/-- On the unit circle, `z + z̄ = 2 cos θ`. -/
theorem unitCircle_add_conj_self (θ : ℝ) :
    circleMap 0 1 θ + conj (circleMap 0 1 θ) = 2 * (Real.cos θ : ℂ) := by
  first
    | rw [Complex.add_conj, circleMap_zero_re, one_mul, Complex.ofReal_mul,
        Complex.ofReal_ofNat]
    | (rw [Complex.add_conj, circleMap_zero_re]; push_cast; ring)
    | simp [Complex.add_conj, circleMap_zero_re]

/-- The factorization behind (109): if `t - L/2 = (L/4) (w + w⁻¹)` and `z = e^{iθ}`, then
`|t - L (1 + cos θ) / 2| = (L/4) |z - w| |z - w̄| / |w|`. -/
theorem abs_sub_arcsineParam_eq {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w ≠ 0) {t : ℝ}
    (ht : (t : ℂ) - L / 2 = L / 4 * (w + w⁻¹)) (θ : ℝ) :
    |t - L * (1 + Real.cos θ) / 2| =
      L / 4 * (‖circleMap 0 1 θ - w‖ * ‖circleMap 0 1 θ - conj w‖) / ‖w‖ := by
  have hz := unitCircle_mul_conj_self θ
  have hre := unitCircle_add_conj_self θ
  have h1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  have hc : ((t - L * (1 + Real.cos θ) / 2 : ℝ) : ℂ) =
      L / 4 * ((w - circleMap 0 1 θ) * (w - conj (circleMap 0 1 θ))) / w := by
    rw [eq_div_iff hw]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    linear_combination w * ht + (L / 4 * w) * hre - (L / 4) * hz + (L / 4) * h1
  have hconj : ‖w - conj (circleMap 0 1 θ)‖ = ‖circleMap 0 1 θ - conj w‖ := by
    rw [← Complex.norm_conj (w - conj (circleMap 0 1 θ)), map_sub, Complex.conj_conj,
      norm_sub_rev]
  have hnorm : ‖((t - L * (1 + Real.cos θ) / 2 : ℝ) : ℂ)‖ = |t - L * (1 + Real.cos θ) / 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hL4 : ‖(L : ℂ) / 4‖ = L / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, Complex.norm_ofNat]
  rw [← hnorm, hc, norm_div, norm_mul, norm_mul, hL4, hconj, norm_sub_rev w]

/-- The logarithm of the factorization, off the zeros of `t - L (1 + cos θ) / 2`. -/
theorem log_abs_sub_arcsineParam_eq {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w ≠ 0) {t : ℝ}
    (ht : (t : ℂ) - L / 2 = L / 4 * (w + w⁻¹)) {θ : ℝ}
    (hθ : t - L * (1 + Real.cos θ) / 2 ≠ 0) :
    Real.log |t - L * (1 + Real.cos θ) / 2| =
      Real.log (L / 4) - Real.log ‖w‖ +
        (Real.log ‖circleMap 0 1 θ - w‖ + Real.log ‖circleMap 0 1 θ - conj w‖) := by
  have habs := abs_sub_arcsineParam_eq hL hw ht θ
  have hpos : 0 < |t - L * (1 + Real.cos θ) / 2| := abs_pos.2 hθ
  have hA : ‖circleMap 0 1 θ - w‖ ≠ 0 := by
    intro h
    rw [habs, h] at hpos
    simp at hpos
  have hB : ‖circleMap 0 1 θ - conj w‖ ≠ 0 := by
    intro h
    rw [habs, h] at hpos
    simp at hpos
  have hW : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hL4 : L / 4 ≠ 0 := by positivity
  rw [habs, Real.log_div (mul_ne_zero hL4 (mul_ne_zero hA hB)) hW,
    Real.log_mul hL4 (mul_ne_zero hA hB), Real.log_mul hA hB]
  ring

/-- `t - L (1 + cos θ) / 2` vanishes only on a codiscrete set of `θ`. -/
theorem arcsineParam_sub_ne_zero_codiscrete {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (fun θ : ℝ => t - L * (1 + Real.cos θ) / 2) ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
  have han : AnalyticOnNhd ℝ (fun θ : ℝ => t - L * (1 + Real.cos θ) / 2) Set.univ :=
    fun _ _ => by fun_prop
  by_cases h0 : t = 0
  · refine han.preimage_zero_mem_codiscrete (x := 0) ?_
    show t - L * (1 + Real.cos 0) / 2 ≠ 0
    rw [Real.cos_zero, h0]
    intro h
    linarith
  · refine han.preimage_zero_mem_codiscrete (x := Real.pi) ?_
    show t - L * (1 + Real.cos Real.pi) / 2 ≠ 0
    rw [Real.cos_pi]
    intro h
    exact h0 (by linarith)

/-- `θ ↦ log |t - L (1 + cos θ) / 2|` is interval integrable: the logarithm of the absolute
value of a real-analytic function. -/
theorem intervalIntegrable_log_abs_sub_arcsineParam (L t a b : ℝ) :
    IntervalIntegrable (fun θ => Real.log |t - L * (1 + Real.cos θ) / 2|) volume a b := by
  have han : AnalyticOnNhd ℝ (fun θ : ℝ => t - L * (1 + Real.cos θ) / 2) Set.univ :=
    fun _ _ => by fun_prop
  simpa only [Real.norm_eq_abs] using
    (han.mono (Set.subset_univ (Set.uIcc a b))).meromorphicOn.intervalIntegrable_log_norm

/-- The `θ`-integral behind (109): if `t - L/2 = (L/4) (w + w⁻¹)` with `w ≠ 0`, then
`∫_0^π log |t - L (1 + cos θ) / 2| dθ = π (log (L/4) - log |w| + 2 log⁺ |w|)`. -/
theorem integral_log_abs_sub_arcsineParam {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w ≠ 0) {t : ℝ}
    (ht : (t : ℂ) - L / 2 = L / 4 * (w + w⁻¹)) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      Real.pi * (Real.log (L / 4) - Real.log ‖w‖ + 2 * Real.posLog ‖w‖) := by
  have hcongr : ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (Real.log (L / 4) - Real.log ‖w‖ +
        (Real.log ‖circleMap 0 1 θ - w‖ + Real.log ‖circleMap 0 1 θ - conj w‖)) := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    apply Filter.codiscreteWithin_mono (Set.subset_univ _)
    filter_upwards [arcsineParam_sub_ne_zero_codiscrete hL t] with θ hθ
    exact log_abs_sub_arcsineParam_eq hL hw ht hθ
  have h1 : CircleIntegrable (fun z => Real.log ‖z - w‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have h2 : CircleIntegrable (fun z => Real.log ‖z - conj w‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have h12 : CircleIntegrable (fun z => Real.log ‖z - w‖ + Real.log ‖z - conj w‖) 0 1 := by
    first
      | exact h1.fun_add h2
      | exact h1.add h2
      | fun_prop
  have hF : Real.circleAverage (fun z => Real.log (L / 4) - Real.log ‖w‖ +
      (Real.log ‖z - w‖ + Real.log ‖z - conj w‖)) 0 1 =
      Real.log (L / 4) - Real.log ‖w‖ + 2 * Real.posLog ‖w‖ := by
    rw [Real.circleAverage_fun_add (circleIntegrable_const _ 0 1) h12, Real.circleAverage_const,
      Real.circleAverage_fun_add h1 h2, circleAverage_log_norm_sub_const_eq_posLog,
      circleAverage_log_norm_sub_const_eq_posLog, Complex.norm_conj]
    ring
  have hfull : ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      2 * Real.pi * (Real.log (L / 4) - Real.log ‖w‖ + 2 * Real.posLog ‖w‖) := by
    rw [hcongr, ← hF, Real.circleAverage_def, smul_eq_mul,
      mul_inv_cancel_left₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  have hsym : ∫ θ in Real.pi..2 * Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      ∫ θ in (0 : ℝ)..Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| := by
    calc ∫ θ in Real.pi..2 * Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2|
        = ∫ θ in Real.pi..2 * Real.pi,
            Real.log |t - L * (1 + Real.cos (2 * Real.pi - θ)) / 2| := by
          refine intervalIntegral.integral_congr fun θ _ => ?_
          simp only [Real.cos_two_pi_sub]
      _ = ∫ θ in 2 * Real.pi - 2 * Real.pi..2 * Real.pi - Real.pi,
            Real.log |t - L * (1 + Real.cos θ) / 2| :=
          intervalIntegral.integral_comp_sub_left
            (fun θ => Real.log |t - L * (1 + Real.cos θ) / 2|) (2 * Real.pi)
      _ = ∫ θ in (0 : ℝ)..Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| := by
          rw [show 2 * Real.pi - 2 * Real.pi = 0 by ring,
            show 2 * Real.pi - Real.pi = Real.pi by ring]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_abs_sub_arcsineParam L t 0 Real.pi)
    (intervalIntegrable_log_abs_sub_arcsineParam L t Real.pi (2 * Real.pi))
  rw [hsym, hfull] at hadd
  linarith

/-- The `θ`-integral of (109) for `0 ≤ t ≤ L`, with `w = e^{iφ}`, `cos φ = 2t/L - 1`. -/
theorem integral_log_abs_sub_arcsineParam_of_le {L t : ℝ} (hL : 0 < L) (ht0 : 0 ≤ t)
    (htL : t ≤ L) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      Real.pi * Real.log (L / 4) := by
  have hx1 : -1 ≤ 2 * t / L - 1 := by
    linarith [div_nonneg (mul_nonneg zero_le_two ht0) hL.le]
  have hx2 : 2 * t / L - 1 ≤ 1 := by
    linarith [(div_le_iff₀ hL).2 (by linarith : 2 * t ≤ 2 * L)]
  have hnorm : ‖circleMap 0 1 (Real.arccos (2 * t / L - 1))‖ = 1 := by
    rw [norm_circleMap_zero, abs_one]
  have hLinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have hreal : t - L / 2 = L / 4 * (2 * (2 * t / L - 1)) := by
    linear_combination (-t) * hLinv
  have hwt : (t : ℂ) - L / 2 = L / 4 * (circleMap 0 1 (Real.arccos (2 * t / L - 1)) +
      (circleMap 0 1 (Real.arccos (2 * t / L - 1)))⁻¹) := by
    rw [Complex.inv_eq_conj hnorm, unitCircle_add_conj_self, Real.cos_arccos hx1 hx2]
    exact_mod_cast hreal
  rw [integral_log_abs_sub_arcsineParam hL (circleMap_ne_center one_ne_zero) hwt, hnorm,
    Real.log_one, Real.posLog_one]
  ring

/-- The `θ`-integral of (109) for `t > L`, with the real root
`w = 2 (t - L/2 + √(t (t - L))) / L > 1`. -/
theorem integral_log_abs_sub_arcsineParam_of_lt {L t : ℝ} (hL : 0 < L) (hLt : L < t) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.log |t - L * (1 + Real.cos θ) / 2| =
      Real.pi * Real.log ((t - L / 2 + Real.sqrt (t * (t - L))) / 2) := by
  have hq : Real.sqrt (t * (t - L)) ^ 2 = t * (t - L) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hLinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have hr1 : 1 < 2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L := by
    rw [lt_div_iff₀ hL]
    linarith [Real.sqrt_nonneg (t * (t - L))]
  have hr0 : 0 < 2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L := by linarith
  have hprod : 2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L *
      (2 * (t - L / 2 - Real.sqrt (t * (t - L))) / L) = 1 := by
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_pos hL hL).ne']
    linear_combination (-4) * hq
  have hreal : t - L / 2 = L / 4 * (2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L +
      (2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L)⁻¹) := by
    rw [inv_eq_of_mul_eq_one_right hprod]
    linear_combination (-(t - L / 2)) * hLinv
  have hwt : (t : ℂ) - L / 2 =
      L / 4 * (((2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L : ℝ) : ℂ) +
        (((2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L : ℝ) : ℂ))⁻¹) := by
    exact_mod_cast hreal
  have hnorm : ‖((2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L : ℝ) : ℂ)‖ =
      2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hposLog : Real.posLog (2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L) =
      Real.log (2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L) :=
    Real.posLog_eq_log (by rw [abs_of_pos hr0]; exact hr1.le)
  have hval : (t - L / 2 + Real.sqrt (t * (t - L))) / 2 =
      L / 4 * (2 * (t - L / 2 + Real.sqrt (t * (t - L))) / L) := by
    linear_combination (-(t - L / 2 + Real.sqrt (t * (t - L))) / 2) * hLinv
  have hL4 : L / 4 ≠ 0 := by positivity
  rw [integral_log_abs_sub_arcsineParam hL (Complex.ofReal_ne_zero.2 hr0.ne') hwt, hnorm,
    hposLog, hval, Real.log_mul hL4 hr0.ne']
  ring

/-! ### Equation (109) and the potential of `ρ` -/

/-- The integrand `u ↦ log |t - u|` of (109) is integrable against `ω_{[0,L]}` for every `t`,
including `t ∈ [0, L]`, where the logarithm is singular inside the support. -/
theorem integrable_log_abs_sub_arcsineMeasure {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Integrable (fun u => Real.log |t - u|) (arcsineMeasure L) :=
  integrable_arcsineMeasure_of_integrableOn hL
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).1
      (intervalIntegrable_log_abs_sub_arcsineParam L t 0 Real.pi)).mono_set
      Set.Ioo_subset_Ioc_self)

/-- Equation (109): the potential `U_{ω_{[0,L]}}(t) = ∫ log |t - u| dω_{[0,L]}(u)` of the unit
arcsine measure equals `log (L/4)` for `0 ≤ t ≤ L` and `log ((t - L/2 + √(t (t - L))) / 2)` for
`t > L`. -/
theorem Ulog_arcsineMeasure {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) :
    Ulog (arcsineMeasure L) t = arcsinePotential L t := by
  rw [Ulog, integral_arcsineMeasure hL, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le, arcsinePotential]
  by_cases htL : t ≤ L
  · rw [if_pos htL, integral_log_abs_sub_arcsineParam_of_le hL ht htL,
      inv_mul_cancel_left₀ Real.pi_ne_zero]
  · rw [if_neg htL, integral_log_abs_sub_arcsineParam_of_lt hL (not_le.1 htL),
      inv_mul_cancel_left₀ Real.pi_ne_zero]

/-- `u ↦ log |t - u|` is integrable against the comparison measure `ρ` for every `t`. -/
theorem integrable_log_abs_sub_compMeasure (t : ℝ) :
    Integrable (fun u => Real.log |t - u|) compMeasure := by
  rw [compMeasure, integrable_finsetSum_measure]
  intro j _
  exact (integrable_log_abs_sub_arcsineMeasure (compEndpoint_pos j) t).smul_measure
    ENNReal.ofReal_ne_top

/-- Equation (109) summed over Table 1: for `t ≥ 0` the potential `U_ρ(t)` of the comparison
measure is `Σ_j c_j U_{ω_{[0,L_j]}}(t)` in the closed form of (109). -/
theorem Ulog_compMeasure {t : ℝ} (ht : 0 ≤ t) : Ulog compMeasure t = compPotential t := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 16)), Integrable (fun u => Real.log |t - u|)
      (ENNReal.ofReal (compWeight j) • arcsineMeasure (compEndpoint j)) := fun j _ =>
    (integrable_log_abs_sub_arcsineMeasure (compEndpoint_pos j) t).smul_measure
      ENNReal.ofReal_ne_top
  rw [Ulog, compMeasure, compPotential, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := Ulog_arcsineMeasure (compEndpoint_pos j) ht
  rw [Ulog] at h
  rw [integral_smul_measure, ENNReal.toReal_ofReal (compWeight_pos j).le, smul_eq_mul, h]

end ZetaSeven
