import ZetaSeven.ZeroMassEnergy
import ZetaSeven.PotentialInequality
import ZetaSeven.EnergyComputation

/-!
# Configuration energy bound (paper Section 6.4, equations (97)-(100))

For `K ≥ 1` and `h = λK` points `t_1, …, t_h ≥ 0` (`λ = 37/40`), the discrete logarithmic
energy with the external field `V` (`ZetaSeven.Vfield`) satisfies (100) in product form,
`∏_{i<j} (t_i - t_j)² · ∏_i e^{-K V(t_i)} ≤ e^{(λM_0 - I(ρ))K² + (120 + √2)h + 2h log K} · ∏_i e^{-√t_i}`
with `M_0 = -109/20` and `I(ρ) = ZetaSeven.Ilog ZetaSeven.compMeasure`
(`configuration_bound`). Taking logarithms gives (100) as printed for distinct points
(`configuration_bound_log`); with Lean's `log 0 = 0` the logarithmic form is false for
coincident points, which is why the main statement is the product form.

The proof follows Section 6.4.

* **Circle regularization.** `ω_i` is normalized arclength on the circle of radius `ε` about
  `t_i` (`circleMeasure`, the image of `dθ / 2π` under `circleMap`), and
  `σ = K⁻¹ Σ_i ω_i`. The circle-average identity of Mathlib
  (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`) gives
  `∫ log |z - a| dω_i(z) = log max(|t_i - a|, ε)`, hence `I(ω_i, ω_j) ≥ log max(|t_i - t_j|, ε)`
  and `I(ω_i, ρ) = ∫ log max(|t_i - u|, ε) dρ(u)`.
* **Zero mass.** `ρ` is carried to `ℂ` along `ℝ ⊆ ℂ` (`compMeasureC`). The circles meet the
  real line in at most two points, so `σ` and `ρ` are mutually singular and `σ - ρ` has Jordan
  decomposition `(σ, ρ)`; its mass is `h/K - λ = 0`. The logarithmic kernel is integrable
  against `(σ + ρ) ⊗ (σ + ρ)`: on each circle `|log x| ≤ 2B - log x` integrates to a bounded
  quantity, and `ρ ⊗ ρ` is handled by `integrable_log_abs_sub_prod_compMeasure`. Lemma 6.2
  (`ZetaSeven.ZeroMassEnergy.zero_mass_energy_nonpos`) gives `I(σ - ρ) ≤ 0`.
* **Regularization error.** `∫ log max(|t - u|, ε) dρ(u) - U_ρ(t) ≤ 60 √ε`. The arcsine density
  satisfies `1/√(u(L - u)) ≤ (u^{-1/2} + (L - u)^{-1/2}) / √L` (as `√L ≤ √u + √(L - u)`), so
  `ω_{[0,L]}` gives mass at most `4 √(2r) / (π √L)` to an interval of radius `r`, the paper's
  arcsine mass estimate (`arcsineMeasure_Ioo_le`). The layer-cake formula then bounds
  `∫ log⁺(ε/|t - u|) dω_{[0,L]}(u)` by `8 √(2ε) / (π √L)`, which is at most `60 √ε` because
  every `L_j > 1/225`; the weights sum to `37/40`.
* **Expansion (97).** Expanding `I(σ - ρ) ≤ 0` gives, for distinct real `t_i` and `ε > 0`,
  `2 Σ_{i<j} log |t_i - t_j| + h log ε ≤ 2K Σ_i U_ρ(t_i) + 120 h K √ε - K² I(ρ)`
  (`configuration_bound_core`).
* **Retained factor (98).** `2U_ρ(t) - V(t) + √t/K ≤ M_0 + √2/K` for `t ≥ 0` and `K ≥ 1`
  (`two_mul_Ulog_sub_Vfield_add_sqrt_div_le`): on `[0, 2]` from (94), and past `2` from the
  corrected tail bound `(29/20) log t + 8α³/t - 2π√t` (source-map erratum 2; the printed `13/10`
  bound fails, for example at `t = 100`: `not_two_mul_Ulog_sub_Vfield_le_printed`) with
  `log t ≤ 2(√t - 1)`, `√t ≥ 7/5` and `π > 3`. The paper's route is also
  recorded: after adding `√t/K` the tail bound is antitone on `[2, ∞)`
  (`antitoneOn_tail_add_sqrt_div`) and its value at `2` is below `M_0 + √2/K`
  (`tail_add_sqrt_div_two_lt`).
* **Assembly (100).** `ε = K⁻²` turns `120 h K √ε` into `120 h` and `-h log ε` into `2h log K`.
-/

namespace ZetaSeven

open MeasureTheory ZeroMassEnergy
open scoped ENNReal

/-! ### Normalized arclength on a circle -/

/-- Normalized arclength on the circle of center `c` and radius `R` in `ℂ`: the image of
`dθ / (2π)` on `(0, 2π]` under `θ ↦ c + R e^{iθ}`. -/
noncomputable def circleMeasure (c : ℂ) (R : ℝ) : Measure ℂ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ •
    (volume.restrict (Set.Ioc 0 (2 * Real.pi))).map (circleMap c R)

/-- `2π > 0`. -/
theorem zero_lt_two_mul_pi : (0 : ℝ) < 2 * Real.pi := by positivity

/-- Normalized arclength has total mass one. -/
theorem circleMeasure_univ (c : ℂ) (R : ℝ) : circleMeasure c R Set.univ = 1 := by
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply (measurable_circleMap c R)
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 zero_lt_two_mul_pi.le),
    inv_mul_cancel₀ zero_lt_two_mul_pi.ne', ENNReal.ofReal_one]

instance isProbabilityMeasure_circleMeasure (c : ℂ) (R : ℝ) :
    IsProbabilityMeasure (circleMeasure c R) :=
  ⟨circleMeasure_univ c R⟩

/-- Lebesgue integrals against normalized arclength are `θ`-integrals over `(0, 2π]`. -/
theorem lintegral_circleMeasure (c : ℂ) (R : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(circleMeasure c R) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), f (circleMap c R θ) := by
  rw [circleMeasure, lintegral_smul_measure, lintegral_map hf (measurable_circleMap c R),
    smul_eq_mul]

/-- Integrals against normalized arclength are Mathlib's circle averages. -/
theorem integral_circleMeasure (c : ℂ) (R : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂(circleMeasure c R) = Real.circleAverage f c R := by
  rw [circleMeasure, integral_smul_measure,
    integral_map (measurable_circleMap c R).aemeasurable hf.aestronglyMeasurable,
    Real.circleAverage_def, intervalIntegral.integral_of_le zero_lt_two_mul_pi.le,
    ENNReal.toReal_ofReal (inv_nonneg.2 zero_lt_two_mul_pi.le)]

/-- Circle-integrable measurable functions are integrable against normalized arclength. -/
theorem integrable_circleMeasure {c : ℂ} {R : ℝ} {f : ℂ → ℝ} (hf : Measurable f)
    (hci : CircleIntegrable f c R) : Integrable f (circleMeasure c R) := by
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [integrable_map_measure hf.aestronglyMeasurable (measurable_circleMap c R).aemeasurable]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_lt_two_mul_pi.le).1 hci

/-- A measurable set whose `circleMap`-preimage is countable is null for normalized arclength. -/
theorem circleMeasure_eq_zero {c : ℂ} {R : ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (h : (circleMap c R ⁻¹' s).Countable) : circleMeasure c R s = 0 := by
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply (measurable_circleMap c R) hs,
    h.measure_zero (volume.restrict (Set.Ioc 0 (2 * Real.pi))), smul_zero]

/-- For `R ≠ 0`, normalized arclength has no atoms. -/
theorem circleMeasure_singleton {c : ℂ} {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    circleMeasure c R {z} = 0 :=
  circleMeasure_eq_zero (measurableSet_singleton z)
    ((Set.countable_singleton z).preimage_circleMap c hR)

/-- A circle of nonzero radius about a real center meets the real line in a null set. -/
theorem circleMeasure_im_eq_zero (t : ℝ) {R : ℝ} (hR : R ≠ 0) :
    circleMeasure (t : ℂ) R {z | z.im = 0} = 0 := by
  refine circleMeasure_eq_zero (isClosed_eq Complex.continuous_im continuous_const).measurableSet
    ((Set.countable_range fun n : ℤ => (n : ℝ) * Real.pi).mono fun θ hθ => ?_)
  have hc : circleMap (t : ℂ) R θ = t + circleMap 0 R θ := by
    rw [← circleMap_sub_center (t : ℂ) R θ]
    ring
  have him : (circleMap (t : ℂ) R θ).im = R * Real.sin θ := by
    rw [hc, Complex.add_im, Complex.ofReal_im, circleMap_zero_im, zero_add]
  have hθ' : (circleMap (t : ℂ) R θ).im = 0 := hθ
  rw [him] at hθ'
  have hs : Real.sin θ = 0 := (mul_eq_zero.1 hθ').resolve_left hR
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  exact ⟨n, hn⟩

/-- Normalized arclength lives on the circle: it gives no mass outside a ball containing it. -/
theorem circleMeasure_norm_sub_gt {c a : ℂ} {R B : ℝ} (hB : |R| + ‖c - a‖ ≤ B) :
    circleMeasure c R {z | B < ‖z - a‖} = 0 := by
  refine circleMeasure_eq_zero
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet
    (Set.countable_empty.mono fun θ hθ => ?_)
  have hθ' : B < ‖circleMap c R θ - a‖ := hθ
  have h := norm_circleMap_sub_le c R θ a
  rw [dist_eq_norm] at h
  exact absurd (h.trans hB) (not_le.2 hθ')

/-- `log |z - a|` is measurable. -/
theorem measurable_log_norm_sub (a : ℂ) : Measurable fun z : ℂ => Real.log ‖z - a‖ :=
  Real.measurable_log.comp (continuous_id.sub continuous_const).norm.measurable

/-- `log |z - a|` is integrable against normalized arclength. -/
theorem integrable_log_norm_sub_circleMeasure (c a : ℂ) (R : ℝ) :
    Integrable (fun z => Real.log ‖z - a‖) (circleMeasure c R) :=
  integrable_circleMeasure (measurable_log_norm_sub a)
    (circleIntegrable_log_norm_sub_const (a := a) (c := c) R)

/-- The circle-average identity: for `R > 0`,
`∫ log |z - a| dω(z) = log max(|c - a|, R)` for normalized arclength `ω` on `|z - c| = R`. -/
theorem integral_log_norm_sub_circleMeasure (c a : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ z, Real.log ‖z - a‖ ∂(circleMeasure c R) = Real.log (max ‖c - a‖ R) := by
  rw [integral_circleMeasure c R (measurable_log_norm_sub a),
    circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR.ne',
    Real.posLog_eq_log_max_one (mul_nonneg (inv_nonneg.2 hR.le) (norm_nonneg (c - a))),
    ← Real.log_mul hR.ne' (lt_of_lt_of_le one_pos (le_max_left _ _)).ne',
    mul_max_of_nonneg _ _ hR.le, mul_one, mul_inv_cancel_left₀ hR.ne', max_comm]

/-! ### The comparison measure on `ℂ` -/

/-- The comparison measure `ρ` carried to `ℂ` along `ℝ ⊆ ℂ`. -/
noncomputable def compMeasureC : Measure ℂ := compMeasure.map ((↑) : ℝ → ℂ)

instance isFiniteMeasure_compMeasureC : IsFiniteMeasure compMeasureC := by
  unfold compMeasureC
  infer_instance

/-- `ρ` on `ℂ` has mass `λ = 37/40`. -/
theorem compMeasureC_univ : compMeasureC Set.univ = ENNReal.ofReal (37 / 40) := by
  rw [compMeasureC, Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
    Set.preimage_univ, compMeasure_univ]

/-- `ρ` has no atoms: each arcsine component has a density. -/
instance nullSingletonClass_compMeasure : NullSingletonClass compMeasure := by
  refine ⟨fun x => ?_⟩
  rw [compMeasure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  have hac := withDensity_absolutelyContinuous (volume.restrict (Set.Ioo 0 (compEndpoint j)))
    (fun t => ENNReal.ofReal (arcsineDensity (compEndpoint j) t))
  exact mul_eq_zero_of_right _ (hac (measure_singleton x))

instance nullSingletonClass_compMeasureC : NullSingletonClass compMeasureC := by
  refine ⟨fun z => ?_⟩
  rw [compMeasureC, Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton z)]
  exact Set.Subsingleton.measure_zero
    (fun x hx y hy => Complex.ofReal_injective (hx.trans hy.symm)) compMeasure

/-- `ρ` on `ℂ` lives on the real line. -/
theorem compMeasureC_compl_im : compMeasureC {z | z.im = 0}ᶜ = 0 := by
  rw [compMeasureC, Measure.map_apply Complex.measurable_ofReal
    (isClosed_eq Complex.continuous_im continuous_const).measurableSet.compl]
  have h : ((↑) : ℝ → ℂ) ⁻¹' {z : ℂ | z.im = 0}ᶜ = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx => hx (Complex.ofReal_im x)
  rw [h, measure_empty]

/-- `ρ` on `ℂ` lives in the disc `|z| ≤ 2`. -/
theorem compMeasureC_norm_sub_gt {a : ℂ} {B : ℝ} (hB : 2 + ‖a‖ ≤ B) :
    compMeasureC {z | B < ‖z - a‖} = 0 := by
  have hmeas : MeasurableSet {z : ℂ | B < ‖z - a‖} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet
  rw [compMeasureC, Measure.map_apply Complex.measurable_ofReal hmeas]
  have hsub : Complex.ofReal ⁻¹' {z : ℂ | B < ‖z - a‖} ⊆ (Set.Ioo 0 2)ᶜ := by
    intro x hx hx2
    have hx' : B < ‖(x : ℂ) - a‖ := hx
    have h1 : ‖(x : ℂ) - a‖ ≤ ‖(x : ℂ)‖ + ‖a‖ := norm_sub_le _ _
    have h2 : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 : |x| < 2 := abs_lt.2 ⟨by linarith [hx2.1], hx2.2⟩
    linarith
  exact measure_mono_null hsub compMeasure_compl_Ioo

/-! ### The logarithmic kernel -/

theorem logKernelAbs_of_ne {z w : ℂ} (h : z ≠ w) :
    logKernelAbs (z, w) = ENNReal.ofReal |Real.log ‖z - w‖| :=
  ite_eq_right h

theorem logKernelAbs_swap (p : ℂ × ℂ) : logKernelAbs p.swap = logKernelAbs p := by
  rcases p with ⟨z, w⟩
  by_cases h : z = w
  · subst h
    rfl
  · rw [Prod.swap_prod_mk, logKernelAbs_of_ne (Ne.symm h), logKernelAbs_of_ne h, norm_sub_rev]

theorem enorm_logKernel_le (p : ℂ × ℂ) : ‖logKernel p‖ₑ ≤ logKernelAbs p := by
  rcases p with ⟨z, w⟩
  by_cases h : z = w
  · have hk : logKernelAbs (z, w) = ⊤ := ite_eq_left h
    rw [hk]
    exact le_top
  · rw [logKernelAbs_of_ne h, Real.enorm_eq_ofReal_abs]
    exact le_rfl

/-- A finite integral of `|log |z - w||` makes the signed kernel integrable. -/
theorem integrable_logKernel_of_lintegral_lt_top {μ : Measure (ℂ × ℂ)}
    (h : ∫⁻ p, logKernelAbs p ∂μ < ∞) : Integrable logKernel μ := by
  refine ⟨aestronglyMeasurable_logKernel μ, ?_⟩
  show ∫⁻ p, ‖logKernel p‖ₑ ∂μ < ∞
  exact (lintegral_mono enorm_logKernel_le).trans_lt h

/-- For `|z - c| ≤ B` and `R > 0`, `∫ |log |z - w|| dω(w) ≤ 2(B + R) - log R` for normalized
arclength `ω` on `|w - c| = R`: on the circle `|log x| ≤ 2(B + R) - log x`, and the right side
integrates by the circle-average identity. -/
theorem lintegral_logKernelAbs_circleMeasure_le {c z : ℂ} {R B : ℝ} (hR : 0 < R)
    (hz : ‖z - c‖ ≤ B) :
    ∫⁻ w, logKernelAbs (z, w) ∂(circleMeasure c R) ≤
      ENNReal.ofReal (2 * (B + R) - Real.log R) := by
  have hmeas : Measurable fun w => logKernelAbs (z, w) :=
    measurable_logKernelAbs.comp measurable_prodMk_left
  have hlogi : IntegrableOn (fun θ => Real.log ‖circleMap c R θ - z‖)
      (Set.Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_lt_two_mul_pi.le).1
      (circleIntegrable_log_norm_sub_const (a := z) (c := c) R)
  have hdist : ∀ θ, ‖circleMap c R θ - z‖ ≤ B + R := fun θ => by
    have h := norm_circleMap_sub_le c R θ z
    rw [abs_of_pos hR, dist_eq_norm, norm_sub_rev c z] at h
    linarith
  have hgi : IntegrableOn (fun θ => 2 * (B + R) - Real.log ‖circleMap c R θ - z‖)
      (Set.Ioc 0 (2 * Real.pi)) :=
    (integrable_const (2 * (B + R))).sub hlogi
  have hbound : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))),
      logKernelAbs (z, circleMap c R θ) ≤
        ENNReal.ofReal (2 * (B + R) - Real.log ‖circleMap c R θ - z‖) := by
    filter_upwards [((Set.countable_singleton z).preimage_circleMap c hR.ne').ae_notMem
      (volume.restrict (Set.Ioc 0 (2 * Real.pi)))] with θ hθ
    have hne : z ≠ circleMap c R θ := fun h => hθ h.symm
    rw [logKernelAbs_of_ne hne, norm_sub_rev z (circleMap c R θ)]
    exact ENNReal.ofReal_le_ofReal (abs_log_le_two_mul_sub_log (norm_nonneg _) (hdist θ))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))]
      fun θ => 2 * (B + R) - Real.log ‖circleMap c R θ - z‖ :=
    ae_of_all _ fun θ =>
      (abs_nonneg _).trans (abs_log_le_two_mul_sub_log (norm_nonneg _) (hdist θ))
  have hav := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := z) (c := c) hR.ne'
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le zero_lt_two_mul_pi.le,
    smul_eq_mul] at hav
  have hint : (2 * Real.pi)⁻¹ *
      ∫ θ in Set.Ioc 0 (2 * Real.pi), (2 * (B + R) - Real.log ‖circleMap c R θ - z‖) ≤
      2 * (B + R) - Real.log R := by
    rw [integral_sub (integrable_const (2 * (B + R))) hlogi, setIntegral_const,
      Real.volume_real_Ioc_of_le zero_lt_two_mul_pi.le, sub_zero, smul_eq_mul, mul_sub, hav,
      inv_mul_cancel_left₀ zero_lt_two_mul_pi.ne']
    linarith [Real.posLog_nonneg (x := R⁻¹ * ‖c - z‖)]
  calc ∫⁻ w, logKernelAbs (z, w) ∂(circleMeasure c R)
      = ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), logKernelAbs (z, circleMap c R θ) :=
        lintegral_circleMeasure c R hmeas
    _ ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
            ENNReal.ofReal (2 * (B + R) - Real.log ‖circleMap c R θ - z‖) :=
        mul_le_mul' le_rfl (lintegral_mono_ae hbound)
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          ∫ θ in Set.Ioc 0 (2 * Real.pi), (2 * (B + R) - Real.log ‖circleMap c R θ - z‖)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hgi hnn,
          ENNReal.ofReal_mul (inv_nonneg.2 zero_lt_two_mul_pi.le)]
    _ ≤ ENNReal.ofReal (2 * (B + R) - Real.log R) := ENNReal.ofReal_le_ofReal hint

/-- The kernel `|log |z - w||` has finite integral against `μ ⊗ ω` for a finite measure `μ`
carried by a disc and normalized arclength `ω`. -/
theorem lintegral_logKernelAbs_prod_circleMeasure_lt_top {μ : Measure ℂ} [IsFiniteMeasure μ]
    {c : ℂ} {R B : ℝ} (hR : 0 < R) (hμ : μ {z | B < ‖z - c‖} = 0) :
    ∫⁻ p, logKernelAbs p ∂(μ.prod (circleMeasure c R)) < ∞ := by
  have hae : ∀ᵐ z ∂μ, ‖z - c‖ ≤ B := by
    rw [ae_iff]
    simpa only [not_le] using hμ
  rw [lintegral_prod _ measurable_logKernelAbs.aemeasurable]
  calc ∫⁻ z, ∫⁻ w, logKernelAbs (z, w) ∂(circleMeasure c R) ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (2 * (B + R) - Real.log R) ∂μ :=
        lintegral_mono_ae (hae.mono fun z hz => lintegral_logKernelAbs_circleMeasure_le hR hz)
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)

/-- The kernel `|log |z - w||` has finite integral against `ω ⊗ μ`. -/
theorem lintegral_logKernelAbs_circleMeasure_prod_lt_top {μ : Measure ℂ} [IsFiniteMeasure μ]
    {c : ℂ} {R B : ℝ} (hR : 0 < R) (hμ : μ {z | B < ‖z - c‖} = 0) :
    ∫⁻ p, logKernelAbs p ∂((circleMeasure c R).prod μ) < ∞ := by
  rw [← lintegral_prod_swap logKernelAbs]
  simp only [logKernelAbs_swap]
  exact lintegral_logKernelAbs_prod_circleMeasure_lt_top hR hμ

/-- The diagonal is null for `ρ ⊗ ρ`. -/
theorem compMeasure_prod_diag :
    (compMeasure.prod compMeasure) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have h : ∀ x : ℝ, compMeasure (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := fun x => by
    have hx : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact eq_comm
    rw [hx, measure_singleton]
  simp only [h, lintegral_zero]

/-- The kernel `|log |z - w||` has finite integral against `ρ ⊗ ρ` on `ℂ`
(`integrable_log_abs_sub_prod_compMeasure`, with the diagonal null). -/
theorem lintegral_logKernelAbs_compMeasureC_lt_top :
    ∫⁻ p, logKernelAbs p ∂(compMeasureC.prod compMeasureC) < ∞ := by
  rw [compMeasureC, Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal,
    lintegral_map measurable_logKernelAbs
      (Complex.measurable_ofReal.prodMap Complex.measurable_ofReal)]
  have hdiag : ∀ᵐ p ∂(compMeasure.prod compMeasure), p ∉ {p : ℝ × ℝ | p.1 = p.2} :=
    measure_eq_zero_iff_ae_notMem.1 compMeasure_prod_diag
  have heq : ∀ᵐ p ∂(compMeasure.prod compMeasure),
      logKernelAbs (Prod.map ((↑) : ℝ → ℂ) ((↑) : ℝ → ℂ) p) = ‖Real.log |p.1 - p.2|‖ₑ := by
    filter_upwards [hdiag] with ⟨x, y⟩ hp
    show logKernelAbs ((x : ℂ), (y : ℂ)) = ‖Real.log |x - y|‖ₑ
    have hne : (x : ℂ) ≠ y := fun h => hp (Complex.ofReal_injective h)
    rw [logKernelAbs_of_ne hne, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Real.enorm_eq_ofReal_abs]
  exact (lintegral_congr_ae heq).trans_lt integrable_log_abs_sub_prod_compMeasure.hasFiniteIntegral

theorem integrable_logKernel_circleMeasure_prod_circleMeasure (c c' : ℂ) {R : ℝ}
    (hR : 0 < R) : Integrable logKernel ((circleMeasure c R).prod (circleMeasure c' R)) :=
  integrable_logKernel_of_lintegral_lt_top
    (lintegral_logKernelAbs_prod_circleMeasure_lt_top (B := |R| + ‖c - c'‖) hR
      (circleMeasure_norm_sub_gt le_rfl))

theorem integrable_logKernel_circleMeasure_prod_compMeasureC (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel ((circleMeasure c R).prod compMeasureC) :=
  integrable_logKernel_of_lintegral_lt_top
    (lintegral_logKernelAbs_circleMeasure_prod_lt_top (B := 2 + ‖c‖) hR
      (compMeasureC_norm_sub_gt le_rfl))

theorem integrable_logKernel_compMeasureC_prod_circleMeasure (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel (compMeasureC.prod (circleMeasure c R)) :=
  integrable_logKernel_of_lintegral_lt_top
    (lintegral_logKernelAbs_prod_circleMeasure_lt_top (B := 2 + ‖c‖) hR
      (compMeasureC_norm_sub_gt le_rfl))

/-! ### Pair energies -/

/-- `I(ρ)` computed on `ℂ` is `I(ρ)`. -/
theorem pairEnergy_compMeasureC : pairEnergy compMeasureC compMeasureC = Ilog compMeasure := by
  rw [pairEnergy, compMeasureC, Measure.map_prod_map _ _ Complex.measurable_ofReal
    Complex.measurable_ofReal, integral_map
      (Complex.measurable_ofReal.prodMap Complex.measurable_ofReal).aemeasurable
      (aestronglyMeasurable_logKernel _), Ilog]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  rcases p with ⟨x, y⟩
  show Real.log ‖(x : ℂ) - y‖ = Real.log |x - y|
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem measurable_log_max_norm_sub (a : ℂ) (R : ℝ) :
    Measurable fun w : ℂ => Real.log (max ‖a - w‖ R) :=
  Real.measurable_log.comp
    ((continuous_const.sub continuous_id).norm.measurable.max measurable_const)

theorem integral_log_max_compMeasureC (t R : ℝ) :
    ∫ w, Real.log (max ‖(t : ℂ) - w‖ R) ∂compMeasureC =
      ∫ u, Real.log (max |t - u| R) ∂compMeasure := by
  rw [compMeasureC, integral_map Complex.measurable_ofReal.aemeasurable
    (measurable_log_max_norm_sub (t : ℂ) R).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show Real.log (max ‖(t : ℂ) - u‖ R) = Real.log (max |t - u| R)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem integral_logKernel_circleMeasure_right (c w : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ z, logKernel (w, z) ∂(circleMeasure c R) = Real.log (max ‖c - w‖ R) := by
  rw [← integral_log_norm_sub_circleMeasure c w hR]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show Real.log ‖w - z‖ = Real.log ‖z - w‖
  rw [norm_sub_rev]

/-- The mutual energy of `ρ` and a circle about a real point:
`I(ρ, ω) = ∫ log max(|t - u|, R) dρ(u)`. -/
theorem pairEnergy_compMeasureC_circleMeasure (t : ℝ) {R : ℝ} (hR : 0 < R) :
    pairEnergy compMeasureC (circleMeasure t R) =
      ∫ u, Real.log (max |t - u| R) ∂compMeasure := by
  rw [pairEnergy, integral_prod _ (integrable_logKernel_compMeasureC_prod_circleMeasure t hR)]
  have h : ∀ w : ℂ, ∫ z, logKernel (w, z) ∂(circleMeasure (t : ℂ) R) =
      Real.log (max ‖(t : ℂ) - w‖ R) := fun w =>
    integral_logKernel_circleMeasure_right (t : ℂ) w hR
  simp_rw [h]
  exact integral_log_max_compMeasureC t R

/-- The mutual energy of a circle about a real point and `ρ`. -/
theorem pairEnergy_circleMeasure_compMeasureC (t : ℝ) {R : ℝ} (hR : 0 < R) :
    pairEnergy (circleMeasure t R) compMeasureC =
      ∫ u, Real.log (max |t - u| R) ∂compMeasure := by
  rw [pairEnergy,
    integral_prod_symm _ (integrable_logKernel_circleMeasure_prod_compMeasureC t hR)]
  have h : ∀ w : ℂ, ∫ z, logKernel (z, w) ∂(circleMeasure (t : ℂ) R) =
      Real.log (max ‖(t : ℂ) - w‖ R) := fun w =>
    integral_log_norm_sub_circleMeasure (t : ℂ) w hR
  simp_rw [h]
  exact integral_log_max_compMeasureC t R

/-- The mutual energy of two circles of radius `R`: applying the circle-average identity on
each circle gives `I(ω, ω') ≥ log max(|c - c'|, R)`. -/
theorem log_max_le_pairEnergy_circleMeasure (c c' : ℂ) {R : ℝ} (hR : 0 < R) :
    Real.log (max ‖c - c'‖ R) ≤ pairEnergy (circleMeasure c R) (circleMeasure c' R) := by
  have hI := integrable_logKernel_circleMeasure_prod_circleMeasure c c' hR
  rw [pairEnergy, integral_prod _ hI]
  have h : ∀ z : ℂ, ∫ w, logKernel (z, w) ∂(circleMeasure c' R) =
      Real.log (max ‖c' - z‖ R) := fun z => integral_logKernel_circleMeasure_right c' z hR
  have hint : Integrable (fun z => Real.log (max ‖c' - z‖ R)) (circleMeasure c R) :=
    hI.integral_prod_left.congr (ae_of_all _ fun z => h z)
  simp_rw [h]
  rw [← integral_log_norm_sub_circleMeasure c c' hR]
  refine integral_mono_ae (integrable_log_norm_sub_circleMeasure c c' R) hint ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (circleMeasure_singleton (c := c) hR.ne' c')]
    with z hz
  have hz' : z - c' ≠ 0 := sub_ne_zero.2 hz
  rw [norm_sub_rev c' z]
  exact Real.log_le_log (norm_pos_iff.2 hz') (le_max_left _ _)

/-! ### Regularization error: the arcsine mass estimate and the layer-cake formula -/

/-- `√y - √x ≤ √(y - x)` for `0 ≤ x ≤ y`. -/
theorem sqrt_sub_sqrt_le_sqrt_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sqrt y - Real.sqrt x ≤ Real.sqrt (y - x) := by
  have hyx : 0 ≤ y - x := sub_nonneg.2 hxy
  have h : y ≤ (Real.sqrt x + Real.sqrt (y - x)) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hyx,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (y - x))]
  have h2 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by positivity)] at h2
  linarith

/-- On `(0, L)` the arcsine density is at most `(u^{-1/2} + (L - u)^{-1/2}) / (π √L)`,
since `√L ≤ √u + √(L - u)`. -/
theorem arcsineDensity_le {L u : ℝ} (hu : u ∈ Set.Ioo 0 L) :
    arcsineDensity L u ≤
      1 / (Real.pi * Real.sqrt L) * (1 / Real.sqrt u + 1 / Real.sqrt (L - u)) := by
  have hu0 : 0 < u := hu.1
  have hLu : 0 < L - u := sub_pos.2 hu.2
  have hs := Real.sqrt_pos.2 hu0
  have hr := Real.sqrt_pos.2 hLu
  have hq := Real.sqrt_pos.2 (hu0.trans hu.2)
  have hqle : Real.sqrt L ≤ Real.sqrt u + Real.sqrt (L - u) := by
    have h : L ≤ (Real.sqrt u + Real.sqrt (L - u)) ^ 2 := by
      nlinarith [Real.sq_sqrt hu0.le, Real.sq_sqrt hLu.le, mul_pos hs hr]
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hsplit : 1 / Real.sqrt u + 1 / Real.sqrt (L - u) =
      (Real.sqrt u + Real.sqrt (L - u)) / (Real.sqrt u * Real.sqrt (L - u)) := by
    rw [div_add_div _ _ hs.ne' hr.ne']
    ring
  rw [arcsineDensity, Real.sqrt_mul hu0.le, hsplit, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (mul_pos Real.pi_pos (mul_pos hs hr))
      (mul_pos (mul_pos Real.pi_pos hq) (mul_pos hs hr))]
  nlinarith [mul_le_mul_of_nonneg_right hqle
    (le_of_lt (mul_pos Real.pi_pos (mul_pos hs hr)))]

/-- The arcsine mass estimate: `ω_{[0,L]}` gives mass at most `4 √(b - a) / (π √L)` to an
interval `(a, b)`. The density bound `arcsineDensity_le` integrates to
`2(√b - √a) + 2(√(L - a) - √(L - b)) ≤ 4 √(b - a)` over `(a, b) ∩ (0, L)`. -/
theorem arcsineMeasure_Ioo_le {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    arcsineMeasure L (Set.Ioo a b) ≤
      ENNReal.ofReal (4 / (Real.pi * Real.sqrt L) * Real.sqrt (b - a)) := by
  have hC0 : 0 ≤ 1 / (Real.pi * Real.sqrt L) := by positivity
  have hS : Set.Ioo a b ∩ Set.Ioo 0 L ⊆ Set.Ioo (max a 0) (min b L) :=
    fun u hu => ⟨max_lt hu.1.1 hu.2.1, lt_min hu.1.2 hu.2.2⟩
  have hSL : Set.Ioo (max a 0) (min b L) ⊆ Set.Ioo 0 L :=
    fun u hu => ⟨(le_max_right a 0).trans_lt hu.1, hu.2.trans_le (min_le_right b L)⟩
  rw [arcsineMeasure, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  rcases le_or_gt (min b L) (max a 0) with hba | hba
  · have hempty : Set.Ioo a b ∩ Set.Ioo 0 L = ∅ :=
      Set.eq_empty_of_subset_empty (hS.trans (Set.Ioo_eq_empty (not_lt.2 hba)).subset)
    rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  have ha0 : 0 ≤ max a 0 := le_max_right a 0
  have hbL : min b L ≤ L := min_le_right b L
  have hderiv : ∀ u ∈ Set.Ioo (max a 0) (min b L), HasDerivAt
      (fun u => 2 * Real.sqrt u - 2 * Real.sqrt (L - u))
      (1 / Real.sqrt u + 1 / Real.sqrt (L - u)) u := by
    intro u hu
    have hu' := hSL hu
    have hs := (Real.sqrt_pos.2 hu'.1).ne'
    have hr := (Real.sqrt_pos.2 (sub_pos.2 hu'.2)).ne'
    have h1 := ((hasDerivAt_id' u).sqrt hu'.1.ne').const_mul 2
    have h2 := (((hasDerivAt_id' u).const_sub L).sqrt (sub_pos.2 hu'.2).ne').const_mul 2
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun u => 2 * Real.sqrt u - 2 * Real.sqrt (L - u))
      (Set.Icc (max a 0) (min b L)) := by fun_prop
  have hnn : ∀ u ∈ Set.Ioo (max a 0) (min b L), 0 ≤ 1 / Real.sqrt u + 1 / Real.sqrt (L - u) :=
    fun u _ => by positivity
  have hint : IntegrableOn (fun u => 1 / Real.sqrt u + 1 / Real.sqrt (L - u))
      (Set.Ioc (max a 0) (min b L)) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnn
  have hval : ∫ u in (max a 0)..(min b L), (1 / Real.sqrt u + 1 / Real.sqrt (L - u)) =
      (2 * Real.sqrt (min b L) - 2 * Real.sqrt (L - min b L)) -
        (2 * Real.sqrt (max a 0) - 2 * Real.sqrt (L - max a 0)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hba.le hcont hderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hba.le).2 hint)
  have hle : (2 * Real.sqrt (min b L) - 2 * Real.sqrt (L - min b L)) -
      (2 * Real.sqrt (max a 0) - 2 * Real.sqrt (L - max a 0)) ≤ 4 * Real.sqrt (b - a) := by
    have h1 := sqrt_sub_sqrt_le_sqrt_sub ha0 hba.le
    have h2 := sqrt_sub_sqrt_le_sqrt_sub (sub_nonneg.2 hbL) (sub_le_sub_left hba.le L)
    have h3 : Real.sqrt (min b L - max a 0) ≤ Real.sqrt (b - a) :=
      Real.sqrt_le_sqrt (by linarith [min_le_left b L, le_max_left a 0])
    rw [sub_sub_sub_cancel_left] at h2
    linarith
  have hintC : IntegrableOn
      (fun u => 1 / (Real.pi * Real.sqrt L) * (1 / Real.sqrt u + 1 / Real.sqrt (L - u)))
      (Set.Ioo (max a 0) (min b L)) :=
    (hint.mono_set Set.Ioo_subset_Ioc_self).const_mul _
  calc ∫⁻ u in Set.Ioo a b ∩ Set.Ioo 0 L, ENNReal.ofReal (arcsineDensity L u)
      ≤ ∫⁻ u in Set.Ioo a b ∩ Set.Ioo 0 L, ENNReal.ofReal
          (1 / (Real.pi * Real.sqrt L) * (1 / Real.sqrt u + 1 / Real.sqrt (L - u))) :=
        lintegral_mono_ae ((ae_restrict_mem (measurableSet_Ioo.inter measurableSet_Ioo)).mono
          fun u hu => ENNReal.ofReal_le_ofReal (arcsineDensity_le hu.2))
    _ ≤ ∫⁻ u in Set.Ioo (max a 0) (min b L), ENNReal.ofReal
          (1 / (Real.pi * Real.sqrt L) * (1 / Real.sqrt u + 1 / Real.sqrt (L - u))) :=
        lintegral_mono_set hS
    _ = ENNReal.ofReal (∫ u in Set.Ioo (max a 0) (min b L),
          1 / (Real.pi * Real.sqrt L) * (1 / Real.sqrt u + 1 / Real.sqrt (L - u))) :=
        (ofReal_integral_eq_lintegral_ofReal hintC
          ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => mul_nonneg hC0 (hnn u hu))).symm
    _ ≤ ENNReal.ofReal (4 / (Real.pi * Real.sqrt L) * Real.sqrt (b - a)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hba.le, hval]
        calc 1 / (Real.pi * Real.sqrt L) *
              ((2 * Real.sqrt (min b L) - 2 * Real.sqrt (L - min b L)) -
                (2 * Real.sqrt (max a 0) - 2 * Real.sqrt (L - max a 0)))
            ≤ 1 / (Real.pi * Real.sqrt L) * (4 * Real.sqrt (b - a)) :=
              mul_le_mul_of_nonneg_left hle hC0
          _ = 4 / (Real.pi * Real.sqrt L) * Real.sqrt (b - a) := by ring

theorem measurable_posLog_div_abs_sub (t ε : ℝ) :
    Measurable fun u : ℝ => Real.posLog (ε / |t - u|) :=
  Real.continuous_posLog.measurable.comp
    (measurable_const.div (continuous_const.sub continuous_id).abs.measurable)

/-- The regularization error of one arcsine component: the layer-cake formula and the mass
estimate `arcsineMeasure_Ioo_le` (for the interval `|u - t| < ε e^{-s}`) give
`∫ log⁺(ε/|t - u|) dω_{[0,L]}(u) ≤ 8 √2 √ε / (π √L)`. -/
theorem lintegral_posLog_arcsineMeasure_le {L : ℝ} (hL : 0 < L) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ u, ENNReal.ofReal (Real.posLog (ε / |t - u|)) ∂(arcsineMeasure L) ≤
      ENNReal.ofReal (8 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) := by
  rw [lintegral_eq_lintegral_meas_lt _ (ae_of_all _ fun u => Real.posLog_nonneg)
    (measurable_posLog_div_abs_sub t ε).aemeasurable]
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ), arcsineMeasure L {u | s < Real.posLog (ε / |t - u|)} ≤
      ENNReal.ofReal (4 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) *
        ENNReal.ofReal (Real.exp (-s * (1 / 2))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hsub : {u | s < Real.posLog (ε / |t - u|)} ⊆
        Set.Ioo (t - ε * Real.exp (-s)) (t + ε * Real.exp (-s)) := by
      intro u hu
      have hu' : s < Real.posLog (ε / |t - u|) := hu
      rw [Real.posLog_apply, lt_max_iff] at hu'
      have hlog : s < Real.log (ε / |t - u|) := hu'.resolve_left (not_lt.2 hs0.le)
      have hpos : 0 < ε / |t - u| := by
        by_contra hneg
        have h0 : ε / |t - u| = 0 :=
          le_antisymm (not_lt.1 hneg) (div_nonneg hε.le (abs_nonneg _))
        rw [h0, Real.log_zero] at hlog
        linarith
      have htu : 0 < |t - u| := by
        rcases (abs_nonneg (t - u)).eq_or_lt with h | h
        · rw [← h, div_zero] at hpos
          exact absurd hpos (lt_irrefl 0)
        · exact h
      rw [Real.lt_log_iff_exp_lt hpos, lt_div_iff₀ htu] at hlog
      have habs : |t - u| < ε * Real.exp (-s) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos s)]
        linarith
      rw [abs_sub_lt_iff] at habs
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have he : Real.sqrt (Real.exp (-s)) = Real.exp (-s * (1 / 2)) := by
      rw [show Real.exp (-s) = Real.exp (-s * (1 / 2)) ^ 2 by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring]
      exact Real.sqrt_sq (Real.exp_pos _).le
    calc arcsineMeasure L {u | s < Real.posLog (ε / |t - u|)}
        ≤ arcsineMeasure L (Set.Ioo (t - ε * Real.exp (-s)) (t + ε * Real.exp (-s))) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (4 / (Real.pi * Real.sqrt L) *
            Real.sqrt (t + ε * Real.exp (-s) - (t - ε * Real.exp (-s)))) :=
          arcsineMeasure_Ioo_le hL _ _
      _ = ENNReal.ofReal (4 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) *
            ENNReal.ofReal (Real.exp (-s * (1 / 2))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show t + ε * Real.exp (-s) - (t - ε * Real.exp (-s)) = 2 * ε * Real.exp (-s) by
              ring,
            Real.sqrt_mul (mul_nonneg zero_le_two hε.le), Real.sqrt_mul zero_le_two, he]
          ring
  calc ∫⁻ s in Set.Ioi 0, arcsineMeasure L {u | s < Real.posLog (ε / |t - u|)}
      ≤ ∫⁻ s in Set.Ioi 0,
          ENNReal.ofReal (4 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) *
            ENNReal.ofReal (Real.exp (-s * (1 / 2))) :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono hpt)
    _ = ENNReal.ofReal (4 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) *
          ENNReal.ofReal (1 / 2)⁻¹ := by
        rw [lintegral_const_mul _ (by fun_prop),
          lintegral_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)]
    _ = ENNReal.ofReal (8 * Real.sqrt 2 / (Real.pi * Real.sqrt L) * Real.sqrt ε) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The regularization error of `ρ`: `∫ log⁺(ε/|t - u|) dρ(u) ≤ 60 √ε`. Each component
contributes at most `8√2 √ε/(π √L_j) ≤ 60 √ε` (as `L_j > 1/225`, `√2 < 3/2`, `π > 3`), and
the weights sum to `37/40`. -/
theorem lintegral_posLog_compMeasure_le (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u, ENNReal.ofReal (Real.posLog (ε / |t - u|)) ∂compMeasure ≤
      ENNReal.ofReal (60 * Real.sqrt ε) := by
  have hj : ∀ j, ∫⁻ u, ENNReal.ofReal (Real.posLog (ε / |t - u|))
      ∂(arcsineMeasure (compEndpoint j)) ≤ ENNReal.ofReal (60 * Real.sqrt ε) := fun j => by
    refine (lintegral_posLog_arcsineMeasure_le (compEndpoint_pos j) t hε).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg ε)))
    have h1 : 1 / 15 < Real.sqrt (compEndpoint j) := (Real.lt_sqrt (by norm_num)).2 (by
      rw [show ((1 : ℝ) / 15) ^ 2 = 1 / 225 by norm_num]
      exact one_div_225_lt_compEndpoint j)
    have h2 : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have h3 := Real.pi_gt_three
    rw [div_le_iff₀ (mul_pos Real.pi_pos ((by norm_num : (0 : ℝ) < 1 / 15).trans h1))]
    nlinarith [mul_pos (sub_pos.2 h3) (sub_pos.2 h1)]
  rw [compMeasure, lintegral_finsetSum_measure]
  calc ∑ j, ∫⁻ u, ENNReal.ofReal (Real.posLog (ε / |t - u|))
        ∂(ENNReal.ofReal (compWeight j) • arcsineMeasure (compEndpoint j))
      = ∑ j, ENNReal.ofReal (compWeight j) * ∫⁻ u, ENNReal.ofReal (Real.posLog (ε / |t - u|))
          ∂(arcsineMeasure (compEndpoint j)) := by
        simp only [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∑ j, ENNReal.ofReal (compWeight j) * ENNReal.ofReal (60 * Real.sqrt ε) :=
        Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hj j)
    _ = ENNReal.ofReal (37 / 40 * (60 * Real.sqrt ε)) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun j _ => (compWeight_pos j).le,
          sum_compWeight, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (60 * Real.sqrt ε) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [Real.sqrt_nonneg ε])

/-- `log max(x, ε) = log x + log⁺(ε/x)` for `x, ε > 0`. -/
theorem log_max_eq_log_add_posLog {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    Real.log (max x ε) = Real.log x + Real.posLog (ε / x) := by
  rw [Real.posLog_eq_log_max_one (div_nonneg hε.le hx.le),
    ← Real.log_mul hx.ne' (lt_of_lt_of_le one_pos (le_max_left _ _)).ne',
    mul_max_of_nonneg _ _ hx.le, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ ε hx.ne']

/-- The regularization error (Section 6.4): for every real `t` and `ε > 0`,
`∫ log max(|t - u|, ε) dρ(u) ≤ U_ρ(t) + 60 √ε`. -/
theorem integral_log_max_le (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ u, Real.log (max |t - u| ε) ∂compMeasure ≤ Ulog compMeasure t + 60 * Real.sqrt ε := by
  have hnn : 0 ≤ᵐ[compMeasure] fun u => Real.posLog (ε / |t - u|) :=
    ae_of_all _ fun u => Real.posLog_nonneg
  have hmeas := measurable_posLog_div_abs_sub t ε
  have hfin := lintegral_posLog_compMeasure_le t hε
  have hint : Integrable (fun u => Real.posLog (ε / |t - u|)) compMeasure :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (hfin.trans_lt ENNReal.ofReal_lt_top)⟩
  have heq : (fun u => Real.log (max |t - u| ε)) =ᵐ[compMeasure]
      fun u => Real.log |t - u| + Real.posLog (ε / |t - u|) := by
    filter_upwards [Measure.ae_ne compMeasure t] with u hu
    exact log_max_eq_log_add_posLog (abs_pos.2 (sub_ne_zero.2 (Ne.symm hu))) hε
  rw [integral_congr_ae heq, integral_add (integrable_log_abs_sub_compMeasure t) hint, Ulog]
  have hle : ∫ u, Real.posLog (ε / |t - u|) ∂compMeasure ≤ 60 * Real.sqrt ε := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hfin
  linarith

/-! ### The circle-regularized configuration -/

theorem measure_prod_finsetSum_left {ι : Type*} [Fintype ι] (m : ι → Measure ℂ)
    (ν : Measure ℂ) [SFinite ν] : (∑ i, m i).prod ν = ∑ i, (m i).prod ν := by
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]

theorem measure_prod_finsetSum_right {ι : Type*} [Fintype ι] (μ : Measure ℂ)
    (m : ι → Measure ℂ) [∀ i, SFinite (m i)] : μ.prod (∑ i, m i) = ∑ i, μ.prod (m i) := by
  rw [← Measure.sum_fintype, Measure.prod_sum_right, Measure.sum_fintype]

/-- The circle-regularized empirical measure `σ = K⁻¹ Σ_i ω_i` of a configuration `t`, with
`ω_i` normalized arclength on the circle of radius `ε` about `t_i`. -/
noncomputable def circleConfig (K ε : ℝ) {h : ℕ} (t : Fin h → ℝ) : Measure ℂ :=
  ∑ i, ENNReal.ofReal K⁻¹ • circleMeasure (t i) ε

theorem circleConfig_apply (K ε : ℝ) {h : ℕ} (t : Fin h → ℝ) (s : Set ℂ) :
    circleConfig K ε t s = ∑ i, ENNReal.ofReal K⁻¹ * circleMeasure (t i) ε s := by
  rw [circleConfig, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem circleConfig_univ (K ε : ℝ) {h : ℕ} (t : Fin h → ℝ) :
    circleConfig K ε t Set.univ = h * ENNReal.ofReal K⁻¹ := by
  rw [circleConfig_apply]
  simp only [measure_univ, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

instance isFiniteMeasure_circleConfig (K ε : ℝ) {h : ℕ} (t : Fin h → ℝ) :
    IsFiniteMeasure (circleConfig K ε t) :=
  ⟨by
    rw [circleConfig_univ]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top h) ENNReal.ofReal_lt_top⟩

/-- `σ` gives no mass outside a disc about `a` containing every circle. -/
theorem circleConfig_norm_sub_gt {K ε : ℝ} {h : ℕ} (t : Fin h → ℝ) {a : ℂ} {B : ℝ}
    (hB : |ε| + ∑ i, ‖(t i : ℂ) - a‖ ≤ B) : circleConfig K ε t {z | B < ‖z - a‖} = 0 := by
  rw [circleConfig_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : ‖(t i : ℂ) - a‖ ≤ ∑ j, ‖(t j : ℂ) - a‖ :=
    Finset.single_le_sum (f := fun j => ‖(t j : ℂ) - a‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  rw [circleMeasure_norm_sub_gt (by linarith), mul_zero]

/-- The circles meet the real line in a null set, so `σ` and `ρ` are mutually singular. -/
theorem circleConfig_mutuallySingular {K ε : ℝ} (hε : 0 < ε) {h : ℕ} (t : Fin h → ℝ) :
    circleConfig K ε t ⟂ₘ compMeasureC := by
  refine ⟨{z | z.im = 0}, (isClosed_eq Complex.continuous_im continuous_const).measurableSet,
    ?_, compMeasureC_compl_im⟩
  rw [circleConfig_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [circleMeasure_im_eq_zero (t i) hε.ne', mul_zero]

theorem circleConfig_prod {K ε : ℝ} {h : ℕ} (t : Fin h → ℝ) (ν : Measure ℂ) [SFinite ν] :
    (circleConfig K ε t).prod ν = ∑ i, ENNReal.ofReal K⁻¹ • (circleMeasure (t i) ε).prod ν := by
  rw [circleConfig, measure_prod_finsetSum_left]
  simp only [Measure.prod_smul_left]

theorem prod_circleConfig {K ε : ℝ} {h : ℕ} (t : Fin h → ℝ) (μ : Measure ℂ) :
    μ.prod (circleConfig K ε t) = ∑ i, ENNReal.ofReal K⁻¹ • μ.prod (circleMeasure (t i) ε) := by
  rw [circleConfig, measure_prod_finsetSum_right]
  simp only [Measure.prod_smul_right]

/-- The logarithmic kernel is integrable against `(σ + ρ) ⊗ (σ + ρ)`: the hypothesis of Lemma 6.2
for `σ - ρ`. -/
theorem lintegral_logKernelAbs_config_lt_top {K ε : ℝ} (hε : 0 < ε) {h : ℕ} (t : Fin h → ℝ) :
    ∫⁻ p, logKernelAbs p ∂((circleConfig K ε t + compMeasureC).prod
      (circleConfig K ε t + compMeasureC)) < ∞ := by
  have hσρ : ∫⁻ p, logKernelAbs p ∂((circleConfig K ε t).prod compMeasureC) < ∞ := by
    rw [circleConfig_prod, lintegral_finsetSum_measure]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    rw [lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lintegral_logKernelAbs_circleMeasure_prod_lt_top hε (compMeasureC_norm_sub_gt le_rfl))
  have hμσ : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ],
      (∀ j, ∃ B, μ {z | B < ‖z - (t j : ℂ)‖} = 0) →
      ∫⁻ p, logKernelAbs p ∂(μ.prod (circleConfig K ε t)) < ∞ := by
    intro μ _ hμ
    rw [prod_circleConfig, lintegral_finsetSum_measure]
    refine ENNReal.sum_lt_top.2 fun j _ => ?_
    rw [lintegral_smul_measure, smul_eq_mul]
    obtain ⟨B, hB⟩ := hμ j
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lintegral_logKernelAbs_prod_circleMeasure_lt_top hε hB)
  have hσσ := hμσ (circleConfig K ε t) fun j => ⟨_, circleConfig_norm_sub_gt t le_rfl⟩
  have hρσ := hμσ compMeasureC fun j => ⟨_, compMeasureC_norm_sub_gt le_rfl⟩
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add, lintegral_add_measure,
    lintegral_add_measure, lintegral_add_measure]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hσσ, hσρ⟩,
    ENNReal.add_lt_top.2 ⟨hρσ, lintegral_logKernelAbs_compMeasureC_lt_top⟩⟩

/-- `I(σ) = K⁻² Σ_i Σ_j I(ω_i, ω_j)`. -/
theorem pairEnergy_circleConfig {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) {h : ℕ} (t : Fin h → ℝ) :
    pairEnergy (circleConfig K ε t) (circleConfig K ε t) =
      ∑ i, ∑ j, K⁻¹ * (K⁻¹ * pairEnergy (circleMeasure (t i) ε) (circleMeasure (t j) ε)) := by
  have hI : ∀ i j, Integrable logKernel ((circleMeasure (t i) ε).prod (circleMeasure (t j) ε)) :=
    fun i j => integrable_logKernel_circleMeasure_prod_circleMeasure _ _ hε
  have hIσ : ∀ i, Integrable logKernel ((circleMeasure (t i) ε).prod (circleConfig K ε t)) := by
    intro i
    rw [prod_circleConfig]
    exact integrable_finsetSum_measure.2 fun j _ => (hI i j).smul_measure ENNReal.ofReal_ne_top
  have ha : (ENNReal.ofReal K⁻¹).toReal = K⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.2 hK.le)
  rw [pairEnergy, circleConfig_prod,
    integral_finsetSum_measure fun i _ => (hIσ i).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ha, smul_eq_mul, prod_circleConfig,
    integral_finsetSum_measure fun j _ => (hI i j).smul_measure ENNReal.ofReal_ne_top,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, ha, smul_eq_mul, pairEnergy]

/-- `I(σ, ρ) = K⁻¹ Σ_i I(ω_i, ρ)`. -/
theorem pairEnergy_circleConfig_compMeasureC {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) {h : ℕ}
    (t : Fin h → ℝ) :
    pairEnergy (circleConfig K ε t) compMeasureC =
      ∑ i, K⁻¹ * pairEnergy (circleMeasure (t i) ε) compMeasureC := by
  have ha : (ENNReal.ofReal K⁻¹).toReal = K⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.2 hK.le)
  rw [pairEnergy, circleConfig_prod, integral_finsetSum_measure fun i _ =>
    (integrable_logKernel_circleMeasure_prod_compMeasureC _ hε).smul_measure
      ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ha, smul_eq_mul, pairEnergy]

/-- `I(ρ, σ) = K⁻¹ Σ_i I(ρ, ω_i)`. -/
theorem pairEnergy_compMeasureC_circleConfig {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) {h : ℕ}
    (t : Fin h → ℝ) :
    pairEnergy compMeasureC (circleConfig K ε t) =
      ∑ i, K⁻¹ * pairEnergy compMeasureC (circleMeasure (t i) ε) := by
  have ha : (ENNReal.ofReal K⁻¹).toReal = K⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.2 hK.le)
  rw [pairEnergy, prod_circleConfig, integral_finsetSum_measure fun i _ =>
    (integrable_logKernel_compMeasureC_prod_circleMeasure _ hε).smul_measure
      ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ha, smul_eq_mul, pairEnergy]

/-- Lemma 6.2 applied to `σ - ρ`: for `h = λK`,
`I(σ) - I(σ, ρ) - I(ρ, σ) + I(ρ) ≤ 0`. The Jordan decomposition of `σ - ρ` is `(σ, ρ)` by
mutual singularity, its mass is `h/K - λ = 0`, and its support is compact. -/
theorem circleConfig_energy_le {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) {h : ℕ}
    (hh : (h : ℝ) = 37 / 40 * K) (t : Fin h → ℝ) :
    pairEnergy (circleConfig K ε t) (circleConfig K ε t) -
        pairEnergy (circleConfig K ε t) compMeasureC -
        pairEnergy compMeasureC (circleConfig K ε t) +
        pairEnergy compMeasureC compMeasureC ≤ 0 := by
  obtain ⟨ν, hν⟩ : ∃ ν : SignedMeasure ℂ,
      ν = (circleConfig K ε t).toSignedMeasure - compMeasureC.toSignedMeasure := ⟨_, rfl⟩
  have hj : ν.toJordanDecomposition =
      ⟨circleConfig K ε t, compMeasureC, circleConfig_mutuallySingular hε t⟩ :=
    SignedMeasure.toJordanDecomposition_eq hν
  have hTV : ν.totalVariation = circleConfig K ε t + compMeasureC := by
    simp only [SignedMeasure.totalVariation, hj]
  have hmass : ν Set.univ = 0 := by
    rw [hν, Measure.toSignedMeasure_sub_apply MeasurableSet.univ, measureReal_def,
      measureReal_def, circleConfig_univ, compMeasureC_univ, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (inv_nonneg.2 hK.le),
      ENNReal.toReal_ofReal (by norm_num), hh, mul_assoc, mul_inv_cancel₀ hK.ne', mul_one,
      sub_self]
  set B : ℝ := |ε| + ∑ i, ‖(t i : ℂ) - 0‖ + 2 with hB
  have hsum : 0 ≤ ∑ i, ‖(t i : ℂ) - 0‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hsupp : ∃ S : Set ℂ, IsCompact S ∧ ν.totalVariation Sᶜ = 0 := by
    refine ⟨Metric.closedBall 0 B, isCompact_closedBall 0 B, ?_⟩
    have hcompl : (Metric.closedBall (0 : ℂ) B)ᶜ = {z | B < ‖z - 0‖} := by
      ext z
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, Set.mem_ofPred_eq,
        not_le]
    rw [hTV, hcompl, Measure.add_apply,
      circleConfig_norm_sub_gt t (by linarith [abs_nonneg ε]),
      compMeasureC_norm_sub_gt (by rw [norm_zero]; linarith [abs_nonneg ε]), add_zero]
  have hInt : ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) < ∞ := by
    rw [hTV]
    exact lintegral_logKernelAbs_config_lt_top hε t
  have key := zero_mass_energy_nonpos ν hmass hsupp hInt
  have e : signedEnergy ν =
      pairEnergy (circleConfig K ε t) (circleConfig K ε t) -
        pairEnergy (circleConfig K ε t) compMeasureC -
        pairEnergy compMeasureC (circleConfig K ε t) +
        pairEnergy compMeasureC compMeasureC := by
    simp only [signedEnergy, hj]
  rw [e] at key
  exact key

/-! ### Equation (97) -/

/-- Splitting a symmetric double sum over `Fin n` into its diagonal and twice its upper half. -/
theorem sum_sum_eq_diag_add_two_mul {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have hsplit : ∀ i j, g i j = (if i < j then g i j else 0) + (if j < i then g i j else 0) +
      (if i = j then g i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt_of_gt hij]
    · subst hij
      simp
    · simp [hij, hij.ne', not_lt_of_gt hij]
  have hlt : ∀ i, ∑ j, (if i < j then g i j else 0) = ∑ j ∈ Finset.Ioi i, g i j := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hgt : ∑ i, ∑ j, (if j < i then g i j else 0) =
      ∑ i, ∑ j, (if i < j then g i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
  have hdiag : ∀ i, ∑ j, (if i = j then g i j else 0) = g i i := by
    intro i
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0) +
          (if i = j then g i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) +
          ∑ i, ∑ j, (if i = j then g i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
        rw [hgt]
        simp only [hlt, hdiag]
        ring

/-- Equation (97) without the external field: for `K > 0`, `h = λK`, distinct real points
`t_1, …, t_h` and `ε > 0`,
`2 Σ_{i<j} log |t_i - t_j| + h log ε ≤ 2K Σ_i U_ρ(t_i) + 120 h K √ε - K² I(ρ)`. -/
theorem configuration_bound_core {K : ℝ} (hK : 0 < K) {h : ℕ} (hh : (h : ℝ) = 37 / 40 * K)
    (t : Fin h → ℝ) (ht : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j| + h * Real.log ε ≤
      2 * K * ∑ i, Ulog compMeasure (t i) + 120 * h * K * Real.sqrt ε -
        K ^ 2 * Ilog compMeasure := by
  have hK0 : K ≠ 0 := hK.ne'
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.2 hK.le
  set g : Fin h → Fin h → ℝ := fun i j => if i = j then Real.log ε else Real.log |t i - t j|
    with hg
  have hgsymm : ∀ i j, g i j = g j i := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · show (if i = j then Real.log ε else Real.log |t i - t j|) =
          (if j = i then Real.log ε else Real.log |t j - t i|)
      rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), abs_sub_comm]
  have hgle : ∀ i j, g i j ≤ pairEnergy (circleMeasure (t i) ε) (circleMeasure (t j) ε) := by
    intro i j
    refine le_trans ?_ (log_max_le_pairEnergy_circleMeasure (t i) (t j) hε)
    by_cases hij : i = j
    · subst hij
      have e1 : max ‖(t i : ℂ) - t i‖ ε = ε := by rw [sub_self, norm_zero, max_eq_right hε.le]
      rw [e1]
      exact le_of_eq (ite_eq_left rfl)
    · have hne : t i ≠ t j := fun h' => hij (ht h')
      have hpos : 0 < |t i - t j| := abs_pos.2 (sub_ne_zero.2 hne)
      have hnorm : ‖(t i : ℂ) - t j‖ = |t i - t j| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      show (if i = j then Real.log ε else Real.log |t i - t j|) ≤ _
      rw [ite_eq_right hij, hnorm]
      exact Real.log_le_log hpos (le_max_left _ _)
  have hgii : ∀ i, g i i = Real.log ε := fun i => ite_eq_left rfl
  have hdiag : ∑ i, g i i = h * Real.log ε := by
    simp only [hgii, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hupper : ∑ i, ∑ j ∈ Finset.Ioi i, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j| :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      ite_eq_right (Finset.mem_Ioi.1 hj).ne
  have hσσ : K⁻¹ * K⁻¹ * (h * Real.log ε + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j|) ≤
      pairEnergy (circleConfig K ε t) (circleConfig K ε t) := by
    rw [pairEnergy_circleConfig hK hε, ← hdiag, ← hupper, ← sum_sum_eq_diag_add_two_mul g hgsymm,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgle i j) hKi) hKi
  have hA : ∀ i, pairEnergy (circleMeasure (t i) ε) compMeasureC ≤
      Ulog compMeasure (t i) + 60 * Real.sqrt ε := fun i => by
    rw [pairEnergy_circleMeasure_compMeasureC (t i) hε]
    exact integral_log_max_le (t i) hε
  have hA' : ∀ i, pairEnergy compMeasureC (circleMeasure (t i) ε) ≤
      Ulog compMeasure (t i) + 60 * Real.sqrt ε := fun i => by
    rw [pairEnergy_compMeasureC_circleMeasure (t i) hε]
    exact integral_log_max_le (t i) hε
  have hsum : ∑ i, (Ulog compMeasure (t i) + 60 * Real.sqrt ε) =
      ∑ i, Ulog compMeasure (t i) + h * (60 * Real.sqrt ε) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hσρ : pairEnergy (circleConfig K ε t) compMeasureC ≤
      K⁻¹ * (∑ i, Ulog compMeasure (t i) + h * (60 * Real.sqrt ε)) := by
    rw [pairEnergy_circleConfig_compMeasureC hK hε, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) hKi
  have hρσ : pairEnergy compMeasureC (circleConfig K ε t) ≤
      K⁻¹ * (∑ i, Ulog compMeasure (t i) + h * (60 * Real.sqrt ε)) := by
    rw [pairEnergy_compMeasureC_circleConfig hK hε, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA' i) hKi
  have key := circleConfig_energy_le hK hε hh t
  rw [pairEnergy_compMeasureC] at key
  set X := h * Real.log ε + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j| with hX
  set Y := ∑ i, Ulog compMeasure (t i) + h * (60 * Real.sqrt ε) with hY
  have hXY : K⁻¹ * K⁻¹ * X ≤ 2 * (K⁻¹ * Y) - Ilog compMeasure := by linarith
  have h2 : X = K ^ 2 * (K⁻¹ * K⁻¹ * X) := by
    rw [sq, show K * K * (K⁻¹ * K⁻¹ * X) = K * K⁻¹ * (K * K⁻¹) * X by ring,
      mul_inv_cancel₀ hK0, one_mul, one_mul]
  have h3 : K ^ 2 * (2 * (K⁻¹ * Y) - Ilog compMeasure) = 2 * K * Y - K ^ 2 * Ilog compMeasure := by
    rw [mul_sub, show K ^ 2 * (2 * (K⁻¹ * Y)) = 2 * (K * K⁻¹) * K * Y by ring,
      mul_inv_cancel₀ hK0]
    ring
  have h4 : X ≤ 2 * K * Y - K ^ 2 * Ilog compMeasure := by
    calc X = K ^ 2 * (K⁻¹ * K⁻¹ * X) := h2
      _ ≤ K ^ 2 * (2 * (K⁻¹ * Y) - Ilog compMeasure) :=
        mul_le_mul_of_nonneg_left hXY (sq_nonneg K)
      _ = 2 * K * Y - K ^ 2 * Ilog compMeasure := h3
  rw [hX, hY] at h4
  linarith

/-! ### Equation (98) and the assembly of (100) -/

/-- Equation (98), the retained factor: for `K ≥ 1` and `t ≥ 0`,
`2U_ρ(t) - V(t) + √t/K ≤ M_0 + √2/K` with `M_0 = -109/20`. On `[0, 2]` this is (94) plus
`√t ≤ √2`; past `2` it follows from the corrected tail bound
`2U_ρ(t) - V(t) ≤ (29/20) log t + 8α³/t - 2π√t` (source-map erratum 2), `√t/K ≤ √t`,
`log t ≤ 2(√t - 1)`, `√t ≥ 7/5` and `π > 3`. -/
theorem two_mul_Ulog_sub_Vfield_add_sqrt_div_le {K t : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t) :
    2 * Ulog compMeasure t - Vfield t + Real.sqrt t / K ≤ -109 / 20 + Real.sqrt 2 / K := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rcases le_or_gt t 2 with h2 | h2
  · have h1 := two_mul_Ulog_compMeasure_sub_Vfield_le ht
    have h3 : Real.sqrt t / K ≤ Real.sqrt 2 / K :=
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h2) hK0.le
    linarith
  · have h1 := two_mul_Ulog_sub_Vfield_le_of_two_le h2.le
    have ht0 : 0 < t := by linarith
    have hs : 7 / 5 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht0)
      rw [Real.log_sqrt ht0.le] at h
      linarith
    have hfrac : 8 * eAlpha ^ 3 / t ≤ 27 / 16000 := by
      rw [div_le_iff₀ ht0, eAlpha_eq]
      norm_num
      linarith
    have hdiv : Real.sqrt t / K ≤ Real.sqrt t := div_le_self (Real.sqrt_nonneg t) hK
    have hpos : 0 ≤ Real.sqrt 2 / K := div_nonneg (Real.sqrt_nonneg 2) hK0.le
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg t)]

/-- The route of the paper to (98) past `2`: after adding `√t/K`, the tail bound
`(29/20) log t + 8α³/t - 2π√t` is antitone on `[2, ∞)` for `K ≥ 1`. With `s = √t ≥ 7/5` its
derivative is at most `(1/s) ((29/20)/s + 1/(2K) - π) < 0`. -/
theorem antitoneOn_tail_add_sqrt_div {K : ℝ} (hK : 1 ≤ K) :
    AntitoneOn (fun t => 29 / 20 * Real.log t + 8 * eAlpha ^ 3 / t -
      2 * Real.pi * Real.sqrt t + Real.sqrt t / K) (Set.Ici 2) := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun t => 29 / 20 * Real.log t +
      8 * eAlpha ^ 3 / t - 2 * Real.pi * Real.sqrt t + Real.sqrt t / K)
      (29 / 20 * x⁻¹ + 8 * eAlpha ^ 3 * (-(x ^ 2)⁻¹) - 2 * Real.pi * (1 / (2 * Real.sqrt x)) +
        1 / (2 * Real.sqrt x) / K) x := by
    intro x hx
    have h1 := (Real.hasDerivAt_log hx.ne').const_mul (29 / 20)
    have h2 := (hasDerivAt_inv hx.ne').const_mul (8 * eAlpha ^ 3)
    have h3 := (Real.hasDerivAt_sqrt hx.ne').const_mul (2 * Real.pi)
    have h4 := (Real.hasDerivAt_sqrt hx.ne').div_const K
    convert ((h1.add h2).sub h3).add h4 using 1
    funext t
    simp only [div_eq_mul_inv, Pi.add_apply, Pi.sub_apply]
  refine antitoneOn_of_deriv_nonpos (convex_Ici 2) ?_ ?_ ?_
  · intro x hx
    exact (hderiv x (lt_of_lt_of_le two_pos hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    exact (hderiv x (lt_trans two_pos hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : 0 < x := lt_trans two_pos hx
    rw [(hderiv x hx0).deriv]
    have hs : 7 / 5 ≤ Real.sqrt x :=
      Real.le_sqrt_of_sq_le (by norm_num; linarith [Set.mem_Ioi.1 hx])
    have hu0 : 0 < 1 / Real.sqrt x := one_div_pos.2 (Real.sqrt_pos.2 hx0)
    have hu57 : 1 / Real.sqrt x ≤ 5 / 7 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 5) hs
      norm_num at h ⊢
      linarith
    have hinv : x⁻¹ = (1 / Real.sqrt x) ^ 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt hx0.le, one_div]
    have hhalf : 1 / (2 * Real.sqrt x) = 1 / Real.sqrt x / 2 := by ring
    have hK' : 1 / Real.sqrt x / 2 / K ≤ 1 / Real.sqrt x / 2 :=
      div_le_self (by positivity) hK
    have hα : 0 ≤ 8 * eAlpha ^ 3 * (x ^ 2)⁻¹ := by
      rw [eAlpha_eq]
      positivity
    rw [hinv, hhalf]
    nlinarith [mul_le_mul_of_nonneg_left hu57 hu0.le,
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le hu0.le]

/-- At `t = 2` the tail bound with the retained factor is below `M_0 + √2/K`, from
`log 2 < 7/10`, `π > 3` and `√2 > 7/5` (the `√2/K` terms cancel). -/
theorem tail_add_sqrt_div_two_lt (K : ℝ) :
    29 / 20 * Real.log 2 + 8 * eAlpha ^ 3 / 2 - 2 * Real.pi * Real.sqrt 2 + Real.sqrt 2 / K <
      -109 / 20 + Real.sqrt 2 / K := by
  have hlog : Real.log 2 < 7 / 10 := by
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  have hs : 7 / 5 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hpi := Real.pi_gt_three
  rw [eAlpha_eq]
  nlinarith [mul_pos (sub_pos.2 hpi) (sub_pos.2 hs)]

/-- `J_1(t) ≤ log (t + 1)` for `t > 0`, since `log (t + u²) ≤ log (t + 1)` on `[0, 1]`. -/
theorem Jfield_one_le_log_add_one {t : ℝ} (ht : 0 < t) : Jfield 1 t ≤ Real.log (t + 1) := by
  have hcont : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => (by positivity : (0 : ℝ) < t + u ^ 2).ne'
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hcont.intervalIntegrable 0 1) (intervalIntegrable_const (c := Real.log (t + 1)))
    (fun u hu => Real.log_le_log (by positivity) (by nlinarith [hu.1, hu.2]))
  simpa [Jfield] using h

/-- `α log t ≤ J_α(t)` for `t > 0`, since `log t ≤ log (t + u²)`. -/
theorem eAlpha_mul_log_le_Jfield {t : ℝ} (ht : 0 < t) :
    eAlpha * Real.log t ≤ Jfield eAlpha t := by
  have hcont : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => (by positivity : (0 : ℝ) < t + u ^ 2).ne'
  have h := intervalIntegral.integral_mono_on (μ := volume) eAlpha_pos.le
    (intervalIntegrable_const (c := Real.log t)) (hcont.intervalIntegrable 0 eAlpha)
    (fun u _ => Real.log_le_log ht (le_add_of_nonneg_right (sq_nonneg u)))
  simpa [Jfield] using h

/-- Each term of (109) at `t = 100` is at least `log 98`. -/
theorem log_98_le_arcsinePotential {L : ℝ} (hL2 : L < 2) :
    Real.log 98 ≤ arcsinePotential L 100 := by
  rw [arcsinePotential, ite_eq_right (not_le.2 (by linarith : L < 100))]
  refine Real.log_le_log (by norm_num) ?_
  have h : 98 ≤ Real.sqrt (100 * (100 - L)) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- Source-map erratum 2: the bound (99) as printed, with the coefficient `13/10`, is false. At
`t = 100`, `2U_ρ(t) - V(t) ≥ (37/20) log 98 - 2π√t - log 101 + (3/5) log 100`, which exceeds
`(13/10) log 100 + 8α³/100 - 2π√t` because `98³⁷ > 2 · 101²⁰ · 100¹⁴`. -/
theorem not_two_mul_Ulog_sub_Vfield_le_printed :
    ¬ (2 * Ulog compMeasure 100 - Vfield 100 ≤
      13 / 10 * Real.log 100 + 8 * eAlpha ^ 3 / 100 - 2 * Real.pi * Real.sqrt 100) := by
  intro h
  have hU : 37 / 40 * Real.log 98 ≤ Ulog compMeasure 100 := by
    rw [Ulog_compMeasure (by norm_num), compPotential, ← sum_compWeight, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (log_98_le_arcsinePotential (compEndpoint_lt_two j))
      (compWeight_pos j).le
  have hJ1 := Jfield_one_le_log_add_one (by norm_num : (0 : ℝ) < 100)
  have hJα := eAlpha_mul_log_le_Jfield (by norm_num : (0 : ℝ) < 100)
  have hV : Vfield 100 ≤ 2 * Real.pi * Real.sqrt 100 + Real.log 101 -
      8 * (eAlpha * Real.log 100) := by
    rw [Vfield]
    norm_num at hJ1
    linarith
  have hbig : (2 : ℝ) * (101 ^ 20 * 100 ^ 14) ≤ 98 ^ 37 := by norm_num
  have hlog := Real.log_le_log (by norm_num) hbig
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  rw [eAlpha_eq] at h hV
  linarith

/-- Equation (100) for distinct points: for `K ≥ 1`, `h = λK` (`λ = 37/40`) and distinct
`t_1, …, t_h ≥ 0`,
`2 Σ_{i<j} log |t_i - t_j| - K Σ_i V(t_i) + Σ_i √t_i ≤ (λM_0 - I(ρ))K² + (120 + √2)h + 2h log K`
with `M_0 = -109/20`. It is (97) with `ε = K⁻²` plus `K` times (98) summed over the points. -/
theorem configuration_bound_log {K : ℝ} (hK : 1 ≤ K) {h : ℕ} (hh : (h : ℝ) = 37 / 40 * K)
    (t : Fin h → ℝ) (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective t) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j| - K * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (37 / 40 * (-109 / 20) - Ilog compMeasure) * K ^ 2 + (120 + Real.sqrt 2) * h +
        2 * h * Real.log K := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hcore := configuration_bound_core hK0 hh t hinj (inv_pos.2 (pow_pos hK0 2))
  have e : (120 : ℝ) * h * K * K⁻¹ = 120 * h := by
    rw [mul_assoc, mul_inv_cancel₀ hK0.ne', mul_one]
  rw [Real.sqrt_inv, Real.sqrt_sq hK0.le, Real.log_inv, Real.log_pow, e] at hcore
  push_cast at hcore
  have h98 : ∀ i, K * (2 * Ulog compMeasure (t i)) ≤
      K * Vfield (t i) - Real.sqrt (t i) + (-109 / 20 * K + Real.sqrt 2) := by
    intro i
    have h := mul_le_mul_of_nonneg_left
      (two_mul_Ulog_sub_Vfield_add_sqrt_div_le hK (ht i)) hK0.le
    have e1 : K * (Real.sqrt (t i) / K) = Real.sqrt (t i) := by
      rw [mul_comm, div_mul_cancel₀ _ hK0.ne']
    have e2 : K * (Real.sqrt 2 / K) = Real.sqrt 2 := by
      rw [mul_comm, div_mul_cancel₀ _ hK0.ne']
    have e3 : K * (2 * Ulog compMeasure (t i) - Vfield (t i) + Real.sqrt (t i) / K) =
        K * (2 * Ulog compMeasure (t i)) - K * Vfield (t i) + K * (Real.sqrt (t i) / K) := by
      ring
    have e4 : K * (-109 / 20 + Real.sqrt 2 / K) = -109 / 20 * K + K * (Real.sqrt 2 / K) := by
      ring
    rw [e3, e4, e1, e2] at h
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h98 i
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hKh : (h : ℝ) * K = 37 / 40 * K ^ 2 := by
    rw [hh]
    ring
  linarith

/-- Equation (100) in product form, the statement of this node: for `K ≥ 1`, `h = λK`
(`λ = 37/40`) and any `t_1, …, t_h ≥ 0`,
`∏_{i<j} (t_i - t_j)² · ∏_i e^{-K V(t_i)} ≤
e^{(λM_0 - I(ρ))K² + (120 + √2)h + 2h log K} · ∏_i e^{-√t_i}` with `M_0 = -109/20`.
Coincident points make the left side vanish; for distinct points this is
`configuration_bound_log` exponentiated. -/
theorem configuration_bound {K : ℝ} (hK : 1 ≤ K) {h : ℕ} (hh : (h : ℝ) = 37 / 40 * K)
    (t : Fin h → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) * ∏ i, Real.exp (-K * Vfield (t i)) ≤
      Real.exp ((37 / 40 * (-109 / 20) - Ilog compMeasure) * K ^ 2 +
          (120 + Real.sqrt 2) * h + 2 * h * Real.log K) *
        ∏ i, Real.exp (-Real.sqrt (t i)) := by
  by_cases hinj : Function.Injective t
  · have hlog := configuration_bound_log hK hh t ht hinj
    have hprod : ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2 =
        Real.exp (2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i - t j|) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : t i - t j ≠ 0 :=
        sub_ne_zero.2 fun h' => (Finset.mem_Ioi.1 hj).ne (hinj h')
      have hsq : 0 < (t i - t j) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      rw [show 2 * Real.log |t i - t j| = Real.log ((t i - t j) ^ 2) by
          rw [← sq_abs, Real.log_pow, Nat.cast_ofNat],
        Real.exp_log hsq]
    have hV : ∏ i, Real.exp (-K * Vfield (t i)) = Real.exp (-(K * ∑ i, Vfield (t i))) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hS : ∏ i, Real.exp (-Real.sqrt (t i)) = Real.exp (-∑ i, Real.sqrt (t i)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    rw [hprod, hV, hS, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hinj
    have hzero : ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2 = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · refine Finset.prod_eq_zero (Finset.mem_univ a)
          (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_)
        rw [hab, sub_self]
        norm_num
      · refine Finset.prod_eq_zero (Finset.mem_univ b)
          (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_)
        rw [hab, sub_self]
        norm_num
    rw [hzero, zero_mul]
    exact (mul_pos (Real.exp_pos _) (Finset.prod_pos fun i _ => Real.exp_pos _)).le

end ZetaSeven
