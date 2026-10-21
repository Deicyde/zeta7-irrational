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
  satisfies `1/√(u(L - u)) ≤ √(2/L) (u^{-1/2} + (L - u)^{-1/2})`, so `ω_{[0,L]}` gives mass at
  most `(4√2 / (π√L)) √ℓ` to an interval of length `ℓ`; the layer-cake formula then bounds
  `∫ log⁺(ε/|t - u|) dω_{[0,L]}(u)` by `16 √ε / (π √L)`, and every `L_j ≥ 1/50`. (With only
  the paper's `L_j > 1/225` this route would give `70.7 √ε`, above the paper's `60 √ε`.)
* **Expansion (97).** Expanding `I(σ - ρ) ≤ 0` gives, for distinct real `t_i` and `ε > 0`,
  `2 Σ_{i<j} log |t_i - t_j| + h log ε ≤ 2K Σ_i U_ρ(t_i) + 120 h K √ε - K² I(ρ)`
  (`configuration_bound_core`).
* **Retained factor (98).** `2U_ρ(t) - V(t) + √t/K ≤ M_0 + √2/K` for `t ≥ 0` and `K ≥ 1`
  (`two_mul_Ulog_sub_Vfield_add_sqrt_div_le`): on `[0, 2]` from (94), and past `2` from the
  corrected tail bound `(29/20) log t + 8α³/t - 2π√t` (source-map erratum 2; the printed `13/10`
  is false) with `log t ≤ 2(√t - 1)`, `√t ≥ 7/5` and `π > 3`.
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
  rw [compMeasureC, Measure.map_apply Complex.measurable_ofReal
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet]
  refine measure_mono_null (fun x hx hx2 => ?_) compMeasure_compl_Ioo
  have hx' : B < ‖(x : ℂ) - a‖ := hx
  have h1 : ‖(x : ℂ) - a‖ ≤ ‖(x : ℂ)‖ + ‖a‖ := norm_sub_le _ _
  have h2 : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h3 : |x| < 2 := abs_lt.2 ⟨by linarith [hx2.1], hx2.2⟩
  linarith

/-! ### The logarithmic kernel -/

theorem logKernelAbs_of_ne {z w : ℂ} (h : z ≠ w) :
    logKernelAbs (z, w) = ENNReal.ofReal |Real.log ‖z - w‖| :=
  if_neg h

theorem logKernelAbs_swap (p : ℂ × ℂ) : logKernelAbs p.swap = logKernelAbs p := by
  rcases p with ⟨z, w⟩
  by_cases h : z = w
  · subst h
    rfl
  · rw [Prod.swap_prod_mk, logKernelAbs_of_ne (Ne.symm h), logKernelAbs_of_ne h, norm_sub_rev]

theorem enorm_logKernel_le (p : ℂ × ℂ) : ‖logKernel p‖ₑ ≤ logKernelAbs p := by
  rcases p with ⟨z, w⟩
  by_cases h : z = w
  · have hk : logKernelAbs (z, w) = ⊤ := if_pos h
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
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
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
theorem arcsineMeasure_Ioo_le {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) :
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
    exact zero_le _
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
    field_simp <;> ring
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
          arcsineMeasure_Ioo_le hL (by nlinarith [Real.exp_pos (-s)])
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

end ZetaSeven
