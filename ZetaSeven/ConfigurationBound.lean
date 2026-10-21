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

end ZetaSeven
