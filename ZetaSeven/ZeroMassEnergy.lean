import Mathlib

open MeasureTheory Filter
open scoped ENNReal

namespace ZetaSeven.ZeroMassEnergy

/-!
# Zero-mass logarithmic energy (Lemma 6.2)

Let `ν` be a finite real signed Borel measure on `ℂ` with compact support and total mass
zero, with `∫∫ |log|z - w|| d|ν|d|ν| < ∞`. Then the logarithmic energy `I(ν) ≤ 0`.

Proof strategy (following Section 6.3 of the paper): regularize with the Gaussian kernel
(completing the square plus Fubini gives a nonnegative square integral), represent the
logarithm as an improper `s`-integral, use mass-zero to drop the constant term, and pass
to the limit by dominated convergence.
-/

/-! ## Layer 0: kernels and energies -/

/-- The absolute logarithmic kernel on `ℂ × ℂ`, valued in `ℝ≥0∞`, taking the value `⊤`
on the diagonal (matching the paper's convention `log 0 = -∞`). -/
noncomputable def logKernelAbs : ℂ × ℂ → ℝ≥0∞ := fun p =>
  if p.1 = p.2 then ⊤ else ENNReal.ofReal |Real.log ‖p.1 - p.2‖|

theorem measurable_logKernelAbs : Measurable logKernelAbs := by
  unfold logKernelAbs
  refine Measurable.ite ?hdiag measurable_const ?hoff
  · have h : Measurable fun p : ℂ × ℂ => p.1 - p.2 :=
      (continuous_fst.sub continuous_snd).measurable
    have hset : {p : ℂ × ℂ | p.1 = p.2} = (fun p : ℂ × ℂ => p.1 - p.2) ⁻¹' {0} := by
      ext p
      simp [sub_eq_zero]
    rw [hset]
    exact h measurableSet_singleton
  · exact ENNReal.continuous_ofReal.measurable.comp
      (continuous_abs.measurable.comp
        (Real.measurable_log.comp (continuous_fst.sub continuous_snd).norm.measurable))

/-- The signed logarithmic kernel on `ℂ × ℂ` (junk value `0` on the diagonal). -/
noncomputable def logKernel : ℂ × ℂ → ℝ := fun p => Real.log ‖p.1 - p.2‖

theorem measurable_logKernel : Measurable logKernel := by
  unfold logKernel
  exact Real.measurable_log.comp (continuous_fst.sub continuous_snd).norm.measurable

theorem aestronglyMeasurable_logKernel (μ : Measure (ℂ × ℂ)) :
    AEStronglyMeasurable logKernel μ :=
  measurable_logKernel.aestronglyMeasurable

/-- Logarithmic pair energy of two (positive) measures. -/
noncomputable def pairEnergy (μ ρ : Measure ℂ) : ℝ :=
  ∫ p, logKernel p ∂(μ.prod ρ)

/-- Logarithmic energy of a signed measure via its Jordan decomposition. -/
noncomputable def signedEnergy (ν : SignedMeasure ℂ) : ℝ :=
  let j := ν.toJordanDecomposition
  pairEnergy j.posPart j.posPart - pairEnergy j.posPart j.negPart
    - pairEnergy j.negPart j.posPart + pairEnergy j.negPart j.negPart

/-! ## Layer 1: Gaussian integral over `ℂ` -/

/-- Gaussian integral over `ℂ`: `∫ u, exp (-c * ‖u‖^2) = π / c`. -/
theorem integral_gaussian_complex_volume {c : ℝ} (hc : 0 < c) :
    ∫ u : ℂ, Real.exp (-c * ‖u‖^2) ∂volume = Real.pi / c := by
  have htrans : ∫ u : ℂ, Real.exp (-c * ‖u‖^2) ∂volume
      = ∫ p : ℝ × ℝ, Real.exp (-c * (p.1^2 + p.2^2)) ∂volume := by
    have h := Complex.volume_preserving_equiv_real_prod.integral_comp'
      (fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
    rw [← h]
    apply integral_congr_ae
    filter_upwards with u
    have hnorm : (Complex.measurableEquivRealProd u).1^2
        + (Complex.measurableEquivRealProd u).2^2 = ‖u‖^2 := by
      rw [Complex.measurableEquivRealProd_apply]
      show u.re^2 + u.im^2 = ‖u‖^2
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hnorm]
  rw [htrans]
  have hfactor : (fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
      = fun p => Real.exp (-c * p.1^2) * Real.exp (-c * p.2^2) := by
    ext p
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
  rw [hvol]
  have hInt : Integrable (fun p : ℝ × ℝ => Real.exp (-c * p.1^2) * Real.exp (-c * p.2^2))
      (volume.prod volume) :=
    (integrable_exp_neg_mul_sq hc).mul_prod (integrable_exp_neg_mul_sq hc)
  rw [integral_prod _ hInt]
  have hinner : ∀ x : ℝ, (∫ y : ℝ, Real.exp (-c * x^2) * Real.exp (-c * y^2) ∂volume)
      = Real.exp (-c * x^2) * √(Real.pi / c) := fun x => by
    rw [integral_const_mul, integral_gaussian c]
  simp_rw [hinner]
  rw [integral_mul_const, integral_gaussian c]
  exact Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)

/-! ## Layer 2: pointwise Gaussian identity (completing the square) -/

/-- For `s > 0`, completing the square gives the Gaussian reproducing identity. -/
theorem gaussian_pointwise {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    Real.exp (-s * ‖z - w‖^2)
      = (4 * s / Real.pi) * ∫ u : ℂ,
        Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2) ∂volume := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  set m : ℂ := ⟨(z.re + w.re)/2, (z.im + w.im)/2⟩ with hm
  have hmre : m.re = (z.re + w.re)/2 := rfl
  have hmim : m.im = (z.im + w.im)/2 := rfl
  have hsq : ∀ u : ℂ, (-2*s*‖z-u‖^2) + (-2*s*‖w-u‖^2)
      = (-s*‖z-w‖^2) + (-4*s*‖u-m‖^2) := by
    intro u
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hmre, hmim]
    ring
  have hfactor : ∀ u : ℂ, Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2)
      = Real.exp (-s*‖z-w‖^2) * Real.exp (-4*s*‖u-m‖^2) := by
    intro u
    simp only [← Real.exp_add, hsq u]
  have htrans : ∫ u : ℂ, Real.exp (-4*s*‖u-m‖^2) ∂volume = Real.pi / (4*s) := by
    have hmp : MeasurePreserving (fun x : ℂ => x + (-m)) volume volume :=
      measurePreserving_add_right volume (-m)
    have hemb : MeasurableEmbedding (fun x : ℂ => x + (-m)) :=
      measurableEmbedding_addRight (-m)
    have h := hmp.integral_comp hemb (fun v : ℂ => Real.exp (-4*s*‖v‖^2))
    have h4s : (0:ℝ) < 4*s := by linarith
    rw [integral_gaussian_complex_volume h4s] at h
    have hcongr : (fun u : ℂ => Real.exp (-4*s*‖u-m‖^2))
        = fun x => Real.exp (-4*s*‖x + -m‖^2) := by
      ext u
      simp only [sub_eq_add_neg]
    rw [hcongr]
    exact h
  have h4s0 : Real.pi * (4*s) ≠ 0 := mul_ne_zero hpi (mul_ne_zero (by norm_num) hs0)
  have hone : (4 * s / Real.pi) * (Real.pi / (4*s)) = 1 := by
    rw [div_mul_div_comm, mul_comm (4*s) Real.pi, div_self h4s0]
  calc Real.exp (-s * ‖z - w‖^2)
      = (4 * s / Real.pi) * (Real.exp (-s*‖z-w‖^2) * (Real.pi / (4*s))) := by
        rw [mul_comm (Real.exp _) _, mul_assoc, hone, one_mul]
    _ = (4 * s / Real.pi) * ∫ u : ℂ,
          Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2) ∂volume := by
        congr 1
        rw [show (fun u : ℂ => Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2))
              = fun u => Real.exp (-s*‖z-w‖^2) * Real.exp (-4*s*‖u-m‖^2)
            from funext hfactor]
        rw [integral_const_mul, htrans]

/-! ## Layer 3: Gaussian energy of a signed combination is nonnegative -/

/-- Gaussian pair interaction at scale `s`. -/
noncomputable def gaussJ (μ ρ : Measure ℂ) (s : ℝ) : ℝ :=
  ∫ p, Real.exp (-s * ‖p.1 - p.2‖^2) ∂(μ.prod ρ)

/-- Gaussian profile of a measure at scale `s`. -/
noncomputable def gaussProfile (μ : Measure ℂ) (s : ℝ) (u : ℂ) : ℝ :=
  ∫ z, Real.exp (-2*s*‖z-u‖^2) ∂μ

/-- The signed Gaussian interaction `J(s)` is nonnegative (a square integral). -/
theorem signed_gaussJ_nonneg (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {s : ℝ} (hs : 0 < s) :
    0 ≤ gaussJ μ μ s - gaussJ μ ρ s - gaussJ ρ μ s + gaussJ ρ ρ s := by
  sorry

/-! ## Layer 4: logarithm as an improper `s`-integral -/

/-- The `s`-integrand representing the logarithm: `(e^{-s} - e^{-s r^2})/s`. -/
noncomputable def logTruncIntegrand (r s : ℝ) : ℝ :=
  (Real.exp (-s) - Real.exp (-s * r^2)) / s

/-- Truncated logarithmic approximation `L_{a,b}(r) = (1/2) ∫_a^b (e^{-s}-e^{-sr²})/s ds`. -/
noncomputable def logTrunc (a b r : ℝ) : ℝ :=
  (1/2) * ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume

/-- Truncation sequences `a_n → 0+` and `b_n → ∞`. -/
noncomputable def truncA : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹
noncomputable def truncB : ℕ → ℝ := fun n => (n : ℝ) + 2

/-- Pointwise domination: `|L_{a,b}(r)| ≤ |log r|`. -/
theorem logTrunc_le_abs_log {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    |logTrunc a b r| ≤ |Real.log r| := by
  sorry

/-- Pointwise convergence: `L_{a_n,b_n}(r) → log r`. -/
theorem tendsto_logTrunc_seq {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => logTrunc (truncA n) (truncB n) r) atTop (𝓝 (Real.log r)) := by
  sorry

/-! ## Layer 5: truncated energy via Fubini (mass-zero step) -/

/-- Per-pair truncated energy identity. -/
theorem pair_truncEnergy_eq (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ p, logTrunc a b ‖p.1 - p.2‖ ∂(μ.prod ρ)
      = (1/2) * ∫ s in Set.Ioo a b,
          (Real.exp (-s) * (μ Set.univ).toReal * (ρ Set.univ).toReal - gaussJ μ ρ s) / s
          ∂volume := by
  sorry

/-! ## Layer 6: dominated convergence and the main theorem -/

/-- Zero-mass logarithmic energy (Lemma 6.2): `I(ν) ≤ 0`. -/
theorem zero_mass_energy_nonpos (ν : SignedMeasure ℂ)
    (hmass : ν Set.univ = 0)
    (hsupp : ∃ K : Set ℂ, IsCompact K ∧ ν.totalVariation Kᶜ = 0)
    (hInt : ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) < ∞) :
    signedEnergy ν ≤ 0 := by
  sorry

end ZetaSeven.ZeroMassEnergy
