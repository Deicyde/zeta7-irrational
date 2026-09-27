import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

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
    exact h (measurableSet_singleton 0)
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
      = (-s*‖z-w‖^2) + (-(4*s)*‖u-m‖^2) := by
    intro u
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hmre, hmim]
    ring
  have hfactor : ∀ u : ℂ, Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2)
      = Real.exp (-s*‖z-w‖^2) * Real.exp (-(4*s)*‖u-m‖^2) := by
    intro u
    simp only [← Real.exp_add, hsq u]
  have htrans : ∫ u : ℂ, Real.exp (-(4*s)*‖u-m‖^2) ∂volume = Real.pi / (4*s) := by
    have hmp : MeasurePreserving (fun x : ℂ => x + (-m)) volume volume :=
      measurePreserving_add_right volume (-m)
    have hemb : MeasurableEmbedding (fun x : ℂ => x + (-m)) :=
      measurableEmbedding_addRight (-m)
    have h := hmp.integral_comp hemb (fun v : ℂ => Real.exp (-(4*s)*‖v‖^2))
    have h4s : (0:ℝ) < 4*s := by linarith
    have hval : ∫ y : ℂ, Real.exp (-(4*s)*‖y‖^2) ∂volume = Real.pi / (4*s) :=
      integral_gaussian_complex_volume h4s
    have hcongr : (fun u : ℂ => Real.exp (-(4*s)*‖u-m‖^2))
        = fun x => Real.exp (-(4*s)*‖x + -m‖^2) := by
      ext u
      simp only [sub_eq_add_neg]
    rw [hcongr, ← hval]
    exact h
  have h4s0 : Real.pi * (4*s) ≠ 0 := mul_ne_zero hpi (mul_ne_zero (by norm_num) hs0)
  have hone : (4 * s / Real.pi) * (Real.pi / (4*s)) = 1 := by
    rw [div_mul_div_comm, mul_comm (4*s) Real.pi, div_self h4s0]
  calc Real.exp (-s * ‖z - w‖^2)
      = (4 * s / Real.pi) * (Real.exp (-s*‖z-w‖^2) * (Real.pi / (4*s))) := by
        rw [mul_comm (Real.exp _) _, ← mul_assoc, hone, one_mul]
    _ = (4 * s / Real.pi) * ∫ u : ℂ,
          Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2) ∂volume := by
        congr 1
        rw [show (fun u : ℂ => Real.exp (-2*s*‖z-u‖^2) * Real.exp (-2*s*‖w-u‖^2))
              = fun u => Real.exp (-s*‖z-w‖^2) * Real.exp (-(4*s)*‖u-m‖^2)
            from funext hfactor]
        rw [integral_const_mul, htrans]

/-! ## Layer 3: Gaussian energy of a signed combination is nonnegative -/

/-- Gaussian pair interaction at scale `s`. -/
noncomputable def gaussJ (μ ρ : Measure ℂ) (s : ℝ) : ℝ :=
  ∫ p, Real.exp (-s * ‖p.1 - p.2‖^2) ∂(μ.prod ρ)

/-- Gaussian profile of a measure at scale `s`. -/
noncomputable def gaussProfile (μ : Measure ℂ) (s : ℝ) (u : ℂ) : ℝ :=
  ∫ z, Real.exp (-2*s*‖z-u‖^2) ∂μ

/-- Shifted Gaussian on `ℂ` is integrable. -/
theorem integrable_gaussian_shift {c : ℝ} (hc : 0 < c) (a : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-c * ‖u - a‖^2)) volume := by
  have hG : Integrable (fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2))) volume := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    rw [hvol]
    have hfactor : (fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
        = fun p => Real.exp (-c * p.1^2) * Real.exp (-c * p.2^2) := by
      ext p
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    exact (integrable_exp_neg_mul_sq hc).mul_prod (integrable_exp_neg_mul_sq hc)
  have hiff : Integrable ((fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
        ∘ Complex.measurableEquivRealProd) volume
      ↔ Integrable (fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2))) volume :=
    Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding
  have hcomp : Integrable ((fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
      ∘ Complex.measurableEquivRealProd) volume := hiff.mpr hG
  have heq : ((fun p : ℝ × ℝ => Real.exp (-c * (p.1^2 + p.2^2)))
        ∘ Complex.measurableEquivRealProd)
      = fun v : ℂ => Real.exp (-c * ‖v‖^2) := by
    ext v
    have hnorm : (Complex.measurableEquivRealProd v).1^2
        + (Complex.measurableEquivRealProd v).2^2 = ‖v‖^2 := by
      rw [Complex.measurableEquivRealProd_apply]
      show v.re^2 + v.im^2 = ‖v‖^2
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    show Real.exp (-c * ((Complex.measurableEquivRealProd v).1^2
      + (Complex.measurableEquivRealProd v).2^2)) = Real.exp (-c * ‖v‖^2)
    rw [hnorm]
  have hbase : Integrable (fun v : ℂ => Real.exp (-c * ‖v‖^2)) volume := by
    rw [← heq]
    exact hcomp
  have hiff2 : Integrable ((fun v : ℂ => Real.exp (-c * ‖v‖^2)) ∘ (fun x => x + -a)) volume
      ↔ Integrable (fun v : ℂ => Real.exp (-c * ‖v‖^2)) volume :=
    (measurePreserving_add_right volume (-a)).integrable_comp_emb
      (measurableEmbedding_addRight (-a))
  have hcomp2 : Integrable ((fun v : ℂ => Real.exp (-c * ‖v‖^2)) ∘ (fun x => x + -a))
      volume := hiff2.mpr hbase
  have heq2 : ((fun v : ℂ => Real.exp (-c * ‖v‖^2)) ∘ (fun x => x + -a))
      = fun u : ℂ => Real.exp (-c * ‖u - a‖^2) := by
    ext u
    show Real.exp (-c * ‖u + -a‖^2) = Real.exp (-c * ‖u - a‖^2)
    rw [sub_eq_add_neg]
  rw [← heq2]
  exact hcomp2

/-- Shifted Gaussian integral on `ℂ`. -/
theorem integral_gaussian_shift {c : ℝ} (hc : 0 < c) (a : ℂ) :
    ∫ u : ℂ, Real.exp (-c * ‖u - a‖^2) ∂volume = Real.pi / c := by
  have hmp : MeasurePreserving (fun x : ℂ => x + (-a)) volume volume :=
    measurePreserving_add_right volume (-a)
  have hemb : MeasurableEmbedding (fun x : ℂ => x + (-a)) :=
    measurableEmbedding_addRight (-a)
  have h := hmp.integral_comp hemb (fun v : ℂ => Real.exp (-c * ‖v‖^2))
  have hval : ∫ y : ℂ, Real.exp (-c * ‖y‖^2) ∂volume = Real.pi / c :=
    integral_gaussian_complex_volume hc
  have hcongr : (fun u : ℂ => Real.exp (-c * ‖u - a‖^2))
      = fun x => Real.exp (-c * ‖x + -a‖^2) := by
    ext u
    simp only [sub_eq_add_neg]
  rw [hcongr, ← hval]
  exact h

/-- The triple Gaussian kernel is integrable (Tonelli bound uniform in `z, w`). -/
theorem integrable_gaussTriple (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : (ℂ × ℂ) × ℂ =>
      Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2))
      ((μ₁.prod μ₂).prod volume) := by
  have h2s : (0:ℝ) < 2*s := by linarith
  have hexp_nonneg : ∀ t : ℝ, 0 ≤ Real.exp t := fun t => (Real.exp_pos t).le
  have hexp_le_one : ∀ t : ℝ, t ≤ 0 → Real.exp t ≤ 1 :=
    fun t ht => Real.exp_le_one_iff.mpr ht
  have h2s0 : (-2:ℝ)*s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs.le
  have hcont : Continuous (fun q : (ℂ × ℂ) × ℂ =>
      Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2)) := by
    fun_prop
  have hAES : AEStronglyMeasurable (fun q : (ℂ × ℂ) × ℂ =>
      Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2))
      ((μ₁.prod μ₂).prod volume) := hcont.aestronglyMeasurable
  refine ⟨hAES, ?_⟩
  show ∫⁻ q : (ℂ × ℂ) × ℂ, ‖Real.exp (-2*s*‖q.1.1 - q.2‖^2)
      * Real.exp (-2*s*‖q.1.2 - q.2‖^2)‖ₑ ∂((μ₁.prod μ₂).prod volume) < ∞
  have hpt : ∀ q : (ℂ × ℂ) × ℂ, (‖Real.exp (-2*s*‖q.1.1 - q.2‖^2)
      * Real.exp (-2*s*‖q.1.2 - q.2‖^2)‖ₑ)
      ≤ ENNReal.ofReal (Real.exp (-2*s*‖q.1.1 - q.2‖^2)) := by
    intro q
    have hK0 : 0 ≤ Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2) :=
      mul_nonneg (hexp_nonneg _) (hexp_nonneg _)
    have hKle : Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2)
        ≤ Real.exp (-2*s*‖q.1.1 - q.2‖^2) := by
      have h2 : Real.exp (-2*s*‖q.1.2 - q.2‖^2) ≤ 1 :=
        hexp_le_one _ (mul_nonpos_of_nonpos_of_nonneg h2s0 (sq_nonneg _))
      calc Real.exp (-2*s*‖q.1.1 - q.2‖^2) * Real.exp (-2*s*‖q.1.2 - q.2‖^2)
          ≤ Real.exp (-2*s*‖q.1.1 - q.2‖^2) * 1 :=
            mul_le_mul_of_nonneg_left h2 (hexp_nonneg _)
        _ = Real.exp (-2*s*‖q.1.1 - q.2‖^2) := mul_one _
    have hnorm : (‖Real.exp (-2*s*‖q.1.1 - q.2‖^2)
          * Real.exp (-2*s*‖q.1.2 - q.2‖^2)‖ₑ)
        = ENNReal.ofReal (Real.exp (-2*s*‖q.1.1 - q.2‖^2)
          * Real.exp (-2*s*‖q.1.2 - q.2‖^2)) := by
      rw [← ofReal_norm, Real.norm_of_nonneg hK0]
    rw [hnorm]
    exact ENNReal.ofReal_le_ofReal hKle
  have hinner : ∀ p : ℂ × ℂ, ∫⁻ u, ENNReal.ofReal (Real.exp (-2*s*‖p.1 - u‖^2)) ∂volume
      = ENNReal.ofReal (Real.pi / (2*s)) := by
    intro p
    have hrewrite : (∫⁻ u, ENNReal.ofReal (Real.exp (-2*s*‖p.1 - u‖^2)) ∂volume)
        = ∫⁻ u, ENNReal.ofReal (Real.exp (-(2*s)*‖u - p.1‖^2)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards with u
      have hrev : ‖p.1 - u‖ = ‖u - p.1‖ := by rw [← norm_neg, neg_sub]
      have h2 : (-2:ℝ)*s*‖p.1-u‖^2 = -(2*s)*‖u-p.1‖^2 := by rw [hrev]; ring
      rw [h2]
    rw [hrewrite,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussian_shift h2s p.1)
        (ae_of_all _ (fun u => hexp_nonneg _))]
    congr 1
    exact integral_gaussian_shift h2s p.1
  calc ∫⁻ q : (ℂ × ℂ) × ℂ, ‖Real.exp (-2*s*‖q.1.1 - q.2‖^2)
          * Real.exp (-2*s*‖q.1.2 - q.2‖^2)‖ₑ ∂((μ₁.prod μ₂).prod volume)
      ≤ ∫⁻ q : (ℂ × ℂ) × ℂ, ENNReal.ofReal (Real.exp (-2*s*‖q.1.1 - q.2‖^2))
          ∂((μ₁.prod μ₂).prod volume) := lintegral_mono hpt
    _ = ∫⁻ p, ∫⁻ u, ENNReal.ofReal (Real.exp (-2*s*‖p.1 - u‖^2))
          ∂volume ∂(μ₁.prod μ₂) := by
        apply lintegral_prod
        apply Continuous.aemeasurable
        refine ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
        fun_prop
    _ = ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (Real.pi / (2*s)) ∂(μ₁.prod μ₂) :=
        lintegral_congr_ae (ae_of_all _ hinner)
    _ < ∞ := by
        rw [lintegral_const]
        apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        exact measure_lt_top _ _

/-- Per-pair Gaussian identity via Fubini: `gaussJ` is a profile inner product. -/
theorem pair_gaussJ_eq (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {s : ℝ} (hs : 0 < s) :
    gaussJ μ₁ μ₂ s = (4*s/Real.pi) * ∫ u,
      gaussProfile μ₁ s u * gaussProfile μ₂ s u ∂volume := by
  unfold gaussJ gaussProfile
  trans (4*s/Real.pi) * ∫ p, ∫ u,
    Real.exp (-2*s*‖p.1-u‖^2) * Real.exp (-2*s*‖p.2-u‖^2) ∂volume ∂(μ₁.prod μ₂)
  · rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    exact gaussian_pointwise hs p.1 p.2
  · congr 1
    have hswap : (∫ p, ∫ u, Real.exp (-2*s*‖p.1-u‖^2) * Real.exp (-2*s*‖p.2-u‖^2)
          ∂volume ∂(μ₁.prod μ₂))
        = ∫ u, ∫ p, Real.exp (-2*s*‖p.1-u‖^2) * Real.exp (-2*s*‖p.2-u‖^2)
          ∂(μ₁.prod μ₂) ∂volume := by
      apply integral_integral_swap
      exact integrable_gaussTriple μ₁ μ₂ hs
    rw [hswap]
    apply integral_congr_ae
    filter_upwards with u
    exact integral_prod_mul (fun z : ℂ => Real.exp (-2*s*‖z-u‖^2))
      (fun z : ℂ => Real.exp (-2*s*‖z-u‖^2))

/-- Products of Gaussian profiles are integrable (via the triple Fubini). -/
theorem integrable_profile_mul (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => gaussProfile μ₁ s u * gaussProfile μ₂ s u) volume := by
  have h := (integrable_gaussTriple μ₁ μ₂ hs).integral_prod_right
  refine Integrable.congr h ?_
  filter_upwards with u
  show (∫ x, (fun q : (ℂ × ℂ) × ℂ => Real.exp (-2*s*‖q.1.1 - q.2‖^2)
      * Real.exp (-2*s*‖q.1.2 - q.2‖^2)) (x, u) ∂(μ₁.prod μ₂))
      = gaussProfile μ₁ s u * gaussProfile μ₂ s u
  unfold gaussProfile
  exact integral_prod_mul (fun z : ℂ => Real.exp (-2*s*‖z-u‖^2))
    (fun z : ℂ => Real.exp (-2*s*‖z-u‖^2))

/-- The signed Gaussian interaction `J(s)` is nonnegative (a square integral). -/
theorem signed_gaussJ_nonneg (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {s : ℝ} (hs : 0 < s) :
    0 ≤ gaussJ μ μ s - gaussJ μ ρ s - gaussJ ρ μ s + gaussJ ρ ρ s := by
  have hpp := pair_gaussJ_eq μ μ hs
  have hpr := pair_gaussJ_eq μ ρ hs
  have hrp := pair_gaussJ_eq ρ μ hs
  have hrr := pair_gaussJ_eq ρ ρ hs
  have hIpp := integrable_profile_mul μ μ hs
  have hIpr := integrable_profile_mul μ ρ hs
  have hIrp := integrable_profile_mul ρ μ hs
  have hIrr := integrable_profile_mul ρ ρ hs
  have hsq : ∫ u, (gaussProfile μ s u - gaussProfile ρ s u)^2 ∂volume
      = ∫ u, gaussProfile μ s u * gaussProfile μ s u ∂volume
        - ∫ u, gaussProfile μ s u * gaussProfile ρ s u ∂volume
        - ∫ u, gaussProfile ρ s u * gaussProfile μ s u ∂volume
        + ∫ u, gaussProfile ρ s u * gaussProfile ρ s u ∂volume := by
    have hcongr : (fun u => (gaussProfile μ s u - gaussProfile ρ s u)^2)
        = fun u => gaussProfile μ s u * gaussProfile μ s u
          - gaussProfile μ s u * gaussProfile ρ s u
          - gaussProfile ρ s u * gaussProfile μ s u
          + gaussProfile ρ s u * gaussProfile ρ s u := by
      ext u
      ring
    have hAB : Integrable (fun u => gaussProfile μ s u * gaussProfile μ s u
        - gaussProfile μ s u * gaussProfile ρ s u) volume := hIpp.sub hIpr
    have hABC : Integrable (fun u => gaussProfile μ s u * gaussProfile μ s u
        - gaussProfile μ s u * gaussProfile ρ s u
        - gaussProfile ρ s u * gaussProfile μ s u) volume := hAB.sub hIrp
    rw [hcongr, integral_add hABC hIrr, integral_sub hAB hIrp,
      integral_sub hIpp hIpr]
  rw [hpp, hpr, hrp, hrr, ← mul_sub, ← mul_sub, ← mul_add, ← hsq]
  have h4s : (0:ℝ) ≤ 4*s/Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  apply mul_nonneg h4s
  apply integral_nonneg_of_ae
  filter_upwards with u
  exact sq_nonneg _

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

/-- FTC step: `∫_{u..v} s e^{-sx} dx = e^{-su} - e^{-sv}` (signed form). -/
theorem ftc_exp_aux {s u v : ℝ} :
    ∫ x in u..v, s * Real.exp (-s*x) ∂volume
      = -Real.exp (-s*v) - -Real.exp (-s*u) := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (fun x => -Real.exp (-s*x)) (s * Real.exp (-s*x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -s*x) (-s) x := by
      simpa using (hasDerivAt_id x).const_mul (-s)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-s*x))
        (Real.exp (-s*x) * (-s)) x := h1.exp
    have h3 : HasDerivAt (fun x : ℝ => -Real.exp (-s*x))
        (-(Real.exp (-s*x) * (-s))) x := h2.neg
    have heq : (-(Real.exp (-s*x) * (-s))) = s * Real.exp (-s*x) := by ring
    rw [heq] at h3
    exact h3
  have hcont : Continuous (fun x : ℝ => s * Real.exp (-s*x)) := by fun_prop
  have hint : IntervalIntegrable (fun x => s * Real.exp (-s*x)) volume u v :=
    hcont.intervalIntegrable u v
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Inner `v`-integral in terms of the truncated integrand shape. -/
theorem inner_exp_eq_general {s u v : ℝ} (hs : 0 < s) (huv : u ≤ v) :
    ∫ w in Set.Ioc u v, Real.exp (-s*w) ∂volume
      = (Real.exp (-s*u) - Real.exp (-s*v))/s := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hftc := ftc_exp_aux (s := s) (u := u) (v := v)
  have hmul : ∫ x in u..v, s * Real.exp (-s*x) ∂volume
      = s * ∫ x in u..v, Real.exp (-s*x) ∂volume :=
    intervalIntegral.integral_const_mul s _
  have hdiv : ∫ x in u..v, Real.exp (-s*x) ∂volume
      = (Real.exp (-s*u) - Real.exp (-s*v))/s := by
    rw [eq_div_iff hs0]
    have h := hmul.symm.trans hftc
    linear_combination h
  have hIoc : ∫ x in u..v, Real.exp (-s*x) ∂volume
      = ∫ w in Set.Ioc u v, Real.exp (-s*w) ∂volume :=
    intervalIntegral.integral_of_le huv
  rw [← hIoc]
  exact hdiv

/-- Exponential decay is integrable on `Ioi 0` (Gamma-integral special case). -/
theorem integrableOn_exp_neg_mul {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun s : ℝ => Real.exp (-s*v)) (Set.Ioi 0) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := v)
    (by norm_num) (by norm_num) hv
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show x ^ (0:ℝ) * Real.exp (-v * x ^ (1:ℝ)) = Real.exp (-x*v)
  rw [Real.rpow_zero, Real.rpow_one, one_mul]
  congr 1
  ring

/-- Inner `s`-integral: `∫_{s>0} e^{-sv} ds = 1/v` (lintegral form). -/
theorem lintegral_exp_neg_mul_Ioi {v : ℝ} (hv : 0 < v) :
    ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (Real.exp (-s*v)) ∂volume
      = ENNReal.ofReal v⁻¹ := by
  have hInt : Integrable (fun s : ℝ => Real.exp (-s*v))
      (volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_neg_mul hv
  have hval : ∫ s in Set.Ioi 0, Real.exp (-s*v) ∂volume = v⁻¹ := by
    have h := integral_exp_mul_Ioi (a := -v) (c := 0) (by linarith : -v < 0)
    have hcongr : (∫ s in Set.Ioi 0, Real.exp (-s*v) ∂volume)
        = ∫ x in Set.Ioi 0, Real.exp ((-v)*x) ∂volume := by
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with s
      intro _
      congr 1
      ring
    rw [hcongr, h, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  calc ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (Real.exp (-s*v)) ∂volume
      = ENNReal.ofReal (∫ s in Set.Ioi 0, Real.exp (-s*v) ∂volume) :=
        (ofReal_integral_eq_lintegral_ofReal hInt
          (ae_of_all _ (fun s => (Real.exp_pos _).le))).symm
    _ = ENNReal.ofReal v⁻¹ := by rw [hval]

/-- Outer `v`-integral: `∫_{Ioc u v} w⁻¹ dw = log (v/u)` (lintegral form). -/
theorem lintegral_inv_Ioc_general {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫⁻ w in Set.Ioc u v, ENNReal.ofReal w⁻¹ ∂volume
      = ENNReal.ofReal (Real.log (v/u)) := by
  have hcont : ContinuousOn (fun w : ℝ => w⁻¹) (Set.Icc u v) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    have hx1 : u ≤ x := (Set.mem_Icc.mp hx).1
    show x ≠ 0
    exact ne_of_gt (lt_of_lt_of_le hu hx1)
  have hInt : Integrable (fun w : ℝ => w⁻¹) (volume.restrict (Set.Ioc u v)) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hval : ∫ w in Set.Ioc u v, w⁻¹ ∂volume = Real.log (v/u) := by
    have h := integral_inv_of_pos (a := u) (b := v) hu (lt_of_lt_of_le hu huv)
    rw [intervalIntegral.integral_of_le huv] at h
    exact h
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc u v)] (fun w : ℝ => w⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hw0 : (0:ℝ) ≤ w := by
      have h1 : u < w := (Set.mem_Ioc.mp hw).1
      linarith [hu]
    exact inv_nonneg.mpr hw0
  calc ∫⁻ w in Set.Ioc u v, ENNReal.ofReal w⁻¹ ∂volume
      = ENNReal.ofReal (∫ w in Set.Ioc u v, w⁻¹ ∂volume) :=
        (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = ENNReal.ofReal (Real.log (v/u)) := by rw [hval]

/-- Tonelli computation: the double integral equals `log (v/u)`. -/
theorem tonelli_exp_Ioc {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫⁻ s in Set.Ioi 0, ∫⁻ w in Set.Ioc u v,
        ENNReal.ofReal (Real.exp (-s*w)) ∂volume ∂volume
      = ENNReal.ofReal (Real.log (v/u)) := by
  have hinner : Continuous (fun q : ℝ × ℝ => -q.1 * q.2) := by fun_prop
  have hcont : Continuous
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-q.1*q.2))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hinner)
  have haesm : AEMeasurable
      (Function.uncurry (fun s w => ENNReal.ofReal (Real.exp (-s*w))))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc u v))) :=
    hcont.aemeasurable
  have hswap : (∫⁻ s in Set.Ioi 0, ∫⁻ w in Set.Ioc u v,
          ENNReal.ofReal (Real.exp (-s*w)) ∂volume ∂volume)
      = ∫⁻ w in Set.Ioc u v, ∫⁻ s in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (-s*w)) ∂volume ∂volume :=
    lintegral_lintegral_swap haesm
  rw [hswap]
  have hstep : (∫⁻ w in Set.Ioc u v, ∫⁻ s in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (-s*w)) ∂volume ∂volume)
      = ∫⁻ w in Set.Ioc u v, ENNReal.ofReal w⁻¹ ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hw0 : (0:ℝ) < w := by
      have h1 : u < w := (Set.mem_Ioc.mp hw).1
      linarith [hu]
    exact lintegral_exp_neg_mul_Ioi hw0
  rw [hstep]
  exact lintegral_inv_Ioc_general hu huv

/-- For `r > 1`: the truncated integrand is a `v`-integral. -/
theorem ofReal_truncIntegrand_gt_one {r s : ℝ} (hr : 1 < r) (hs : 0 < s) :
    ENNReal.ofReal (logTruncIntegrand r s)
      = ∫⁻ v in Set.Ioc 1 (r^2), ENNReal.ofReal (Real.exp (-s*v)) ∂volume := by
  have hr2 : (1:ℝ) ≤ r^2 := by nlinarith [hr]
  have e1 : Continuous (fun v : ℝ => Real.exp (-s*v)) := by fun_prop
  have hInt : Integrable (fun v : ℝ => Real.exp (-s*v))
      (volume.restrict (Set.Ioc 1 (r^2))) :=
    (e1.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hval : ∫ v in Set.Ioc 1 (r^2), Real.exp (-s*v) ∂volume
      = logTruncIntegrand r s := by
    have h := inner_exp_eq_general (s := s) (u := 1) (v := r^2) hs hr2
    rw [mul_one] at h
    unfold logTruncIntegrand
    exact h
  calc ENNReal.ofReal (logTruncIntegrand r s)
      = ENNReal.ofReal (∫ v in Set.Ioc 1 (r^2), Real.exp (-s*v) ∂volume) := by
        rw [hval]
    _ = ∫⁻ v in Set.Ioc 1 (r^2), ENNReal.ofReal (Real.exp (-s*v)) ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hInt
          (ae_of_all _ (fun v => (Real.exp_pos _).le))

/-- For `r > 1`: the truncated integrand is nonnegative on `Ioi 0`. -/
theorem nonneg_truncIntegrand_gt_one {r s : ℝ} (hr : 1 < r) (hs : 0 < s) :
    0 ≤ logTruncIntegrand r s := by
  have hr2 : (1:ℝ) ≤ r^2 := by nlinarith [hr]
  have hprod : (0:ℝ) ≤ s * (r^2 - 1) := mul_nonneg hs.le (by linarith)
  unfold logTruncIntegrand
  apply div_nonneg _ hs.le
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  linarith

/-- For `r > 1`: full integral and integrability. -/
theorem integral_truncIntegrand_gt_one {r : ℝ} (hr : 1 < r) :
    Integrable (logTruncIntegrand r) (volume.restrict (Set.Ioi 0))
    ∧ ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume = 2 * Real.log r := by
  have hr2 : (1:ℝ) ≤ r^2 := by nlinarith [hr]
  have hlin : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (logTruncIntegrand r s) ∂volume
      = ENNReal.ofReal (2 * Real.log r) := by
    have hstep : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (logTruncIntegrand r s) ∂volume)
        = ∫⁻ s in Set.Ioi 0, ∫⁻ v in Set.Ioc 1 (r^2),
            ENNReal.ofReal (Real.exp (-s*v)) ∂volume ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
      exact ofReal_truncIntegrand_gt_one hr (Set.mem_Ioi.mp hs0)
    rw [hstep]
    have hton := tonelli_exp_Ioc (u := 1) (v := r^2) (by norm_num) hr2
    rw [div_one] at hton
    rw [hton]
    congr 1
    rw [pow_two, Real.log_mul (by linarith : r ≠ 0) (by linarith : r ≠ 0)]
    ring
  have haesm : AEStronglyMeasurable (logTruncIntegrand r)
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    have e1 : Continuous (fun s : ℝ => Real.exp (-s)) := by fun_prop
    have e2 : Continuous (fun s : ℝ => Real.exp (-s*r^2)) := by fun_prop
    have hnum : ContinuousOn
        (fun s : ℝ => Real.exp (-s) - Real.exp (-s*r^2)) (Set.Ioi 0) :=
      e1.continuousOn.sub e2.continuousOn
    have hdiv : ContinuousOn
        (fun s : ℝ => (Real.exp (-s) - Real.exp (-s*r^2))/s) (Set.Ioi 0) :=
      hnum.div continuousOn_id (fun s hs0 => by
        have hs0' : (0:ℝ) < s := Set.mem_Ioi.mp hs0
        show s ≠ 0
        exact ne_of_gt hs0')
    exact hdiv
  have hInt : Integrable (logTruncIntegrand r) (volume.restrict (Set.Ioi 0)) := by
    refine ⟨haesm, ?_⟩
    show ∫⁻ s, ‖logTruncIntegrand r s‖ₑ ∂(volume.restrict (Set.Ioi 0)) < ∞
    calc ∫⁻ s, ‖logTruncIntegrand r s‖ₑ ∂(volume.restrict (Set.Ioi 0))
        ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (logTruncIntegrand r s) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
          have hg0 := nonneg_truncIntegrand_gt_one hr (Set.mem_Ioi.mp hs0)
          rw [← ofReal_norm, Real.norm_of_nonneg hg0]
      _ = ENNReal.ofReal (2 * Real.log r) := hlin
      _ < ∞ := ENNReal.ofReal_lt_top
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] (logTruncIntegrand r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
    exact nonneg_truncIntegrand_gt_one hr (Set.mem_Ioi.mp hs0)
  have hval : ENNReal.ofReal (∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume)
      = ENNReal.ofReal (2 * Real.log r) :=
    (ofReal_integral_eq_lintegral_ofReal hInt hnn).trans hlin
  have h1 : (0:ℝ) ≤ ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume :=
    integral_nonneg_of_ae hnn
  have h2 : (0:ℝ) ≤ 2 * Real.log r := by
    have hlog : (0:ℝ) ≤ Real.log r := Real.log_nonneg (by linarith : (1:ℝ) ≤ r)
    linarith
  exact ⟨hInt, (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp hval⟩

/-- For `r < 1`: the negated truncated integrand is a `v`-integral. -/
theorem ofReal_neg_truncIntegrand_lt_one {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) :
    ENNReal.ofReal (-logTruncIntegrand r s)
      = ∫⁻ v in Set.Ioc (r^2) 1, ENNReal.ofReal (Real.exp (-s*v)) ∂volume := by
  have hr2 : (r^2:ℝ) ≤ 1 := by nlinarith [hr0, hr1]
  have e1 : Continuous (fun v : ℝ => Real.exp (-s*v)) := by fun_prop
  have hInt : Integrable (fun v : ℝ => Real.exp (-s*v))
      (volume.restrict (Set.Ioc (r^2) 1)) :=
    (e1.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hval : ∫ v in Set.Ioc (r^2) 1, Real.exp (-s*v) ∂volume
      = -logTruncIntegrand r s := by
    have h := inner_exp_eq_general (s := s) (u := r^2) (v := 1) hs hr2
    rw [mul_one] at h
    unfold logTruncIntegrand
    rw [h]
    ring
  calc ENNReal.ofReal (-logTruncIntegrand r s)
      = ENNReal.ofReal (∫ v in Set.Ioc (r^2) 1, Real.exp (-s*v) ∂volume) := by
        rw [hval]
    _ = ∫⁻ v in Set.Ioc (r^2) 1, ENNReal.ofReal (Real.exp (-s*v)) ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hInt
          (ae_of_all _ (fun v => (Real.exp_pos _).le))

/-- For `r < 1`: the truncated integrand is nonpositive on `Ioi 0`. -/
theorem nonpos_truncIntegrand_lt_one {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) :
    logTruncIntegrand r s ≤ 0 := by
  have hr2 : (r^2:ℝ) ≤ 1 := by nlinarith [hr0, hr1]
  have hprod : s * (r^2 - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)
  unfold logTruncIntegrand
  apply div_nonpos_of_nonpos_of_nonneg _ hs.le
  apply sub_nonpos.mpr
  apply Real.exp_le_exp.mpr
  linarith

/-- For `r < 1`: full integral and integrability. -/
theorem integral_truncIntegrand_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Integrable (logTruncIntegrand r) (volume.restrict (Set.Ioi 0))
    ∧ ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume = 2 * Real.log r := by
  have hr2 : (r^2:ℝ) ≤ 1 := by nlinarith [hr0, hr1]
  have hr20 : (0:ℝ) < r^2 := pow_pos hr0 2
  have hlin : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (-logTruncIntegrand r s) ∂volume
      = ENNReal.ofReal (-2 * Real.log r) := by
    have hstep : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (-logTruncIntegrand r s) ∂volume)
        = ∫⁻ s in Set.Ioi 0, ∫⁻ v in Set.Ioc (r^2) 1,
            ENNReal.ofReal (Real.exp (-s*v)) ∂volume ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
      exact ofReal_neg_truncIntegrand_lt_one hr0 hr1 (Set.mem_Ioi.mp hs0)
    rw [hstep]
    have hton := tonelli_exp_Ioc (u := r^2) (v := 1) hr20 hr2
    rw [hton]
    congr 1
    rw [one_div, Real.log_inv, pow_two,
      Real.log_mul (by linarith : r ≠ 0) (by linarith : r ≠ 0)]
    ring
  have haesm : AEStronglyMeasurable (logTruncIntegrand r)
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    have e1 : Continuous (fun s : ℝ => Real.exp (-s)) := by fun_prop
    have e2 : Continuous (fun s : ℝ => Real.exp (-s*r^2)) := by fun_prop
    have hnum : ContinuousOn
        (fun s : ℝ => Real.exp (-s) - Real.exp (-s*r^2)) (Set.Ioi 0) :=
      e1.continuousOn.sub e2.continuousOn
    have hdiv : ContinuousOn
        (fun s : ℝ => (Real.exp (-s) - Real.exp (-s*r^2))/s) (Set.Ioi 0) :=
      hnum.div continuousOn_id (fun s hs0 => by
        have hs0' : (0:ℝ) < s := Set.mem_Ioi.mp hs0
        show s ≠ 0
        exact ne_of_gt hs0')
    exact hdiv
  have hInt : Integrable (logTruncIntegrand r) (volume.restrict (Set.Ioi 0)) := by
    refine ⟨haesm, ?_⟩
    show ∫⁻ s, ‖logTruncIntegrand r s‖ₑ ∂(volume.restrict (Set.Ioi 0)) < ∞
    have hpt : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
        (‖logTruncIntegrand r s‖ₑ) ≤ ENNReal.ofReal (-logTruncIntegrand r s) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
      have hg0 := nonpos_truncIntegrand_lt_one hr0 hr1 (Set.mem_Ioi.mp hs0)
      have habs : |logTruncIntegrand r s| = -logTruncIntegrand r s :=
        abs_of_nonpos hg0
      rw [← ofReal_norm, Real.norm_eq_abs, habs]
    calc ∫⁻ s, ‖logTruncIntegrand r s‖ₑ ∂(volume.restrict (Set.Ioi 0))
        ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (-logTruncIntegrand r s) ∂volume :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (-2 * Real.log r) := hlin
      _ < ∞ := ENNReal.ofReal_lt_top
  have hneg : Integrable (fun s => -logTruncIntegrand r s)
      (volume.restrict (Set.Ioi 0)) := hInt.neg
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun s => -logTruncIntegrand r s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
    have hg0 := nonpos_truncIntegrand_lt_one hr0 hr1 (Set.mem_Ioi.mp hs0)
    show (0:ℝ) ≤ -logTruncIntegrand r s
    linarith
  have hval : ∫ s in Set.Ioi 0, (fun s => -logTruncIntegrand r s) s ∂volume
      = -2 * Real.log r := by
    have hof : ENNReal.ofReal
          (∫ s in Set.Ioi 0, (fun s => -logTruncIntegrand r s) s ∂volume)
        = ENNReal.ofReal (-2 * Real.log r) :=
      (ofReal_integral_eq_lintegral_ofReal hneg hnn).trans hlin
    have h1 : (0:ℝ) ≤ ∫ s in Set.Ioi 0, (fun s => -logTruncIntegrand r s) s ∂volume :=
      integral_nonneg_of_ae hnn
    have h2 : (0:ℝ) ≤ -2 * Real.log r := by
      have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
      linarith
    exact (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp hof
  have hfinal : ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume = 2 * Real.log r := by
    have hneg_eq : ∫ s in Set.Ioi 0, (fun s => -logTruncIntegrand r s) s ∂volume
        = -(∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume) :=
      integral_neg (logTruncIntegrand r)
    rw [hneg_eq] at hval
    linarith
  exact ⟨hInt, hfinal⟩

/-- The absolute truncated integrand is integrable (`r > 1` case). -/
theorem integrable_abs_truncIntegrand_gt_one {r : ℝ} (hr : 1 < r) :
    Integrable (fun s => |logTruncIntegrand r s|)
      (volume.restrict (Set.Ioi 0)) := by
  have hInt := (integral_truncIntegrand_gt_one hr).1
  refine Integrable.congr hInt ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
  show logTruncIntegrand r s = |logTruncIntegrand r s|
  rw [abs_of_nonneg (nonneg_truncIntegrand_gt_one hr (Set.mem_Ioi.mp hs0))]

/-- The absolute truncated integrand is integrable (`r < 1` case). -/
theorem integrable_abs_truncIntegrand_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Integrable (fun s => |logTruncIntegrand r s|)
      (volume.restrict (Set.Ioi 0)) := by
  have hInt := (integral_truncIntegrand_lt_one hr0 hr1).1
  have hneg : Integrable (fun s => -logTruncIntegrand r s)
      (volume.restrict (Set.Ioi 0)) := hInt.neg
  refine Integrable.congr hneg ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
  show -logTruncIntegrand r s = |logTruncIntegrand r s|
  rw [abs_of_nonpos (nonpos_truncIntegrand_lt_one hr0 hr1 (Set.mem_Ioi.mp hs0))]

/-- The truncated integrand vanishes for `r = 1`. -/
theorem truncIntegrand_eq_zero_one (s : ℝ) : logTruncIntegrand 1 s = 0 := by
  unfold logTruncIntegrand
  rw [one_pow, mul_one, sub_self, zero_div]

/-- Truncation sequences: positivity, limits. -/
theorem truncA_pos (n : ℕ) : 0 < truncA n := by
  unfold truncA
  apply inv_pos.mpr
  have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

theorem tendsto_truncB_top : Tendsto truncB atTop atTop := by
  have hle : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ) + 2 :=
    fun n => le_add_of_nonneg_right (by norm_num)
  have htop : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
  exact htop

theorem tendsto_truncA_zero : Tendsto truncA atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ) + 2 :=
    fun n => le_add_of_nonneg_right (by norm_num)
  have htop : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.inv_tendsto_atTop htop

/-- Pointwise domination: `|L_{a,b}(r)| ≤ |log r|`. -/
theorem logTrunc_le_abs_log {a b r : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hr : 0 < r) :
    |logTrunc a b r| ≤ |Real.log r| := by
  have hIoo_sub : Set.Ioo a b ⊆ Set.Ioi 0 := by
    intro s hs
    have h1 : a < s := (Set.mem_Ioo.mp hs).1
    exact Set.mem_Ioi.mpr (lt_trans ha h1)
  by_cases hr1 : r = 1
  · subst hr1
    have hL : logTrunc a b 1 = 0 := by
      unfold logTrunc
      have h0 : ∫ s in Set.Ioo a b, logTruncIntegrand 1 s ∂volume = 0 := by
        trans ∫ s in Set.Ioo a b, (0:ℝ) ∂volume
        · apply integral_congr_ae
          filter_upwards with s
          exact truncIntegrand_eq_zero_one s
        · rw [integral_const]
          exact smul_zero _
      rw [h0, mul_zero]
    rw [hL, Real.log_one, abs_zero]
  · by_cases hr1' : 1 < r
    · have hInt := (integral_truncIntegrand_gt_one hr1').1
      have hval := (integral_truncIntegrand_gt_one hr1').2
      have hlog : Real.log r
          = (1/2) * ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume := by
        rw [hval]; ring
      have hX0 : (0:ℝ) ≤ ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume := by
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact nonneg_truncIntegrand_gt_one hr1'
          (Set.mem_Ioi.mp (hIoo_sub hs))
      have hXY : ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume
          ≤ ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume := by
        apply setIntegral_mono_set hInt _ _
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
          exact nonneg_truncIntegrand_gt_one hr1' (Set.mem_Ioi.mp hs0)
        · exact ae_of_all _ (fun s hs => hIoo_sub hs)
      have hY0 : (0:ℝ) ≤ ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume :=
        le_trans hX0 hXY
      have hL0 : (0:ℝ) ≤ (1/2)
          * ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume :=
        mul_nonneg (by norm_num) hX0
      have hR0 : (0:ℝ) ≤ (1/2)
          * ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume :=
        mul_nonneg (by norm_num) hY0
      unfold logTrunc
      rw [hlog, abs_of_nonneg hL0, abs_of_nonneg hR0]
      exact mul_le_mul_of_nonneg_left hXY (by norm_num)
    · have hr1'' : r < 1 := by
        rcases lt_trichotomy r 1 with h | h | h
        · exact h
        · exact absurd h hr1
        · exact absurd h hr1'
      have hInt := (integral_truncIntegrand_lt_one hr hr1'').1
      have hval := (integral_truncIntegrand_lt_one hr hr1'').2
      have hlog : Real.log r
          = (1/2) * ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume := by
        rw [hval]; ring
      have hX0 : ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume ≤ 0 := by
        apply integral_nonpos_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact nonpos_truncIntegrand_lt_one hr hr1''
          (Set.mem_Ioi.mp (hIoo_sub hs))
      have hYX : ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume
          ≤ ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume := by
        have hneg : Integrable (fun s => -logTruncIntegrand r s)
            (volume.restrict (Set.Ioi 0)) := hInt.neg
        have hmono : ∫ s in Set.Ioo a b, -logTruncIntegrand r s ∂volume
            ≤ ∫ s in Set.Ioi 0, -logTruncIntegrand r s ∂volume := by
          apply setIntegral_mono_set hneg _ _
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
            have hg0 := nonpos_truncIntegrand_lt_one hr hr1'' (Set.mem_Ioi.mp hs0)
            show (0:ℝ) ≤ -logTruncIntegrand r s
            linarith
          · exact ae_of_all _ (fun s hs => hIoo_sub hs)
        have e1 : ∫ s in Set.Ioo a b, -logTruncIntegrand r s ∂volume
            = -(∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume) :=
          integral_neg (logTruncIntegrand r)
        have e2 : ∫ s in Set.Ioi 0, -logTruncIntegrand r s ∂volume
            = -(∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume) :=
          integral_neg (logTruncIntegrand r)
        rw [e1, e2] at hmono
        exact neg_le_neg_iff.mp hmono
      have hL0 : (1/2) * ∫ s in Set.Ioo a b, logTruncIntegrand r s ∂volume ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by norm_num) hX0
      have hR0 : (1/2) * ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_trans hYX hX0)
      unfold logTrunc
      rw [hlog, abs_of_nonpos hL0, abs_of_nonpos hR0, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left hYX (by norm_num)

/-- Pointwise convergence: `L_{a_n,b_n}(r) → log r`. -/
theorem tendsto_logTrunc_seq {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => logTrunc (truncA n) (truncB n) r) atTop (𝓝 (Real.log r)) := by
  by_cases hr1 : r = 1
  · subst hr1
    have h0 : ∀ n, logTrunc (truncA n) (truncB n) 1 = 0 := by
      intro n
      unfold logTrunc
      have h0' : ∫ s in Set.Ioo (truncA n) (truncB n), logTruncIntegrand 1 s ∂volume
          = 0 := by
        trans ∫ s in Set.Ioo (truncA n) (truncB n), (0:ℝ) ∂volume
        · apply integral_congr_ae
          filter_upwards with s
          exact truncIntegrand_eq_zero_one s
        · rw [integral_const]
          exact smul_zero _
      rw [h0', mul_zero]
    simp_rw [h0]
    rw [Real.log_one]
    exact tendsto_const_nhds
  · have hIntAbs : Integrable (fun s => |logTruncIntegrand r s|)
        (volume.restrict (Set.Ioi 0)) := by
      by_cases hr1' : 1 < r
      · exact integrable_abs_truncIntegrand_gt_one hr1'
      · have hr1'' : r < 1 := by
          rcases lt_trichotomy r 1 with h | h | h
          · exact h
          · exact absurd h hr1
          · exact absurd h hr1'
        exact integrable_abs_truncIntegrand_lt_one hr hr1''
    have hval : ∫ s in Set.Ioi 0, logTruncIntegrand r s ∂volume = 2 * Real.log r := by
      by_cases hr1' : 1 < r
      · exact (integral_truncIntegrand_gt_one hr1').2
      · have hr1'' : r < 1 := by
          rcases lt_trichotomy r 1 with h | h | h
          · exact h
          · exact absurd h hr1
          · exact absurd h hr1'
        exact (integral_truncIntegrand_lt_one hr hr1'').2
    have haesm : AEStronglyMeasurable (logTruncIntegrand r)
        (volume.restrict (Set.Ioi 0)) := by
      by_cases hr1' : 1 < r
      · exact (integral_truncIntegrand_gt_one hr1').1.aestronglyMeasurable
      · have hr1'' : r < 1 := by
          rcases lt_trichotomy r 1 with h | h | h
          · exact h
          · exact absurd h hr1
          · exact absurd h hr1'
        exact (integral_truncIntegrand_lt_one hr hr1'').1.aestronglyMeasurable
    have hA := tendsto_truncA_zero
    have hB := tendsto_truncB_top
    have hIoo_sub : ∀ n, Set.Ioo (truncA n) (truncB n) ⊆ Set.Ioi 0 := by
      intro n s hs
      have h1 : truncA n < s := (Set.mem_Ioo.mp hs).1
      exact Set.mem_Ioi.mpr (lt_trans (truncA_pos n) h1)
    have hmeas : ∀ n, AEStronglyMeasurable
          ((Set.Ioo (truncA n) (truncB n)).indicator (logTruncIntegrand r))
          (volume.restrict (Set.Ioi 0)) :=
      fun n => haesm.indicator measurableSet_Ioo
    have hbound : ∀ n, ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
        ‖((Set.Ioo (truncA n) (truncB n)).indicator (logTruncIntegrand r)) s‖
          ≤ |logTruncIntegrand r s| := by
      intro n
      apply ae_of_all
      intro s
      by_cases hs : s ∈ Set.Ioo (truncA n) (truncB n)
      · rw [Set.indicator_of_mem hs]
        exact le_of_eq (Real.norm_eq_abs _).symm
      · rw [Set.indicator_of_notMem hs]
        simp
    have hlim : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), Tendsto
          (fun n => ((Set.Ioo (truncA n) (truncB n)).indicator
            (logTruncIntegrand r)) s) atTop (𝓝 (logTruncIntegrand r s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
      have hs0' : (0:ℝ) < s := Set.mem_Ioi.mp hs0
      have hev1 : ∀ᶠ n in atTop, truncA n < s :=
        Filter.Tendsto.eventually_lt_const hs0' hA
      have hev2 : ∀ᶠ n in atTop, s < truncB n := hB.eventually_gt_atTop s
      have hev : ∀ᶠ n in atTop, logTruncIntegrand r s
          = ((Set.Ioo (truncA n) (truncB n)).indicator (logTruncIntegrand r)) s := by
        filter_upwards [hev1, hev2] with n hn1 hn2
        exact (Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hn1, hn2⟩) _).symm
      exact Filter.Tendsto.congr' hev tendsto_const_nhds
    have hF : ∀ n, (∫ s, ((Set.Ioo (truncA n) (truncB n)).indicator
          (logTruncIntegrand r)) s ∂(volume.restrict (Set.Ioi 0)))
        = ∫ s in Set.Ioo (truncA n) (truncB n), logTruncIntegrand r s ∂volume := by
      intro n
      rw [integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict_of_subset (hIoo_sub n)]
    have hdct := tendsto_integral_of_dominated_convergence
      (F := fun n => (Set.Ioo (truncA n) (truncB n)).indicator (logTruncIntegrand r))
      (f := logTruncIntegrand r)
      (fun s => |logTruncIntegrand r s|) hmeas hIntAbs hbound hlim
    simp_rw [hF] at hdct
    rw [show (∫ s, logTruncIntegrand r s ∂(volume.restrict (Set.Ioi 0)))
      = 2 * Real.log r from hval] at hdct
    have hfin : Tendsto (fun n => (1/2)
          * ∫ s in Set.Ioo (truncA n) (truncB n), logTruncIntegrand r s ∂volume)
        atTop (𝓝 ((1/2) * (2 * Real.log r))) :=
      Filter.Tendsto.const_mul (1/2) hdct
    rw [show (1/2:ℝ) * (2 * Real.log r) = Real.log r by ring] at hfin
    exact hfin

/-! ## Layer 5: truncated energy via Fubini (mass-zero step) -/

/-- Joint integrability of the truncated kernel (bounded on a finite product). -/
theorem integrable_truncKernel (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun q : (ℂ × ℂ) × ℝ => logTruncIntegrand ‖q.1.1 - q.1.2‖ q.2)
      ((μ.prod ρ).prod (volume.restrict (Set.Ioo a b))) := by
  have hprod : (μ.prod ρ).prod (volume.restrict (Set.Ioo a b))
      = ((μ.prod ρ).prod volume).restrict (Set.univ ×ˢ Set.Ioo a b) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas_prod : MeasurableSet (Set.univ ×ˢ Set.Ioo a b : Set ((ℂ × ℂ) × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hAES : AEStronglyMeasurable
      (fun q : (ℂ × ℂ) × ℝ => logTruncIntegrand ‖q.1.1 - q.1.2‖ q.2)
      ((μ.prod ρ).prod (volume.restrict (Set.Ioo a b))) := by
    rw [hprod]
    apply ContinuousOn.aestronglyMeasurable _ hmeas_prod
    have c1 : Continuous
        (fun q : (ℂ × ℂ) × ℝ => Real.exp (-q.2)) := by fun_prop
    have c2 : Continuous
        (fun q : (ℂ × ℂ) × ℝ => Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)) := by fun_prop
    have hnum : ContinuousOn (fun q : (ℂ × ℂ) × ℝ =>
        Real.exp (-q.2) - Real.exp (-q.2*‖q.1.1 - q.1.2‖^2))
        (Set.univ ×ˢ Set.Ioo a b) := c1.continuousOn.sub c2.continuousOn
    have hdiv : ContinuousOn (fun q : (ℂ × ℂ) × ℝ =>
        (Real.exp (-q.2) - Real.exp (-q.2*‖q.1.1 - q.1.2‖^2))/q.2)
        (Set.univ ×ˢ Set.Ioo a b) := by
      refine ContinuousOn.div hnum continuousOn_snd ?_
      intro q hq
      have hmem : q.1 ∈ (Set.univ : Set (ℂ × ℂ)) ∧ q.2 ∈ Set.Ioo a b := hq
      have h2 : a < q.2 ∧ q.2 < b := Set.mem_Ioo.mp hmem.2
      exact ne_of_gt (lt_trans ha h2.1)
    unfold logTruncIntegrand
    exact hdiv
  have hbdd : ∀ᵐ q ∂((μ.prod ρ).prod (volume.restrict (Set.Ioo a b))),
      ‖logTruncIntegrand ‖q.1.1 - q.1.2‖ q.2‖ ≤ 2/a := by
    rw [hprod]
    filter_upwards [ae_restrict_mem hmeas_prod] with q hq
    have hmem : q.1 ∈ (Set.univ : Set (ℂ × ℂ)) ∧ q.2 ∈ Set.Ioo a b := hq
    have h2 : a < q.2 ∧ q.2 < b := Set.mem_Ioo.mp hmem.2
    have hs0 : (0:ℝ) ≤ q.2 := le_trans ha.le h2.1.le
    have hspos : (0:ℝ) < q.2 := lt_trans ha h2.1
    have ha0 : a ≠ 0 := ne_of_gt ha
    have e1 : |Real.exp (-q.2)| ≤ 1 := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0)
    have e2 : |Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)| ≤ 1 := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs0) (sq_nonneg _)
    have hsub : |Real.exp (-q.2) - Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)| ≤ 2 := by
      calc |Real.exp (-q.2) - Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)|
          ≤ |Real.exp (-q.2)| + |Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)| :=
            abs_sub _ _
        _ ≤ 1 + 1 := add_le_add e1 e2
        _ = 2 := by norm_num
    unfold logTruncIntegrand
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    calc |Real.exp (-q.2) - Real.exp (-q.2*‖q.1.1 - q.1.2‖^2)|
        ≤ 2 := hsub
      _ = (2/a)*a := (div_mul_cancel₀ 2 ha0).symm
      _ ≤ (2/a)*q.2 :=
          mul_le_mul_of_nonneg_left h2.1.le (div_nonneg (by norm_num) ha.le)
  exact Integrable.of_bound hAES (2/a) hbdd

/-- Inner integral over `ℂ × ℂ` at fixed `s`. -/
theorem inner_trunc_eq (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {a b : ℝ} (ha : 0 < a) {s : ℝ} (hs : s ∈ Set.Ioo a b) :
    (∫ p, logTruncIntegrand ‖p.1 - p.2‖ s ∂(μ.prod ρ))
      = (Real.exp (-s) * (μ Set.univ).toReal * (ρ Set.univ).toReal
        - gaussJ μ ρ s)/s := by
  have hspos : (0:ℝ) < s := lt_trans ha (Set.mem_Ioo.mp hs).1
  have hs0' : (0:ℝ) ≤ s := hspos.le
  unfold logTruncIntegrand
  rw [integral_div]
  congr 1
  have hconst : Integrable (fun _ : ℂ × ℂ => Real.exp (-s)) (μ.prod ρ) :=
    integrable_const _
  have hK : Integrable
      (fun p : ℂ × ℂ => Real.exp (-s*‖p.1 - p.2‖^2)) (μ.prod ρ) := by
    refine Integrable.of_bound ?_ 1 ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs0') (sq_nonneg _)
  rw [integral_sub hconst hK]
  congr 1
  have huniv : (Set.univ ×ˢ Set.univ : Set (ℂ × ℂ)) = Set.univ := by
    ext p; simp
  have hprod_univ : (μ.prod ρ) Set.univ = μ Set.univ * ρ Set.univ := by
    have h := Measure.prod_prod (μ := μ) (ν := ρ) Set.univ Set.univ
    rwa [huniv] at h
  rw [integral_const]
  show ((μ.prod ρ) Set.univ).toReal • Real.exp (-s) = _
  rw [hprod_univ, ENNReal.toReal_mul, smul_eq_mul]
  ring

/-- Per-pair truncated energy identity. -/
theorem pair_truncEnergy_eq (μ ρ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {a b : ℝ} (ha : 0 < a) :
    ∫ p, logTrunc a b ‖p.1 - p.2‖ ∂(μ.prod ρ)
      = (1/2) * ∫ s in Set.Ioo a b,
          (Real.exp (-s) * (μ Set.univ).toReal * (ρ Set.univ).toReal - gaussJ μ ρ s) / s
          ∂volume := by
  have hswap : (∫ p, ∫ s in Set.Ioo a b, logTruncIntegrand ‖p.1 - p.2‖ s
          ∂volume ∂(μ.prod ρ))
      = ∫ s in Set.Ioo a b, ∫ p, logTruncIntegrand ‖p.1 - p.2‖ s
          ∂(μ.prod ρ) ∂volume :=
    integral_integral_swap (integrable_truncKernel μ ρ ha)
  unfold logTrunc
  rw [integral_const_mul]
  congr 1
  rw [hswap]
  apply setIntegral_congr_ae measurableSet_Ioo
  filter_upwards with s
  intro hs
  exact inner_trunc_eq μ ρ ha hs

/-! ## Layer 6: dominated convergence and the main theorem -/

/-- Truncation sequences are ordered. -/
theorem truncA_le_truncB (n : ℕ) : truncA n ≤ truncB n := by
  have h2 : (1:ℝ) < (n:ℝ) + 2 := by
    have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hlt : ((n:ℝ) + 2)⁻¹ < (n:ℝ) + 2 :=
    lt_trans (inv_lt_one_of_one_lt₀ h2) h2
  unfold truncA truncB
  exact hlt.le

/-- Zero-mass logarithmic energy (Lemma 6.2): `I(ν) ≤ 0`. -/
theorem zero_mass_energy_nonpos (ν : SignedMeasure ℂ)
    (hmass : ν Set.univ = 0)
    (_hsupp : ∃ K : Set ℂ, IsCompact K ∧ ν.totalVariation Kᶜ = 0)
    (hInt : ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) < ∞) :
    signedEnergy ν ≤ 0 := by
  set j := ν.toJordanDecomposition with hj
  have hmass_eq : (j.posPart Set.univ).toReal = (j.negPart Set.univ).toReal := by
    have h := SignedMeasure.apply_eq_posPart_real_sub_negPart_real ν measurableSet_univ
    rw [hmass] at h
    have h2 : j.posPart.real Set.univ = j.negPart.real Set.univ := by linarith
    exact h2
  have hle_p : j.posPart ≤ ν.totalVariation := by
    show j.posPart ≤ j.posPart + j.negPart
    exact le_add_right _ _
  have hle_n : j.negPart ≤ ν.totalVariation := by
    show j.negPart ≤ j.posPart + j.negPart
    exact le_add_left _ _
  have hDmeas : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := by
    have h : Measurable fun p : ℂ × ℂ => p.1 - p.2 :=
      (continuous_fst.sub continuous_snd).measurable
    have hset : {p : ℂ × ℂ | p.1 = p.2} = (fun p : ℂ × ℂ => p.1 - p.2) ⁻¹' {0} := by
      ext p
      simp [sub_eq_zero]
    rw [hset]
    exact h (measurableSet_singleton 0)
  have hDnull_TV : (ν.totalVariation.prod ν.totalVariation)
      {p : ℂ × ℂ | p.1 = p.2} = 0 := by
    by_contra hne
    have hge : ∫⁻ p in {p : ℂ × ℂ | p.1 = p.2}, logKernelAbs p
          ∂(ν.totalVariation.prod ν.totalVariation)
        ≤ ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) :=
      setLIntegral_le_lintegral _ _
    have heq : (∫⁻ p in {p : ℂ × ℂ | p.1 = p.2}, logKernelAbs p
          ∂(ν.totalVariation.prod ν.totalVariation)) = ⊤ := by
      have hconst : (∫⁻ p in {p : ℂ × ℂ | p.1 = p.2}, logKernelAbs p
            ∂(ν.totalVariation.prod ν.totalVariation))
          = ∫⁻ p in {p : ℂ × ℂ | p.1 = p.2}, ⊤
            ∂(ν.totalVariation.prod ν.totalVariation) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hDmeas] with p hp
        have hp' : p.1 = p.2 := hp
        unfold logKernelAbs
        rw [if_pos hp']
      rw [hconst, lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.top_mul hne
    have htop_le : (⊤ : ℝ≥0∞)
        ≤ ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) := by
      rw [← heq]
      exact hge
    have htop := top_le_iff.mp htop_le
    rw [htop] at hInt
    exact absurd hInt (lt_irrefl _)
  have hDnull : ∀ (μ₁ μ₂ : Measure ℂ), μ₁ ≤ ν.totalVariation →
      μ₂ ≤ ν.totalVariation →
      (μ₁.prod μ₂) {p : ℂ × ℂ | p.1 = p.2} = 0 := by
    intro μ₁ μ₂ h1 h2
    have hle : μ₁.prod μ₂ ≤ ν.totalVariation.prod ν.totalVariation :=
      Measure.prod_mono h1 h2
    have hle0 : (μ₁.prod μ₂) {p : ℂ × ℂ | p.1 = p.2}
        ≤ (ν.totalVariation.prod ν.totalVariation) {p : ℂ × ℂ | p.1 = p.2} :=
      hle _
    rw [hDnull_TV] at hle0
    exact nonpos_iff_eq_zero.mp hle0
  have haeD : ∀ (μ₁ μ₂ : Measure ℂ) (h1 : μ₁ ≤ ν.totalVariation)
      (h2 : μ₂ ≤ ν.totalVariation),
      ∀ᵐ p ∂(μ₁.prod μ₂), p ∉ {p : ℂ × ℂ | p.1 = p.2} :=
    fun μ₁ μ₂ h1 h2 => measure_eq_zero_iff_ae_notMem.mp (hDnull μ₁ μ₂ h1 h2)
  have hIntAbs : ∀ (μ₁ μ₂ : Measure ℂ) (h1 : μ₁ ≤ ν.totalVariation)
      (h2 : μ₂ ≤ ν.totalVariation),
      Integrable (fun p : ℂ × ℂ => |logKernel p|) (μ₁.prod μ₂) := by
    intro μ₁ μ₂ h1 h2
    have haesm : AEStronglyMeasurable (fun p : ℂ × ℂ => |logKernel p|) (μ₁.prod μ₂) :=
      (continuous_abs.measurable.comp measurable_logKernel).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    show ∫⁻ p, ‖|logKernel p|‖ₑ ∂(μ₁.prod μ₂) < ∞
    have hpt : ∀ p : ℂ × ℂ, (‖|logKernel p|‖ₑ) ≤ logKernelAbs p := by
      intro p
      by_cases hp : p.1 = p.2
      · have hK : logKernelAbs p = ⊤ := by
          unfold logKernelAbs
          rw [if_pos hp]
        rw [hK]
        exact le_top
      · have hK : logKernelAbs p = ENNReal.ofReal |Real.log ‖p.1 - p.2‖| := by
          unfold logKernelAbs
          rw [if_neg hp]
        have hL : logKernel p = Real.log ‖p.1 - p.2‖ := rfl
        rw [hK, ← ofReal_norm, Real.norm_of_nonneg (abs_nonneg _)]
        exact le_of_eq (by rw [hL])
    calc ∫⁻ p, ‖|logKernel p|‖ₑ ∂(μ₁.prod μ₂)
        ≤ ∫⁻ p, logKernelAbs p ∂(μ₁.prod μ₂) := lintegral_mono hpt
      _ ≤ ∫⁻ p, logKernelAbs p ∂(ν.totalVariation.prod ν.totalVariation) :=
          lintegral_mono' (Measure.prod_mono h1 h2) (le_rfl _)
      _ < ∞ := hInt
  have hIntS : ∀ (μ₁ μ₂ : Measure ℂ) (h1 : μ₁ ≤ ν.totalVariation)
      (h2 : μ₂ ≤ ν.totalVariation),
      Integrable logKernel (μ₁.prod μ₂) := by
    intro μ₁ μ₂ h1 h2
    have hAbs := hIntAbs μ₁ μ₂ h1 h2
    refine ⟨aestronglyMeasurable_logKernel _, ?_⟩
    show ∫⁻ p, ‖logKernel p‖ₑ ∂(μ₁.prod μ₂) < ∞
    have heq : (∫⁻ p, ‖logKernel p‖ₑ ∂(μ₁.prod μ₂))
        = ∫⁻ p, ‖|logKernel p|‖ₑ ∂(μ₁.prod μ₂) := by
      apply lintegral_congr_ae
      filter_upwards with p
      have e1 : (‖logKernel p‖ₑ) = ENNReal.ofReal |logKernel p| := by
        rw [← ofReal_norm, Real.norm_eq_abs]
      have e2 : (‖|logKernel p|‖ₑ) = ENNReal.ofReal |logKernel p| := by
        rw [← ofReal_norm, Real.norm_of_nonneg (abs_nonneg _)]
      rw [e1, e2]
    rw [heq]
    exact hAbs.hasFiniteIntegral
  have hDCT : ∀ (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
      (h1 : μ₁ ≤ ν.totalVariation) (h2 : μ₂ ≤ ν.totalVariation),
      Tendsto (fun n => ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(μ₁.prod μ₂))
        atTop (𝓝 (∫ p, logKernel p ∂(μ₁.prod μ₂))) := by
    intro μ₁ μ₂ _ _ h1 h2
    have hmeas : ∀ n, AEStronglyMeasurable
        (fun p : ℂ × ℂ => logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖) (μ₁.prod μ₂) := by
      intro n
      have hpart := (integrable_truncKernel μ₁ μ₂ (truncA_pos n)).integral_prod_left
      have haesm := hpart.aestronglyMeasurable.const_mul (1/2)
      exact haesm
    have hbound : ∀ n, ∀ᵐ p ∂(μ₁.prod μ₂),
        ‖logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖‖ ≤ |logKernel p| := by
      intro n
      filter_upwards [haeD μ₁ μ₂ h1 h2] with p hp
      have hp' : p.1 ≠ p.2 := hp
      have hr : (0:ℝ) < ‖p.1 - p.2‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hp')
      rw [Real.norm_eq_abs]
      have hle := logTrunc_le_abs_log (truncA_pos n) (truncA_le_truncB n) hr
      show |logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖| ≤ |logKernel p|
      unfold logKernel
      exact hle
    have hlim : ∀ᵐ p ∂(μ₁.prod μ₂), Tendsto
        (fun n => logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖)
        atTop (𝓝 (logKernel p)) := by
      filter_upwards [haeD μ₁ μ₂ h1 h2] with p hp
      have hp' : p.1 ≠ p.2 := hp
      have hr : (0:ℝ) < ‖p.1 - p.2‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hp')
      exact tendsto_logTrunc_seq hr
    exact tendsto_integral_of_dominated_convergence
      (fun p => |logKernel p|) hmeas (hIntAbs μ₁ μ₂ h1 h2) hbound hlim
  have hMZ : ∀ n, (∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖
          ∂(j.posPart.prod j.posPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.posPart.prod j.negPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.posPart)
        + ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.negPart))
        = (1/2) * ∫ s in Set.Ioo (truncA n) (truncB n),
            (-(gaussJ j.posPart j.posPart s - gaussJ j.posPart j.negPart s
              - gaussJ j.negPart j.posPart s + gaussJ j.negPart j.negPart s))/s
            ∂volume := by
    intro n
    have ha' := truncA_pos n
    rw [pair_truncEnergy_eq j.posPart j.posPart ha',
      pair_truncEnergy_eq j.posPart j.negPart ha',
      pair_truncEnergy_eq j.negPart j.posPart ha',
      pair_truncEnergy_eq j.negPart j.negPart ha']
    have hFint : ∀ (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂],
        Integrable (fun s => (Real.exp (-s) * (μ₁ Set.univ).toReal
          * (μ₂ Set.univ).toReal - gaussJ μ₁ μ₂ s)/s)
          (volume.restrict (Set.Ioo (truncA n) (truncB n))) := by
      intro μ₁ μ₂ _ _
      have hpart := (integrable_truncKernel μ₁ μ₂ ha').integral_prod_right
      refine Integrable.congr hpart ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact inner_trunc_eq μ₁ μ₂ ha' hs
    have ePP := hFint j.posPart j.posPart
    have ePN := hFint j.posPart j.negPart
    have eNP := hFint j.negPart j.posPart
    have eNN := hFint j.negPart j.negPart
    have eAB : Integrable (fun s =>
        (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.posPart Set.univ).toReal
          - gaussJ j.posPart j.posPart s)/s
        - (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.negPart Set.univ).toReal
          - gaussJ j.posPart j.negPart s)/s)
        (volume.restrict (Set.Ioo (truncA n) (truncB n))) := ePP.sub ePN
    have eABC : Integrable (fun s =>
        (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.posPart Set.univ).toReal
          - gaussJ j.posPart j.posPart s)/s
        - (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.negPart Set.univ).toReal
          - gaussJ j.posPart j.negPart s)/s
        - (Real.exp (-s) * (j.negPart Set.univ).toReal * (j.posPart Set.univ).toReal
          - gaussJ j.negPart j.posPart s)/s)
        (volume.restrict (Set.Ioo (truncA n) (truncB n))) := eAB.sub eNP
    rw [← mul_sub, ← mul_sub, ← mul_add]
    congr 1
    rw [← integral_sub ePP ePN, ← integral_sub eAB eNP, ← integral_add eABC eNN]
    apply setIntegral_congr_ae measurableSet_Ioo
    filter_upwards with s
    intro _
    show (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.posPart Set.univ).toReal
          - gaussJ j.posPart j.posPart s)/s
        - (Real.exp (-s) * (j.posPart Set.univ).toReal * (j.negPart Set.univ).toReal
          - gaussJ j.posPart j.negPart s)/s
        - (Real.exp (-s) * (j.negPart Set.univ).toReal * (j.posPart Set.univ).toReal
          - gaussJ j.negPart j.posPart s)/s
        + (Real.exp (-s) * (j.negPart Set.univ).toReal * (j.negPart Set.univ).toReal
          - gaussJ j.negPart j.negPart s)/s
        = (-(gaussJ j.posPart j.posPart s - gaussJ j.posPart j.negPart s
          - gaussJ j.negPart j.posPart s + gaussJ j.negPart j.negPart s))/s
    rw [hmass_eq, ← sub_div, ← sub_div, ← add_div]
    congr 1
    ring
  have hnonpos : ∀ n, (∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖
          ∂(j.posPart.prod j.posPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.posPart.prod j.negPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.posPart)
        + ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.negPart))
        ≤ 0 := by
    intro n
    rw [hMZ n]
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hspos : (0:ℝ) < s :=
      lt_trans (truncA_pos n) (Set.mem_Ioo.mp hs).1
    have hJ : 0 ≤ gaussJ j.posPart j.posPart s - gaussJ j.posPart j.negPart s
        - gaussJ j.negPart j.posPart s + gaussJ j.negPart j.negPart s :=
      signed_gaussJ_nonneg j.posPart j.negPart hspos
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hJ) hspos.le
  have hlim : Tendsto (fun n => (∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖
          ∂(j.posPart.prod j.posPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.posPart.prod j.negPart)
        - ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.posPart)
        + ∫ p, logTrunc (truncA n) (truncB n) ‖p.1 - p.2‖ ∂(j.negPart.prod j.negPart)))
      atTop (𝓝 (pairEnergy j.posPart j.posPart - pairEnergy j.posPart j.negPart
        - pairEnergy j.negPart j.posPart + pairEnergy j.negPart j.negPart)) :=
    ((hDCT j.posPart j.posPart hle_p hle_p).sub
      (hDCT j.posPart j.negPart hle_p hle_n)).sub
      (hDCT j.negPart j.posPart hle_n hle_p) |>.add
      (hDCT j.negPart j.negPart hle_n hle_n)
  have hfinal : pairEnergy j.posPart j.posPart - pairEnergy j.posPart j.negPart
      - pairEnergy j.negPart j.posPart + pairEnergy j.negPart j.negPart ≤ 0 :=
    le_of_tendsto' hlim hnonpos
  show pairEnergy j.posPart j.posPart - pairEnergy j.posPart j.negPart
      - pairEnergy j.negPart j.posPart + pairEnergy j.negPart j.negPart ≤ 0
  exact hfinal

end ZetaSeven.ZeroMassEnergy
