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
        = ∫⁻ u, ENNReal.ofReal (Real.exp (-2*s*‖u - p.1‖^2)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards with u
      have hrev : ‖p.1 - u‖ = ‖u - p.1‖ := by rw [← norm_neg, neg_sub]
      rw [hrev]
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
    have h12 : Integrable (fun u => gaussProfile μ s u * gaussProfile μ s u
        - gaussProfile μ s u * gaussProfile ρ s u
        - gaussProfile ρ s u * gaussProfile μ s u) volume := (hIpp.sub hIpr).sub hIrp
    rw [hcongr, integral_add h12 hIrr, integral_sub (hIpp.sub hIpr) hIrp,
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
