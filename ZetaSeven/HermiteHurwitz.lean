import Mathlib

/-!
# Hermite's integral for the Hurwitz zeta function at `s = 7`

Paper: Prince Anand, "Zeta 7 is Irrational", proof of Proposition 2.4 (Section 2.5),
the paragraph before equation (19): Hermite's integral formula (DLMF 25.11.29) at `s = 7`,

`ζ(7, a) = 1/(2a⁷) + 1/(6a⁶) + 2 ∫₀^∞ y (7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/(y² + a²)⁷ dy/(e^{2πy} - 1)`.

We prove it for real `a > 0` (the paper uses it at positive integers `a = j`), with
`ζ(7, a) = ∑_{n ≥ 0} (n + a)⁻⁷` as a real series (`hurwitzZeta7`), and we prove that the
integrand is integrable on `(0, ∞)`, so the Bochner integral is a genuine value.

Route:
* `720 ζ(7, a) = ∫₀^∞ t⁶ e^{-at}/(1 - e^{-t}) dt` (Gamma integrals of `(n + a)⁻⁷` summed);
* the Laplace transform `∫₀^∞ t⁶ e^{-at} sin(yt) dt = 720 y(7a⁶ - …)/(y² + a²)⁷`, the
  imaginary part of `∫₀^∞ t⁶ e^{-(a - iy)t} dt = 720/(a - iy)⁷`;
* the kernel `∫₀^∞ sin(yt)/(e^{2πy} - 1) dy = (1/(1 - e^{-t}) - 1/2 - 1/t)/2`, from the
  geometric expansion of `1/(e^{2πy} - 1)`, the Laplace transform of the sine, and the
  Mittag-Leffler series of the cotangent (`cot_series_rep'`) on the imaginary axis;
* Fubini on `(0, ∞)²`.
-/

namespace ZetaSeven

open Real MeasureTheory Set Filter Topology

/-! ### The Hurwitz zeta value `ζ(7, a)` -/

/-- The Hurwitz zeta value `ζ(7, a) = ∑_{n ≥ 0} 1/(n + a)⁷`, as a real series. For `a > 0`
the series converges (`summable_hurwitzZeta7`). -/
noncomputable def hurwitzZeta7 (a : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + a) ^ 7

/-- Shifted `p`-series: `∑ 1/(n + a)^p` converges for `a > 0` and `p > 1`. -/
private lemma summable_one_div_nat_add_pow {a : ℝ} (ha : 0 < a) {p : ℕ} (hp : 1 < p) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + a) ^ p := by
  have h := (Real.summable_one_div_nat_add_rpow a (p : ℝ)).mpr (by exact_mod_cast hp)
  refine h.congr fun n => ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + a), Real.rpow_natCast]

/-- The series defining `ζ(7, a)` converges for `a > 0`. -/
theorem summable_hurwitzZeta7 {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + a) ^ 7 :=
  summable_one_div_nat_add_pow ha (by norm_num)

private lemma hurwitzZeta7_pos {a : ℝ} (ha : 0 < a) : 0 < hurwitzZeta7 a := by
  unfold hurwitzZeta7
  exact (summable_hurwitzZeta7 ha).tsum_pos (fun n => by positivity) 0 (by positivity)

/-! ### Gamma integrals -/

/-- `t^n e^{-bt}` is integrable on `(0, ∞)` for `b > 0`. -/
lemma integrableOn_pow_mul_exp_neg_mul (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-b * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) one_pos hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

/-- `∫₀^∞ t^n e^{-bt} dt = n!/b^{n+1}` for `b > 0`. -/
lemma integral_pow_mul_exp_neg_mul (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-b * t) = (Nat.factorial n : ℝ) / b ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := b) (by positivity) hb
  rw [Real.Gamma_nat_eq_factorial] at h
  calc ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-b * t)
      = ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(b * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
    _ = (1 / b) ^ ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := h
    _ = (Nat.factorial n : ℝ) / b ^ (n + 1) := by
        rw [← Nat.cast_add_one, Real.rpow_natCast, one_div_pow]
        ring

private lemma integral_pow_five_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ 5 * Real.exp (-b * t) = 120 / b ^ 6 := by
  rw [integral_pow_mul_exp_neg_mul 5 hb]
  norm_num [Nat.factorial]

private lemma integral_pow_six_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-b * t) = 720 / b ^ 7 := by
  rw [integral_pow_mul_exp_neg_mul 6 hb]
  norm_num [Nat.factorial]

/-! ### `ζ(7, a)` as a Gamma-type integral -/

/-- Gamma-integral representation: `720 ζ(7, a) = ∫₀^∞ t⁶ e^{-at}/(1 - e^{-t}) dt`. -/
lemma hurwitzZeta7_eq_integral {a : ℝ} (ha : 0 < a) :
    720 * hurwitzZeta7 a =
      ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) := by
  have hb : ∀ n : ℕ, 0 < (n : ℝ) + a := fun n => by positivity
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ 6 * Real.exp (-((n : ℝ) + a) * t))
      (volume.restrict (Ioi 0)) := fun n => integrableOn_pow_mul_exp_neg_mul 6 (hb n)
  have hval : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-((n : ℝ) + a) * t) =
      720 * (1 / ((n : ℝ) + a) ^ 7) := fun n => by
    rw [integral_pow_six_mul_exp (hb n)]
    ring
  have hnorm : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), ‖t ^ 6 * Real.exp (-((n : ℝ) + a) * t)‖ =
      720 * (1 / ((n : ℝ) + a) ^ 7) := fun n => by
    rw [← hval n]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    exact Real.norm_of_nonneg (by positivity)
  have hsum : Summable fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖t ^ 6 * Real.exp (-((n : ℝ) + a) * t)‖ :=
    ((summable_hurwitzZeta7 ha).mul_left 720).congr fun n => (hnorm n).symm
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ∑' n : ℕ, t ^ 6 * Real.exp (-((n : ℝ) + a) * t) =
      t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht')
    have hterm : ∀ n : ℕ, t ^ 6 * Real.exp (-((n : ℝ) + a) * t) =
        t ^ 6 * Real.exp (-a * t) * Real.exp (-t) ^ n := by
      intro n
      rw [show -((n : ℝ) + a) * t = -a * t + n * (-t) by ring, Real.exp_add, Real.exp_nat_mul]
      ring
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]
  calc 720 * hurwitzZeta7 a = ∑' n : ℕ, 720 * (1 / ((n : ℝ) + a) ^ 7) := by
        rw [hurwitzZeta7, tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-((n : ℝ) + a) * t) :=
        tsum_congr fun n => (hval n).symm
    _ = ∫ t in Ioi (0 : ℝ), ∑' n : ℕ, t ^ 6 * Real.exp (-((n : ℝ) + a) * t) :=
        integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) :=
        setIntegral_congr_fun measurableSet_Ioi hpt

/-! ### Laplace transforms -/

/-- Laplace transform of the sine: `∫₀^∞ sin(yt) e^{-cy} dy = t/(t² + c²)` for `c > 0`. -/
lemma integral_sin_mul_exp_neg_mul (t : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), Real.sin (y * t) * Real.exp (-c * y) = t / (t ^ 2 + c ^ 2) := by
  have hre : (-(c : ℂ) + t * Complex.I).re = -c := by simp
  have him : (-(c : ℂ) + t * Complex.I).im = t := by simp
  have hw : (-(c : ℂ) + t * Complex.I).re < 0 := by rw [hre]; linarith
  have hpt : ∀ y : ℝ, Real.sin (y * t) * Real.exp (-c * y) =
      (Complex.exp ((-(c : ℂ) + t * Complex.I) * y)).im := by
    intro y
    rw [Complex.exp_im, Complex.re_mul_ofReal, Complex.im_mul_ofReal, hre, him]
    ring_nf
  have hI := integral_im (μ := volume.restrict (Ioi (0 : ℝ)))
    (integrableOn_exp_mul_complex_Ioi hw 0)
  simp only [RCLike.im_to_complex] at hI
  calc ∫ y in Ioi (0 : ℝ), Real.sin (y * t) * Real.exp (-c * y)
      = ∫ y in Ioi (0 : ℝ), (Complex.exp ((-(c : ℂ) + t * Complex.I) * y)).im :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = (∫ y in Ioi (0 : ℝ), Complex.exp ((-(c : ℂ) + t * Complex.I) * y)).im := hI
    _ = (-Complex.exp ((-(c : ℂ) + t * Complex.I) * ((0 : ℝ) : ℂ)) /
          (-(c : ℂ) + t * Complex.I)).im := by
        rw [integral_exp_mul_complex_Ioi hw 0]
    _ = t / (t ^ 2 + c ^ 2) := by
        rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, Complex.neg_im, one_div,
          Complex.inv_im, him, Complex.normSq_apply, hre, him,
          show -c * -c + t * t = t ^ 2 + c ^ 2 by ring]
        ring

/-- Derivative of the polynomial part of the antiderivative of `w⁶ e^{-zw}`
(written with `u = z⁻¹`). -/
private lemma hasDerivAt_laplacePoly (u w : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ 6 * u + 6 * w ^ 5 * u ^ 2 + 30 * w ^ 4 * u ^ 3 +
        120 * w ^ 3 * u ^ 4 + 360 * w ^ 2 * u ^ 5 + 720 * w * u ^ 6 + 720 * u ^ 7)
      (6 * w ^ 5 * u + 30 * w ^ 4 * u ^ 2 + 120 * w ^ 3 * u ^ 3 + 360 * w ^ 2 * u ^ 4 +
        720 * w * u ^ 5 + 720 * u ^ 6) w := by
  have d6 : HasDerivAt (fun x : ℂ => x ^ 6) (6 * w ^ 5) w :=
    (hasDerivAt_pow 6 w).congr_deriv (by norm_num)
  have d5 : HasDerivAt (fun x : ℂ => x ^ 5) (5 * w ^ 4) w :=
    (hasDerivAt_pow 5 w).congr_deriv (by norm_num)
  have d4 : HasDerivAt (fun x : ℂ => x ^ 4) (4 * w ^ 3) w :=
    (hasDerivAt_pow 4 w).congr_deriv (by norm_num)
  have d3 : HasDerivAt (fun x : ℂ => x ^ 3) (3 * w ^ 2) w :=
    (hasDerivAt_pow 3 w).congr_deriv (by norm_num)
  have d2 : HasDerivAt (fun x : ℂ => x ^ 2) (2 * w) w :=
    (hasDerivAt_pow 2 w).congr_deriv (by norm_num)
  have d1 : HasDerivAt (fun x : ℂ => x) 1 w := hasDerivAt_id' w
  exact ((((((d6.mul_const u).fun_add ((d5.const_mul 6).mul_const (u ^ 2))).fun_add
    ((d4.const_mul 30).mul_const (u ^ 3))).fun_add
    ((d3.const_mul 120).mul_const (u ^ 4))).fun_add
    ((d2.const_mul 360).mul_const (u ^ 5))).fun_add
    ((d1.const_mul 720).mul_const (u ^ 6))).add_const (720 * u ^ 7) |>.congr_deriv (by ring)

/-- An antiderivative of `w⁶ e^{-zw}`, given `u` with `z u = 1`. -/
private lemma hasDerivAt_laplaceAnti {z u : ℂ} (hzu : z * u = 1) (w : ℂ) :
    HasDerivAt (fun w : ℂ => -Complex.exp (-z * w) * (w ^ 6 * u + 6 * w ^ 5 * u ^ 2 +
        30 * w ^ 4 * u ^ 3 + 120 * w ^ 3 * u ^ 4 + 360 * w ^ 2 * u ^ 5 + 720 * w * u ^ 6 +
        720 * u ^ 7))
      (w ^ 6 * Complex.exp (-z * w)) w := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp (-z * w))
      (Complex.exp (-z * w) * (-z * 1)) w :=
    ((hasDerivAt_id' w).const_mul (-z)).cexp
  exact (he.fun_neg.fun_mul (hasDerivAt_laplacePoly u w)).congr_deriv (by
    linear_combination (Complex.exp (-z * w) * (w ^ 6 + 6 * w ^ 5 * u + 30 * w ^ 4 * u ^ 2 +
      120 * w ^ 3 * u ^ 3 + 360 * w ^ 2 * u ^ 4 + 720 * w * u ^ 5 + 720 * u ^ 6)) * hzu)

private lemma integrableOn_cpow_six_mul_cexp {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ 6 * Complex.exp (-z * t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_pow_mul_exp_neg_mul 6 hz)
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ 6 * Complex.exp (-z * t)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
  apply le_of_eq
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show (0 : ℝ) < t from ht), hre]

private lemma tendsto_cpow_mul_cexp (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ j * Complex.exp (-z * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) z.re hz).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
  rw [Real.rpow_natCast, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, hre]

/-- `∫₀^∞ t⁶ e^{-zt} dt = 720/z⁷` for `Re z > 0`. -/
private lemma integral_cpow_six_mul_cexp {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 6 * Complex.exp (-z * t) = 720 / z ^ 7 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hzu : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -Complex.exp (-z * t) *
      ((t : ℂ) ^ 6 * z⁻¹ + 6 * (t : ℂ) ^ 5 * z⁻¹ ^ 2 + 30 * (t : ℂ) ^ 4 * z⁻¹ ^ 3 +
        120 * (t : ℂ) ^ 3 * z⁻¹ ^ 4 + 360 * (t : ℂ) ^ 2 * z⁻¹ ^ 5 + 720 * (t : ℂ) * z⁻¹ ^ 6 +
        720 * z⁻¹ ^ 7)) ((x : ℂ) ^ 6 * Complex.exp (-z * x)) x :=
    fun x _ => (hasDerivAt_laplaceAnti hzu (x : ℂ)).comp_ofReal
  have htend : Tendsto (fun t : ℝ => -Complex.exp (-z * t) *
      ((t : ℂ) ^ 6 * z⁻¹ + 6 * (t : ℂ) ^ 5 * z⁻¹ ^ 2 + 30 * (t : ℂ) ^ 4 * z⁻¹ ^ 3 +
        120 * (t : ℂ) ^ 3 * z⁻¹ ^ 4 + 360 * (t : ℂ) ^ 2 * z⁻¹ ^ 5 + 720 * (t : ℂ) * z⁻¹ ^ 6 +
        720 * z⁻¹ ^ 7)) atTop (𝓝 0) := by
    have h := ((((((((tendsto_cpow_mul_cexp 6 hz).const_mul z⁻¹).add
      ((tendsto_cpow_mul_cexp 5 hz).const_mul (6 * z⁻¹ ^ 2))).add
      ((tendsto_cpow_mul_cexp 4 hz).const_mul (30 * z⁻¹ ^ 3))).add
      ((tendsto_cpow_mul_cexp 3 hz).const_mul (120 * z⁻¹ ^ 4))).add
      ((tendsto_cpow_mul_cexp 2 hz).const_mul (360 * z⁻¹ ^ 5))).add
      ((tendsto_cpow_mul_cexp 1 hz).const_mul (720 * z⁻¹ ^ 6))).add
      ((tendsto_cpow_mul_cexp 0 hz).const_mul (720 * z⁻¹ ^ 7))).neg
    simp only [mul_zero, add_zero, neg_zero] at h
    refine h.congr fun t => ?_
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_cpow_six_mul_cexp hz) htend]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

private lemma im_720_div_ofReal_add_mul_I {A B D : ℝ} (hD : A ^ 2 + B ^ 2 = D) :
    ((720 : ℂ) / ((A : ℂ) + B * Complex.I)).im = -720 * B / D := by
  have hre : ((A : ℂ) + B * Complex.I).re = A := by simp
  have him : ((A : ℂ) + B * Complex.I).im = B := by simp
  have h720re : (720 : ℂ).re = 720 := by norm_num
  have h720im : (720 : ℂ).im = 0 := by norm_num
  rw [Complex.div_im, hre, him, h720re, h720im, Complex.normSq_add_mul_I, hD]
  ring

/-- The Laplace transform behind Hermite's integrand:
`∫₀^∞ t⁶ e^{-at} sin(yt) dt = 720 y (7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/(y² + a²)⁷` for `a > 0`. -/
lemma integral_pow_six_mul_exp_mul_sin {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) =
      720 * (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7) := by
  have hz : 0 < ((a : ℂ) - y * Complex.I).re := by simpa using ha
  have hpt : ∀ t : ℝ, t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) =
      ((t : ℂ) ^ 6 * Complex.exp (-((a : ℂ) - y * Complex.I) * t)).im := by
    intro t
    have hre : (-((a : ℂ) - y * Complex.I) * t).re = -a * t := by simp
    have him : (-((a : ℂ) - y * Complex.I) * t).im = y * t := by simp
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, Complex.exp_im, hre, him]
    ring
  have hI := integral_im (μ := volume.restrict (Ioi (0 : ℝ)))
    (integrableOn_cpow_six_mul_cexp hz)
  simp only [RCLike.im_to_complex] at hI
  have hz7 : ((a : ℂ) - y * Complex.I) ^ 7 =
      ((a ^ 7 - 21 * a ^ 5 * y ^ 2 + 35 * a ^ 3 * y ^ 4 - 7 * a * y ^ 6 : ℝ) : ℂ) +
        ((-7 * a ^ 6 * y + 35 * a ^ 4 * y ^ 3 - 21 * a ^ 2 * y ^ 5 + y ^ 7 : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    linear_combination (21 * (a : ℂ) ^ 5 * (y : ℂ) ^ 2 -
      35 * (a : ℂ) ^ 4 * (y : ℂ) ^ 3 * Complex.I +
      35 * (a : ℂ) ^ 3 * (y : ℂ) ^ 4 * Complex.I ^ 2 - 35 * (a : ℂ) ^ 3 * (y : ℂ) ^ 4 -
      21 * (a : ℂ) ^ 2 * (y : ℂ) ^ 5 * Complex.I ^ 3 +
      21 * (a : ℂ) ^ 2 * (y : ℂ) ^ 5 * Complex.I +
      7 * (a : ℂ) * (y : ℂ) ^ 6 * Complex.I ^ 4 - 7 * (a : ℂ) * (y : ℂ) ^ 6 * Complex.I ^ 2 +
      7 * (a : ℂ) * (y : ℂ) ^ 6 - (y : ℂ) ^ 7 * Complex.I ^ 5 + (y : ℂ) ^ 7 * Complex.I ^ 3 -
      (y : ℂ) ^ 7 * Complex.I) * Complex.I_sq
  have hD : (a ^ 7 - 21 * a ^ 5 * y ^ 2 + 35 * a ^ 3 * y ^ 4 - 7 * a * y ^ 6) ^ 2 +
      (-7 * a ^ 6 * y + 35 * a ^ 4 * y ^ 3 - 21 * a ^ 2 * y ^ 5 + y ^ 7) ^ 2 =
        (y ^ 2 + a ^ 2) ^ 7 := by
    ring
  calc ∫ t in Ioi (0 : ℝ), t ^ 6 * Real.exp (-a * t) * Real.sin (y * t)
      = ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ 6 * Complex.exp (-((a : ℂ) - y * Complex.I) * t)).im :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 6 * Complex.exp (-((a : ℂ) - y * Complex.I) * t)).im :=
        hI
    _ = ((720 : ℂ) / ((a : ℂ) - y * Complex.I) ^ 7).im := by
        rw [integral_cpow_six_mul_cexp hz]
    _ = -720 * (-7 * a ^ 6 * y + 35 * a ^ 4 * y ^ 3 - 21 * a ^ 2 * y ^ 5 + y ^ 7) /
          (y ^ 2 + a ^ 2) ^ 7 := by
        rw [hz7, im_720_div_ofReal_add_mul_I hD]
    _ = 720 * (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
          (y ^ 2 + a ^ 2) ^ 7) := by
        ring

/-! ### The kernel `∫₀^∞ sin(yt)/(e^{2πy} - 1) dy` -/

/-- A cotangent-series term on the imaginary axis: for `x = s i` and `m = n + 1`,
`1/(x - m) + 1/(x + m) = (s/(s² + m²)) · (-2i)`. -/
private lemma cotTerm_imag (s : ℝ) (n : ℕ) :
    1 / ((s : ℂ) * Complex.I - ((n : ℂ) + 1)) + 1 / ((s : ℂ) * Complex.I + ((n : ℂ) + 1)) =
      ((s / (s ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) * (-2 * Complex.I) := by
  have hD : (0 : ℝ) < s ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
  have hDc : ((s ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  have hprod : ((s : ℂ) * Complex.I - ((n : ℂ) + 1)) * ((s : ℂ) * Complex.I + ((n : ℂ) + 1)) =
      -((s ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (s : ℂ) ^ 2 * Complex.I_sq
  have hne : ((s : ℂ) * Complex.I - ((n : ℂ) + 1)) *
      ((s : ℂ) * Complex.I + ((n : ℂ) + 1)) ≠ 0 := by
    rw [hprod]
    exact neg_ne_zero.mpr hDc
  rw [div_add_div _ _ (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne), hprod,
    Complex.ofReal_div]
  field

/-- The Mittag-Leffler series of the cotangent on the imaginary axis:
`∑_{n ≥ 1} s/(s² + n²) = (π (e^{-2πs} + 1)/(1 - e^{-2πs}) - 1/s)/2` for `s > 0`. -/
private lemma tsum_imag_cot {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, s / (s ^ 2 + ((n : ℝ) + 1) ^ 2) =
      (π * (Real.exp (-(2 * π * s)) + 1) / (1 - Real.exp (-(2 * π * s))) - 1 / s) / 2 := by
  have hxim : 0 < ((s : ℂ) * Complex.I).im := by simpa using hs
  have hx : (s : ℂ) * Complex.I ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨(s : ℂ) * Complex.I, hxim⟩
  have hE : Complex.exp (2 * π * Complex.I * ((s : ℂ) * Complex.I)) =
      ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (2 * (π : ℂ) * s) * Complex.I_sq
  have hsum : ∑' n : ℕ, ((s / (s ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      ((∑' n : ℕ, s / (s ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm
  have h1 := cot_series_rep' hx
  rw [tsum_congr (cotTerm_imag s), tsum_mul_right, hsum, Complex.cot_pi_eq_exp_ratio, hE] at h1
  set E := Real.exp (-(2 * π * s))
  set T := ∑' n : ℕ, s / (s ^ 2 + ((n : ℝ) + 1) ^ 2)
  have hinv1 : (Complex.I * (1 - (E : ℂ)))⁻¹ = -Complex.I * (1 - (E : ℂ))⁻¹ := by
    rw [mul_inv, Complex.inv_I]
  have hinv2 : ((s : ℂ) * Complex.I)⁻¹ = -(s : ℂ)⁻¹ * Complex.I := by
    rw [mul_inv, Complex.inv_I]
    ring
  have h3 : ((-2 * T : ℝ) : ℂ) * Complex.I =
      ((-(π * (E + 1) / (1 - E)) + 1 / s : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination -h1 + ((π : ℂ) * ((E : ℂ) + 1)) * hinv1 - hinv2
  have h4 := Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h3)
  linarith

/-- `∑_{k ≥ 1} t/(t² + (2πk)²) = (1/(1 - e^{-t}) - 1/2 - 1/t)/2` for `t > 0`. -/
private lemma tsum_coth {t : ℝ} (ht : 0 < t) :
    ∑' k : ℕ, t / (t ^ 2 + (2 * π * ((k : ℝ) + 1)) ^ 2) =
      (1 / (1 - Real.exp (-t)) - 1 / 2 - 1 / t) / 2 := by
  have hs : 0 < t / (2 * π) := by positivity
  have hterm : ∀ k : ℕ, t / (t ^ 2 + (2 * π * ((k : ℝ) + 1)) ^ 2) =
      1 / (2 * π) * (t / (2 * π) / ((t / (2 * π)) ^ 2 + ((k : ℝ) + 1) ^ 2)) := fun k => by
    field
  have h2 : 2 * π * (t / (2 * π)) = t := by field
  have hE : 1 - Real.exp (-t) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))).ne'
  rw [tsum_congr hterm, tsum_mul_left, tsum_imag_cot hs, h2]
  field

/-- Geometric expansion: `sin(yt)/(e^{2πy} - 1) = ∑_{k ≥ 1} sin(yt) e^{-2πky}` for `y > 0`. -/
private lemma tsum_sin_mul_exp (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ∑' k : ℕ, Real.sin (y * t) * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) =
      Real.sin (y * t) / (Real.exp (2 * π * y) - 1) := by
  have hq0 : 0 ≤ Real.exp (-(2 * π * y)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * π * y)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hterm : ∀ k : ℕ, Real.sin (y * t) * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) =
      Real.sin (y * t) * Real.exp (-(2 * π * y)) * Real.exp (-(2 * π * y)) ^ k := by
    intro k
    rw [show -(2 * π * ((k : ℝ) + 1)) * y = -(2 * π * y) + k * (-(2 * π * y)) by ring,
      Real.exp_add, Real.exp_nat_mul]
    ring
  have hE0 : Real.exp (2 * π * y) ≠ 0 := (Real.exp_pos _).ne'
  have hE1 : Real.exp (2 * π * y) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have hsub : 1 - (Real.exp (2 * π * y))⁻¹ =
      (Real.exp (2 * π * y) - 1) / Real.exp (2 * π * y) := by
    field
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, Real.exp_neg, hsub,
    inv_div]
  field

/-- The Hermite kernel: `∫₀^∞ sin(yt)/(e^{2πy} - 1) dy = (1/(1 - e^{-t}) - 1/2 - 1/t)/2`
for `t > 0`. -/
lemma integral_sin_div_exp_sub_one {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioi (0 : ℝ), Real.sin (y * t) / (Real.exp (2 * π * y) - 1) =
      (1 / (1 - Real.exp (-t)) - 1 / 2 - 1 / t) / 2 := by
  have hc : ∀ k : ℕ, 0 < 2 * π * ((k : ℝ) + 1) := fun k => by positivity
  have hint : ∀ k : ℕ, Integrable (fun y : ℝ => Real.sin (y * t) *
      Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)) (volume.restrict (Ioi 0)) := by
    intro k
    refine Integrable.mono' (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (hc k)) 0)
      (by fun_prop : Continuous fun y : ℝ => Real.sin (y * t) *
        Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hbound : ∀ k : ℕ, ∫ y in Ioi (0 : ℝ), ‖Real.sin (y * t) *
      Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)‖ ≤ t / (2 * π * ((k : ℝ) + 1)) ^ 2 := by
    intro k
    calc ∫ y in Ioi (0 : ℝ), ‖Real.sin (y * t) * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)‖
        ≤ ∫ y in Ioi (0 : ℝ), t * (y ^ 1 * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
            (Integrable.const_mul (integrableOn_pow_mul_exp_neg_mul 1 (hc k)) t)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
          have hy' : (0 : ℝ) < y := hy
          have he : 0 < Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) := Real.exp_pos _
          have hs : |Real.sin (y * t)| ≤ y * t := by
            have h := Real.abs_sin_le_abs (x := y * t)
            rwa [abs_of_pos (mul_pos hy' ht)] at h
          dsimp only
          rw [norm_mul, Real.norm_of_nonneg he.le, Real.norm_eq_abs, pow_one]
          calc |Real.sin (y * t)| * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)
              ≤ y * t * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) :=
                mul_le_mul_of_nonneg_right hs he.le
            _ = t * (y * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)) := by ring
      _ = t / (2 * π * ((k : ℝ) + 1)) ^ 2 := by
          rw [integral_const_mul, integral_pow_mul_exp_neg_mul 1 (hc k), Nat.factorial_one,
            Nat.cast_one]
          ring
  have hsumm : Summable fun k : ℕ => t / (2 * π * ((k : ℝ) + 1)) ^ 2 := by
    have h := (summable_one_div_nat_add_pow (a := 1) one_pos (p := 2) one_lt_two).mul_left
      (t / (2 * π) ^ 2)
    refine h.congr fun k => ?_
    field
  have hsum : Summable fun k : ℕ => ∫ y in Ioi (0 : ℝ), ‖Real.sin (y * t) *
      Real.exp (-(2 * π * ((k : ℝ) + 1)) * y)‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) hbound hsumm
  calc ∫ y in Ioi (0 : ℝ), Real.sin (y * t) / (Real.exp (2 * π * y) - 1)
      = ∫ y in Ioi (0 : ℝ), ∑' k : ℕ,
          Real.sin (y * t) * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) :=
        setIntegral_congr_fun measurableSet_Ioi fun y hy => (tsum_sin_mul_exp t hy).symm
    _ = ∑' k : ℕ, ∫ y in Ioi (0 : ℝ),
          Real.sin (y * t) * Real.exp (-(2 * π * ((k : ℝ) + 1)) * y) :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' k : ℕ, t / (t ^ 2 + (2 * π * ((k : ℝ) + 1)) ^ 2) :=
        tsum_congr fun k => integral_sin_mul_exp_neg_mul t (hc k)
    _ = (1 / (1 - Real.exp (-t)) - 1 / 2 - 1 / t) / 2 := tsum_coth ht

/-! ### Fubini on `(0, ∞)²` and Hermite's formula -/

/-- `y/(e^{2πy} - 1) ≤ e^{-πy}/π` for `y > 0`. -/
private lemma div_exp_sub_one_le {y : ℝ} (hy : 0 < y) :
    y / (Real.exp (2 * π * y) - 1) ≤ Real.exp (-π * y) / π := by
  have hπ : 0 < π := Real.pi_pos
  have hu : 0 < π * y := mul_pos hπ hy
  have h1 : π * y + 1 ≤ Real.exp (π * y) := Real.add_one_le_exp _
  have h2 : 1 ≤ Real.exp (π * y) := Real.one_le_exp hu.le
  have h3 : Real.exp (2 * π * y) = Real.exp (π * y) * Real.exp (π * y) := by
    rw [← Real.exp_add]
    ring_nf
  have h4 : π * y * Real.exp (π * y) ≤ Real.exp (2 * π * y) - 1 := by
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (π * y)).le]
  have h5 : 0 < Real.exp (2 * π * y) - 1 := lt_of_lt_of_le (by positivity) h4
  have h6 : Real.exp (-π * y) * Real.exp (π * y) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [div_le_div_iff₀ h5 hπ]
  calc y * π = Real.exp (-π * y) * (π * y * Real.exp (π * y)) := by
        rw [show Real.exp (-π * y) * (π * y * Real.exp (π * y)) =
          π * y * (Real.exp (-π * y) * Real.exp (π * y)) by ring, h6]
        ring
    _ ≤ Real.exp (-π * y) * (Real.exp (2 * π * y) - 1) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le

/-- Pointwise domination of the Fubini integrand on `(0, ∞)²`. -/
private lemma hermiteKernel_bound {a y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    ‖t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1)‖ ≤
      Real.exp (-π * y) / π * (t ^ 7 * Real.exp (-a * t)) := by
  have hE : 0 < Real.exp (2 * π * y) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hsin : |Real.sin (y * t)| ≤ y * t := by
    have h := Real.abs_sin_le_abs (x := y * t)
    rwa [abs_of_pos (mul_pos hy ht)] at h
  have hA : 0 ≤ t ^ 6 * Real.exp (-a * t) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hA, abs_of_pos hE]
  calc t ^ 6 * Real.exp (-a * t) * |Real.sin (y * t)| / (Real.exp (2 * π * y) - 1)
      ≤ t ^ 6 * Real.exp (-a * t) * (y * t) / (Real.exp (2 * π * y) - 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsin hA) hE.le
    _ = t ^ 7 * Real.exp (-a * t) * (y / (Real.exp (2 * π * y) - 1)) := by ring
    _ ≤ t ^ 7 * Real.exp (-a * t) * (Real.exp (-π * y) / π) :=
        mul_le_mul_of_nonneg_left (div_exp_sub_one_le hy) (by positivity)
    _ = Real.exp (-π * y) / π * (t ^ 7 * Real.exp (-a * t)) := by ring

/-- The Fubini integrand `t⁶ e^{-at} sin(yt)/(e^{2πy} - 1)` is integrable on `(0, ∞)²`. -/
private lemma integrable_hermiteKernel {a : ℝ} (ha : 0 < a) :
    Integrable (Function.uncurry fun y t : ℝ =>
        t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg : Integrable (fun p : ℝ × ℝ => Real.exp (-π * p.1) / π * (p.2 ^ 7 * Real.exp (-a * p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod (f := fun y : ℝ => Real.exp (-π * y) / π)
      (g := fun t : ℝ => t ^ 7 * Real.exp (-a * t))
      (Integrable.div_const (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 0) π)
      (integrableOn_pow_mul_exp_neg_mul 7 ha)
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.2 ^ 6 * Real.exp (-a * p.2) * Real.sin (p.1 * p.2) /
        (Real.exp (2 * π * p.1) - 1)).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    exact ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      fun p hp => hermiteKernel_bound hp.1 hp.2

/-- Inner `t`-integral: `720` times Hermite's integrand. -/
private lemma hermite_left {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
        t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1) =
      720 * ∫ y in Ioi (0 : ℝ), y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7 / (Real.exp (2 * π * y) - 1) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [integral_div, integral_pow_six_mul_exp_mul_sin ha y]
  ring

/-- Inner `y`-integral, then the Gamma integrals. -/
private lemma hermite_right {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1) =
      1 / 2 * (720 * hurwitzZeta7 a - 1 / 2 * (720 / a ^ 7) - 120 / a ^ 6) := by
  have hin : ∀ t ∈ Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1) =
      1 / 2 * (t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) -
        1 / 2 * (t ^ 6 * Real.exp (-a * t)) - t ^ 5 * Real.exp (-a * t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hq : 1 - Real.exp (-t) ≠ 0 :=
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht'))).ne'
    calc ∫ y in Ioi (0 : ℝ),
          t ^ 6 * Real.exp (-a * t) * Real.sin (y * t) / (Real.exp (2 * π * y) - 1)
        = ∫ y in Ioi (0 : ℝ),
          t ^ 6 * Real.exp (-a * t) * (Real.sin (y * t) / (Real.exp (2 * π * y) - 1)) :=
          integral_congr_ae (ae_of_all _ fun y => by ring)
      _ = t ^ 6 * Real.exp (-a * t) *
          ∫ y in Ioi (0 : ℝ), Real.sin (y * t) / (Real.exp (2 * π * y) - 1) :=
          integral_const_mul _ _
      _ = 1 / 2 * (t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) -
          1 / 2 * (t ^ 6 * Real.exp (-a * t)) - t ^ 5 * Real.exp (-a * t)) := by
          rw [integral_sin_div_exp_sub_one ht']
          field
  have hA : Integrable (fun t : ℝ => t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← hurwitzZeta7_eq_integral ha]
    exact (mul_pos (by norm_num) (hurwitzZeta7_pos ha)).ne'
  have hB : Integrable (fun t : ℝ => 1 / 2 * (t ^ 6 * Real.exp (-a * t)))
      (volume.restrict (Ioi 0)) :=
    Integrable.const_mul (integrableOn_pow_mul_exp_neg_mul 6 ha) _
  have hC : Integrable (fun t : ℝ => t ^ 5 * Real.exp (-a * t)) (volume.restrict (Ioi 0)) :=
    integrableOn_pow_mul_exp_neg_mul 5 ha
  have hAB : Integrable (fun t : ℝ => t ^ 6 * Real.exp (-a * t) / (1 - Real.exp (-t)) -
      1 / 2 * (t ^ 6 * Real.exp (-a * t))) (volume.restrict (Ioi 0)) := hA.sub hB
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul, integral_sub hAB hC,
    integral_sub hA hB, integral_const_mul, ← hurwitzZeta7_eq_integral ha,
    integral_pow_six_mul_exp ha, integral_pow_five_mul_exp ha]

/-- **Hermite's integral formula at `s = 7`** (DLMF 25.11.29; proof of Proposition 2.4,
before equation (19)): for real `a > 0`,
`ζ(7, a) = 1/(2a⁷) + 1/(6a⁶) + 2 ∫₀^∞ y(7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/(y² + a²)⁷ dy/(e^{2πy} - 1)`.
The integrand is integrable (`integrableOn_hermite_integrand`). -/
theorem hurwitzZeta7_eq_hermite_integral {a : ℝ} (ha : 0 < a) :
    hurwitzZeta7 a = 1 / (2 * a ^ 7) + 1 / (6 * a ^ 6) +
      2 * ∫ y in Ioi (0 : ℝ), y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7 / (Real.exp (2 * π * y) - 1) := by
  have key := (hermite_left ha).symm.trans
    ((integral_integral_swap (integrable_hermiteKernel ha)).trans (hermite_right ha))
  linear_combination (-1 / 360 : ℝ) * key

/-- Hermite's integrand `y(7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/((y² + a²)⁷ (e^{2πy} - 1))` is
integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_hermite_integrand {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
      (y ^ 2 + a ^ 2) ^ 7 / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
  refine (((integrable_hermiteKernel ha).integral_prod_left).const_mul (1 / 720)).congr
    (ae_of_all _ fun y => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [integral_div, integral_pow_six_mul_exp_mul_sin ha y]
  ring

end ZetaSeven
