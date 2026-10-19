import ZetaSeven.Andreief
import ZetaSeven.PositiveIntegral
import ZetaSeven.ExternalField

/-!
# Andreief's identity and scaling (paper Section 6.5, equations (101)-(104))

Prince Anand, "Zeta 7 is Irrational", Section 6.5. Throughout `K = 40n`, `N = 3n`,
`h = 37n` (`hDim n`), and `Δ_K(ζ(7)) = det G_K(ζ(7))` is
`aeval (riemannZeta 7).re (DeltaK n)`.

* (101) `aeval_DeltaK_zeta_eq_andreief`: Andreief's identity applied to the moment matrix (7),
  `Δ_K(ζ(7)) = (1/h!) ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏_i D_N(y_i²)⁸/D_K(y_i²) w₇(y_i) dy`,
  where the integrand is integrable (`integrable_andreief_integrand`).
* (102) `w7_le`: `w₇(y) ≤ 8192 (1 + y)⁷ e^{-2πy}` for `y > 0`.
* (103) `riemann_sum_log_bound`: for `1 ≤ m ≤ K` and `t ≥ 0`,
  `0 ≤ ∑_{j=1}^m log(t + (j/K)²) - K ∫_0^{m/K} log(t + u²) du ≤ 2 log K + 2`.
* (104) `aeval_DeltaK_zeta_le_scaled`: after `y_i = K √t_i`,
  `Δ_K(ζ(7)) ≤ K^{2h(h+8N-K)+16h} (4096 e¹²)^h / h! ·
  ∫_{(0,∞)^h} ∏_{i<j} (t_i - t_j)² ∏_i e^{-K V(t_i)} t_i^{-1/2} (1 + √t_i)⁷ dt`,
  with `V = Vfield` the external field (91); the integrand is integrable
  (`integrable_scaled_integrand`), and the residual density `t^{-1/2} (1 + √t)⁷ e^{-√t}` is
  integrable on `(0, ∞)` (`integrableOn_residual_density`).

Proof notes. (102): the terms `ℓ ≥ 2` of the series of `w₇` are bounded with
`x⁶ e^{-x} ≤ 6!`, and the remaining geometric series is summed. (103): on each step
`[(j-1)/K, j/K]` the integrand lies between its values at the two ends; for the upper bound,
`log((t + b²)/(t + u²)) ≤ log(b²/u²)` for `0 < u ≤ b` reduces every step to `t = 0`, where the
difference is `2(log m! - m log m + m) ≤ log m + 2` by Mathlib's Stirling sequence. This sharper
form of (103), with `log m` in place of `2 log K`, is what yields the constants of (104).
(104) is proved entrywise: the substitution `y = K√t` in each entry of `G_K(ζ(7))`, then
Andreief's identity in the `t` variables and a pointwise bound of the scaled weight by (102),
(103) and the definition (91) of `V`.
-/

namespace ZetaSeven

open Real MeasureTheory Set Filter Polynomial

/-! ### The weight bound (102) -/

/-- `x⁶ e^{-x} ≤ 6!` for `x ≥ 0`. -/
private lemma pow_six_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) : x ^ 6 * Real.exp (-x) ≤ 720 := by
  have h := Real.pow_div_factorial_le_exp (x := x) hx 6
  have h6 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [h6, div_le_iff₀ (by norm_num)] at h
  calc x ^ 6 * Real.exp (-x) ≤ Real.exp x * 720 * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 720 * (Real.exp x * Real.exp (-x)) := by ring
    _ = 720 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- One term of the series of `w₇` beyond the first: for `y > 0` and `a ≥ 1`,
`y⁶ (a + 1)⁶ e^{-2π(a+1)y} ≤ (46080/π⁶) e^{-2πy} e^{-πay}`. -/
private lemma w7_term_le {y a : ℝ} (hy : 0 < y) (ha : 1 ≤ a) :
    y ^ 6 * ((a + 1) ^ 6 * Real.exp (-(2 * π * (a + 1)) * y)) ≤
      46080 / π ^ 6 * Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y)) := by
  have ha0 : 0 < a := by linarith
  have hx := pow_six_mul_exp_neg_le (x := π * a * y) (by positivity)
  have key : a ^ 6 * y ^ 6 * Real.exp (-(π * a * y)) ≤ 720 / π ^ 6 := by
    rw [le_div_iff₀ (by positivity)]
    calc a ^ 6 * y ^ 6 * Real.exp (-(π * a * y)) * π ^ 6
        = (π * a * y) ^ 6 * Real.exp (-(π * a * y)) := by ring
      _ ≤ 720 := hx
  have hexp : Real.exp (-(2 * π * (a + 1)) * y) =
      Real.exp (-(π * a * y)) * (Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ha6 : (a + 1) ^ 6 ≤ 64 * a ^ 6 := by
    have h2 : a + 1 ≤ 2 * a := by linarith
    calc (a + 1) ^ 6 ≤ (2 * a) ^ 6 := by gcongr
      _ = 64 * a ^ 6 := by ring
  have hE : 0 ≤ Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y)) := by positivity
  have hY : 0 ≤ y ^ 6 * Real.exp (-(π * a * y)) := by positivity
  calc y ^ 6 * ((a + 1) ^ 6 * Real.exp (-(2 * π * (a + 1)) * y))
      = (a + 1) ^ 6 * (y ^ 6 * Real.exp (-(π * a * y))) *
          (Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y))) := by rw [hexp]; ring
    _ ≤ (64 * a ^ 6) * (y ^ 6 * Real.exp (-(π * a * y))) *
          (Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha6 hY) hE
    _ = 64 * (a ^ 6 * y ^ 6 * Real.exp (-(π * a * y))) *
          (Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y))) := by ring
    _ ≤ 64 * (720 / π ^ 6) * (Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (by norm_num)) hE
    _ = 46080 / π ^ 6 * Real.exp (-(2 * π * y)) * Real.exp (-(π * a * y)) := by ring

/-- Equation (102): `w₇(y) ≤ 8192 (1 + y)⁷ e^{-2πy}` for `y > 0`. -/
theorem w7_le {y : ℝ} (hy : 0 < y) :
    w7 y ≤ 8192 * (1 + y) ^ 7 * Real.exp (-(2 * π * y)) := by
  set r : ℝ := Real.exp (-(π * y)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos Real.pi_pos hy))
  have hsum := summable_w7_series hy
  have hS : (∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) =
      Real.exp (-(2 * π * y)) + ∑' ℓ : ℕ, (((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
        Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y) := by
    rw [hsum.tsum_eq_zero_add]
    congr 1
    simp only [Nat.cast_zero, zero_add, one_pow, one_mul]
    congr 1
    ring
  have hsum1 : Summable fun ℓ : ℕ => (((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
      Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y) :=
    (summable_nat_add_iff 1).mpr hsum
  have hgeo : Summable fun ℓ : ℕ => 46080 / π ^ 6 * Real.exp (-(2 * π * y)) * r ^ (ℓ + 1) :=
    ((summable_geometric_of_lt_one hr0 hr1).mul_left
      (46080 / π ^ 6 * Real.exp (-(2 * π * y)) * r)).congr fun ℓ => by ring
  have hterm : ∀ ℓ : ℕ, y ^ 6 * ((((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
      Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y)) ≤
      46080 / π ^ 6 * Real.exp (-(2 * π * y)) * r ^ (ℓ + 1) := by
    intro ℓ
    have h := w7_term_le hy (a := ((ℓ + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.le_add_left 1 ℓ)
    have hrl : r ^ (ℓ + 1) = Real.exp (-(π * ((ℓ + 1 : ℕ) : ℝ) * y)) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [hrl]
    exact h
  have hT : y ^ 6 * ∑' ℓ : ℕ, (((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
      Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y) ≤
      46080 / π ^ 6 * Real.exp (-(2 * π * y)) * (r * (1 - r)⁻¹) := by
    rw [← tsum_mul_left]
    calc ∑' ℓ : ℕ, y ^ 6 * ((((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
          Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y))
        ≤ ∑' ℓ : ℕ, 46080 / π ^ 6 * Real.exp (-(2 * π * y)) * r ^ (ℓ + 1) :=
          Summable.tsum_le_tsum hterm (hsum1.mul_left _) hgeo
      _ = 46080 / π ^ 6 * Real.exp (-(2 * π * y)) * (r * ∑' ℓ : ℕ, r ^ ℓ) := by
          rw [← tsum_mul_left, ← tsum_mul_left]
          congr 1
          ext ℓ
          ring
      _ = 46080 / π ^ 6 * Real.exp (-(2 * π * y)) * (r * (1 - r)⁻¹) := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
  have hyr : y * (r * (1 - r)⁻¹) ≤ 1 / π := by
    have h1 : π * y + 1 ≤ Real.exp (π * y) := Real.add_one_le_exp _
    have h2 : r * Real.exp (π * y) = 1 := by
      rw [hr, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : 0 < 1 - r := by linarith
    have h4 : y * r * π ≤ 1 - r := by linarith [mul_le_mul_of_nonneg_left h1 hr0]
    rw [← mul_assoc, ← div_eq_mul_inv, div_le_div_iff₀ h3 Real.pi_pos]
    linarith
  have hc' : (2 * π) ^ 6 / 360 * (46080 / π ^ 6) = 8192 := by
    rw [div_mul_div_comm, mul_pow, div_eq_iff (by positivity)]
    ring
  have hc : (2 * π) ^ 6 / 360 ≤ 8192 := by
    have h1 := Real.pi_lt_d2
    have h2 : (2 * π) ^ 6 ≤ ((63 : ℝ) / 10) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h3 : ((63 : ℝ) / 10) ^ 6 ≤ 8192 * 360 := by norm_num
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hπ1 : 8192 / π ≤ 8192 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hy7 : 1 + y ^ 7 ≤ (1 + y) ^ 7 := by
    have h := pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hy.le (by norm_num : (7 : ℕ) ≠ 0)
    rwa [one_pow] at h
  have hE := Real.exp_pos (-(2 * π * y))
  have hS1 : 0 ≤ ∑' ℓ : ℕ, (((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
      Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y) :=
    tsum_nonneg fun ℓ => by positivity
  set S1 := ∑' ℓ : ℕ, (((ℓ + 1 : ℕ) : ℝ) + 1) ^ 6 *
      Real.exp (-(2 * π * (((ℓ + 1 : ℕ) : ℝ) + 1)) * y) with hS1def
  set E := Real.exp (-(2 * π * y)) with hEdef
  set q := r * (1 - r)⁻¹ with hq
  set c := (2 * π) ^ 6 / 360 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have h8E : (0 : ℝ) ≤ 8192 * E := mul_nonneg (by norm_num) hE.le
  have step2 : c * y * (y ^ 6 * S1) ≤ c * y * (46080 / π ^ 6 * E * q) :=
    mul_le_mul_of_nonneg_left hT (mul_nonneg hc0.le hy.le)
  have step3 : c * y * (46080 / π ^ 6 * E * q) = 8192 * E * (y * q) := by
    rw [← hc']
    ring
  have step4 : 8192 * E * (y * q) ≤ 8192 * E * (1 / π) :=
    mul_le_mul_of_nonneg_left hyr h8E
  have hyE : 0 ≤ y ^ 7 * E := mul_nonneg (pow_nonneg hy.le 7) hE.le
  have hfin1 := mul_le_mul_of_nonneg_right hc hyE
  have hfin2 := mul_le_mul_of_nonneg_right hπ1 hE.le
  have hfin3 := mul_le_mul_of_nonneg_left hy7 h8E
  have hw : w7 y = c * y ^ 7 * E + c * y * (y ^ 6 * S1) := by
    rw [w7, hS, hcdef]
    ring
  rw [hw]
  have h1π : 8192 * E * (1 / π) = 8192 / π * E := by ring
  linarith [step2, step3, step4, hfin1, hfin2, hfin3, h1π]

/-! ### The Riemann-sum comparison (103) -/

private lemma intervalIntegrable_log_add_sq {t : ℝ} (ht : 0 ≤ t) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log (t + u ^ 2)) volume a b := by
  rcases ht.eq_or_lt with h | h
  · subst h
    have hfun : (fun u : ℝ => Real.log (0 + u ^ 2)) = fun u => 2 * Real.log u := by
      ext u
      rw [zero_add, Real.log_pow]
      norm_num
    rw [hfun]
    exact intervalIntegral.intervalIntegrable_log'.const_mul 2
  · have hc : Continuous fun u : ℝ => t + u ^ 2 := continuous_const.add (continuous_pow 2)
    have hne : ∀ u : ℝ, t + u ^ 2 ≠ 0 := fun u => by positivity
    exact (hc.log hne).intervalIntegrable a b

/-- Splitting `∫_0^{m/K}` at the points `j/K`. -/
private lemma integral_eq_sum_steps (K m : ℕ) (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    ∫ u in (0 : ℝ)..((m : ℝ) / K), f u =
      ∑ j ∈ Finset.range m, ∫ u in ((j : ℝ) / K)..(((j : ℝ) + 1) / K), f u := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun j : ℕ => (j : ℝ) / K) (n := m) (fun j _ => hf _ _)
  simp only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one] at h
  exact h.symm

/-- One step of (103), lower bound: `K ∫_{j/K}^{(j+1)/K} log(t + u²) du ≤ log(t + ((j+1)/K)²)`,
since the integrand is increasing in `u > 0`. -/
private lemma step_integral_le (K j : ℕ) (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    (K : ℝ) * ∫ u in ((j : ℝ) / K)..(((j : ℝ) + 1) / K), Real.log (t + u ^ 2) ≤
      Real.log (t + (((j : ℝ) + 1) / K) ^ 2) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hle : (j : ℝ) / K ≤ ((j : ℝ) + 1) / K := div_le_div_of_nonneg_right (by linarith) hK'.le
  have hpt : ∀ u ∈ Ioo ((j : ℝ) / K) (((j : ℝ) + 1) / K),
      Real.log (t + u ^ 2) ≤ Real.log (t + (((j : ℝ) + 1) / K) ^ 2) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu.1
    have hsq : u ^ 2 ≤ (((j : ℝ) + 1) / K) ^ 2 := pow_le_pow_left₀ hu0.le hu.2.le 2
    exact Real.log_le_log (by positivity) (by linarith)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hle
    (intervalIntegrable_log_add_sq ht _ _) intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  calc (K : ℝ) * ∫ u in ((j : ℝ) / K)..(((j : ℝ) + 1) / K), Real.log (t + u ^ 2)
      ≤ (K : ℝ) * ((((j : ℝ) + 1) / K - (j : ℝ) / K) *
          Real.log (t + (((j : ℝ) + 1) / K) ^ 2)) := mul_le_mul_of_nonneg_left h hK'.le
    _ = Real.log (t + (((j : ℝ) + 1) / K) ^ 2) := by
        rw [← sub_div, add_sub_cancel_left, ← mul_assoc, mul_one_div_cancel hK'.ne', one_mul]

/-- One step of (103), upper bound, reduced to `t = 0`: with `b = (j+1)/K`,
`log(t + b²) - K ∫_{j/K}^{b} log(t + u²) du ≤ 2 log b - 2K ∫_{j/K}^{b} log u du`,
because `log((t + b²)/(t + u²)) ≤ log(b²/u²)` for `0 < u ≤ b`. -/
private lemma step_sub_integral_le (K j : ℕ) (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (t + (((j : ℝ) + 1) / K) ^ 2) -
        (K : ℝ) * ∫ u in ((j : ℝ) / K)..(((j : ℝ) + 1) / K), Real.log (t + u ^ 2) ≤
      2 * Real.log (((j : ℝ) + 1) / K) -
        2 * ((K : ℝ) * ∫ u in ((j : ℝ) / K)..(((j : ℝ) + 1) / K), Real.log u) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  set b : ℝ := ((j : ℝ) + 1) / K with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hle : (j : ℝ) / K ≤ b := by
    rw [hb]
    exact div_le_div_of_nonneg_right (by linarith) hK'.le
  have hpt : ∀ u ∈ Ioo ((j : ℝ) / K) b,
      Real.log (t + b ^ 2) - 2 * Real.log b + 2 * Real.log u ≤ Real.log (t + u ^ 2) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu.1
    have hsq : u ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hu0.le hu.2.le 2
    have hmul : (t + b ^ 2) * u ^ 2 ≤ b ^ 2 * (t + u ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hsq ht]
    have hA : 0 < t + b ^ 2 := by positivity
    have hB : 0 < u ^ 2 := by positivity
    have hC : 0 < b ^ 2 := by positivity
    have hD : 0 < t + u ^ 2 := by positivity
    have hlog := Real.log_le_log (mul_pos hA hB) hmul
    rw [Real.log_mul hA.ne' hB.ne', Real.log_mul hC.ne' hD.ne', Real.log_pow, Real.log_pow]
      at hlog
    push_cast at hlog
    linarith
  have hint1 : IntervalIntegrable
      (fun u => Real.log (t + b ^ 2) - 2 * Real.log b + 2 * Real.log u) volume ((j : ℝ) / K) b :=
    intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_log'.const_mul 2)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hle hint1
    (intervalIntegrable_log_add_sq ht _ _) hpt
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_log'.const_mul 2), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, smul_eq_mul] at h
  have hlen : (K : ℝ) * (b - (j : ℝ) / K) = 1 := by
    rw [hb, ← sub_div, add_sub_cancel_left, mul_one_div_cancel hK'.ne']
  have hc : (K : ℝ) * ((b - (j : ℝ) / K) * (Real.log (t + b ^ 2) - 2 * Real.log b)) =
      Real.log (t + b ^ 2) - 2 * Real.log b := by
    rw [← mul_assoc, hlen, one_mul]
  linarith [mul_le_mul_of_nonneg_left h hK'.le, hc]

/-- (103), lower bound, for any positive integer `K`. -/
private lemma le_riemann_sum (K m : ℕ) (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    (K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) ≤
      ∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2) := by
  rw [integral_eq_sum_steps K m _ (intervalIntegrable_log_add_sq ht), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => step_integral_le K j hK ht

/-- `∑_{j=1}^m log(j/K) = log m! - m log K`. -/
private lemma sum_log_succ_div (K m : ℕ) (hK : 0 < K) :
    ∑ j ∈ Finset.range m, Real.log (((j : ℝ) + 1) / K) =
      Real.log (m.factorial : ℝ) - m * Real.log K := by
  have hK' : (K : ℝ) ≠ 0 := by positivity
  have hprod : (∏ j ∈ Finset.range m, ((j : ℝ) + 1)) = (m.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial m
  have h1 : ∀ j ∈ Finset.range m,
      Real.log (((j : ℝ) + 1) / K) = Real.log ((j : ℝ) + 1) - Real.log K :=
    fun j _ => Real.log_div (Nat.cast_add_one_ne_zero j) hK'
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Real.log_prod (s := Finset.range m) (f := fun j : ℕ => (j : ℝ) + 1)
      (fun j _ => Nat.cast_add_one_ne_zero j), hprod]

/-- `K ∫_0^{m/K} log u du = m log m - m log K - m`. -/
private lemma mul_integral_log (K m : ℕ) (hK : 0 < K) :
    (K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log u =
      m * Real.log m - m * Real.log K - m := by
  have hK' : (K : ℝ) ≠ 0 := by positivity
  rw [integral_log]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hKm : (K : ℝ) * ((m : ℝ) / K) = m := mul_div_cancel₀ _ hK'
    rw [Real.log_div (Nat.cast_pos.mpr hm).ne' hK']
    calc (K : ℝ) * ((m : ℝ) / K * (Real.log m - Real.log K) - 0 * Real.log 0 - (m : ℝ) / K + 0)
        = ((K : ℝ) * ((m : ℝ) / K)) * (Real.log m - Real.log K) - (K : ℝ) * ((m : ℝ) / K) := by
          ring
      _ = m * Real.log m - m * Real.log K - m := by rw [hKm]; ring

/-- (103), upper bound in the sharp form: the difference is at most its value
`2 (log m! - m log m + m)` at `t = 0`. -/
private lemma riemann_sum_sub_le (K m : ℕ) (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2)) -
        (K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) ≤
      2 * (Real.log (m.factorial : ℝ) - m * Real.log m + m) := by
  have hsteps : (∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2)) -
        (K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) ≤
      2 * (∑ j ∈ Finset.range m, Real.log (((j : ℝ) + 1) / K)) -
        2 * ((K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log u) := by
    rw [integral_eq_sum_steps K m _ (intervalIntegrable_log_add_sq ht),
      integral_eq_sum_steps K m _ (fun _ _ => intervalIntegral.intervalIntegrable_log'),
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => step_sub_integral_le K j hK ht
  rw [mul_integral_log K m hK, sum_log_succ_div K m hK] at hsteps
  linarith

/-- Stirling's upper bound `log m! ≤ m log m - m + (log m)/2 + 1` for `m ≥ 1`, from the
monotonicity of Mathlib's Stirling sequence. -/
private lemma log_factorial_le {m : ℕ} (hm : 0 < m) :
    Real.log (m.factorial : ℝ) ≤ m * Real.log m - m + Real.log m / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.stirlingSeq_one] at h1
  have h2 := Real.log_le_log (Stirling.stirlingSeq'_pos k) h1
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num), Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at h2
  linarith

/-- (103) with `log m + 2` in place of `2 log K + 2`, for any positive integers `m` and `K`. -/
private lemma riemann_sum_sub_le_log (K m : ℕ) (hK : 0 < K) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / K) ^ 2)) -
        (K : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / K), Real.log (t + u ^ 2) ≤ Real.log m + 2 := by
  have h1 := riemann_sum_sub_le K m hK ht
  have h2 := log_factorial_le hm
  linarith

/-- Equation (103): for `1 ≤ m ≤ K` and `t ≥ 0`,
`0 ≤ ∑_{j=1}^m log(t + (j/K)²) - K ∫_0^{m/K} log(t + u²) du ≤ 2 log K + 2`. -/
theorem riemann_sum_log_bound (n m : ℕ) (hm : 1 ≤ m) (hmK : m ≤ K n) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / (K n : ℝ)) ^ 2)) -
        (K n : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / (K n : ℝ)), Real.log (t + u ^ 2) ∧
      (∑ j ∈ Finset.range m, Real.log (t + (((j : ℝ) + 1) / (K n : ℝ)) ^ 2)) -
        (K n : ℝ) * ∫ u in (0 : ℝ)..((m : ℝ) / (K n : ℝ)), Real.log (t + u ^ 2) ≤
      2 * Real.log (K n : ℝ) + 2 := by
  have hK : 0 < K n := by omega
  refine ⟨sub_nonneg.mpr (le_riemann_sum (K n) m hK ht), ?_⟩
  have h1 := riemann_sum_sub_le_log (K n) m hK (by omega) ht
  have h3 : Real.log m ≤ Real.log (K n) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hmK)
  have h4 : 0 ≤ Real.log m := Real.log_nonneg (Nat.one_le_cast.mpr hm)
  linarith

/-! ### Andreief's identity at `ζ(7)` (101) -/

/-- The weight `D_N(y²)⁸/D_K(y²) w₇(y)` of the moment matrix of `G_K(ζ(7))`. -/
private noncomputable def rhoW (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (Dpoly (N n)) ^ 8 / aeval (y ^ 2) (Dpoly (K n)) * w7 y

private lemma aeval_Dpoly_eq_prod (m : ℕ) (x : ℝ) :
    aeval x (Dpoly m) = ∏ j ∈ Finset.range m, (x + ((j : ℝ) + 1) ^ 2) := by
  rw [Dpoly, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

private lemma rhoW_pos (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 < rhoW n y := by
  have h1 : 0 < aeval (y ^ 2) (Dpoly (N n)) := by
    rw [aeval_Dpoly_eq_prod]
    exact Finset.prod_pos fun j _ => by positivity
  have h2 : 0 < aeval (y ^ 2) (Dpoly (K n)) := by
    rw [aeval_Dpoly_eq_prod]
    exact Finset.prod_pos fun j _ => by positivity
  rw [rhoW]
  exact mul_pos (div_pos (pow_pos h1 8) h2) (w7_pos hy)

/-- The entry `(i, j)` of `G_K(ζ(7))` as an integral against `w₇` (Proposition 2.4). -/
private lemma aeval_Gentry_zeta_eq (n i j : ℕ) :
    aeval (riemannZeta 7).re (Gentry n i j) = ∫ y in Ioi (0 : ℝ),
      aeval (y ^ 2) (Dpoly (N n)) ^ 8 * (y ^ 2) ^ (i + j) / aeval (y ^ 2) (Dpoly (K n)) *
        w7 y := by
  rw [Gentry, aeval_muFunctional_zeta_eq_integral _ _ (poleCoeffs_apply_zero n i j)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [aeval_polyPart_add_poleCoeffs n i j (sq_nonneg y)]

private lemma integrableOn_Gentry_integrand (n i j : ℕ) :
    IntegrableOn (fun y : ℝ => aeval (y ^ 2) (Dpoly (N n)) ^ 8 * (y ^ 2) ^ (i + j) /
      aeval (y ^ 2) (Dpoly (K n)) * w7 y) (Ioi 0) :=
  (integrableOn_muIntegrand (polyPart n i j) (poleCoeffs n i j)
    (poleCoeffs_apply_zero n i j)).congr_fun (fun y _ => by
      beta_reduce
      rw [aeval_polyPart_add_poleCoeffs n i j (sq_nonneg y)]) measurableSet_Ioi

private lemma integrableOn_rhoW_moment (n i j : ℕ) :
    IntegrableOn (fun y : ℝ => (y ^ 2) ^ i * rhoW n y * (y ^ 2) ^ j) (Ioi 0) :=
  (integrableOn_Gentry_integrand n i j).congr_fun (fun y _ => by
    beta_reduce
    rw [rhoW, pow_add]
    ring) measurableSet_Ioi

/-- `Δ_K(ζ(7))` is the determinant of the moment matrix `∫ (y²)^i ρ(y) (y²)^j dy`. -/
private lemma aeval_DeltaK_eq_det (n : ℕ) :
    aeval (riemannZeta 7).re (DeltaK n) = (Matrix.of fun i j : Fin (hDim n) =>
      ∫ y in Ioi (0 : ℝ), (y ^ 2) ^ (i : ℕ) * rhoW n y * (y ^ 2) ^ (j : ℕ)).det := by
  rw [DeltaK, AlgHom.map_det, AlgHom.mapMatrix_apply]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Gmat, Matrix.of_apply]
  rw [aeval_Gentry_zeta_eq]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [rhoW, pow_add]
  ring

/-- The product of the two determinants in Andreief's identity for the weighted moment matrix
`∫ g^i w g^j`: the squared Vandermonde determinant of the nodes `g(x_j)` times the weights. -/
private lemma det_mul_det_eq {h : ℕ} (g w : ℝ → ℝ) (x : Fin h → ℝ) :
    (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ) * w (x j)).det *
        (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ)).det =
      (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (g (x i) - g (x j)) ^ 2) * ∏ i : Fin h, w (x i) := by
  have hV : (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ)).det =
      ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (g (x j) - g (x i)) := by
    have hT : (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ)) =
        (Matrix.vandermonde fun j => g (x j)).transpose := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [hT, Matrix.det_transpose, Matrix.det_vandermonde]
  have hW : (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ) * w (x j)).det =
      (∏ j : Fin h, w (x j)) * (Matrix.of fun i j : Fin h => g (x j) ^ (i : ℕ)).det := by
    rw [← Matrix.det_mul_row]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    ring
  have hsq : ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (g (x i) - g (x j)) ^ 2 =
      (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (g (x j) - g (x i))) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hW, hV, hsq]
  ring

/-- The integrand of Andreief's identity is integrable on the product space when every
mixed moment is integrable (expansion of both determinants). -/
private lemma integrable_det_mul_det {h : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (φ ψ : Fin h → ℝ → ℝ) (hint : ∀ i j, Integrable (fun x => φ i x * ψ j x) μ) :
    Integrable (fun x : Fin h → ℝ => (Matrix.of fun i j => φ i (x j)).det *
      (Matrix.of fun i j => ψ i (x j)).det) (Measure.pi fun _ => μ) := by
  have hpoint : ∀ x : Fin h → ℝ, (Matrix.of fun i j => φ i (x j)).det *
      (Matrix.of fun i j => ψ i (x j)).det =
      ∑ τ : Equiv.Perm (Fin h), ∑ ρ : Equiv.Perm (Fin h),
        ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ) * ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)) := by
    intro x
    rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  have hterm : ∀ τ ρ : Equiv.Perm (Fin h), Integrable (fun x : Fin h → ℝ =>
      ((τ.sign : ℤ) : ℝ) * ((ρ.sign : ℤ) : ℝ) * ∏ i, (φ (τ i) (x i) * ψ (ρ i) (x i)))
      (Measure.pi fun _ => μ) := fun τ ρ =>
    (MeasureTheory.Integrable.fintype_prod (f := fun i x => φ (τ i) x * ψ (ρ i) x)
      (fun i => hint (τ i) (ρ i))).const_mul _
  refine (integrable_finsetSum Finset.univ fun τ _ =>
    integrable_finsetSum Finset.univ fun ρ _ => hterm τ ρ).congr ?_
  filter_upwards with x
  exact (hpoint x).symm

/-- Equation (101): Andreief's identity applied to the moment matrix (7),
`Δ_K(ζ(7)) = (1/h!) ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏_i D_N(y_i²)⁸/D_K(y_i²) w₇(y_i) dy`. -/
theorem aeval_DeltaK_zeta_eq_andreief (n : ℕ) :
    aeval (riemannZeta 7).re (DeltaK n) = ((hDim n).factorial : ℝ)⁻¹ *
      ∫ y : Fin (hDim n) → ℝ, (∏ i, ∏ j ∈ Finset.Ioi i, (y i ^ 2 - y j ^ 2) ^ 2) *
        ∏ i, (aeval (y i ^ 2) (Dpoly (N n)) ^ 8 / aeval (y i ^ 2) (Dpoly (K n)) * w7 (y i))
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  rw [aeval_DeltaK_eq_det]
  refine (Andreief.andreief_integral (volume.restrict (Ioi (0 : ℝ)))
    (fun i y => (y ^ 2) ^ (i : ℕ) * rhoW n y) (fun j y => (y ^ 2) ^ (j : ℕ))
    (fun i j => integrableOn_rhoW_moment n i j)).trans ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with y
  exact det_mul_det_eq (fun x => x ^ 2) (rhoW n) y

/-- The integrand of (101) is integrable on `(0, ∞)^h`, so (101) is an identity between finite
values (absolute convergence). -/
theorem integrable_andreief_integrand (n : ℕ) :
    Integrable (fun y : Fin (hDim n) → ℝ => (∏ i, ∏ j ∈ Finset.Ioi i, (y i ^ 2 - y j ^ 2) ^ 2) *
        ∏ i, (aeval (y i ^ 2) (Dpoly (N n)) ^ 8 / aeval (y i ^ 2) (Dpoly (K n)) * w7 (y i)))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  refine (integrable_det_mul_det (volume.restrict (Ioi (0 : ℝ)))
    (fun i y => (y ^ 2) ^ (i : ℕ) * rhoW n y) (fun j y => (y ^ 2) ^ (j : ℕ))
    (fun i j => integrableOn_rhoW_moment n i j)).congr ?_
  filter_upwards with y
  exact det_mul_det_eq (fun x => x ^ 2) (rhoW n) y

end ZetaSeven
