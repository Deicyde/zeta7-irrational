import ZetaSeven.ConfigurationBound
import ZetaSeven.AndreiefScaling
import ZetaSeven.Stirling

/-!
# The real bound (paper Section 6.6, Proposition 6.3, equations (105)-(108))

Prince Anand, "Zeta 7 is Irrational", Section 6.6. Throughout `K = 40n`, `N = 3n`,
`h = 37n` (`hDim n`), `λ = 37/40`, `α = 3/40`, `M_0 = -109/20`, `I(ρ) = Ilog compMeasure`,
and `F_K(ζ(7)) = S_K Δ_K(ζ(7))` is `aeval (riemannZeta 7).re (FK n)`.

* `integral_residual_density_le`: the residual integral
  `∫_0^∞ t^{-1/2} (1 + √t)⁷ e^{-√t} dt` left after (104) is at most `2^21`
  (its exact value is `27400`).
* `scaled_integral_le`: (100), applied pointwise and integrated, bounds the integral of (104) by
  `e^{(λM_0 - I(ρ))K² + (120 + √2)h + 2h log K} (∫_0^∞ t^{-1/2} (1 + √t)⁷ e^{-√t} dt)^h`.
* (105) `log_aeval_DeltaK_zeta_le`: for `n ≥ 1`,
  `log Δ_K(ζ(7)) ≤ 2h(h + 8N - K) log K + (λM_0 - I(ρ))K² + 18h log K + 220h`.
* `SK_cast_eq`: the rational `S_K` of (8) is the real `ZetaSeven.Stirling.SK K h N`.
* (107) `log_SK_le`: for `n ≥ 1`,
  `log S_K ≤ (2λ - 16αλ - 2λ²)K² log K + C* K² + 6h log K + 6h`.
* Proposition 6.3, (108) `real_bound`: for `n ≥ 1`, `0 < F_K(ζ(7))` and
  `log F_K(ζ(7)) ≤ U K² + 24K log K + 220K` with `U = 44/25`.

Proof notes. If some `t_i < 0` then `√t_i = 0`, so the integrand of (104) and the residual
density both vanish; otherwise (100) (`configuration_bound`) applies, so the pointwise bound
holds everywhere. The residual integral is bounded through `(1 + s)⁷ ≤ 2⁷ (1 + s⁷)` and
`∫_0^∞ t^q e^{-t^{1/2}} dt = 2 Γ(2q + 2)` at `q = -1/2` and `q = 3`, which gives the linear
constant `12 log 2 + 12 + 120 + √2 + 21 log 2 < 220` in (105). The `K² log K` terms of (105)
and (107) cancel exactly: `2h(h + 8N - K) = 1554n²` and `(2λ - 16αλ - 2λ²)K² = -1554n²`.
The quadratic coefficient `λM_0 - I(ρ) + C*` is at most `44/25` by `energy_norm_bound`, and the
remaining terms satisfy `24h log K + 226h ≤ 24K log K + 220K` for every `K ≥ 1`.
-/

namespace ZetaSeven

open MeasureTheory Set Polynomial

/-! ### The residual integral -/

/-- `(1 + s)^M ≤ 2^M (1 + s^M)` for `s ≥ 0`. -/
private lemma one_add_pow_le_two_pow {s : ℝ} (hs : 0 ≤ s) (M : ℕ) :
    (1 + s) ^ M ≤ 2 ^ M * (1 + s ^ M) := by
  have h1 : 1 + s ≤ 2 * max 1 s := by
    have := le_max_left 1 s
    have := le_max_right 1 s
    linarith
  have h2 : (max 1 s) ^ M ≤ 1 + s ^ M := by
    rcases le_total 1 s with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg hs M]
  calc (1 + s) ^ M ≤ (2 * max 1 s) ^ M := pow_le_pow_left₀ (by positivity) h1 M
    _ = 2 ^ M * (max 1 s) ^ M := mul_pow 2 (max 1 s) M
    _ ≤ 2 ^ M * (1 + s ^ M) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `Γ(8) = 7! = 5040`. -/
private lemma Gamma_eight : Real.Gamma 8 = 5040 := by
  rw [show (8 : ℝ) = (7 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
    show Nat.factorial 7 = 5040 by rfl, Nat.cast_ofNat]

/-- The residual integral after (104): `∫_0^∞ t^{-1/2} (1 + √t)⁷ e^{-√t} dt ≤ 2^21`.
The proof bounds it by `2⁷ (2Γ(1) + 2Γ(8)) = 1290496`; its exact value is `27400`. -/
theorem integral_residual_density_le :
    ∫ t in Ioi (0 : ℝ), (Real.sqrt t)⁻¹ * (1 + Real.sqrt t) ^ 7 * Real.exp (-Real.sqrt t)
      ≤ 2 ^ 21 := by
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hi1 := integrableOn_rpow_mul_exp_neg_rpow (s := -(1 / 2)) (p := 1 / 2) (by norm_num) hp
  have hi2 := integrableOn_rpow_mul_exp_neg_rpow (s := 3) (p := 1 / 2) (by norm_num) hp
  have hJ1 : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Real.exp (-t ^ (1 / 2 : ℝ)) = 2 := by
    rw [integral_rpow_mul_exp_neg_rpow (q := -(1 / 2)) hp (by norm_num)]
    norm_num [Real.Gamma_one]
  have hJ2 : ∫ t in Ioi (0 : ℝ), t ^ (3 : ℝ) * Real.exp (-t ^ (1 / 2 : ℝ)) = 10080 := by
    rw [integral_rpow_mul_exp_neg_rpow (q := 3) hp (by norm_num)]
    norm_num [Gamma_eight]
  have hmono : ∫ t in Ioi (0 : ℝ),
      (Real.sqrt t)⁻¹ * (1 + Real.sqrt t) ^ 7 * Real.exp (-Real.sqrt t) ≤
      ∫ t in Ioi (0 : ℝ), 2 ^ 7 * (t ^ (-(1 / 2) : ℝ) * Real.exp (-t ^ (1 / 2 : ℝ)) +
        t ^ (3 : ℝ) * Real.exp (-t ^ (1 / 2 : ℝ))) := by
    refine setIntegral_mono_on integrableOn_residual_density
      (Integrable.const_mul (hi1.add hi2) _) measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have e1 : t ^ (3 : ℝ) = Real.sqrt t ^ 7 * (Real.sqrt t)⁻¹ := by
      rw [show (3 : ℝ) = 1 / 2 * ((7 : ℕ) : ℝ) + -(1 / 2) by norm_num, Real.rpow_add ht',
        Real.rpow_mul_natCast ht'.le, Real.rpow_neg ht'.le, ← Real.sqrt_eq_rpow]
    have e2 : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg ht'.le, ← Real.sqrt_eq_rpow]
    have e3 : t ^ (1 / 2 : ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
    rw [e1, e2, e3]
    have hE : 0 ≤ (Real.sqrt t)⁻¹ * Real.exp (-Real.sqrt t) := by positivity
    calc (Real.sqrt t)⁻¹ * (1 + Real.sqrt t) ^ 7 * Real.exp (-Real.sqrt t)
        = (Real.sqrt t)⁻¹ * Real.exp (-Real.sqrt t) * (1 + Real.sqrt t) ^ 7 := by ring
      _ ≤ (Real.sqrt t)⁻¹ * Real.exp (-Real.sqrt t) * (2 ^ 7 * (1 + Real.sqrt t ^ 7)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le_two_pow (Real.sqrt_nonneg t) 7) hE
      _ = 2 ^ 7 * ((Real.sqrt t)⁻¹ * Real.exp (-Real.sqrt t) +
          Real.sqrt t ^ 7 * (Real.sqrt t)⁻¹ * Real.exp (-Real.sqrt t)) := by ring
  rw [integral_const_mul, integral_add hi1 hi2, hJ1, hJ2] at hmono
  exact hmono.trans (by norm_num)

/-! ### Applying (100) inside the integral of (104) -/

/-- The integrand of (104) is nonnegative. -/
private lemma scaled_integrand_nonneg (n : ℕ) (t : Fin (hDim n) → ℝ) :
    0 ≤ (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
        ∏ i, (Real.exp (-(K n : ℝ) * Vfield (t i)) * (Real.sqrt (t i))⁻¹ *
          (1 + Real.sqrt (t i)) ^ 7) :=
  mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => sq_nonneg _)
    (Finset.prod_nonneg fun i _ => by positivity)

/-- (100) applied pointwise to the integrand of (104): for `n ≥ 1` and every `t`,
the integrand is at most
`e^{(λM_0 - I(ρ))K² + (120 + √2)h + 2h log K} ∏_i t_i^{-1/2} (1 + √t_i)⁷ e^{-√t_i}`.
If some `t_i < 0` then `√t_i = 0` and the left side vanishes. -/
private lemma scaled_integrand_le (n : ℕ) (hn : 1 ≤ n) (t : Fin (hDim n) → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
        ∏ i, (Real.exp (-(K n : ℝ) * Vfield (t i)) * (Real.sqrt (t i))⁻¹ *
          (1 + Real.sqrt (t i)) ^ 7) ≤
      Real.exp ((37 / 40 * (-109 / 20) - Ilog compMeasure) * (K n : ℝ) ^ 2 +
          (120 + Real.sqrt 2) * (hDim n : ℝ) + 2 * (hDim n : ℝ) * Real.log (K n : ℝ)) *
        ∏ i, ((Real.sqrt (t i))⁻¹ * (1 + Real.sqrt (t i)) ^ 7 *
          Real.exp (-Real.sqrt (t i))) := by
  by_cases ht : ∀ i, 0 ≤ t i
  · have hK1 : (1 : ℝ) ≤ (K n : ℝ) := by
      have : 1 ≤ K n := by unfold K; omega
      exact_mod_cast this
    have hh : (hDim n : ℝ) = 37 / 40 * (K n : ℝ) := by
      unfold hDim K
      push_cast
      ring
    have hc := configuration_bound hK1 hh t ht
    have hP : 0 ≤ (∏ i, (Real.sqrt (t i))⁻¹) * ∏ i, (1 + Real.sqrt (t i)) ^ 7 :=
      mul_nonneg (Finset.prod_nonneg fun i _ => inv_nonneg.2 (Real.sqrt_nonneg _))
        (Finset.prod_nonneg fun i _ => by positivity)
    have key := mul_le_mul_of_nonneg_right hc hP
    simp only [Finset.prod_mul_distrib]
    linarith [key]
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp ht
    have hs : Real.sqrt (t i) = 0 := Real.sqrt_eq_zero'.2 (not_le.mp hi).le
    have h0 : ∏ i, (Real.exp (-(K n : ℝ) * Vfield (t i)) * (Real.sqrt (t i))⁻¹ *
        (1 + Real.sqrt (t i)) ^ 7) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hs])
    rw [h0, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ => by positivity)

/-- (100) integrated against the residual density: for `n ≥ 1` the integral in (104) is at most
`e^{(λM_0 - I(ρ))K² + (120 + √2)h + 2h log K} (∫_0^∞ t^{-1/2} (1 + √t)⁷ e^{-√t} dt)^h`. -/
theorem scaled_integral_le (n : ℕ) (hn : 1 ≤ n) :
    ∫ t : Fin (hDim n) → ℝ, (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
        ∏ i, (Real.exp (-(K n : ℝ) * Vfield (t i)) * (Real.sqrt (t i))⁻¹ *
          (1 + Real.sqrt (t i)) ^ 7)
        ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) ≤
      Real.exp ((37 / 40 * (-109 / 20) - Ilog compMeasure) * (K n : ℝ) ^ 2 +
          (120 + Real.sqrt 2) * (hDim n : ℝ) + 2 * (hDim n : ℝ) * Real.log (K n : ℝ)) *
        (∫ t in Ioi (0 : ℝ), (Real.sqrt t)⁻¹ * (1 + Real.sqrt t) ^ 7 *
          Real.exp (-Real.sqrt t)) ^ hDim n := by
  have hint : Integrable (fun t : Fin (hDim n) → ℝ =>
      Real.exp ((37 / 40 * (-109 / 20) - Ilog compMeasure) * (K n : ℝ) ^ 2 +
          (120 + Real.sqrt 2) * (hDim n : ℝ) + 2 * (hDim n : ℝ) * Real.log (K n : ℝ)) *
        ∏ i, ((Real.sqrt (t i))⁻¹ * (1 + Real.sqrt (t i)) ^ 7 *
          Real.exp (-Real.sqrt (t i))))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) :=
    (Integrable.fintype_prod (μ := fun _ => volume.restrict (Ioi (0 : ℝ)))
      (f := fun _ s => (Real.sqrt s)⁻¹ * (1 + Real.sqrt s) ^ 7 * Real.exp (-Real.sqrt s))
      fun _ => integrableOn_residual_density).const_mul _
  refine (integral_mono_of_nonneg ?_ hint ?_).trans_eq ?_
  · filter_upwards with t
    exact scaled_integrand_nonneg n t
  · filter_upwards with t
    exact scaled_integrand_le n hn t
  · rw [integral_const_mul, integral_fintype_prod_eq_pow
      (fun s : ℝ => (Real.sqrt s)⁻¹ * (1 + Real.sqrt s) ^ 7 * Real.exp (-Real.sqrt s)),
      Fintype.card_fin]

/-! ### Equation (105) -/

/-- (104) combined with `scaled_integral_le` and `integral_residual_density_le`, before
taking logarithms. -/
private lemma aeval_DeltaK_zeta_le_exp (n : ℕ) (hn : 1 ≤ n) :
    aeval (riemannZeta 7).re (DeltaK n) ≤
      (K n : ℝ) ^ (2 * hDim n * (hDim n + 8 * N n - K n) + 16 * hDim n) *
        (4096 * Real.exp 12) ^ hDim n *
        (Real.exp ((37 / 40 * (-109 / 20) - Ilog compMeasure) * (K n : ℝ) ^ 2 +
            (120 + Real.sqrt 2) * (hDim n : ℝ) + 2 * (hDim n : ℝ) * Real.log (K n : ℝ)) *
          ((2 : ℝ) ^ 21) ^ hDim n) := by
  have hI0 : 0 ≤ ∫ t in Ioi (0 : ℝ), (Real.sqrt t)⁻¹ * (1 + Real.sqrt t) ^ 7 *
      Real.exp (-Real.sqrt t) :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => by positivity
  have hIpow := pow_le_pow_left₀ hI0 integral_residual_density_le (hDim n)
  have hfact : (1 : ℝ) ≤ ((hDim n).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc _ ≤ _ := aeval_DeltaK_zeta_le_scaled n
    _ ≤ _ := mul_le_mul_of_nonneg_left (scaled_integral_le n hn) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hIpow (Real.exp_pos _).le) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_self (by positivity) hfact) (by positivity)

/-- Equation (105): taking logarithms of (104) after (100), for `n ≥ 1`,
`log Δ_K(ζ(7)) ≤ 2h(h + 8N - K) log K + (λM_0 - I(ρ))K² + 18h log K + 220h`.
The subtraction `h + 8N - K` is real; it equals `21n ≥ 0`. -/
theorem log_aeval_DeltaK_zeta_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (aeval (riemannZeta 7).re (DeltaK n)) ≤
      2 * (hDim n : ℝ) * ((hDim n : ℝ) + 8 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ) +
        (37 / 40 * (-109 / 20) - Ilog compMeasure) * (K n : ℝ) ^ 2 +
        18 * (hDim n : ℝ) * Real.log (K n : ℝ) + 220 * (hDim n : ℝ) := by
  have hKpos : (0 : ℝ) < (K n : ℝ) := by
    have : 0 < K n := by unfold K; omega
    exact_mod_cast this
  have hlog := Real.log_le_log (aeval_DeltaK_zeta_pos n) (aeval_DeltaK_zeta_le_exp n hn)
  have h1 : (K n : ℝ) ^ (2 * hDim n * (hDim n + 8 * N n - K n) + 16 * hDim n) ≠ 0 :=
    pow_ne_zero _ hKpos.ne'
  have h2 : ((4096 : ℝ) * Real.exp 12) ^ hDim n ≠ 0 := pow_ne_zero _ (by positivity)
  have h4 : ((2 : ℝ) ^ 21) ^ hDim n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_mul (mul_ne_zero h1 h2) (mul_ne_zero (Real.exp_pos _).ne' h4),
    Real.log_mul h1 h2, Real.log_mul (Real.exp_pos _).ne' h4, Real.log_exp] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hsub : hDim n + 8 * N n - K n = 21 * n := by
    unfold hDim N K
    omega
  have h4096 : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow, Nat.cast_ofNat]
  have he : ((2 * hDim n * (21 * n) + 16 * hDim n : ℕ) : ℝ) =
      2 * (hDim n : ℝ) * (21 * (n : ℝ)) + 16 * (hDim n : ℝ) := by
    push_cast
    ring
  rw [Real.log_mul (by norm_num : (4096 : ℝ) ≠ 0) (Real.exp_pos 12).ne', Real.log_exp, h4096,
    hsub, he] at hlog
  have hsubR : (hDim n : ℝ) + 8 * (N n : ℝ) - (K n : ℝ) = 21 * (n : ℝ) := by
    unfold hDim N K
    push_cast
    ring
  rw [hsubR]
  have hh0 : (0 : ℝ) ≤ (hDim n : ℝ) := Nat.cast_nonneg _
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hA : (hDim n : ℝ) * Real.log 2 ≤ (hDim n : ℝ) * 1 := mul_le_mul_of_nonneg_left hl2 hh0
  have hB : (hDim n : ℝ) * Real.sqrt 2 ≤ (hDim n : ℝ) * 2 := mul_le_mul_of_nonneg_left hs2 hh0
  linarith

/-! ### Equation (107) for the factor `S_K` of (8) -/

/-- The rational `S_K` of (8) (`ZetaSeven.SK`) is the real `ZetaSeven.Stirling.SK K h N`
of the Stirling estimate, with the product over `1 ≤ i ≤ h - 1` reindexed from `0`. -/
theorem SK_cast_eq (n : ℕ) :
    ((SK n : ℚ) : ℝ) = ZetaSeven.Stirling.SK (K n) (hDim n) (N n) := by
  have hprod : ∏ i ∈ Finset.Icc 1 (hDim n - 1), (Nat.factorial (2 * i) : ℚ) ^ 2 =
      ∏ i ∈ Finset.range (hDim n - 1), (Nat.factorial (2 * (i + 1)) : ℚ) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.add_comm 1 i]
  rw [SK, hprod, ZetaSeven.Stirling.SK]
  push_cast
  ring

/-- Equation (107) for the factor `S_K` of (8): for `n ≥ 1`,
`log S_K ≤ (2λ - 16αλ - 2λ²)K² log K + C* K² + 6h log K + 6h`, with `C* = cStar`. -/
theorem log_SK_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((SK n : ℚ) : ℝ) ≤
      (2 * (37 / 40 : ℝ) - 16 * (3 / 40) * (37 / 40) - 2 * (37 / 40) ^ 2) * (K n : ℝ) ^ 2 *
          Real.log (K n : ℝ) + cStar * (K n : ℝ) ^ 2 +
        6 * (hDim n : ℝ) * Real.log (K n : ℝ) + 6 * (hDim n : ℝ) := by
  have hK : 1 ≤ K n := by unfold K; omega
  have hN1 : 1 ≤ N n := by unfold N; omega
  have hh : (hDim n : ℝ) = 37 / 40 * (K n : ℝ) := by
    unfold hDim K
    push_cast
    ring
  have hN : (N n : ℝ) = 3 / 40 * (K n : ℝ) := by
    unfold N K
    push_cast
    ring
  have h107 := ZetaSeven.Stirling.stirling_107 hK hh hN hN1
  have hc : cStar = -2 * (37 / 40 : ℝ) + 16 * (3 / 40 : ℝ) * (37 / 40 : ℝ) *
      (1 - Real.log (3 / 40 : ℝ)) + 3 * (37 / 40 : ℝ) ^ 2 -
      2 * (37 / 40 : ℝ) ^ 2 * Real.log (2 * (37 / 40 : ℝ)) := by
    rw [cStar, eAlpha]
  rw [SK_cast_eq, hc]
  linarith

/-! ### Proposition 6.3 -/

/-- Proposition 6.3 (Real bound), equation (108): for every `K = 40n` with `n ≥ 1`,
`0 < F_K(ζ(7))` and `log F_K(ζ(7)) ≤ U K² + 24K log K + 220K` with `U = 44/25`. -/
theorem real_bound (n : ℕ) (hn : 1 ≤ n) :
    0 < aeval (riemannZeta 7).re (FK n) ∧
      Real.log (aeval (riemannZeta 7).re (FK n)) ≤
        44 / 25 * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ) + 220 * (K n : ℝ) := by
  refine ⟨aeval_FK_zeta_pos n, ?_⟩
  have hF : aeval (riemannZeta 7).re (FK n) =
      ((SK n : ℚ) : ℝ) * aeval (riemannZeta 7).re (DeltaK n) := by
    rw [FK, map_mul, aeval_C, eq_ratCast]
  rw [hF, Real.log_mul (Rat.cast_pos.mpr (SK_pos n)).ne' (aeval_DeltaK_zeta_pos n).ne']
  have hS := log_SK_le n hn
  have hD := log_aeval_DeltaK_zeta_le n hn
  have hKr : (K n : ℝ) = 40 * (n : ℝ) := by
    unfold K
    push_cast
    ring
  have hhr : (hDim n : ℝ) = 37 * (n : ℝ) := by
    unfold hDim
    push_cast
    ring
  have hNr : (N n : ℝ) = 3 * (n : ℝ) := by
    unfold N
    push_cast
    ring
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : 0 ≤ Real.log (K n : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hKr]
    linarith
  have hnL : 0 ≤ (n : ℝ) * Real.log (K n : ℝ) := mul_nonneg hn0 hL
  have hU := mul_le_mul_of_nonneg_right energy_norm_bound (sq_nonneg (K n : ℝ))
  rw [hKr, hhr, hNr] at hD
  rw [hKr, hhr] at hS
  rw [hKr] at hU hnL ⊢
  linarith

end ZetaSeven
