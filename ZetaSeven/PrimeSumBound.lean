import ZetaSeven.NormalizationIntegrality
import ZetaSeven.InnerLimiting
import ZetaSeven.OuterLimiting
import ZetaSeven.TailIntegral
import ZetaSeven.PrimeNumberTheorem

/-!
# Prime-sum bound (paper Section 5.5, Proposition 5.4, equations (87)-(90))

Prince Anand, "Zeta 7 is Irrational", Section 5.5. With `K = 40n`, `h = 37n`, `λ = 37/40` and
the normalization factor `m_{K,M}` of (61) (`ZetaSeven.mKM`), this module defines

* `primeSumA0`: the rational `A_0` of (87);
* `primeSumB0`: `B_0 = A_0 + I_out + ∫_3^20 R(x)/x³ dx` of (88), with the project's outer
  integral `I_out = outerIntegral` (source-map errata 8-9), not the printed (122);
* `primeSumA`: `A_M = B_0 + 9λ/M - 11549/(720M²) + 44/M³` of (89);

and proves **Proposition 5.4** (`prime_sum_bound`): for `M ∈ 40ℤ_{>0}` and every `ε > 0`,
`K⁻² log m_{K,M} ≤ A_M + ε` for all large `n`, i.e. `lim sup K⁻² log m_{K,M} ≤ A_M`.

## Proof

`log m_{K,M} = ∑_{p ≤ 2h} (-L_p) log p` (`log_mKM`) splits into four prime ranges:

* small primes `p ≤ √(5K)`: each contributes at most `8h log p + 8h log(5K) + h log 720`,
  and the excess over `8h log p` totals `O(K^{3/2} log K) = o(K²)` (`crude_term_le`,
  `crude_sum_le`, `tendsto_crude_bound`);
* the crude range `√(5K) < p ≤ K/M`: `-L_p ≤ 8h`, so the whole range `p ≤ K/M` contributes at
  most `8h θ(K/M)` plus the small-prime excess, that is `8λK²/M + o(K²)` by the prime number
  theorem (`crude_sum_le`, `tendsto_crude_bound`);
* the inner range `K/M < p ≤ K/3`: `-L_p = p R(K/p) + O_M(1)` by (70) (`LpKM_inner_approx`),
  and the prime Riemann sum with weight `y R(1/y)` on `[1/M, 1/3]` gives
  `∫_3^M R(x)/x³ dx` (`tendsto_inner_sum`, `integral_innerWeight`);
* the outer range `K/3 < p ≤ 2h`: `-γ^out_p = K g(p/K) + O(1)` (`gammaOut_approx`) and
  `-v_p(S_K) = K s(p/K) + O(1)` (`padicValRat_SK_add_outerScalar`), so
  `-L_p = K T(p/K) + O(1)` with `T` the integrand of (73) (`LpKM_outer_approx`), and the prime
  Riemann sum gives `I_out` (`tendsto_outer_sum`).

The weights are bounded, and continuous off finitely many points: `R` is continuous wherever
`cx ∉ ℤ` for `c ∈ {2, 2α, 2H, 2λ}` (`innerR_continuousAt`), and `T` is continuous on
`(1/3, ∞)` except at `y = 1/2` and `y = 1`, where `⌊1/y⌋` jumps
(`outerIntegrand_continuousAt`). Finally `∫_3^M = ∫_3^20 + ∫_20^∞ - ∫_M^∞`, the tail bound (86)
for `40 ∣ M`, and `∫_20^∞ R(x)/x³ dx ≤ -2069/36000 ≤ A_0` from (85) at `T = 20`
(`integral_Ioi_twenty_le`; source-map erratum 14) give (90) (`integral_three_le`).
-/

namespace ZetaSeven

open Filter Topology MeasureTheory

/-! ## The constants (87)-(89) -/

/-- (87): `A_0 = 9928298118277006344769/7535670527041937280000`. -/
def primeSumA0 : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- (88): `B_0 = A_0 + I_out + ∫_3^20 R(x)/x³ dx`, with the outer integral
`I_out = outerIntegral` of (73) (its value is `453803/288000`, not the printed (122);
source-map errata 8-9). -/
noncomputable def primeSumB0 : ℝ :=
  (primeSumA0 : ℝ) + outerIntegral + ∫ x in (3 : ℝ)..20, innerR x / x ^ 3

/-- (89): `A_M = B_0 + 9λ/M - 11549/(720M²) + 44/M³`. -/
noncomputable def primeSumA (M : ℕ) : ℝ :=
  primeSumB0 + 9 * (lam : ℝ) / M - 11549 / (720 * (M : ℝ) ^ 2) + 44 / (M : ℝ) ^ 3

/-! ## `log m_{K,M}` as a prime sum and the split into ranges -/

/-- From (61): `log m_{K,M} = ∑_{p ≤ 2h} (-L_p(K,M)) log p`. -/
theorem log_mKM (n M : ℕ) :
    Real.log (mKM n M : ℝ) =
      ∑ p ∈ (Finset.Iic (2 * hDim n)).filter Nat.Prime, (-(LpKM n M p : ℝ)) * Real.log p := by
  have hcast : ((mKM n M : ℚ) : ℝ) =
      ∏ p ∈ (Finset.Iic (2 * hDim n)).filter Nat.Prime, (p : ℝ) ^ (-LpKM n M p) := by
    rw [mKM, Rat.cast_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Rat.cast_zpow, Rat.cast_natCast]
  have hne : ∀ p ∈ (Finset.Iic (2 * hDim n)).filter Nat.Prime, (p : ℝ) ^ (-LpKM n M p) ≠ 0 :=
    fun p hp => zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero)
  rw [hcast, Real.log_prod hne]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_zpow, Int.cast_neg]

/-- A sum over the primes `p ≤ c` splits at `a ≤ b ≤ c`. -/
theorem sum_Iic_prime_split (F : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ p ∈ (Finset.Iic c).filter Nat.Prime, F p =
      (∑ p ∈ Finset.Ioc 0 a with p.Prime, F p) + (∑ p ∈ Finset.Ioc a b with p.Prime, F p)
        + ∑ p ∈ Finset.Ioc b c with p.Prime, F p := by
  have h0 : (Finset.Iic c).filter Nat.Prime = (Finset.Ioc 0 c).filter (fun p => p.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.pos, h1⟩, h2⟩
    · rintro ⟨⟨_, h1⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [h0, ← PrimeSum.sum_Ioc_prime_consecutive F (Nat.zero_le b) hbc,
    ← PrimeSum.sum_Ioc_prime_consecutive F (Nat.zero_le a) hab]

/-- `⌊K/M⌋₊ = K/M`. -/
theorem floor_one_div_mul_K (M n : ℕ) : ⌊1 / (M : ℝ) * K n⌋₊ = K n / M := by
  rw [show 1 / (M : ℝ) * K n = (K n : ℝ) / M by ring, Nat.floor_div_eq_div]

/-- `⌊K/3⌋₊ = K/3`. -/
theorem floor_one_third_mul_K (n : ℕ) : ⌊1 / 3 * (K n : ℝ)⌋₊ = K n / 3 := by
  rw [show 1 / 3 * (K n : ℝ) = (K n : ℝ) / ((3 : ℕ) : ℝ) by rw [Nat.cast_ofNat]; ring,
    Nat.floor_div_eq_div]

/-- `⌊2λK⌋₊ = 2h`. -/
theorem floor_two_lam_mul_K (n : ℕ) : ⌊2 * (lam : ℝ) * K n⌋₊ = 2 * hDim n := by
  rw [show 2 * (lam : ℝ) * K n = ((2 * hDim n : ℕ) : ℝ) by
    rw [lam_real]; simp only [K, hDim]; push_cast; ring, Nat.floor_natCast]

/-- For `M ≥ 3`, `log m_{K,M}` is the sum of the crude range `p ≤ K/M`, the inner range
`K/M < p ≤ K/3` and the outer range `K/3 < p ≤ 2h` of (60). -/
theorem log_mKM_split {n M : ℕ} (hM : 3 ≤ M) :
    Real.log (mKM n M : ℝ) =
      (∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime, (-(LpKM n M p : ℝ)) * Real.log p)
      + (∑ p ∈ Finset.Ioc ⌊1 / (M : ℝ) * K n⌋₊ ⌊1 / 3 * (K n : ℝ)⌋₊ with p.Prime,
          (-(LpKM n M p : ℝ)) * Real.log p)
      + ∑ p ∈ Finset.Ioc ⌊1 / 3 * (K n : ℝ)⌋₊ ⌊2 * (lam : ℝ) * K n⌋₊ with p.Prime,
          (-(LpKM n M p : ℝ)) * Real.log p := by
  have hK0 : (0 : ℝ) ≤ K n := Nat.cast_nonneg _
  rw [log_mKM, floor_two_lam_mul_K]
  apply sum_Iic_prime_split
  · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)) hK0)
  · rw [← floor_two_lam_mul_K]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by rw [lam_real]; norm_num) hK0)

/-! ## Scaling by `K` -/

theorem K_pos {n : ℕ} (hn : 0 < n) : (0 : ℝ) < K n := by
  have : 0 < K n := by unfold K; omega
  exact_mod_cast this

theorem K_mul_div_K (p : ℕ) {n : ℕ} (hn : 0 < n) : (K n : ℝ) * ((p : ℝ) / K n) = p :=
  mul_div_cancel₀ _ (K_pos hn).ne'

theorem K_mul_alpha (n : ℕ) : (K n : ℝ) * (alpha : ℝ) = N n := by
  rw [alpha_real]; simp only [K, N]; push_cast; ring

theorem K_mul_lam (n : ℕ) : (K n : ℝ) * (lam : ℝ) = hDim n := by
  rw [lam_real]; simp only [K, hDim]; push_cast; ring

/-- `K = 40n → ∞`. -/
theorem tendsto_K_atTop : Tendsto (fun n : ℕ => (K n : ℝ)) atTop atTop := by
  have h : (fun n : ℕ => (K n : ℝ)) = fun n : ℕ => 40 * (n : ℝ) := by
    funext n
    rw [K, Nat.cast_mul, Nat.cast_ofNat]
  rw [h]
  exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop

/-! ## Weighted prime sums -/

/-- `|∑_{a < p ≤ b} f(p) log p| ≤ C θ(x)` for `b = ⌊x⌋₊` and `|f| ≤ C` on the primes. -/
theorem abs_sum_prime_le {a b : ℕ} {f : ℕ → ℝ} {C x : ℝ} (hb : b = ⌊x⌋₊) (hC : 0 ≤ C)
    (hf : ∀ p ∈ Finset.Ioc a b, p.Prime → |f p| ≤ C) :
    |∑ p ∈ Finset.Ioc a b with p.Prime, f p * Real.log p| ≤ C * Chebyshev.theta x := by
  calc |∑ p ∈ Finset.Ioc a b with p.Prime, f p * Real.log p|
      ≤ ∑ p ∈ Finset.Ioc a b with p.Prime, |f p * Real.log p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Ioc a b with p.Prime, C * Real.log p := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter] at hp
        have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
        rw [abs_mul, abs_of_nonneg hl]
        exact mul_le_mul_of_nonneg_right (hf p hp.1 hp.2) hl
    _ ≤ ∑ p ∈ Finset.Ioc 0 b with p.Prime, C * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          exact ⟨⟨hp.2.pos, hp.1.2⟩, hp.2⟩
        · intro p hp _
          rw [Finset.mem_filter] at hp
          exact mul_nonneg hC (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
    _ = C * Chebyshev.theta x := by
        rw [← Finset.mul_sum]
        unfold Chebyshev.theta
        rw [← hb]

/-- If `g → L` and `|f - g| ≤ e → 0`, then `f → L`. -/
theorem tendsto_of_abs_sub_le {f g e : ℕ → ℝ} {L : ℝ} (hg : Tendsto g atTop (𝓝 L))
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, |f n - g n| ≤ e n) :
    Tendsto f atTop (𝓝 L) := by
  have h0 : Tendsto (fun n => f n - g n) atTop (𝓝 0) :=
    squeeze_zero_norm' (h.mono fun n hn => by rwa [Real.norm_eq_abs]) he
  have h1 := hg.add h0
  rw [add_zero] at h1
  exact h1.congr fun n => by simp

/-- The prime Riemann sum with uniformly approximated weights. If `G` is bounded on `[a, b]`
with finitely many discontinuities and the weights satisfy `|w_p - K G(p/K)| ≤ C` on the primes
`aK < p ≤ bK` for all large `n`, then `K⁻² ∑_{aK < p ≤ bK} w_p log p → ∫_a^b G`. The error is
at most `C θ(bK)/K² ≤ C log 4 · b/K`. -/
theorem tendsto_weighted_prime_sum {a b : ℝ} (ha : 0 < a) (hab : a < b) {G : ℝ → ℝ}
    (hG : ∃ C, ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite)
    (w : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ᶠ n : ℕ in atTop, ∀ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊, p.Prime →
      |w n p - (K n : ℝ) * G ((p : ℝ) / K n)| ≤ C) :
    Tendsto (fun n : ℕ => (∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
      w n p * Real.log p) / (K n : ℝ) ^ 2) atTop (𝓝 (∫ y in a..b, G y)) := by
  have hb : 0 < b := ha.trans hab
  have hRS := (tendsto_primeRiemannSum ha hab hG hGc).comp tendsto_K_atTop
  have he : Tendsto (fun n : ℕ => C * Real.log 4 * b * (K n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_K_atTop).const_mul (C * Real.log 4 * b)
    rw [mul_zero] at h
    exact h
  refine tendsto_of_abs_sub_le hRS he ?_
  filter_upwards [hw, eventually_ge_atTop 1] with n hwn hn
  have hK := K_pos hn
  have hXX : (K n : ℝ) * (K n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  show |(∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime, w n p * Real.log p)
      / (K n : ℝ) ^ 2 - (K n : ℝ)⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
        G ((p : ℝ) / K n) * Real.log p| ≤ C * Real.log 4 * b * (K n : ℝ)⁻¹
  have hsplit : (∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime, w n p * Real.log p)
      / (K n : ℝ) ^ 2 - (K n : ℝ)⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
        G ((p : ℝ) / K n) * Real.log p
      = (∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
          (w n p - (K n : ℝ) * G ((p : ℝ) / K n)) * Real.log p) / (K n : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    linear_combination (G ((p : ℝ) / K n) * Real.log p * (K n : ℝ)⁻¹) * hXX
  have hsum := abs_sum_prime_le (x := b * K n) rfl hC fun p hp hpp => hwn p hp hpp
  have hθ := Chebyshev.theta_le_log4_mul_x (mul_nonneg hb.le (Nat.cast_nonneg (K n)))
  have hK2 : (0 : ℝ) < (K n : ℝ) ^ 2 := pow_pos hK 2
  rw [hsplit, abs_div, abs_of_pos hK2]
  calc |∑ p ∈ Finset.Ioc ⌊a * K n⌋₊ ⌊b * K n⌋₊ with p.Prime,
          (w n p - (K n : ℝ) * G ((p : ℝ) / K n)) * Real.log p| / (K n : ℝ) ^ 2
      ≤ C * Chebyshev.theta (b * K n) / (K n : ℝ) ^ 2 := div_le_div_of_nonneg_right hsum hK2.le
    _ ≤ C * (Real.log 4 * (b * K n)) / (K n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hC) hK2.le
    _ = C * Real.log 4 * b * (K n : ℝ)⁻¹ := by
        linear_combination (C * Real.log 4 * b * (K n : ℝ)⁻¹) * hXX

/-! ## Small primes and the crude range `p ≤ K/M` -/

/-- The crude branch of (60): for a prime `p` with `pM ≤ K`, `-L_p log p ≤ 8h log p`, plus
`8h log(5K) + h log 720` when `p² ≤ 5K`. For `p² > 5K`, `⌊log_p(5K)⌋ ≤ 1` and `p ∤ 720`, so
`-L_p ≤ 8h`. -/
theorem crude_term_le {n M p : ℕ} (hp : p.Prime) (hn : 0 < n) (hMp : M * p ≤ K n) :
    (-(LpKM n M p : ℝ)) * Real.log p ≤ 8 * (hDim n : ℝ) * Real.log p +
      if p * p ≤ 5 * K n then
        8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720
      else 0 := by
  have hKdef : K n = 40 * n := rfl
  have h5K : 5 * K n ≠ 0 := by omega
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hh : (0 : ℝ) ≤ hDim n := Nat.cast_nonneg _
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [LpKM_of_le hMp]
  split_ifs with hsq
  · have h1 : (Nat.log p (5 * K n) : ℝ) * Real.log p ≤ Real.log (5 * (K n : ℝ)) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hpR _) (by exact_mod_cast Nat.pow_log_le_self p h5K)
    have h2 : (padicValNat p 720 : ℝ) * Real.log p ≤ Real.log 720 := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hpR _)
        (by
          exact_mod_cast Nat.le_of_dvd (by norm_num) (pow_padicValNat_dvd (p := p) (n := 720)))
    have e1 := mul_le_mul_of_nonneg_left h1 hh
    have e2 := mul_le_mul_of_nonneg_left h2 hh
    have e3 := mul_nonneg hh hlogp
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith
  · have hlt' : 5 * K n < p * p := Nat.lt_of_not_le hsq
    have hlt : 5 * K n < p ^ 2 := by rw [pow_two]; exact hlt'
    have hlog : Nat.log p (5 * K n) ≤ 1 := by
      have := Nat.log_lt_of_lt_pow h5K hlt
      omega
    have hp15 : 15 ≤ p := by
      by_contra hcon
      have h14 : p * p ≤ 14 * 14 := Nat.mul_le_mul (by omega) (by omega)
      have : 5 * K n < 14 * 14 := lt_of_lt_of_le hlt' h14
      omega
    have hnd : ¬ p ∣ 720 := by
      intro hd
      have h720 : p ∣ 2 ^ 4 * (3 ^ 2 * 5) := by norm_num; exact hd
      rcases (Nat.Prime.dvd_mul hp).mp h720 with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
        · have := Nat.le_of_dvd (by norm_num) h
          omega
    have hv0 : (hDim n : ℝ) * (padicValNat p 720 : ℝ) * Real.log p = 0 := by
      rw [padicValNat.eq_zero_of_not_dvd hnd, Nat.cast_zero, mul_zero, zero_mul]
    have hL : (Nat.log p (5 * K n) : ℝ) ≤ 1 := by exact_mod_cast hlog
    have e1 := mul_le_mul_of_nonneg_right hL (mul_nonneg hh hlogp)
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith

/-- The crude range: `∑_{p ≤ K/M} (-L_p) log p ≤ 8h θ(K/M) + ⌊√(5K)⌋ (8h log(5K) + h log 720)`. -/
theorem crude_sum_le {n M : ℕ} (hn : 0 < n) (hM : 0 < M) :
    ∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime, (-(LpKM n M p : ℝ)) * Real.log p ≤
      8 * (hDim n : ℝ) * Chebyshev.theta (1 / (M : ℝ) * K n) + (Nat.sqrt (5 * K n) : ℝ) *
        (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720) := by
  have hKdef : K n = 40 * n := rfl
  have hc : 0 ≤ 8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720 := by
    have h1 : (1 : ℝ) ≤ 5 * (K n : ℝ) := by
      have : (1 : ℝ) ≤ K n := by exact_mod_cast (show 1 ≤ K n by omega)
      linarith
    have hh : (0 : ℝ) ≤ hDim n := Nat.cast_nonneg _
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) (Real.log_nonneg h1))
      (mul_nonneg hh (Real.log_nonneg (by norm_num)))
  have hsum : ∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime,
      (if p * p ≤ 5 * K n then
        8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720 else 0)
      ≤ (Nat.sqrt (5 * K n) : ℝ) *
        (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720) := by
    rw [← Finset.sum_filter]
    calc _ ≤ ∑ _p ∈ Finset.Ioc 0 (Nat.sqrt (5 * K n)),
            (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => hc)
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          exact ⟨hp.1.1.1, Nat.le_sqrt.mpr hp.2⟩
      _ = _ := by rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  calc ∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime, (-(LpKM n M p : ℝ)) * Real.log p
      ≤ ∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime, (8 * (hDim n : ℝ) * Real.log p +
          if p * p ≤ 5 * K n then
            8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720
          else 0) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter, Finset.mem_Ioc, floor_one_div_mul_K] at hp
        have hMp : p * M ≤ K n := (Nat.le_div_iff_mul_le hM).mp hp.1.2
        exact crude_term_le hp.2 hn (by rw [Nat.mul_comm]; exact hMp)
    _ = 8 * (hDim n : ℝ) * Chebyshev.theta (1 / (M : ℝ) * K n)
          + ∑ p ∈ Finset.Ioc 0 ⌊1 / (M : ℝ) * K n⌋₊ with p.Prime,
            (if p * p ≤ 5 * K n then
              8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720
            else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        unfold Chebyshev.theta
        rfl
    _ ≤ _ := add_le_add le_rfl hsum

/-- The small-prime error: for `n ≥ 1`,
`⌊√(5K)⌋ (8h log(5K) + h log 720)/K² ≤ 5λ (8 log(5K) + log 720) √(5K)/(5K)`. -/
theorem small_prime_error_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.sqrt (5 * K n) : ℝ) * (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ))
        + (hDim n : ℝ) * Real.log 720) / (K n : ℝ) ^ 2
      ≤ (lam : ℝ) * ((8 * Real.log (5 * (K n : ℝ)) + Real.log 720) * Real.sqrt (5 * (K n : ℝ))
        / (5 * (K n : ℝ))) * 5 := by
  have hK := K_pos hn
  have hKK : (K n : ℝ) * (K n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  have hh : (hDim n : ℝ) = (lam : ℝ) * K n := by rw [← K_mul_lam]; ring
  have hs : (Nat.sqrt (5 * K n) : ℝ) ≤ Real.sqrt (5 * (K n : ℝ)) := by
    have h := Real.nat_sqrt_le_real_sqrt (a := 5 * K n)
    push_cast at h
    exact h
  have h1 : (1 : ℝ) ≤ 5 * (K n : ℝ) := by
    have : (1 : ℝ) ≤ K n := by
      have : 1 ≤ K n := by unfold K; omega
      exact_mod_cast this
    linarith
  have hL : 0 ≤ 8 * Real.log (5 * (K n : ℝ)) + Real.log 720 :=
    add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg h1)) (Real.log_nonneg (by norm_num))
  have hlam : (0 : ℝ) ≤ lam := by rw [lam_real]; norm_num
  have e1 : (Nat.sqrt (5 * K n) : ℝ) * (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ))
        + (hDim n : ℝ) * Real.log 720) / (K n : ℝ) ^ 2
      = (Nat.sqrt (5 * K n) : ℝ) * ((lam : ℝ) * (8 * Real.log (5 * (K n : ℝ)) + Real.log 720)
        * (K n : ℝ)⁻¹) := by
    rw [hh]
    linear_combination ((Nat.sqrt (5 * K n) : ℝ) * (lam : ℝ)
      * (8 * Real.log (5 * (K n : ℝ)) + Real.log 720) * (K n : ℝ)⁻¹) * hKK
  have e2 : (lam : ℝ) * ((8 * Real.log (5 * (K n : ℝ)) + Real.log 720)
        * Real.sqrt (5 * (K n : ℝ)) / (5 * (K n : ℝ))) * 5
      = Real.sqrt (5 * (K n : ℝ)) * ((lam : ℝ) * (8 * Real.log (5 * (K n : ℝ)) + Real.log 720)
        * (K n : ℝ)⁻¹) := by
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg hlam hL) (inv_nonneg.mpr hK.le))

theorem small_prime_error_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (Nat.sqrt (5 * K n) : ℝ) * (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ))
        + (hDim n : ℝ) * Real.log 720) / (K n : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ 5 * (K n : ℝ) := by
    have : (1 : ℝ) ≤ K n := by
      have : 1 ≤ K n := by unfold K; omega
      exact_mod_cast this
    linarith
  have hh : (0 : ℝ) ≤ hDim n := Nat.cast_nonneg _
  have hc : 0 ≤ 8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) (Real.log_nonneg h1))
      (mul_nonneg hh (Real.log_nonneg (by norm_num)))
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hc) (sq_nonneg _)

/-- The primes `p ≤ K/M` contribute at most `8λ/M + o(1)` to `K⁻² log m_{K,M}`: the bound of
`crude_sum_le`, divided by `K²`, tends to `8λ/M` (its small-prime term is `o(K²)`). This uses
`θ(x) ~ x`. -/
theorem tendsto_crude_bound (M : ℕ) :
    Tendsto (fun n : ℕ => (8 * (hDim n : ℝ) * Chebyshev.theta (1 / (M : ℝ) * K n)
        + (Nat.sqrt (5 * K n) : ℝ) * (8 * (hDim n : ℝ) * Real.log (5 * (K n : ℝ))
          + (hDim n : ℝ) * Real.log 720)) / (K n : ℝ) ^ 2) atTop (𝓝 (8 * (lam : ℝ) / M)) := by
  have h1 : Tendsto (fun n : ℕ => Chebyshev.theta (1 / (M : ℝ) * K n) / K n) atTop
      (𝓝 (1 / M)) :=
    (PrimeSum.tendsto_theta_mul_div theta_isEquivalent_id (by positivity)).comp tendsto_K_atTop
  have hφ : Tendsto (fun x : ℝ => (8 * Real.log x + Real.log 720) * Real.sqrt x / x) atTop
      (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hb : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have hc := (ha.const_mul 8).add (hb.const_mul (Real.log 720))
    rw [mul_zero, mul_zero, add_zero] at hc
    refine hc.congr fun x => ?_
    simp only [mul_div_assoc, Real.sqrt_div_self, ← Real.sqrt_eq_rpow]
    ring
  have h5 : Tendsto (fun n : ℕ => 5 * (K n : ℝ)) atTop atTop :=
    tendsto_K_atTop.const_mul_atTop (by norm_num)
  have h2 : Tendsto (fun n : ℕ => (lam : ℝ) * ((8 * Real.log (5 * (K n : ℝ)) + Real.log 720)
      * Real.sqrt (5 * (K n : ℝ)) / (5 * (K n : ℝ))) * 5) atTop (𝓝 0) := by
    have h := ((hφ.comp h5).const_mul (lam : ℝ)).mul_const 5
    rw [mul_zero, zero_mul] at h
    exact h
  have h3 : Tendsto (fun n : ℕ => (Nat.sqrt (5 * K n) : ℝ) * (8 * (hDim n : ℝ)
      * Real.log (5 * (K n : ℝ)) + (hDim n : ℝ) * Real.log 720) / (K n : ℝ) ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (eventually_atTop.mpr ⟨1, fun n hn => small_prime_error_nonneg hn⟩)
      (eventually_atTop.mpr ⟨1, fun n hn => small_prime_error_le hn⟩) h2
  have h4 := (h1.const_mul (8 * (lam : ℝ))).add h3
  rw [show 8 * (lam : ℝ) * (1 / (M : ℝ)) + 0 = 8 * (lam : ℝ) / M by ring] at h4
  refine Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩) h4
  have hK := K_pos hn
  have hKK : (K n : ℝ) * (K n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  have hh : (hDim n : ℝ) = (lam : ℝ) * K n := by rw [← K_mul_lam]; ring
  beta_reduce
  linear_combination (-8 * Chebyshev.theta (1 / (M : ℝ) * K n) * (K n : ℝ)⁻¹ * (lam : ℝ)) * hKK
    + (-8 * Chebyshev.theta (1 / (M : ℝ) * K n) * (K n : ℝ)⁻¹ ^ 2) * hh

/-! ## The inner range `K/M < p ≤ K/3` -/

/-- (70) for the branch exponent: uniformly in the inner range,
`-L_p = p R(K/p) + O_M(1)`, from `L_p = v_p(S_K) + γ^in_p` and `R = -Γ - N`. -/
theorem LpKM_inner_approx (M : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n p : ℕ, p.Prime → InnerRange n M p →
    |(-(LpKM n M p : ℝ)) - p * innerR ((K n : ℝ) / p)| ≤ C := by
  obtain ⟨C1, hC1⟩ := gammaIn_approx M
  obtain ⟨C2, hC2⟩ := padicValRat_SK_approx M
  refine ⟨max (C1 + C2) 0, le_max_right _ _, fun n p hp hR => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have h1 := hC1 n p (innerExtraRows n M p) hp hR (innerExtraRows_spec hR)
  have h2 := hC2 n p hp hR
  have hmax := le_max_left (C1 + C2) 0
  rw [LpKM_of_inner hR.K_lt hR.three_mul_le, innerR]
  push_cast
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `|R(x)| ≤ 24|x| + 27/8`, from `R = xF + Q`, `|F| ≤ 24` and `|Q| ≤ 27/8`. -/
theorem abs_innerR_le (x : ℝ) : |innerR x| ≤ 24 * |x| + 27 / 8 := by
  rw [innerR_eq_tail]
  calc |x * tailF x + tailQ x| ≤ |x * tailF x| + |tailQ x| := abs_add_le _ _
    _ = |x| * |tailF x| + |tailQ x| := by rw [abs_mul]
    _ ≤ |x| * 24 + 27 / 8 :=
        add_le_add (mul_le_mul_of_nonneg_left (abs_tailF_le x) (abs_nonneg x)) (abs_tailQ_le x)
    _ = 24 * |x| + 27 / 8 := by ring

private theorem psb_continuous_tailD : Continuous tailD := by
  unfold tailD
  exact continuous_id.min (continuous_const.sub continuous_id)

private theorem psb_tailEps_continuousAt {u : ℝ} (hu : u ≠ 1 / 2) :
    ContinuousAt tailEps u := by
  rcases lt_or_gt_of_ne hu with h | h
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) u).congr ?_
    filter_upwards [Iio_mem_nhds h] with v hv
    have hv' : v < 1 / 2 := hv
    show (1 : ℝ) = tailEps v
    rw [tailEps, ite_eq_left hv']
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) u).congr ?_
    filter_upwards [Ioi_mem_nhds h] with v hv
    have hv' : ¬ v < 1 / 2 := not_lt.mpr (le_of_lt hv)
    show (-1 : ℝ) = tailEps v
    rw [tailEps, ite_eq_right hv']

private theorem psb_fract_mul_continuousAt {c x : ℝ} (h : ∀ k : ℤ, c * x ≠ k) :
    ContinuousAt (fun y : ℝ => Int.fract (c * y)) x :=
  ContinuousAt.comp (g := Int.fract) (f := fun y : ℝ => c * y)
    (continuousAt_fract (h ⌊c * x⌋)) (by fun_prop)

private theorem psb_tailF_shape_continuousAt {F G : ℝ → ℝ} {x : ℝ} (hF : ContinuousAt F x)
    (hG : ContinuousAt G x) (a b c : ℝ) :
    ContinuousAt (fun y => a + b * F y - c * G y) x := by
  fun_prop

private theorem psb_tailQ_shape_continuousAt {F1 F2 F3 Df Da Ef Ea : ℝ → ℝ} {x : ℝ}
    (h1 : ContinuousAt F1 x) (h2 : ContinuousAt F2 x) (h3 : ContinuousAt F3 x)
    (h4 : ContinuousAt Df x) (h5 : ContinuousAt Da x) (h6 : ContinuousAt Ef x)
    (h7 : ContinuousAt Ea x) :
    ContinuousAt (fun y => (F1 y * (F1 y - F2 y) - max (F1 y - F2 y) 0 + F3 y * (1 - F3 y)) / 2
      + 16 * (Da y * (1 - 2 * Da y))
      - 4 * (Ef y * Ea y * (min (Df y) (Da y) - 2 * Df y * Da y))) x := by
  fun_prop

/-- `R` jumps only where `cx` is an integer for some `c ∈ {2, 2α, 2H, 2λ}`: off that set it is
continuous, by `R = xF + Q` and the closed form of `Q` (`tailQ_eq`). -/
theorem innerR_continuousAt {x : ℝ} (h1 : ∀ k : ℤ, 2 * x ≠ k)
    (h2 : ∀ k : ℤ, 2 * (alpha : ℝ) * x ≠ k) (h3 : ∀ k : ℤ, 2 * (bigH : ℝ) * x ≠ k)
    (h4 : ∀ k : ℤ, 2 * (lam : ℝ) * x ≠ k) : ContinuousAt innerR x := by
  have hx : ∀ k : ℤ, x ≠ k := fun k hk => h1 (2 * k) (by push_cast; linarith)
  have hax : ∀ k : ℤ, (alpha : ℝ) * x ≠ k := fun k hk => h2 (2 * k) (by push_cast; linarith)
  have hfx : Int.fract x ≠ 1 / 2 := fun hf => h1 (2 * ⌊x⌋ + 1) (by
    have e := Int.floor_add_fract x
    rw [hf] at e
    push_cast
    linarith)
  have hfa : Int.fract ((alpha : ℝ) * x) ≠ 1 / 2 := fun hf => h2 (2 * ⌊(alpha : ℝ) * x⌋ + 1) (by
    have e := Int.floor_add_fract ((alpha : ℝ) * x)
    rw [hf] at e
    push_cast
    linarith)
  have cf : ContinuousAt Int.fract x := continuousAt_fract (hx ⌊x⌋)
  have ca : ContinuousAt (fun y : ℝ => Int.fract ((alpha : ℝ) * y)) x :=
    psb_fract_mul_continuousAt hax
  have c2 : ContinuousAt (fun y : ℝ => Int.fract (2 * y)) x := psb_fract_mul_continuousAt h1
  have c2H : ContinuousAt (fun y : ℝ => Int.fract (2 * (bigH : ℝ) * y)) x :=
    psb_fract_mul_continuousAt h3
  have c2l : ContinuousAt (fun y : ℝ => Int.fract (2 * (lam : ℝ) * y)) x :=
    psb_fract_mul_continuousAt h4
  have cdf : ContinuousAt (fun y : ℝ => tailD (Int.fract y)) x :=
    psb_continuous_tailD.continuousAt.comp cf
  have cda : ContinuousAt (fun y : ℝ => tailD (Int.fract ((alpha : ℝ) * y))) x :=
    psb_continuous_tailD.continuousAt.comp ca
  have cef : ContinuousAt (fun y : ℝ => tailEps (Int.fract y)) x :=
    (psb_tailEps_continuousAt hfx).comp cf
  have cea : ContinuousAt (fun y : ℝ => tailEps (Int.fract ((alpha : ℝ) * y))) x :=
    (psb_tailEps_continuousAt hfa).comp (f := fun y : ℝ => Int.fract ((alpha : ℝ) * y)) ca
  have cF : ContinuousAt tailF x := by
    rw [show tailF = fun y => 6 * (lam : ℝ) + 2 * (lam : ℝ) * Int.fract y
      - 16 * (lam : ℝ) * Int.fract ((alpha : ℝ) * y) from rfl]
    exact psb_tailF_shape_continuousAt cf ca _ _ _
  have cQ : ContinuousAt tailQ x := by
    rw [show tailQ = _ from funext tailQ_eq]
    exact psb_tailQ_shape_continuousAt c2H c2 c2l cdf cda cef cea
  rw [show innerR = _ from funext innerR_eq_tail]
  exact (continuousAt_id.mul cF).add cQ

/-- The inner weight `G(y) = y R(1/y)` is bounded on `[1/M, 1/3]` (by `24 + 27/24 ≤ 26`). -/
theorem innerWeight_bounded {M : ℕ} (hM : 0 < M) :
    ∃ C, ∀ y ∈ Set.Icc (1 / (M : ℝ)) (1 / 3), |y * innerR y⁻¹| ≤ C := by
  refine ⟨26, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by exact_mod_cast hM)) hy.1
  have h := abs_innerR_le y⁻¹
  rw [abs_of_pos (inv_pos.mpr hy0)] at h
  rw [abs_mul, abs_of_pos hy0]
  have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
  have h2 : y * |innerR y⁻¹| ≤ y * (24 * y⁻¹ + 27 / 8) := mul_le_mul_of_nonneg_left h hy0.le
  have h3 : y * (24 * y⁻¹ + 27 / 8) = 24 + 27 / 8 * y := by linear_combination 24 * hyy
  linarith [hy.2]

private theorem psb_mul_inv_ne_int {M : ℕ} (hM : 0 < M) {c y : ℝ} (hc : 0 < c)
    (hy : y ∈ Set.Icc (1 / (M : ℝ)) (1 / 3))
    (hF : y ∉ (fun k : ℤ => c / k) '' Set.Icc ⌈3 * c⌉ ⌊(M : ℝ) * c⌋) :
    ∀ k : ℤ, c * y⁻¹ ≠ k := by
  intro k hk
  apply hF
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr hMR) hy.1
  have hx3 : 3 ≤ y⁻¹ := by
    rw [← one_div, le_div_iff₀ hy0]
    linarith [hy.2]
  have hxM : y⁻¹ ≤ M := by
    have h1 := hy.1
    rw [div_le_iff₀ hMR] at h1
    rw [← one_div, div_le_iff₀ hy0]
    linarith
  refine ⟨k, ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩, ?_⟩
  · rw [← hk]
    have := mul_le_mul_of_nonneg_left hx3 hc.le
    linarith
  · rw [← hk]
    have := mul_le_mul_of_nonneg_left hxM hc.le
    linarith
  · show c / (k : ℝ) = y
    rw [← hk, div_mul_eq_div_div, div_self hc.ne', one_div, inv_inv]

/-- The inner weight `G(y) = y R(1/y)` has finitely many discontinuities in `[1/M, 1/3]`: they
lie at `y = c/k` with `c ∈ {2, 2α, 2H, 2λ}` and `3c ≤ k ≤ Mc`. -/
theorem innerWeight_disc_finite {M : ℕ} (hM : 0 < M) :
    {y ∈ Set.Icc (1 / (M : ℝ)) (1 / 3) |
      ¬ContinuousWithinAt (fun z : ℝ => z * innerR z⁻¹) (Set.Icc (1 / (M : ℝ)) (1 / 3)) y}.Finite
    := by
  have hfin : ∀ c : ℝ, ((fun k : ℤ => c / k) '' Set.Icc ⌈3 * c⌉ ⌊(M : ℝ) * c⌋).Finite :=
    fun c => (Set.finite_Icc _ _).image _
  refine (((hfin 2).union (hfin (2 * (alpha : ℝ)))).union
    ((hfin (2 * (bigH : ℝ))).union (hfin (2 * (lam : ℝ))))).subset ?_
  rintro y ⟨hy, hdisc⟩
  by_contra hF
  simp only [Set.mem_union, not_or] at hF
  obtain ⟨⟨hF1, hF2⟩, hF3, hF4⟩ := hF
  apply hdisc
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by exact_mod_cast hM)) hy.1
  have hR : ContinuousAt innerR y⁻¹ :=
    innerR_continuousAt (psb_mul_inv_ne_int hM (by norm_num) hy hF1)
      (psb_mul_inv_ne_int hM (by rw [alpha_real]; norm_num) hy hF2)
      (psb_mul_inv_ne_int hM (by rw [bigH_real]; norm_num) hy hF3)
      (psb_mul_inv_ne_int hM (by rw [lam_real]; norm_num) hy hF4)
  exact (continuousAt_id.mul (hR.comp (continuousAt_inv₀ hy0.ne'))).continuousWithinAt

/-- The change of variables pointwise: `R(1/y)/(1/y)³ · (-1/y²) = -y R(1/y)`. -/
theorem innerWeight_identity {y : ℝ} (hy : y ≠ 0) :
    innerR y⁻¹ / y⁻¹ ^ 3 * -(y ^ 2)⁻¹ = -(y * innerR y⁻¹) := by
  have h : y ^ 3 * (y ^ 2)⁻¹ = y := by
    rw [← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hy)]
    ring
  rw [inv_pow, div_inv_eq_mul]
  linear_combination (-(innerR y⁻¹)) * h

/-- The change of variables `x = 1/y`: `∫_{1/M}^{1/3} y R(1/y) dy = ∫_3^M R(x)/x³ dx`. -/
theorem integral_innerWeight {M : ℕ} (hM : 3 ≤ M) :
    ∫ y in (1 / (M : ℝ))..(1 / 3), y * innerR y⁻¹ = ∫ x in (3 : ℝ)..M, innerR x / x ^ 3 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ha : (0 : ℝ) < 1 / M := one_div_pos.mpr hM0
  have hab : 1 / (M : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)
  have hpos : ∀ y ∈ Set.uIcc (1 / (M : ℝ)) (1 / 3), 0 < y := fun y hy => by
    rw [Set.uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  have hpos' : ∀ y ∈ Set.Ioo (min (1 / (M : ℝ)) (1 / 3)) (max (1 / (M : ℝ)) (1 / 3)),
      0 < y := fun y hy => by
    rw [min_eq_left hab] at hy
    exact lt_trans ha hy.1
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := 1 / (M : ℝ)) (b := 1 / 3) (f := fun y : ℝ => y⁻¹) (f' := fun y : ℝ => -(y ^ 2)⁻¹)
    (g := fun x : ℝ => innerR x / x ^ 3)
    (fun y hy => (continuousAt_inv₀ (hpos y hy).ne').continuousWithinAt)
    (fun y hy => hasDerivAt_inv (hpos' y hy).ne')
    (fun y _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg y)))
  simp only [Function.comp_apply] at key
  have e1 : (1 / (M : ℝ))⁻¹ = M := by rw [inv_div, div_one]
  have e2 : (1 / (3 : ℝ))⁻¹ = 3 := by norm_num
  have hcongr : ∫ x in (1 / (M : ℝ))..(1 / 3), innerR x⁻¹ / x⁻¹ ^ 3 * -(x ^ 2)⁻¹
      = ∫ x in (1 / (M : ℝ))..(1 / 3), -(x * innerR x⁻¹) :=
    intervalIntegral.integral_congr fun y hy => innerWeight_identity (hpos y hy).ne'
  rw [e1, e2, hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_symm 3 (M : ℝ)]
    at key
  linarith

/-- The inner range: `K⁻² ∑_{K/M < p ≤ K/3} (-L_p) log p → ∫_3^M R(x)/x³ dx`, by (70), the prime
Riemann sum with weight `y R(1/y)` on `[1/M, 1/3]` and the change of variables `x = 1/y`. -/
theorem tendsto_inner_sum {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => (∑ p ∈ Finset.Ioc ⌊1 / (M : ℝ) * K n⌋₊ ⌊1 / 3 * (K n : ℝ)⌋₊ with p.Prime,
        (-(LpKM n M p : ℝ)) * Real.log p) / (K n : ℝ) ^ 2) atTop
      (𝓝 (∫ x in (3 : ℝ)..M, innerR x / x ^ 3)) := by
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  obtain ⟨C, hC0, hC⟩ := LpKM_inner_approx M
  rw [← integral_innerWeight (by omega : 3 ≤ M)]
  refine tendsto_weighted_prime_sum (G := fun y => y * innerR y⁻¹) (one_div_pos.mpr hMR)
    (one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast (show 3 < M by omega)))
    (innerWeight_bounded hM0) (innerWeight_disc_finite hM0) (fun n p => -(LpKM n M p : ℝ))
    hC0 ?_
  filter_upwards [eventually_ge_atTop (5 * M ^ 2), eventually_ge_atTop 1] with n hn hn1
  intro p hp hpp
  have hKdef : K n = 40 * n := rfl
  rw [Finset.mem_Ioc, floor_one_div_mul_K, floor_one_third_mul_K] at hp
  have hKlt : K n < p * M := (Nat.div_lt_iff_lt_mul hM0).mp hp.1
  have h3p : p * 3 ≤ K n := (Nat.le_div_iff_mul_le (by norm_num)).mp hp.2
  have hR : InnerRange n M p :=
    ⟨hM, by omega, by rw [Nat.mul_comm]; exact hKlt, by omega⟩
  have hKpos := K_pos hn1
  show |(-(LpKM n M p : ℝ)) - (K n : ℝ) * ((p : ℝ) / K n * innerR ((p : ℝ) / K n)⁻¹)| ≤ C
  rw [inv_div, ← mul_assoc, mul_div_cancel₀ _ hKpos.ne']
  exact hC n p hpp hR

/-! ## The outer range `K/3 < p ≤ 2h` -/

private theorem psb_floor_one_div_eq_two {y : ℝ} (h1 : 1 / 3 < y) (h2 : y ≤ 1 / 2) :
    ⌊1 / y⌋ = 2 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hy]
    linarith
  · rw [div_lt_iff₀ hy]
    linarith

private theorem psb_floor_one_div_eq_one {y : ℝ} (h1 : 1 / 2 < y) (h2 : y ≤ 1) :
    ⌊1 / y⌋ = 1 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hy]
    linarith
  · rw [div_lt_iff₀ hy]
    linarith

private theorem psb_floor_one_div_eq_zero {y : ℝ} (h : 1 < y) : ⌊1 / y⌋ = 0 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_zero_iff]
  exact Set.mem_Ico.mpr ⟨div_nonneg zero_le_one hy.le, (div_lt_one hy).mpr h⟩

/-- `K v(k, p/K) = K - kp`. -/
theorem K_mul_outerV {n : ℕ} (p : ℕ) (hn : 0 < n) (k : ℤ) :
    (K n : ℝ) * outerV k ((p : ℝ) / K n) = (K n : ℝ) - k * p := by
  unfold outerV
  linear_combination (-(k : ℝ)) * K_mul_div_K p hn

/-- `K u(k, p/K) = max(0, N + (K - kp) - p)`. -/
theorem K_mul_outerU {n : ℕ} (p : ℕ) (hn : 0 < n) (k : ℤ) :
    (K n : ℝ) * outerU k ((p : ℝ) / K n) = max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p) := by
  unfold outerU
  rw [mul_max_of_nonneg _ _ (K_pos hn).le, mul_zero]
  congr 1
  unfold outerV
  linear_combination K_mul_alpha n + (-(k : ℝ) - 1) * K_mul_div_K p hn

/-- `K t(k, p/K) = min(N, K - kp) + max(0, N + (K - kp) - p)`. -/
theorem K_mul_outerT {n : ℕ} (p : ℕ) (hn : 0 < n) (k : ℤ) :
    (K n : ℝ) * outerT k ((p : ℝ) / K n) =
      min (N n : ℝ) ((K n : ℝ) - k * p) + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p) := by
  unfold outerT
  rw [mul_add, mul_min_of_nonneg _ _ (K_pos hn).le, K_mul_outerU p hn, K_mul_outerV p hn,
    K_mul_alpha]

/-- `K r(p/K) = min(h, max(0, K + 6N - 3p))`. -/
theorem K_mul_outerR {n : ℕ} (p : ℕ) (hn : 0 < n) :
    (K n : ℝ) * outerR ((p : ℝ) / K n) =
      min (hDim n : ℝ) (max 0 ((K n : ℝ) + 6 * N n - 3 * p)) := by
  unfold outerR
  rw [mul_min_of_nonneg _ _ (K_pos hn).le, mul_max_of_nonneg _ _ (K_pos hn).le, mul_zero,
    K_mul_lam]
  congr 2
  linear_combination 6 * K_mul_alpha n - 3 * K_mul_div_K p hn

/-- `K` times the formula for `g` on `1/2 < y ≤ 1` (the case `K < 2p` of (59)). -/
theorem K_mul_outerGHigh {n : ℕ} (p : ℕ) (hn : 0 < n) (k : ℤ) :
    (K n : ℝ) * outerGHigh k ((p : ℝ) / K n) =
      9 * ((K n : ℝ) - p)
        - 8 * (min (N n : ℝ) ((K n : ℝ) - k * p) + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p))
        + min (min (hDim n : ℝ) (max 0 ((K n : ℝ) + 6 * N n - 3 * p)))
            ((p : ℝ) - N n + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p)) := by
  have hm : (K n : ℝ) * min (outerR ((p : ℝ) / K n))
        ((p : ℝ) / K n - (alpha : ℝ) + outerU k ((p : ℝ) / K n)) =
      min (min (hDim n : ℝ) (max 0 ((K n : ℝ) + 6 * N n - 3 * p)))
        ((p : ℝ) - N n + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p)) := by
    rw [mul_min_of_nonneg _ _ (K_pos hn).le, K_mul_outerR p hn]
    congr 1
    rw [mul_add, K_mul_outerU p hn]
    linear_combination K_mul_div_K p hn - K_mul_alpha n
  unfold outerGHigh
  linear_combination (-9 : ℝ) * K_mul_div_K p hn - 8 * K_mul_outerT p hn k + hm

/-- `K` times the formula for `g` on `1/3 < y ≤ 1/2` (the case `K ≥ 2p` of (59)). -/
theorem K_mul_outerGLow {n : ℕ} (p : ℕ) (hn : 0 < n) (k : ℤ) :
    (K n : ℝ) * outerGLow k ((p : ℝ) / K n) =
      9 * ((K n : ℝ) - p) - 16 * (N n : ℝ)
        - 7 * (min (N n : ℝ) ((K n : ℝ) - k * p) + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p))
        + min (min (hDim n : ℝ) (max 0 ((K n : ℝ) + 6 * N n - 3 * p)))
            ((p : ℝ) + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p)) := by
  have hm : (K n : ℝ) * min (outerR ((p : ℝ) / K n))
        ((p : ℝ) / K n + outerU k ((p : ℝ) / K n)) =
      min (min (hDim n : ℝ) (max 0 ((K n : ℝ) + 6 * N n - 3 * p)))
        ((p : ℝ) + max 0 ((N n : ℝ) + ((K n : ℝ) - k * p) - p)) := by
    rw [mul_min_of_nonneg _ _ (K_pos hn).le, K_mul_outerR p hn, mul_add, K_mul_outerU p hn,
      K_mul_div_K p hn]
  unfold outerGLow
  linear_combination (-9 : ℝ) * K_mul_div_K p hn - 16 * K_mul_alpha n
    - 7 * K_mul_outerT p hn k + hm

/-- The outer exponent and the outer limiting function: `|-γ^out_p - K g(p/K)| ≤ 10` for every
`p > K/3`. For `p > K` both sides vanish; for `K/3 < p ≤ K` the difference is
`-8(u_p - Ku) + 1 + (min - min) ∈ [-8, 5]` (case `K < 2p`) or
`-3 - 7(u_p - Ku) + (min - min) ∈ [-10, 1]` (case `K ≥ 2p`), where `u_p` and `r_p` exceed their
scaled limits by at most `1` and `4`. -/
theorem gammaOut_approx (n p : ℕ) (h3 : K n < 3 * p) :
    |(-(gammaOut n p : ℝ)) - (K n : ℝ) * outerG ((p : ℝ) / K n)| ≤ 10 := by
  have hKdef : K n = 40 * n := rfl
  by_cases hKp : K n < p
  · rw [gammaOut_of_K_lt hKp]
    have h0 : (K n : ℝ) * outerG ((p : ℝ) / K n) = 0 := by
      rcases Nat.eq_zero_or_pos (K n) with hK | hK
      · rw [hK, Nat.cast_zero, zero_mul]
      · have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK
        rw [outerG_of_one_lt ((one_lt_div hK0).mpr (by exact_mod_cast hKp)), mul_zero]
    rw [h0]
    norm_num
  have hpK : p ≤ K n := not_lt.mp hKp
  have hn : 0 < n := by omega
  have hp0 : 0 < p := by omega
  have hK0 := K_pos hn
  by_cases h2 : K n < 2 * p
  · have hmK : K n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hvZ : (classV n p : ℤ) = (K n : ℤ) - p := by
      unfold classV mK
      rw [hmK]
      omega
    have hy1 : 1 / 2 < (p : ℝ) / K n := by
      rw [lt_div_iff₀ hK0]
      have : (K n : ℝ) < 2 * p := by exact_mod_cast h2
      linarith
    have hy2 : (p : ℝ) / K n ≤ 1 := by
      rw [div_le_one hK0]
      exact_mod_cast hpK
    have hfl : ⌊1 / ((p : ℝ) / K n)⌋ = 1 := by
      rw [one_div_div, floor_natCast_div _ _ hp0, hmK, Nat.cast_one]
    have hKg : (K n : ℝ) * outerG ((p : ℝ) / K n) = (((9 * (K n : ℤ) - 9 * p
        - 8 * (min (N n : ℤ) ((K n : ℤ) - p) + max 0 ((N n : ℤ) + ((K n : ℤ) - p) - p))
        + min (min (hDim n : ℤ) (max 0 ((K n : ℤ) + 6 * N n - 3 * p)))
          ((p : ℤ) - N n + max 0 ((N n : ℤ) + ((K n : ℤ) - p) - p))) : ℤ) : ℝ) := by
      rw [outerG_of_half_lt hy1 hy2, hfl, K_mul_outerGHigh p hn]
      push_cast
      ring_nf
    have hZ : |(-(gammaOut n p) - (9 * (K n : ℤ) - 9 * p
        - 8 * (min (N n : ℤ) ((K n : ℤ) - p) + max 0 ((N n : ℤ) + ((K n : ℤ) - p) - p))
        + min (min (hDim n : ℤ) (max 0 ((K n : ℤ) + 6 * N n - 3 * p)))
          ((p : ℤ) - N n + max 0 ((N n : ℤ) + ((K n : ℤ) - p) - p))) : ℤ)| ≤ 10 := by
      rw [gammaOut_of_lt_two_mul hpK h2, rankCorr_cast]
      unfold classT classU
      rw [hvZ, abs_le]
      constructor <;> omega
    rw [hKg]
    exact_mod_cast hZ
  · have h2' : 2 * p ≤ K n := not_lt.mp h2
    have hmK : K n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hvZ : (classV n p : ℤ) = (K n : ℤ) - 2 * p := by
      unfold classV mK
      rw [hmK]
      omega
    have hy1 : 1 / 3 < (p : ℝ) / K n := by
      rw [lt_div_iff₀ hK0]
      have : (K n : ℝ) < 3 * p := by exact_mod_cast h3
      linarith
    have hy2 : (p : ℝ) / K n ≤ 1 / 2 := by
      rw [div_le_iff₀ hK0]
      have : (2 * p : ℝ) ≤ K n := by exact_mod_cast h2'
      linarith
    have hfl : ⌊1 / ((p : ℝ) / K n)⌋ = 2 := by
      rw [one_div_div, floor_natCast_div _ _ hp0, hmK, Nat.cast_ofNat]
    have hKg : (K n : ℝ) * outerG ((p : ℝ) / K n) = (((9 * (K n : ℤ) - 9 * p - 16 * N n
        - 7 * (min (N n : ℤ) ((K n : ℤ) - 2 * p) + max 0 ((N n : ℤ) + ((K n : ℤ) - 2 * p) - p))
        + min (min (hDim n : ℤ) (max 0 ((K n : ℤ) + 6 * N n - 3 * p)))
          ((p : ℤ) + max 0 ((N n : ℤ) + ((K n : ℤ) - 2 * p) - p))) : ℤ) : ℝ) := by
      rw [outerG_of_le_half hy1 hy2, hfl, K_mul_outerGLow p hn]
      push_cast
      ring_nf
    have hZ : |(-(gammaOut n p) - (9 * (K n : ℤ) - 9 * p - 16 * N n
        - 7 * (min (N n : ℤ) ((K n : ℤ) - 2 * p) + max 0 ((N n : ℤ) + ((K n : ℤ) - 2 * p) - p))
        + min (min (hDim n : ℤ) (max 0 ((K n : ℤ) + 6 * N n - 3 * p)))
          ((p : ℤ) + max 0 ((N n : ℤ) + ((K n : ℤ) - 2 * p) - p))) : ℤ)| ≤ 10 := by
      rw [gammaOut_of_two_mul_le h2', rankCorr_cast]
      unfold classT classU
      rw [hvZ, abs_le]
      constructor <;> omega
    rw [hKg]
    exact_mod_cast hZ

/-- `2 ∑_{j=1}^{m} (a - jb) = 2ma - bm(m+1)`. -/
theorem sum_Icc_sub_mul (a b : ℝ) (m : ℕ) :
    2 * ∑ j ∈ Finset.Icc 1 m, (a - (j : ℝ) * b) = 2 * m * a - b * m * (m + 1) := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), mul_add, ih]
    push_cast
    ring

/-- If `mb ≤ a < (m+1)b` with `b > 0` and `m ≤ 7`, then
`2 ∑_{j=1}^{7} (a - jb)₊ = 2ma - bm(m+1)`. -/
theorem sum_max_sub_mul {a b : ℝ} (hb : 0 < b) {m : ℕ} (hm : m ≤ 7) (h1 : (m : ℝ) * b ≤ a)
    (h2 : a < ((m : ℝ) + 1) * b) :
    2 * ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (a - (j : ℝ) * b) 0 = 2 * m * a - b * m * (m + 1) := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 7,
      max (a - (j : ℝ) * b) 0 = if j ≤ m then a - (j : ℝ) * b else 0 := by
    intro j _
    split_ifs with hj
    · apply max_eq_left
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      have := mul_le_mul_of_nonneg_right hj' hb.le
      linarith
    · apply max_eq_right
      have hj' : (m : ℝ) + 1 ≤ j := by exact_mod_cast (show m + 1 ≤ j by omega)
      have := mul_le_mul_of_nonneg_right hj' hb.le
      linarith
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hf : (Finset.Icc (1 : ℕ) 7).filter (fun j => j ≤ m) = Finset.Icc 1 m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf]
  exact sum_Icc_sub_mul a b m

/-- `K s(p/K) = -2h⌊K/p⌋ + ∑_{j=1}^{7} (2h - jp)₊` for the scalar term `s` of (73). -/
theorem K_mul_outerScalar {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    (K n : ℝ) * outerScalar ((p : ℝ) / K n) = -2 * (hDim n : ℝ) * ((K n / p : ℕ) : ℝ)
      + ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (hDim n : ℝ) - (j : ℝ) * p) 0 := by
  have hK0 := K_pos hn
  have hfl : ⌊1 / ((p : ℝ) / K n)⌋ = ((K n / p : ℕ) : ℤ) := by
    rw [one_div_div]
    exact floor_natCast_div _ _ hp
  have hs : ∀ j ∈ Finset.Icc (1 : ℕ) 7,
      (K n : ℝ) * max (2 * (lam : ℝ) - (j : ℝ) * ((p : ℝ) / K n)) 0
        = max (2 * (hDim n : ℝ) - (j : ℝ) * p) 0 := by
    intro j _
    rw [mul_max_of_nonneg _ _ hK0.le, mul_zero]
    congr 1
    linear_combination 2 * K_mul_lam n - (j : ℝ) * K_mul_div_K p hn
  have hc : (K n : ℝ) * (-2 * (lam : ℝ) * (((K n / p : ℕ) : ℤ) : ℝ))
      = -2 * (hDim n : ℝ) * ((K n / p : ℕ) : ℝ) := by
    rw [Int.cast_natCast]
    linear_combination (-2 * ((K n / p : ℕ) : ℝ)) * K_mul_lam n
  unfold outerScalar
  rw [hfl, mul_add, Finset.mul_sum, Finset.sum_congr rfl hs, hc]

/-- The valuation of `S_K` and the scalar term of (73) in the outer range: for a prime `p > K/3`,
`0 ≤ v_p(S_K) + K s(p/K) ≤ 10`. By (62) with `p² > 2h`, `p² > K` and `N < p`,
`v_p(S_K) = 2h⌊K/p⌋ - 2∑_{i<h} ⌊2i/p⌋`, and `K s(p/K) = -2h⌊K/p⌋ + 2p J(h/p)`, so the sum is
`2(p J(h/p) - ∑_{i<h} ⌊2i/p⌋) ∈ [0, 2⌊2h/p⌋]` with `⌊2h/p⌋ ≤ 5`. -/
theorem padicValRat_SK_add_outerScalar {n p : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h3 : K n < 3 * p) :
    0 ≤ (padicValRat p (SK n) : ℝ) + (K n : ℝ) * outerScalar ((p : ℝ) / K n) ∧
      (padicValRat p (SK n) : ℝ) + (K n : ℝ) * outerScalar ((p : ℝ) / K n) ≤ 10 := by
  have : Fact p.Prime := ⟨hp⟩
  have hKdef : K n = 40 * n := rfl
  have hNdef : N n = 3 * n := rfl
  have hhdef : hDim n = 37 * n := rfl
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have h13 : 13 * n + 1 ≤ p := by omega
  have h14 : 14 ≤ p := by omega
  have h4 : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hsq : 2 * hDim n < p ^ 2 := by
    calc 2 * hDim n < (13 * n + 1) * 14 := by omega
      _ ≤ p * p := Nat.mul_le_mul h13 h14
      _ = p ^ 2 := (sq p).symm
  have hK2 : K n < p ^ 2 := by omega
  have hNp : N n / p = 0 := Nat.div_eq_of_lt (by omega)
  have hrange : ∑ i ∈ Finset.Icc 1 (hDim n - 1), ((2 * i / p : ℕ) : ℝ)
      = ∑ i ∈ Finset.range (hDim n), ((2 * i / p : ℕ) : ℝ) := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      omega
    · intro i hi hni
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc, not_and_or, not_le] at hni
      have hi0 : i = 0 := by omega
      subst hi0
      simp
  have hv : (padicValRat p (SK n) : ℝ) = 2 * (hDim n : ℝ) * ((K n / p : ℕ) : ℝ)
      - 2 * ∑ i ∈ Finset.range (hDim n), ((2 * i / p : ℕ) : ℝ) := by
    rw [padicValRat_SK h4 hsq hK2, hNp, ← hrange]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sum,
      Nat.cast_zero, Int.cast_zero]
    ring
  have hKs := K_mul_outerScalar hn hp0
  have hm5 : 2 * hDim n / p ≤ 5 := by
    have : 2 * hDim n / p < 6 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
    omega
  have hdmR : (p : ℝ) * ((2 * hDim n / p : ℕ) : ℝ) + ((2 * hDim n % p : ℕ) : ℝ)
      = 2 * (hDim n : ℝ) := by
    exact_mod_cast Nat.div_add_mod (2 * hDim n) p
  have hmlR : ((2 * hDim n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt (2 * hDim n) hp0
  have hr0 : (0 : ℝ) ≤ ((2 * hDim n % p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm1 : ((2 * hDim n / p : ℕ) : ℝ) * p ≤ 2 * (hDim n : ℝ) := by linarith
  have hm2 : 2 * (hDim n : ℝ) < (((2 * hDim n / p : ℕ) : ℝ) + 1) * p := by linarith
  have hsum := sum_max_sub_mul hpR (show 2 * hDim n / p ≤ 7 by omega) hm1 hm2
  have hpJ : 4 * ((p : ℝ) * innerJ ((hDim n : ℝ) / p)) = 4 * ((2 * hDim n / p : ℕ) : ℝ) * hDim n
      - p * ((2 * hDim n / p : ℕ) : ℝ) * (((2 * hDim n / p : ℕ) : ℝ) + 1) := by
    have hfl : ⌊2 * ((hDim n : ℝ) / p)⌋ = ((2 * hDim n / p : ℕ) : ℤ) := by
      rw [show 2 * ((hDim n : ℝ) / p) = ((2 * hDim n : ℕ) : ℝ) / p by push_cast; ring]
      exact floor_natCast_div _ _ hp0
    rw [innerJ, hfl, Int.cast_natCast]
    have hk : (p : ℝ) * ((hDim n : ℝ) / p) = hDim n := mul_div_cancel₀ _ hpR.ne'
    linear_combination (4 * ((2 * hDim n / p : ℕ) : ℝ)) * hk
  obtain ⟨hJ1, hJ2⟩ := innerJ_sum_bounds hp.two_le (hDim n)
  have hm5R : ((2 * hDim n / p : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hm5
  rw [hv, hKs]
  constructor <;> linarith

/-- The outer branch of (60): for a prime `p > K/3`, `|-L_p - K T(p/K)| ≤ 20` with `T` the
integrand of (73). -/
theorem LpKM_outer_approx {n M p : ℕ} (hp : p.Prime) (hn : 0 < n) (hM : 3 ≤ M)
    (h3 : K n < 3 * p) :
    |(-(LpKM n M p : ℝ)) - (K n : ℝ) * outerIntegrand ((p : ℝ) / K n)| ≤ 20 := by
  have h1 := gammaOut_approx n p h3
  obtain ⟨h2, h3'⟩ := padicValRat_SK_add_outerScalar hp hn h3
  rw [abs_le] at h1
  rw [LpKM_of_outer hM h3, outerIntegrand_eq, abs_le]
  push_cast
  constructor <;> linarith [h1.1, h1.2]

/-- `|g(y)| ≤ 10` for every `y`. -/
theorem abs_outerG_le (y : ℝ) : |outerG y| ≤ 10 := by
  by_cases h1 : 1 / 3 < y ∧ y ≤ 1 / 2
  · obtain ⟨hy0, hy1⟩ := h1
    rw [outerG_of_le_half hy0 hy1, psb_floor_one_div_eq_two hy0 hy1]
    have hV : outerV 2 y = 1 - 2 * y := by norm_num [outerV]
    have hU0 : 0 ≤ outerU 2 y := le_max_left _ _
    have hU1 : outerU 2 y ≤ 3 / 40 := by
      unfold outerU
      rw [hV, alpha_real]
      exact max_le (by norm_num) (by linarith)
    have hA0 : 0 ≤ min (alpha : ℝ) (outerV 2 y) := by
      rw [hV, alpha_real]
      exact le_min (by norm_num) (by linarith)
    have hA1 : min (alpha : ℝ) (outerV 2 y) ≤ 3 / 40 := by
      rw [alpha_real]
      exact min_le_left _ _
    have hR0 : 0 ≤ outerR y := by
      unfold outerR
      exact le_min (by rw [lam_real]; norm_num) (le_max_left _ _)
    have hR1 : outerR y ≤ 37 / 40 := by
      unfold outerR
      rw [lam_real]
      exact min_le_left _ _
    have hm0 : 0 ≤ min (outerR y) (y + outerU 2 y) := le_min hR0 (by linarith)
    have hm1 : min (outerR y) (y + outerU 2 y) ≤ 37 / 40 := (min_le_left _ _).trans hR1
    unfold outerGLow outerT
    rw [alpha_real] at hA0 hA1 ⊢
    rw [abs_le]
    constructor <;> linarith
  by_cases h2 : 1 / 2 < y ∧ y ≤ 1
  · obtain ⟨hy0, hy1⟩ := h2
    rw [outerG_of_half_lt hy0 hy1, psb_floor_one_div_eq_one hy0 hy1]
    have hV : outerV 1 y = 1 - y := by norm_num [outerV]
    have hU0 : 0 ≤ outerU 1 y := le_max_left _ _
    have hU1 : outerU 1 y ≤ 3 / 40 := by
      unfold outerU
      rw [hV, alpha_real]
      exact max_le (by norm_num) (by linarith)
    have hA0 : 0 ≤ min (alpha : ℝ) (outerV 1 y) := by
      rw [hV, alpha_real]
      exact le_min (by norm_num) (by linarith)
    have hA1 : min (alpha : ℝ) (outerV 1 y) ≤ 3 / 40 := by
      rw [alpha_real]
      exact min_le_left _ _
    have hR0 : 0 ≤ outerR y := by
      unfold outerR
      exact le_min (by rw [lam_real]; norm_num) (le_max_left _ _)
    have hR1 : outerR y ≤ 37 / 40 := by
      unfold outerR
      rw [lam_real]
      exact min_le_left _ _
    have hm0 : 0 ≤ min (outerR y) (y - (alpha : ℝ) + outerU 1 y) :=
      le_min hR0 (by rw [alpha_real]; linarith)
    have hm1 : min (outerR y) (y - (alpha : ℝ) + outerU 1 y) ≤ 37 / 40 :=
      (min_le_left _ _).trans hR1
    unfold outerGHigh outerT
    rw [alpha_real] at hA0 hA1 hm0 hm1 ⊢
    rw [abs_le]
    constructor <;> linarith
  · rw [outerG, ite_eq_right h1, ite_eq_right h2, abs_zero]
    norm_num

/-- `|s(y)| ≤ 19` for `y ≥ 1/3`. -/
theorem abs_outerScalar_le {y : ℝ} (hy : 1 / 3 ≤ y) : |outerScalar y| ≤ 19 := by
  have hy0 : 0 < y := by linarith
  have hf0 : (0 : ℝ) ≤ ⌊1 / y⌋ := by
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg zero_le_one hy0.le)
  have hf3 : (⌊1 / y⌋ : ℝ) ≤ 3 :=
    (Int.floor_le _).trans (by rw [div_le_iff₀ hy0]; linarith)
  have hs0 : 0 ≤ ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * y) 0 :=
    Finset.sum_nonneg fun j _ => le_max_right _ _
  have hs1 : ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * y) 0
      ≤ 7 * (2 * (lam : ℝ)) := by
    calc _ ≤ ∑ _j ∈ Finset.Icc (1 : ℕ) 7, 2 * (lam : ℝ) :=
          Finset.sum_le_sum fun j _ =>
            max_le (sub_le_self _ (mul_nonneg (Nat.cast_nonneg j) hy0.le))
              (by rw [lam_real]; norm_num)
      _ = 7 * (2 * (lam : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Icc]
          norm_num
  have hl : (lam : ℝ) = 37 / 40 := lam_real
  have e1 : 0 ≤ (lam : ℝ) * ⌊1 / y⌋ := mul_nonneg (by rw [hl]; norm_num) hf0
  have e2 : (lam : ℝ) * ⌊1 / y⌋ ≤ 37 / 40 * 3 := by
    rw [hl]
    exact mul_le_mul_of_nonneg_left hf3 (by norm_num)
  unfold outerScalar
  rw [abs_le]
  constructor <;> linarith

/-- The integrand `T` of (73) is bounded on `[1/3, ∞)`, by `29`. -/
theorem abs_outerIntegrand_le {y : ℝ} (hy : 1 / 3 ≤ y) : |outerIntegrand y| ≤ 29 := by
  rw [outerIntegrand_eq]
  calc |outerG y + outerScalar y| ≤ |outerG y| + |outerScalar y| := abs_add_le _ _
    _ ≤ 10 + 19 := add_le_add (abs_outerG_le y) (abs_outerScalar_le hy)
    _ = 29 := by norm_num

/-- On `(1/3, ∞)` the integrand `T` of (73) jumps only where `⌊1/y⌋` changes, at `y = 1/2`
and `y = 1`: elsewhere it is continuous. -/
theorem outerIntegrand_continuousAt {y : ℝ} (h1 : 1 / 3 < y) (h2 : y ≠ 1 / 2) (h3 : y ≠ 1) :
    ContinuousAt outerIntegrand y := by
  have hS : ∀ k : ℤ, Continuous fun z : ℝ => -2 * (lam : ℝ) * (k : ℝ)
      + ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * z) 0 :=
    fun k => continuous_const.add (continuous_finsetSum _ fun j _ => by fun_prop)
  rcases lt_or_gt_of_ne h2 with h2 | h2
  · refine ContinuousAt.congr ((continuous_outerGLow 2).add (hS 2)).continuousAt ?_
    filter_upwards [Ioo_mem_nhds h1 h2] with z hz
    rw [outerIntegrand_eq, outerG_of_le_half hz.1 hz.2.le, outerScalar,
      psb_floor_one_div_eq_two hz.1 hz.2.le]
    rfl
  · rcases lt_or_gt_of_ne h3 with h3 | h3
    · refine ContinuousAt.congr ((continuous_outerGHigh 1).add (hS 1)).continuousAt ?_
      filter_upwards [Ioo_mem_nhds h2 h3] with z hz
      rw [outerIntegrand_eq, outerG_of_half_lt hz.1 hz.2.le, outerScalar,
        psb_floor_one_div_eq_one hz.1 hz.2.le]
      rfl
    · refine ContinuousAt.congr
        ((continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).add (hS 0)).continuousAt ?_
      filter_upwards [Ioi_mem_nhds h3] with z hz
      rw [outerIntegrand_eq, outerG_of_one_lt hz, outerScalar, psb_floor_one_div_eq_zero hz]
      rfl

/-- The integrand `T` of (73) has finitely many discontinuities in `[1/3, 2λ]`: they lie in
`{1/3, 1/2, 1}`. -/
theorem outerIntegrand_disc_finite :
    {y ∈ Set.Icc (1 / 3 : ℝ) (2 * (lam : ℝ)) |
      ¬ContinuousWithinAt outerIntegrand (Set.Icc (1 / 3 : ℝ) (2 * (lam : ℝ))) y}.Finite := by
  refine (((Set.finite_singleton (1 : ℝ)).insert (1 / 2)).insert (1 / 3)).subset ?_
  rintro y ⟨hy, hc⟩
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  obtain ⟨h1, h2, h3⟩ := hne
  exact hc (outerIntegrand_continuousAt (lt_of_le_of_ne hy.1 (Ne.symm h1)) h2 h3).continuousWithinAt

/-- The outer range: `K⁻² ∑_{K/3 < p ≤ 2h} (-L_p) log p → I_out`, by the prime Riemann sum with
the integrand of (73) on `[1/3, 2λ]`. -/
theorem tendsto_outer_sum {M : ℕ} (hM : 3 ≤ M) :
    Tendsto (fun n : ℕ => (∑ p ∈ Finset.Ioc ⌊1 / 3 * (K n : ℝ)⌋₊ ⌊2 * (lam : ℝ) * K n⌋₊ with p.Prime,
        (-(LpKM n M p : ℝ)) * Real.log p) / (K n : ℝ) ^ 2) atTop (𝓝 outerIntegral) := by
  refine tendsto_weighted_prime_sum (G := outerIntegrand) (by norm_num)
    (by rw [lam_real]; norm_num) ⟨29, fun y hy => abs_outerIntegrand_le hy.1⟩
    outerIntegrand_disc_finite (fun n p => -(LpKM n M p : ℝ)) (by norm_num : (0 : ℝ) ≤ 20) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro p hp hpp
  rw [Finset.mem_Ioc, floor_one_third_mul_K] at hp
  have h3 : K n < p * 3 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp hp.1
  exact LpKM_outer_approx hpp hn hM (by omega)

/-! ## The tail split and Proposition 5.4 -/

/-- (85) at `T = 20`, with `P(20) = 74/3`, `C(20) = 0`, `|C| < 22` and `Q ≤ 27/8`:
`∫_20^∞ R(x)/x³ dx ≤ -2069/36000` (source-map erratum 14). -/
theorem integral_Ioi_twenty_le :
    ∫ x in Set.Ioi (20 : ℝ), innerR x / x ^ 3 ≤ -2069 / 36000 := by
  have h20 : (0 : ℝ) < 20 := by norm_num
  rw [integral_innerR_div_cube_eq h20, tailP_twenty, tailC_twenty, lam_real]
  have hC : ∫ x in Set.Ioi (20 : ℝ), tailC x / x ^ 4 ≤ 22 * (((20 : ℝ) ^ 3)⁻¹ / 3) := by
    have h' := setIntegral_mono_on (integrableOn_tailC_div h20)
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 4) (by norm_num) h20) 22)
      measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans h20 hx
        have hc := (abs_lt.mp (abs_tailC_lt x)).2
        show tailC x / x ^ 4 ≤ 22 * (x ^ 4)⁻¹
        rw [div_eq_mul_inv (tailC x) (x ^ 4)]
        exact mul_le_mul_of_nonneg_right hc.le (inv_nonneg.mpr (pow_pos hx0 4).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_four h20] at h'
  have hQ : ∫ x in Set.Ioi (20 : ℝ), tailQ x / x ^ 3 ≤ 27 / 8 * (((20 : ℝ) ^ 2)⁻¹ / 2) := by
    have h' := setIntegral_mono_on (integrableOn_tailQ_div h20)
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 3) (by norm_num) h20) (27 / 8))
      measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans h20 hx
        have hq := (tailQ_bounds x).2
        show tailQ x / x ^ 3 ≤ 27 / 8 * (x ^ 3)⁻¹
        rw [div_eq_mul_inv (tailQ x) (x ^ 3)]
        exact mul_le_mul_of_nonneg_right hq (inv_nonneg.mpr (pow_pos hx0 3).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_three h20] at h'
  have key : (-(37 / 40 : ℝ) / 20 - 74 / 3 / (20 : ℝ) ^ 2 + 11729 / 720 / (20 : ℝ) ^ 2
        - 2 * 0 / (20 : ℝ) ^ 3 + 6 * (∫ x in Set.Ioi (20 : ℝ), tailC x / x ^ 4)
        + ∫ x in Set.Ioi (20 : ℝ), tailQ x / x ^ 3) - -2069 / 36000
      = 6 * ((∫ x in Set.Ioi (20 : ℝ), tailC x / x ^ 4) - 22 * (((20 : ℝ) ^ 3)⁻¹ / 3))
        + ((∫ x in Set.Ioi (20 : ℝ), tailQ x / x ^ 3) - 27 / 8 * (((20 : ℝ) ^ 2)⁻¹ / 2)) := by
    ring
  linarith [key, hC, hQ]

/-- `R(x)/x³` is interval integrable on `[a, b]` for `0 < a ≤ b`, so the integrals
`∫_3^20 R(x)/x³ dx` in `B_0` (88) and `∫_3^M R(x)/x³ dx` in the proof of (90) are genuine
integrals, not the junk value `0`. -/
theorem intervalIntegrable_innerR_div_cube_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => innerR x / x ^ 3) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    ((integrableOn_innerR_div_cube ha).mono_set Set.Ioc_subset_Ioi_self)

/-- `∫_20^∞ R(x)/x³ dx ≤ A_0`: the step of the proof of (90) that substitutes `A_0`
(source-map erratum 14: `A_0` bounds this integral; it is not equal to it). -/
theorem integral_Ioi_twenty_le_A0 :
    ∫ x in Set.Ioi (20 : ℝ), innerR x / x ^ 3 ≤ (primeSumA0 : ℝ) := by
  have h := integral_Ioi_twenty_le
  have hA : (-2069 / 36000 : ℝ) ≤ (primeSumA0 : ℝ) := by norm_num [primeSumA0]
  linarith

/-- The split of the inner integral at `20`: for `M ∈ 40ℤ_{>0}`,
`∫_3^M R/x³ = ∫_3^20 + ∫_20^∞ - ∫_M^∞ ≤ ∫_3^20 R/x³ + A_0 + λ/M - 11549/(720M²) + 44/M³`, by
`∫_20^∞ ≤ A_0` and the tail bound (86), which is where `40 ∣ M` is used. -/
theorem integral_three_le {M : ℕ} (hM : 0 < M) (h40 : 40 ∣ M) :
    ∫ x in (3 : ℝ)..M, innerR x / x ^ 3 ≤
      (∫ x in (3 : ℝ)..20, innerR x / x ^ 3) + (primeSumA0 : ℝ) + (lam : ℝ) / M
        - 11549 / (720 * (M : ℝ) ^ 2) + 44 / (M : ℝ) ^ 3 := by
  have hM40 : (40 : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM h40
  have h1 := intervalIntegrable_innerR_div_cube_of_pos (a := 3) (b := 20) (by norm_num)
    (by norm_num)
  have h2 := intervalIntegrable_innerR_div_cube_of_pos (a := 20) (b := M) (by norm_num)
    (by linarith)
  have h20 := integrableOn_innerR_div_cube (T := 20) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_Ioi_sub_Ioi h20 (show (20 : ℝ) ≤ M by linarith)]
  have htail := tail_integral_bound hM h40
  have hA := integral_Ioi_twenty_le_A0
  have e : -(lam : ℝ) / M = -((lam : ℝ) / M) := by ring
  linarith

/-- The combining step of the proof of (90), before the split at `20`: for `M ≥ 40` and
`ε > 0`, eventually `K⁻² log m_{K,M} ≤ 8λ/M + ∫_3^M R(x)/x³ dx + I_out + ε`. -/
theorem prime_sum_bound_integrals {M : ℕ} (hM : 40 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (mKM n M : ℝ) / (K n : ℝ) ^ 2 ≤
      8 * (lam : ℝ) / M + (∫ x in (3 : ℝ)..M, innerR x / x ^ 3) + outerIntegral + ε := by
  have h3 : (0 : ℝ) < ε / 3 := div_pos hε (by norm_num)
  filter_upwards [(tendsto_crude_bound M).eventually_lt_const (lt_add_of_pos_right _ h3),
    (tendsto_inner_sum hM).eventually_lt_const (lt_add_of_pos_right _ h3),
    (tendsto_outer_sum (M := M) (by omega)).eventually_lt_const (lt_add_of_pos_right _ h3),
    eventually_ge_atTop 1] with n hc hi ho hn
  have hK2 : (0 : ℝ) < (K n : ℝ) ^ 2 := pow_pos (K_pos hn) 2
  have hcr := div_le_div_of_nonneg_right (crude_sum_le hn (by omega : 0 < M)) hK2.le
  rw [log_mKM_split (by omega : 3 ≤ M), add_div, add_div]
  linarith

/-- **Proposition 5.4** (90). For `M ∈ 40ℤ_{>0}` (`0 < M` and `40 ∣ M`), with `K = 40n` and the
normalization factor `m_{K,M}`, `lim sup_{n→∞} K⁻² log m_{K,M} ≤ A_M`: for every `ε > 0`,
`K⁻² log m_{K,M} ≤ A_M + ε` for all large `n`. -/
theorem prime_sum_bound {M : ℕ} (hM : 0 < M) (h40 : 40 ∣ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (mKM n M : ℝ) / (K n : ℝ) ^ 2 ≤ primeSumA M + ε := by
  have htail := integral_three_le hM h40
  have e : 9 * (lam : ℝ) / M = 8 * (lam : ℝ) / M + (lam : ℝ) / M := by ring
  filter_upwards [prime_sum_bound_integrals (Nat.le_of_dvd hM h40) hε] with n hn
  unfold primeSumA primeSumB0
  linarith

end ZetaSeven
