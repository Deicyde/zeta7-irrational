import ZetaSeven.InnerEstimate

/-!
# Inner limiting functions (paper Section 5.2, Definition 5.2, equations (64)-(70))

Prince Anand, "Zeta 7 is Irrational", Section 5.2. In the variable `x = K/p` the inner
exponents are approximated by the continuum-limit functions of Definition 5.2:

* (64) `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1` (`ellLim`), `b(x, z) = 4 ℓ(αx, z)` (`bLim`);
* (65) `T = ⌊2Hx⌋` (`TLim`), `s = Hx - T/2` (`sLim`), `q = ⌊2x⌋` (`qLim`),
  `n₊ = (2x - q)/2` (`nPlus`);
* (66) `Γ(x) = ∫_0^{1/2} (T - b)(T + b - ℓ - 7) dz + s(2T - q - 7) + (s - n₊)₊`
  (`innerGamma`, integrand `gammaIntegrand`);
* (67) `J(u) = m u - m(m+1)/4`, `m = ⌊2u⌋` (`innerJ`);
* (68) `N(x) = 2λx⌊x⌋ - 16λx⌊αx⌋ - 2J(λx)` (`innerN`);
* (69) `R(x) = -Γ(x) - N(x)` (`innerR`).

## Main results

* `gammaIntegrand_intervalIntegrable`: the integrand of (66) is interval integrable on
  `[0, 1/2]` for every `x`, so the integral in `Γ(x)` is a genuine Lebesgue integral.
* **(70), first formula** (`gammaIn_approx`): for each `M` there is `C` with
  `|γ^in_p - p Γ(K/p)| ≤ C` for all `n`, `p` in the inner range and every admissible choice of
  extra rows.
* **(70), second formula** (`padicValRat_SK_approx`): for each `M` there is `C` with
  `|v_p(S_K) - p N(K/p)| ≤ C` for all `n`, `p` in the inner range.

## Proof

For `1 ≤ a ≤ m` the class counts are `ℓ_K(a) = ℓ(x, a/p)` and `ℓ_N(a) = ℓ(αx, a/p)`
(`ell_eq_ellLim`). The weight sum over class `a` is then the integrand at `z = a/p`, and the sum
over the grid `a/p` differs from `p` times the integral by `O(1)` per cell on which one of the
four floors jumps; there are at most four such cells (`riemann_cells`). The extra rows go to the
classes with `ℓ_K = q + 1` first (`sum_mul_eq_min`), which produces `(s - n₊)₊`. The allocation
`T` of (45) is `⌊2Hx⌋` or `⌊2Hx⌋ - 1` (`allocT_eq`), and both cases cost `O_M(1)`
(`alloc_arith`). For `v_p(S_K)`, Legendre's formula with `p² > 2h` gives
`v_p(S_K) = 2h⌊K/p⌋ - 16h⌊N/p⌋ - 2 ∑_{i<h} ⌊2i/p⌋`, and
`0 ≤ p J(h/p) - ∑_{i<h} ⌊2i/p⌋ ≤ ⌊2h/p⌋` (`innerJ_sum_bounds`).
-/

namespace ZetaSeven

open Finset MeasureTheory

/-! ## Definition 5.2 -/

section Defs

/-- (64): `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`. -/
noncomputable def ellLim (x z : ℝ) : ℤ := ⌊x - z⌋ + ⌊x + z⌋ + 1

/-- (64): `b(x, z) = 4 ℓ(αx, z)`. -/
noncomputable def bLim (x z : ℝ) : ℤ := 4 * ellLim ((alpha : ℝ) * x) z

/-- (65): `T = ⌊2Hx⌋`. -/
noncomputable def TLim (x : ℝ) : ℤ := ⌊2 * (bigH : ℝ) * x⌋

/-- (65): `s = Hx - T/2`. -/
noncomputable def sLim (x : ℝ) : ℝ := (bigH : ℝ) * x - (TLim x : ℝ) / 2

/-- (65): `q = ⌊2x⌋`. -/
noncomputable def qLim (x : ℝ) : ℤ := ⌊2 * x⌋

/-- (65): `n₊ = (2x - q)/2`. -/
noncomputable def nPlus (x : ℝ) : ℝ := (2 * x - (qLim x : ℝ)) / 2

/-- The integrand of (66): `(T - b(x, z))(T + b(x, z) - ℓ(x, z) - 7)`. -/
noncomputable def gammaIntegrand (x z : ℝ) : ℝ :=
  ((TLim x : ℝ) - (bLim x z : ℝ)) * ((TLim x : ℝ) + (bLim x z : ℝ) - (ellLim x z : ℝ) - 7)

/-- (66): `Γ(x) = ∫_0^{1/2} (T - b(x,z))(T + b(x,z) - ℓ(x,z) - 7) dz + s(2T - q - 7)
+ (s - n₊)₊`. -/
noncomputable def innerGamma (x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z)
    + sLim x * (2 * (TLim x : ℝ) - (qLim x : ℝ) - 7) + max (sLim x - nPlus x) 0

/-- (67): `J(u) = m u - m(m+1)/4` with `m = ⌊2u⌋`. -/
noncomputable def innerJ (u : ℝ) : ℝ :=
  (⌊2 * u⌋ : ℝ) * u - (⌊2 * u⌋ : ℝ) * ((⌊2 * u⌋ : ℝ) + 1) / 4

/-- (68): `N(x) = 2λx⌊x⌋ - 16λx⌊αx⌋ - 2J(λx)`. -/
noncomputable def innerN (x : ℝ) : ℝ :=
  2 * (lam : ℝ) * x * (⌊x⌋ : ℝ) - 16 * (lam : ℝ) * x * (⌊(alpha : ℝ) * x⌋ : ℝ)
    - 2 * innerJ ((lam : ℝ) * x)

/-- (69): `R(x) = -Γ(x) - N(x)`. -/
noncomputable def innerR (x : ℝ) : ℝ := -innerGamma x - innerN x

theorem alpha_real : (alpha : ℝ) = 3 / 40 := by
  norm_num [alpha]

theorem lam_real : (lam : ℝ) = 37 / 40 := by
  norm_num [lam]

theorem bigH_real : (bigH : ℝ) = 49 / 40 := by
  norm_num [bigH]

end Defs

/-! ## Integrability of the integrand of (66) -/

section Integrable

theorem measurable_floor_cast {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable fun z => ((⌊g z⌋ : ℤ) : ℝ) :=
  (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp hg.floor

/-- The integrand of (66) written with the four floors `⌊x ∓ z⌋`, `⌊αx ∓ z⌋`. -/
theorem gammaIntegrand_eq (x z : ℝ) :
    gammaIntegrand x z =
      ((TLim x : ℝ) - 4 * ((⌊(alpha : ℝ) * x - z⌋ : ℝ) + (⌊(alpha : ℝ) * x + z⌋ : ℝ) + 1))
        * ((TLim x : ℝ) + 4 * ((⌊(alpha : ℝ) * x - z⌋ : ℝ) + (⌊(alpha : ℝ) * x + z⌋ : ℝ) + 1)
          - ((⌊x - z⌋ : ℝ) + (⌊x + z⌋ : ℝ) + 1) - 7) := by
  simp only [gammaIntegrand, bLim, ellLim]
  push_cast
  ring

theorem measurable_gammaIntegrand (x : ℝ) : Measurable (gammaIntegrand x) := by
  have h1 : Measurable fun z : ℝ => ((⌊x - z⌋ : ℤ) : ℝ) :=
    measurable_floor_cast (measurable_const.sub measurable_id)
  have h2 : Measurable fun z : ℝ => ((⌊x + z⌋ : ℤ) : ℝ) :=
    measurable_floor_cast (measurable_const.add measurable_id)
  have h3 : Measurable fun z : ℝ => ((⌊(alpha : ℝ) * x - z⌋ : ℤ) : ℝ) :=
    measurable_floor_cast (measurable_const.sub measurable_id)
  have h4 : Measurable fun z : ℝ => ((⌊(alpha : ℝ) * x + z⌋ : ℤ) : ℝ) :=
    measurable_floor_cast (measurable_const.add measurable_id)
  have hb : Measurable fun z : ℝ =>
      4 * (((⌊(alpha : ℝ) * x - z⌋ : ℤ) : ℝ) + ((⌊(alpha : ℝ) * x + z⌋ : ℤ) : ℝ) + 1) :=
    measurable_const.mul ((h3.add h4).add measurable_const)
  have hl : Measurable fun z : ℝ => ((⌊x - z⌋ : ℤ) : ℝ) + ((⌊x + z⌋ : ℤ) : ℝ) + 1 :=
    (h1.add h2).add measurable_const
  have e : gammaIntegrand x = fun z =>
      ((TLim x : ℝ) - 4 * (((⌊(alpha : ℝ) * x - z⌋ : ℤ) : ℝ)
          + ((⌊(alpha : ℝ) * x + z⌋ : ℤ) : ℝ) + 1))
        * ((TLim x : ℝ) + 4 * (((⌊(alpha : ℝ) * x - z⌋ : ℤ) : ℝ)
          + ((⌊(alpha : ℝ) * x + z⌋ : ℤ) : ℝ) + 1)
          - (((⌊x - z⌋ : ℤ) : ℝ) + ((⌊x + z⌋ : ℤ) : ℝ) + 1) - 7) := by
    funext z
    exact gammaIntegrand_eq x z
  rw [e]
  exact (measurable_const.sub hb).mul (((measurable_const.add hb).sub hl).sub measurable_const)

/-- A bound for the integrand of (66) on `0 ≤ z ≤ 1/2`. -/
theorem abs_gammaIntegrand_le (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    |gammaIntegrand x z|
      ≤ (|(TLim x : ℝ)| + 8 * |x| + 20) * (|(TLim x : ℝ)| + 10 * |x| + 32) := by
  have hfl : ∀ w : ℝ, |w| ≤ |x| →
      -(|x| + 2) ≤ ((⌊w - z⌋ : ℤ) : ℝ) ∧ ((⌊w - z⌋ : ℤ) : ℝ) ≤ |x| + 2 ∧
      -(|x| + 2) ≤ ((⌊w + z⌋ : ℤ) : ℝ) ∧ ((⌊w + z⌋ : ℤ) : ℝ) ≤ |x| + 2 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    have h1 := Int.floor_le (w - z)
    have h2 := Int.lt_floor_add_one (w - z)
    have h3 := Int.floor_le (w + z)
    have h4 := Int.lt_floor_add_one (w + z)
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hαx : |(alpha : ℝ) * x| ≤ |x| := by
    rw [abs_mul, alpha_real, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 40)]
    have := abs_nonneg x
    linarith
  obtain ⟨a1, a2, a3, a4⟩ := hfl x le_rfl
  obtain ⟨b1, b2, b3, b4⟩ := hfl _ hαx
  have hT1 := neg_abs_le (TLim x : ℝ)
  have hT2 := le_abs_self (TLim x : ℝ)
  have hx0 := abs_nonneg x
  have hT0 := abs_nonneg (TLim x : ℝ)
  rw [gammaIntegrand_eq, abs_mul]
  apply mul_le_mul
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · exact abs_nonneg _
  · linarith

/-- The integrand of (66) is interval integrable on `[0, 1/2]` for every `x`: it is
measurable and bounded there. -/
theorem gammaIntegrand_intervalIntegrable (x : ℝ) :
    IntervalIntegrable (gammaIntegrand x) volume 0 (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine Measure.integrableOn_of_bounded
    (M := (|(TLim x : ℝ)| + 8 * |x| + 20) * (|(TLim x : ℝ)| + 10 * |x| + 32))
    measure_Ioc_lt_top.ne (measurable_gammaIntegrand x).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => ?_
  rw [Real.norm_eq_abs]
  exact abs_gammaIntegrand_le x z hz.1.le hz.2

end Integrable

/-! ## Grid sums against integrals -/

section Riemann

/-- Compare the grid sum `∑_{k<m} φ((k+1)/p)` with `p ∫_0^{1/2} φ` when `p = 2m + 1` and
`|φ| ≤ B` on `[0, 1/2]`: a cell `(k/p, (k+1)/p]` on which `φ` is constant contributes nothing,
any other cell at most `2B`, and the last half cell `(m/p, 1/2]` at most `B`. -/
theorem riemann_cells {φ : ℝ → ℝ} {m p : ℕ} (hp : 2 * m + 1 = p) {B : ℝ}
    (hB : ∀ z, 0 ≤ z → z ≤ 1 / 2 → |φ z| ≤ B)
    (hint : IntervalIntegrable φ volume 0 (1 / 2)) (S : Finset ℕ)
    (hS : ∀ k < m, k ∉ S → ∀ z, (k : ℝ) / p < z → z ≤ ((k : ℝ) + 1) / p →
      φ z = φ (((k : ℝ) + 1) / p)) :
    |∑ k ∈ range m, φ (((k : ℝ) + 1) / p) - p * ∫ z in (0 : ℝ)..(1 / 2), φ z|
      ≤ (2 * S.card + 1) * B := by
  have hpR : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpm : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hp.symm
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 le_rfl (by norm_num))
  have hc0 : ∀ k : ℕ, 0 ≤ (k : ℝ) / p := fun k => by positivity
  have hcm : ∀ k : ℕ, k ≤ m → (k : ℝ) / p ≤ 1 / 2 := by
    intro k hk
    have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
    rw [div_le_iff₀ hpR]
    linarith
  have hcell_int : ∀ k < m,
      IntervalIntegrable φ volume ((k : ℝ) / p) (((k + 1 : ℕ) : ℝ) / p) := by
    intro k hk
    refine hint.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨hc0 k, hcm k hk.le⟩
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨hc0 (k + 1), hcm (k + 1) hk⟩
  have htail_int : IntervalIntegrable φ volume ((m : ℝ) / p) (1 / 2) := by
    refine hint.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨hc0 m, hcm m le_rfl⟩
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨by norm_num, le_rfl⟩
  have hhead_int : IntervalIntegrable φ volume 0 ((m : ℝ) / p) := by
    refine hint.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨le_rfl, by norm_num⟩
    · rw [Set.uIcc_of_le (by norm_num)]; exact ⟨hc0 m, hcm m le_rfl⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / p) hcell_int
  simp only [Nat.cast_zero, zero_div] at hsum
  have hsplit : ∫ z in (0 : ℝ)..(1 / 2), φ z
      = ∑ k ∈ range m, (∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z)
        + ∫ z in ((m : ℝ) / p)..(1 / 2), φ z := by
    rw [hsum, intervalIntegral.integral_add_adjacent_intervals hhead_int htail_int]
  have hcell : ∀ k ∈ range m,
      |φ (((k : ℝ) + 1) / p) - p * ∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z|
        ≤ if k ∈ S then 2 * B else 0 := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := Nat.cast_succ k
    rw [hcast]
    have hle : (k : ℝ) / p ≤ ((k : ℝ) + 1) / p :=
      (div_le_div_iff_of_pos_right hpR).mpr (by linarith)
    have hlen : ((k : ℝ) + 1) / p - (k : ℝ) / p = 1 / p := by ring
    have hk1 : ((k : ℝ) + 1) / p ≤ 1 / 2 := by
      have := hcm (k + 1) hk'
      push_cast at this
      exact this
    split_ifs with hkS
    · have hv : |φ (((k : ℝ) + 1) / p)| ≤ B := hB _ (by positivity) hk1
      have hI : ‖∫ z in ((k : ℝ) / p)..(((k : ℝ) + 1) / p), φ z‖
          ≤ B * |((k : ℝ) + 1) / p - (k : ℝ) / p| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro z hz
        rw [Set.uIoc_of_le hle] at hz
        rw [Real.norm_eq_abs]
        exact hB z (by linarith [hz.1, hc0 k]) (by linarith [hz.2])
      rw [Real.norm_eq_abs, hlen, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)] at hI
      have hpI : |(p : ℝ) * ∫ z in ((k : ℝ) / p)..(((k : ℝ) + 1) / p), φ z| ≤ B := by
        rw [abs_mul, abs_of_pos hpR]
        calc (p : ℝ) * |∫ z in ((k : ℝ) / p)..(((k : ℝ) + 1) / p), φ z|
            ≤ p * (B * (1 / p)) := mul_le_mul_of_nonneg_left hI hpR.le
          _ = B := by rw [mul_comm B, ← mul_assoc, mul_one_div_cancel hpR.ne', one_mul]
      obtain ⟨hv1, hv2⟩ := abs_le.mp hv
      obtain ⟨hp1, hp2⟩ := abs_le.mp hpI
      rw [abs_le]
      constructor <;> linarith
    · have hconst : ∫ z in ((k : ℝ) / p)..(((k : ℝ) + 1) / p), φ z
          = ∫ z in ((k : ℝ) / p)..(((k : ℝ) + 1) / p), φ (((k : ℝ) + 1) / p) := by
        apply intervalIntegral.integral_congr_ae
        refine Filter.Eventually.of_forall fun z hz => ?_
        rw [Set.uIoc_of_le hle] at hz
        exact hS k hk' hkS z hz.1 hz.2
      rw [hconst, intervalIntegral.integral_const, smul_eq_mul, hlen, ← mul_assoc,
        mul_one_div_cancel hpR.ne', one_mul]
      simp
  have htail : |(p : ℝ) * ∫ z in ((m : ℝ) / p)..(1 / 2), φ z| ≤ B := by
    have hle : (m : ℝ) / p ≤ 1 / 2 := hcm m le_rfl
    have hI : ‖∫ z in ((m : ℝ) / p)..(1 / 2), φ z‖ ≤ B * |1 / 2 - (m : ℝ) / p| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro z hz
      rw [Set.uIoc_of_le hle] at hz
      rw [Real.norm_eq_abs]
      exact hB z (by linarith [hz.1, hc0 m]) hz.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - (m : ℝ) / p)] at hI
    have hpm' : (p : ℝ) * ((m : ℝ) / p) = m := mul_div_cancel₀ _ hpR.ne'
    rw [abs_mul, abs_of_pos hpR]
    have h2 : (p : ℝ) * |∫ z in ((m : ℝ) / p)..(1 / 2), φ z|
        ≤ p * (B * (1 / 2 - (m : ℝ) / p)) := mul_le_mul_of_nonneg_left hI hpR.le
    have h3 : (p : ℝ) * (B * (1 / 2 - (m : ℝ) / p)) = B / 2 := by
      have e : (p : ℝ) * (B * (1 / 2 - (m : ℝ) / p)) = B * (p / 2 - p * ((m : ℝ) / p)) := by
        ring
      rw [e, hpm', hpm]
      ring
    linarith
  rw [hsplit, mul_add, Finset.mul_sum]
  have hrw : ∑ k ∈ range m, φ (((k : ℝ) + 1) / p)
      - (∑ k ∈ range m, (p : ℝ) * ∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z
        + (p : ℝ) * ∫ z in ((m : ℝ) / p)..(1 / 2), φ z)
      = ∑ k ∈ range m, (φ (((k : ℝ) + 1) / p)
          - (p : ℝ) * ∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z)
        - (p : ℝ) * ∫ z in ((m : ℝ) / p)..(1 / 2), φ z := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrw]
  have hsum_le : |∑ k ∈ range m, (φ (((k : ℝ) + 1) / p)
      - (p : ℝ) * ∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z)| ≤ 2 * S.card * B := by
    calc _ ≤ ∑ k ∈ range m, |φ (((k : ℝ) + 1) / p)
            - (p : ℝ) * ∫ z in ((k : ℝ) / p)..(((k + 1 : ℕ) : ℝ) / p), φ z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range m, (if k ∈ S then 2 * B else 0) := Finset.sum_le_sum hcell
      _ = ∑ k ∈ range m ∩ S, 2 * B := Finset.sum_ite_mem _ _ _
      _ = ((range m ∩ S).card : ℝ) * (2 * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) * (2 * B) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      _ = 2 * S.card * B := by ring
  obtain ⟨h1, h2⟩ := abs_le.mp hsum_le
  obtain ⟨h3, h4⟩ := abs_le.mp htail
  rw [abs_le]
  constructor <;> linarith

open Classical in
/-- The cells `(k/p, (k+1)/p]`, `k < m`, on which `F` is not constant. -/
noncomputable def badCells (m p : ℕ) (F : ℝ → ℤ) : Finset ℕ :=
  (range m).filter fun k =>
    ∃ z : ℝ, (k : ℝ) / p < z ∧ z ≤ ((k : ℝ) + 1) / p ∧ F z ≠ F (((k : ℝ) + 1) / p)

theorem eq_of_not_mem_badCells {m p : ℕ} {F : ℝ → ℤ} {k : ℕ} (hk : k < m)
    (hkS : k ∉ badCells m p F) {z : ℝ} (hz1 : (k : ℝ) / p < z)
    (hz2 : z ≤ ((k : ℝ) + 1) / p) : F z = F (((k : ℝ) + 1) / p) := by
  by_contra hne
  exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, z, hz1, hz2, hne⟩)

/-- `z ↦ ⌊y + z⌋` jumps on at most one cell of `(0, 1/2]`. -/
theorem card_badCells_floor_add_le {m p : ℕ} (hp : 2 * m + 1 = p) (y : ℝ) :
    (badCells m p fun z => ⌊y + z⌋).card ≤ 1 := by
  have hpR : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpm : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hp.symm
  have key : ∀ k ∈ badCells m p (fun z => ⌊y + z⌋), ∃ j : ℤ,
      (k : ℝ) / p < (j : ℝ) - y ∧ (j : ℝ) - y ≤ ((k : ℝ) + 1) / p ∧
        ((k : ℝ) + 1) / p ≤ 1 / 2 := by
    intro k hk
    obtain ⟨hkm, z, hz1, hz2, hne⟩ := Finset.mem_filter.mp hk
    have hkm' : (k : ℝ) + 1 ≤ m := by
      have := Nat.succ_le_of_lt (Finset.mem_range.mp hkm)
      exact_mod_cast this
    have hne' : ⌊y + z⌋ ≠ ⌊y + ((k : ℝ) + 1) / p⌋ := hne
    refine ⟨⌊y + ((k : ℝ) + 1) / p⌋, ?_, ?_, ?_⟩
    · have hle : ⌊y + z⌋ ≤ ⌊y + ((k : ℝ) + 1) / p⌋ := Int.floor_mono (by linarith)
      have hlt : ⌊y + z⌋ < ⌊y + ((k : ℝ) + 1) / p⌋ := lt_of_le_of_ne hle hne'
      have := Int.floor_lt.mp hlt
      linarith
    · have := Int.floor_le (y + ((k : ℝ) + 1) / p)
      linarith
    · rw [div_le_iff₀ hpR]
      linarith
  rw [Finset.card_le_one]
  intro k₁ h₁ k₂ h₂
  obtain ⟨j₁, a1, b1, c1⟩ := key k₁ h₁
  obtain ⟨j₂, a2, b2, c2⟩ := key k₂ h₂
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) / p := fun k => by positivity
  have hj : j₁ = j₂ := by
    have e1 : ((j₁ - j₂ : ℤ) : ℝ) < 1 := by push_cast; linarith [hk0 k₁, hk0 k₂]
    have e2 : (-1 : ℝ) < ((j₁ - j₂ : ℤ) : ℝ) := by push_cast; linarith [hk0 k₁, hk0 k₂]
    have e1' : j₁ - j₂ < 1 := by exact_mod_cast e1
    have e2' : -1 < j₁ - j₂ := by exact_mod_cast e2
    omega
  subst hj
  have l1 : (k₁ : ℝ) < k₂ + 1 :=
    (div_lt_div_iff_of_pos_right hpR).mp (lt_of_lt_of_le a1 b2)
  have l2 : (k₂ : ℝ) < k₁ + 1 :=
    (div_lt_div_iff_of_pos_right hpR).mp (lt_of_lt_of_le a2 b1)
  have l1' : k₁ < k₂ + 1 := by exact_mod_cast l1
  have l2' : k₂ < k₁ + 1 := by exact_mod_cast l2
  omega

/-- `z ↦ ⌊y - z⌋` jumps on at most one cell of `(0, 1/2]`. -/
theorem card_badCells_floor_sub_le {m p : ℕ} (hp : 2 * m + 1 = p) (y : ℝ) :
    (badCells m p fun z => ⌊y - z⌋).card ≤ 1 := by
  have hpR : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpm : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hp.symm
  have key : ∀ k ∈ badCells m p (fun z => ⌊y - z⌋), ∃ j : ℤ,
      (k : ℝ) / p < y - (j : ℝ) ∧ y - (j : ℝ) < ((k : ℝ) + 1) / p ∧
        ((k : ℝ) + 1) / p ≤ 1 / 2 := by
    intro k hk
    obtain ⟨hkm, z, hz1, hz2, hne⟩ := Finset.mem_filter.mp hk
    have hkm' : (k : ℝ) + 1 ≤ m := by
      have := Nat.succ_le_of_lt (Finset.mem_range.mp hkm)
      exact_mod_cast this
    have hne' : ⌊y - z⌋ ≠ ⌊y - ((k : ℝ) + 1) / p⌋ := hne
    refine ⟨⌊y - z⌋, ?_, ?_, ?_⟩
    · have := Int.floor_le (y - z)
      linarith
    · have hle : ⌊y - ((k : ℝ) + 1) / p⌋ ≤ ⌊y - z⌋ := Int.floor_mono (by linarith)
      have hlt : ⌊y - ((k : ℝ) + 1) / p⌋ < ⌊y - z⌋ := lt_of_le_of_ne hle (Ne.symm hne')
      have := Int.floor_lt.mp hlt
      linarith
    · rw [div_le_iff₀ hpR]
      linarith
  rw [Finset.card_le_one]
  intro k₁ h₁ k₂ h₂
  obtain ⟨j₁, a1, b1, c1⟩ := key k₁ h₁
  obtain ⟨j₂, a2, b2, c2⟩ := key k₂ h₂
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) / p := fun k => by positivity
  have hj : j₁ = j₂ := by
    have e1 : ((j₁ - j₂ : ℤ) : ℝ) < 1 := by push_cast; linarith [hk0 k₁, hk0 k₂]
    have e2 : (-1 : ℝ) < ((j₁ - j₂ : ℤ) : ℝ) := by push_cast; linarith [hk0 k₁, hk0 k₂]
    have e1' : j₁ - j₂ < 1 := by exact_mod_cast e1
    have e2' : -1 < j₁ - j₂ := by exact_mod_cast e2
    omega
  subst hj
  have l1 : (k₁ : ℝ) < k₂ + 1 :=
    (div_lt_div_iff_of_pos_right hpR).mp (lt_trans a1 b2)
  have l2 : (k₂ : ℝ) < k₁ + 1 :=
    (div_lt_div_iff_of_pos_right hpR).mp (lt_trans a2 b1)
  have l1' : k₁ < k₂ + 1 := by exact_mod_cast l1
  have l2' : k₂ < k₁ + 1 := by exact_mod_cast l2
  omega

end Riemann

/-! ## Class counts as floors -/

section Floors

/-- `⌊a/b⌋` of naturals is the natural quotient. -/
theorem floor_natCast_div (a b : ℕ) (hb : 0 < b) : ⌊(a : ℝ) / b⌋ = ((a / b : ℕ) : ℤ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (b : ℝ) * ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) = a := by
    exact_mod_cast Nat.div_add_mod a b
  have h2 : ((a % b : ℕ) : ℝ) + 1 ≤ b := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt a hb)
  have h3 : (0 : ℝ) ≤ ((a % b : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Int.floor_eq_iff, le_div_iff₀ hbR, div_lt_iff₀ hbR]
  push_cast
  constructor <;> linarith

/-- For `1 ≤ a ≤ m` the class count (43) is the floor count (64):
`ℓ_A(a) = ⌊A/p - a/p⌋ + ⌊A/p + a/p⌋ + 1 = ℓ(A/p, a/p)`. -/
theorem ell_eq_ellLim {p : ℕ} (hp : 2 * mHalf p + 1 = p) (A a : ℕ) (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) : (ell p A a : ℤ) = ellLim ((A : ℝ) / p) ((a : ℝ) / p) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [ell_eq_count hp A a ha1 ham]
  have hQr : (p : ℝ) * (((A + 1) / p : ℕ) : ℝ) + (((A + 1) % p : ℕ) : ℝ) = A + 1 := by
    exact_mod_cast Nat.div_add_mod (A + 1) p
  have hr : (((A + 1) % p : ℕ) : ℝ) + 1 ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt (A + 1) hp0)
  have hrp : (A + 1) % p < p := Nat.mod_lt (A + 1) hp0
  have hap : (a : ℝ) + 1 ≤ p := by
    have : a + 1 ≤ p := by omega
    exact_mod_cast this
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hr0 : (0 : ℝ) ≤ (((A + 1) % p : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize (A + 1) / p = Q at hQr ⊢
  generalize (A + 1) % p = r at hQr hr hr0 hrp ⊢
  have key1 : ⌊(A : ℝ) / p - (a : ℝ) / p⌋ = (Q : ℤ) - 1 + (if a < r then 1 else 0) := by
    rw [Int.floor_eq_iff, ← sub_div, le_div_iff₀ hpR, div_lt_iff₀ hpR]
    split_ifs with h
    · have h' : (a : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt h
      push_cast
      constructor <;> linarith
    · have h' : (r : ℝ) ≤ a := by exact_mod_cast not_lt.mp h
      push_cast
      constructor <;> linarith
  have key2 : ⌊(A : ℝ) / p + (a : ℝ) / p⌋ = (Q : ℤ) + (if p - a < r then 1 else 0) := by
    rw [Int.floor_eq_iff, ← add_div, le_div_iff₀ hpR, div_lt_iff₀ hpR]
    split_ifs with h
    · have h' : (p : ℝ) + 1 ≤ r + a := by
        have : p + 1 ≤ r + a := by omega
        exact_mod_cast this
      push_cast
      constructor <;> linarith
    · have h' : (r : ℝ) + a ≤ p := by
        have : r + a ≤ p := by omega
        exact_mod_cast this
      push_cast
      constructor <;> linarith
  rw [ellLim, key1, key2]
  push_cast
  split_ifs <;> ring

/-- `ℓ(x, z) ∈ {⌊2x⌋, ⌊2x⌋ + 1}`: indeed `⌊x - z⌋ + ⌊x + z⌋ ≤ 2x < ⌊x - z⌋ + ⌊x + z⌋ + 2`. -/
theorem ellLim_eq_qLim_or (x z : ℝ) : ellLim x z = qLim x ∨ ellLim x z = qLim x + 1 := by
  have h1 := Int.floor_le (x - z)
  have h2 := Int.lt_floor_add_one (x - z)
  have h3 := Int.floor_le (x + z)
  have h4 := Int.lt_floor_add_one (x + z)
  have h5 := Int.floor_le (2 * x)
  have h6 := Int.lt_floor_add_one (2 * x)
  have e1 : ⌊x - z⌋ + ⌊x + z⌋ < ⌊2 * x⌋ + 1 := by
    have : ((⌊x - z⌋ + ⌊x + z⌋ : ℤ) : ℝ) < ((⌊2 * x⌋ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have e2 : ⌊2 * x⌋ < ⌊x - z⌋ + ⌊x + z⌋ + 2 := by
    have : ((⌊2 * x⌋ : ℤ) : ℝ) < ((⌊x - z⌋ + ⌊x + z⌋ + 2 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  unfold ellLim qLim
  omega

end Floors

/-! ## Elementary bookkeeping -/

section Arith

theorem sum_range_two_mul_add (L : ℕ) (c : ℝ) :
    ∑ i ∈ range L, (2 * (i : ℝ) + c) = L * (L + c - 1) := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- If `e` and `d` take values in `{0, 1}` and `d` is at least as large on the support of `e`
as off it, then `∑ e_a d_a = min(∑ e_a, ∑ d_a)`: the extra rows sit on the classes with the
larger count first. -/
theorem sum_mul_eq_min {s : Finset ℕ} {e d : ℕ → ℝ} (he : ∀ a ∈ s, e a = 0 ∨ e a = 1)
    (hd : ∀ a ∈ s, d a = 0 ∨ d a = 1)
    (hmono : ∀ a ∈ s, ∀ b ∈ s, e a = 0 → e b = 1 → d a ≤ d b) :
    ∑ a ∈ s, e a * d a = min (∑ a ∈ s, e a) (∑ a ∈ s, d a) := by
  by_cases h : ∃ a ∈ s, d a = 1 ∧ e a = 0
  · obtain ⟨a, ha, hda, hea⟩ := h
    have hb : ∀ b ∈ s, e b * d b = e b ∧ e b ≤ d b := by
      intro b hb
      rcases he b hb with heb | heb
      · rw [heb, zero_mul]
        rcases hd b hb with hdb | hdb
        · rw [hdb]; exact ⟨rfl, le_rfl⟩
        · rw [hdb]; exact ⟨rfl, zero_le_one⟩
      · have hab := hmono a ha b hb hea heb
        rcases hd b hb with hdb | hdb
        · rw [hdb, hda] at hab
          norm_num at hab
        · rw [heb, hdb]
          exact ⟨one_mul 1, le_rfl⟩
    rw [Finset.sum_congr rfl fun b hb => (hb b hb).1,
      min_eq_left (Finset.sum_le_sum fun b hb => (hb b hb).2)]
  · push_neg at h
    have hb : ∀ b ∈ s, e b * d b = d b ∧ d b ≤ e b := by
      intro b hb
      rcases hd b hb with hdb | hdb
      · rw [hdb, mul_zero]
        rcases he b hb with heb | heb
        · rw [heb]; exact ⟨rfl, le_rfl⟩
        · rw [heb]; exact ⟨rfl, zero_le_one⟩
      · have hne := h b hb hdb
        rcases he b hb with heb | heb
        · exact absurd heb hne
        · rw [heb, hdb]
          exact ⟨one_mul 1, le_rfl⟩
    rw [Finset.sum_congr rfl fun b hb => (hb b hb).1,
      min_eq_right (Finset.sum_le_sum fun b hb => (hb b hb).2)]

/-- The allocation bookkeeping behind the first formula of (70), as pure real arithmetic.
Here `ΦT'` is the weight sum with `T' ∈ {T, T - 1}` rows per class, `E = mT' + E - mT'` the
number of extra rows, `μ = min(E, c₊)` the extra rows that land on the `c₊` classes with
`ℓ_K = q + 1`, and `PS = ps`, `PN = pn₊`, `ν = p(s - n₊)₊` the continuum counterparts. -/
theorem alloc_arith {m T T' E q cp PS PN Sl ΦT ΦT' μ ν δ δ' Δ1 Δ2 Δ3 γm : ℝ}
    (hγ : γm = ΦT' + E * (2 * T' - q - 7) + E - μ)
    (hμ1 : μ ≤ E) (hμ2 : μ ≤ cp) (hμ3 : μ = E ∨ μ = cp)
    (hν1 : 0 ≤ ν) (hν2 : PS - PN ≤ ν) (hν3 : ν = 0 ∨ ν = PS - PN)
    (hSl : Sl = m * q + cp) (hAlloc : m * T' + E = m * T + PS + δ) (hcp : cp - PN = δ')
    (hT : (T' = T ∧ ΦT' = ΦT) ∨ (T' = T - 1 ∧ ΦT' = ΦT - (m * (2 * T - 8) - Sl)))
    (hEm : E < m) (hcpm : cp ≤ m) (hPS : 0 ≤ PS) (hPN : 0 ≤ PN)
    (hδ : |δ| ≤ Δ1) (hδ' : |δ'| ≤ Δ2) (hX : |2 * T - q - 7| ≤ Δ3) :
    |γm - (ΦT + PS * (2 * T - q - 7) + ν)| ≤ Δ1 * (Δ3 + 8) + Δ2 := by
  have hΔ1 : 0 ≤ Δ1 := le_trans (abs_nonneg _) hδ
  have hΔ2 : 0 ≤ Δ2 := le_trans (abs_nonneg _) hδ'
  have hprod : |δ * (2 * T - q - 7)| ≤ Δ1 * Δ3 := by
    rw [abs_mul]
    exact mul_le_mul hδ hX (abs_nonneg _) hΔ1
  obtain ⟨hp1, hp2⟩ := abs_le.mp hprod
  obtain ⟨hd1, hd2⟩ := abs_le.mp hδ
  obtain ⟨hd'1, hd'2⟩ := abs_le.mp hδ'
  have hν4 : ν ≤ PS := by rcases hν3 with h | h <;> linarith
  rw [hγ, abs_le]
  rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩
  · subst hT1
    have hE : E = PS + δ := by linarith
    subst hE
    rw [hT2]
    rcases hμ3 with h1 | h1 <;> rcases hν3 with h2 | h2 <;> constructor <;> linarith
  · subst hT1
    have hE : E = PS + δ + m := by linarith
    subst hE
    rw [hT2, hSl]
    rcases hμ3 with h1 | h1 <;> rcases hν3 with h2 | h2 <;> constructor <;> linarith

end Arith

/-! ## The first formula of (70) -/

section GammaApprox

variable {n M p : ℕ} {ε : ℕ → ℕ}

/-- (49) split into the zero class and the classes `1 ≤ a ≤ m`; class `a` contributes
`∑_{i < L_a} 2w_{a,i} = L_a (L_a + 2b_a - ℓ_K(a) - 7)` with `L_a = T + ε_a - b_a`. -/
theorem gammaIn_split (hR : InnerRange n M p) [Fact p.Prime] :
    (gammaIn n M p ε : ℝ) = (∑ i ∈ range (L0 M), (weight2 n M p ε 0 i : ℝ))
      + ∑ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) + ε a - bA n p a)
          * ((allocT n M p : ℝ) + ε a + bA n p a - ell p (K n) a - 7) := by
  have hm := hR.two_mul_mHalf
  rw [gammaIn, Finset.sum_range_eq_add_Ico _ (by omega : 0 < mHalf p + 1),
    Finset.Ico_add_one_right_eq_Icc]
  push_cast
  have hL0 : allocL n M p ε 0 = L0 M := by rw [allocL, if_pos rfl]
  rw [hL0]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
  have hb := bA_lt_allocT hR ha1 ham
  have hL : allocL n M p ε a = allocT n M p + ε a - bA n p a := by
    rw [allocL, if_neg (by omega), allocZ]
  have hw : ∀ i, (weight2 n M p ε a i : ℝ)
      = 2 * (i : ℝ) + (8 * (ell p (N n) a : ℝ) - (ell p (K n) a : ℝ) - 6) := by
    intro i
    rw [weight2, if_neg (by omega)]
    push_cast
    ring
  simp only [hw]
  rw [sum_range_two_mul_add, hL, Nat.cast_sub (by omega)]
  push_cast [bA]
  ring

/-- The zero-class half-weights (48) are `O(M)`. -/
theorem abs_weight2_zero_le (hR : InnerRange n M p) [Fact p.Prime] {i : ℕ} (hi : i < L0 M) :
    |(weight2 n M p ε 0 i : ℝ)| ≤ 40 * M + 37 := by
  have hm := hR.two_mul_mHalf
  have hmK := hR.mK_lt
  have hmN := mN_le_mK n p
  have hKlt := hR.K_lt
  have hp := hR.p_gt
  have hell : ∀ c ∈ Icc 1 (mHalf p), ell p (K n) c ≤ 2 * M + 1 := by
    intro c hc
    obtain ⟨hc1, hcm⟩ := Finset.mem_Icc.mp hc
    have h1 := mul_ell_le hm (K n) c hc1 hcm
    by_contra hcon
    push_neg at hcon
    have h2 : p * (2 * M + 2) ≤ p * ell p (K n) c := Nat.mul_le_mul_left p hcon
    linarith
  have hupper : weight2 n M p ε 0 i ≤ 4 * (i : ℤ) + 16 * mN n p - 2 * mK n p + 1 := by
    rw [weight2, if_pos rfl]
    exact Finset.fold_min_le.mpr (Or.inl le_rfl)
  have hlower : -(2 * (M : ℤ) + 8) ≤ weight2 n M p ε 0 i := by
    rw [weight2, if_pos rfl]
    refine Finset.le_fold_min.mpr ⟨?_, fun c hc => ?_⟩
    · have : (mK n p : ℤ) < M := by exact_mod_cast hmK
      omega
    · have h1 := hell c hc
      have h2 : (ell p (K n) c : ℤ) ≤ 2 * M + 1 := by exact_mod_cast h1
      show -(2 * (M : ℤ) + 8) ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6
      omega
  have hi' : (i : ℤ) < 6 * M + 10 := by
    have : i < 6 * M + 10 := hi
    exact_mod_cast this
  have hmN' : (mN n p : ℤ) < M := by
    have := lt_of_le_of_lt hmN hmK
    exact_mod_cast this
  have hw1 : weight2 n M p ε 0 i ≤ 40 * M + 37 := by omega
  have hw2 : -(40 * (M : ℤ) + 37) ≤ weight2 n M p ε 0 i := by omega
  rw [abs_le]
  constructor
  · have : ((-(40 * (M : ℤ) + 37) : ℤ) : ℝ) ≤ (weight2 n M p ε 0 i : ℝ) := by exact_mod_cast hw2
    push_cast at this
    linarith
  · have : (weight2 n M p ε 0 i : ℝ) ≤ ((40 * (M : ℤ) + 37 : ℤ) : ℝ) := by exact_mod_cast hw1
    push_cast at this
    linarith

/-- The weight sum with `T = ⌊2Hx⌋` rows per class is the grid sum of the integrand of (66)
at `z = a/p`, so it is `p ∫_0^{1/2}` of the integrand up to `O_M(1)`. -/
theorem gammaRiemann (hR : InnerRange n M p) [Fact p.Prime] {x : ℝ}
    (hx : x = (K n : ℝ) / p) :
    |∑ a ∈ Icc 1 (mHalf p), ((TLim x : ℝ) - bA n p a)
        * ((TLim x : ℝ) + bA n p a - ell p (K n) a - 7)
      - p * ∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z|
      ≤ 9 * ((11 * M + 20) * (13 * M + 32)) := by
  have hm := hR.two_mul_mHalf
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hx3 : 3 ≤ x := by
    rw [hx, le_div_iff₀ hpR]
    exact_mod_cast hR.three_mul_le
  have hxM : x < M := by
    rw [hx, div_lt_iff₀ hpR]
    exact_mod_cast hR.K_lt
  have hαx : (alpha : ℝ) * x = (N n : ℝ) / p := by
    rw [hx, alpha_real]
    simp only [K, N]
    push_cast
    ring
  have hterm : ∀ a ∈ Icc 1 (mHalf p), ((TLim x : ℝ) - bA n p a)
      * ((TLim x : ℝ) + bA n p a - ell p (K n) a - 7) = gammaIntegrand x ((a : ℝ) / p) := by
    intro a ha
    obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
    have h1 : (ell p (K n) a : ℝ) = (ellLim x ((a : ℝ) / p) : ℝ) := by
      rw [hx]
      exact_mod_cast ell_eq_ellLim hm (K n) a ha1 ham
    have h2 : (bA n p a : ℝ) = (bLim x ((a : ℝ) / p) : ℝ) := by
      have e := ell_eq_ellLim hm (N n) a ha1 ham
      rw [bLim, hαx, ← e, bA]
      push_cast
    rw [gammaIntegrand, h1, h2]
  rw [Finset.sum_congr rfl hterm]
  have hre : ∑ a ∈ Icc 1 (mHalf p), gammaIntegrand x ((a : ℝ) / p)
      = ∑ k ∈ range (mHalf p), gammaIntegrand x (((k : ℝ) + 1) / p) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    push_cast
    ring
  rw [hre]
  have hT0 : (0 : ℝ) ≤ (TLim x : ℝ) := by
    have : (0 : ℤ) ≤ ⌊2 * (bigH : ℝ) * x⌋ :=
      Int.floor_nonneg.mpr (by rw [bigH_real]; linarith)
    exact_mod_cast this
  have hTle : (TLim x : ℝ) ≤ 2 * (bigH : ℝ) * x := Int.floor_le (2 * (bigH : ℝ) * x)
  rw [bigH_real] at hTle
  have hB : ∀ z, 0 ≤ z → z ≤ 1 / 2 →
      |gammaIntegrand x z| ≤ (11 * M + 20) * (13 * M + 32) := by
    intro z hz0 hz1
    refine le_trans (abs_gammaIntegrand_le x z hz0 hz1) ?_
    rw [abs_of_nonneg hT0, abs_of_pos (by linarith : (0 : ℝ) < x)]
    apply mul_le_mul <;> linarith
  set S := badCells (mHalf p) p (fun z => ⌊x + z⌋) ∪ badCells (mHalf p) p (fun z => ⌊x - z⌋)
    ∪ badCells (mHalf p) p (fun z => ⌊(alpha : ℝ) * x + z⌋)
    ∪ badCells (mHalf p) p (fun z => ⌊(alpha : ℝ) * x - z⌋) with hS
  have hcard : S.card ≤ 4 := by
    have h1 := card_badCells_floor_add_le hm x
    have h2 := card_badCells_floor_sub_le hm x
    have h3 := card_badCells_floor_add_le hm ((alpha : ℝ) * x)
    have h4 := card_badCells_floor_sub_le hm ((alpha : ℝ) * x)
    have u1 := Finset.card_union_le (badCells (mHalf p) p (fun z => ⌊x + z⌋)
      ∪ badCells (mHalf p) p (fun z => ⌊x - z⌋)
      ∪ badCells (mHalf p) p (fun z => ⌊(alpha : ℝ) * x + z⌋))
      (badCells (mHalf p) p (fun z => ⌊(alpha : ℝ) * x - z⌋))
    have u2 := Finset.card_union_le (badCells (mHalf p) p (fun z => ⌊x + z⌋)
      ∪ badCells (mHalf p) p (fun z => ⌊x - z⌋))
      (badCells (mHalf p) p (fun z => ⌊(alpha : ℝ) * x + z⌋))
    have u3 := Finset.card_union_le (badCells (mHalf p) p (fun z => ⌊x + z⌋))
      (badCells (mHalf p) p (fun z => ⌊x - z⌋))
    rw [hS]
    omega
  have hgood : ∀ k < mHalf p, k ∉ S → ∀ z, (k : ℝ) / p < z → z ≤ ((k : ℝ) + 1) / p →
      gammaIntegrand x z = gammaIntegrand x (((k : ℝ) + 1) / p) := by
    intro k hk hkS z hz1 hz2
    rw [hS] at hkS
    simp only [Finset.mem_union, not_or] at hkS
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hkS
    have e1 : ⌊x + z⌋ = ⌊x + ((k : ℝ) + 1) / p⌋ := eq_of_not_mem_badCells hk h1 hz1 hz2
    have e2 : ⌊x - z⌋ = ⌊x - ((k : ℝ) + 1) / p⌋ := eq_of_not_mem_badCells hk h2 hz1 hz2
    have e3 : ⌊(alpha : ℝ) * x + z⌋ = ⌊(alpha : ℝ) * x + ((k : ℝ) + 1) / p⌋ :=
      eq_of_not_mem_badCells hk h3 hz1 hz2
    have e4 : ⌊(alpha : ℝ) * x - z⌋ = ⌊(alpha : ℝ) * x - ((k : ℝ) + 1) / p⌋ :=
      eq_of_not_mem_badCells hk h4 hz1 hz2
    rw [gammaIntegrand_eq, gammaIntegrand_eq, e1, e2, e3, e4]
  have key := riemann_cells hm hB (gammaIntegrand_intervalIntegrable x) S hgood
  have hB0 : (0 : ℝ) ≤ (11 * M + 20) * (13 * M + 32) := by positivity
  have hc4 : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  calc _ ≤ (2 * S.card + 1) * ((11 * M + 20) * (13 * M + 32)) := key
    _ ≤ 9 * ((11 * M + 20) * (13 * M + 32)) := by
      apply mul_le_mul_of_nonneg_right _ hB0
      linarith

/-- The allocation `T` of (45) is `⌊2Hx⌋` or `⌊2Hx⌋ - 1`, with `x = K/p`. -/
theorem allocT_eq (hR : InnerRange n M p) [Fact p.Prime] {x : ℝ} (hx : x = (K n : ℝ) / p) :
    (allocT n M p : ℤ) = TLim x ∨ (allocT n M p : ℤ) = TLim x - 1 := by
  have hm := hR.two_mul_mHalf
  have hp := hR.p_gt
  have hM := hR.forty_le
  have hTlt := allocT_lt hR
  have hmK := hR.mK_lt
  have hmN := mN_le_mK n p
  have hE := (alloc_eq hR).2
  have hdm : mHalf p * allocT n M p + allocE n M p = allocTotal n M p :=
    Nat.div_add_mod (allocTotal n M p) (mHalf p)
  have htot := hR.allocTotal_eq
  have hpR : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hmR : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by exact_mod_cast hm.symm
  have hdmR : (mHalf p : ℝ) * (allocT n M p : ℝ) + (allocE n M p : ℝ)
      = (allocTotal n M p : ℝ) := by exact_mod_cast hdm
  have htotR : (allocTotal n M p : ℝ) + (6 * M + 10) + 4 * (mN n p : ℝ) = 49 * n := by
    have h : (allocTotal n M p : ℝ) + (L0 M : ℝ) + 4 * (mN n p : ℝ)
        = (hDim n : ℝ) + 4 * (N n : ℝ) := by exact_mod_cast htot
    simp only [L0, hDim, N] at h
    push_cast at h
    linarith
  have hER : (allocE n M p : ℝ) + 1 ≤ mHalf p := by exact_mod_cast Nat.succ_le_of_lt hE
  have hTR : (allocT n M p : ℝ) + 1 ≤ 3 * M := by exact_mod_cast Nat.succ_le_of_lt hTlt
  have hpMR : 200 * (M : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hmNR : (mN n p : ℝ) + 1 ≤ M := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt hmN hmK)
  have hE0 : (0 : ℝ) ≤ allocE n M p := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ allocT n M p := Nat.cast_nonneg _
  have hmN0 : (0 : ℝ) ≤ mN n p := Nat.cast_nonneg _
  have h2Hx : 2 * (bigH : ℝ) * x = 98 * n / p := by
    rw [hx, bigH_real]
    simp only [K]
    push_cast
    ring
  have hup : (allocT n M p : ℝ) ≤ 2 * (bigH : ℝ) * x := by
    rw [h2Hx, le_div_iff₀ hpR, hmR]
    linarith
  have hlo : 2 * (bigH : ℝ) * x < (allocT n M p : ℝ) + 2 := by
    rw [h2Hx, div_lt_iff₀ hpR, hmR]
    linarith
  have h1 : (allocT n M p : ℤ) ≤ ⌊2 * (bigH : ℝ) * x⌋ := Int.le_floor.mpr (by exact_mod_cast hup)
  have h2 : ⌊2 * (bigH : ℝ) * x⌋ < (allocT n M p : ℤ) + 2 :=
    Int.floor_lt.mpr (by exact_mod_cast hlo)
  unfold TLim
  omega

/-- **Equation (70), first formula.** For fixed `M`, uniformly in the inner range
`K/M < p ≤ K/3` (`K = 40n ≥ 200M²`, `M ≥ 40`) and for every admissible choice of extra rows,
`γ^in_p = p Γ(K/p) + O_M(1)`. -/
theorem gammaIn_approx (M : ℕ) : ∃ C : ℝ, ∀ (n p : ℕ) (ε : ℕ → ℕ), p.Prime →
    InnerRange n M p → ExtraRows n M p ε →
      |(gammaIn n M p ε : ℝ) - p * innerGamma ((K n : ℝ) / p)| ≤ C := by
  refine ⟨(6 * M + 10) * (40 * M + 37) + 9 * ((11 * M + 20) * (13 * M + 32))
    + ((12 * M + 10) * ((7 * M + 7) + 8) + 2 * M), fun n p ε hp hR hε => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (K n : ℝ) / p := ⟨_, rfl⟩
  rw [← hx]
  have hm := hR.two_mul_mHalf
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpm : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by exact_mod_cast hm.symm
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hR.forty_le
  have hmK : (mK n p : ℝ) + 1 ≤ M := by exact_mod_cast Nat.succ_le_of_lt hR.mK_lt
  have hmN : (mN n p : ℝ) ≤ mK n p := by exact_mod_cast mN_le_mK n p
  have hmN0 : (0 : ℝ) ≤ mN n p := Nat.cast_nonneg _
  have hmK0 : (0 : ℝ) ≤ mK n p := Nat.cast_nonneg _
  have hx3 : 3 ≤ x := by
    rw [hx, le_div_iff₀ hpR]
    exact_mod_cast hR.three_mul_le
  have hxM : x < M := by
    rw [hx, div_lt_iff₀ hpR]
    exact_mod_cast hR.K_lt
  have hpx : (p : ℝ) * x = 40 * n := by
    rw [hx, mul_div_cancel₀ _ hpR.ne']
    simp only [K]
    push_cast
  -- `T = ⌊2Hx⌋` and `q = ⌊2x⌋`
  have hT0 : (0 : ℝ) ≤ (TLim x : ℝ) := by
    have : (0 : ℤ) ≤ ⌊2 * (bigH : ℝ) * x⌋ :=
      Int.floor_nonneg.mpr (by rw [bigH_real]; linarith)
    exact_mod_cast this
  have hTle : (TLim x : ℝ) ≤ 2 * (bigH : ℝ) * x := Int.floor_le (2 * (bigH : ℝ) * x)
  rw [bigH_real] at hTle
  have hq0 : (0 : ℝ) ≤ (qLim x : ℝ) := by
    have : (0 : ℤ) ≤ ⌊2 * x⌋ := Int.floor_nonneg.mpr (by linarith)
    exact_mod_cast this
  have hqle : (qLim x : ℝ) ≤ 2 * x := Int.floor_le (2 * x)
  -- the zero class
  have hW0 : |∑ i ∈ range (L0 M), (weight2 n M p ε 0 i : ℝ)|
      ≤ (6 * M + 10) * (40 * M + 37) := by
    calc _ ≤ ∑ i ∈ range (L0 M), |(weight2 n M p ε 0 i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (L0 M), (40 * (M : ℝ) + 37) :=
          Finset.sum_le_sum fun i hi => abs_weight2_zero_le hR (Finset.mem_range.mp hi)
      _ = (6 * M + 10) * (40 * M + 37) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp [L0]
  -- the weight sum with `T = ⌊2Hx⌋` rows per class
  have hriem := gammaRiemann hR hx
  -- class counts: `ℓ_K(a) - q ∈ {0, 1}`
  have hd01 : ∀ a ∈ Icc 1 (mHalf p),
      (ell p (K n) a : ℝ) - qLim x = 0 ∨ (ell p (K n) a : ℝ) - qLim x = 1 := by
    intro a ha
    obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
    have e : (ell p (K n) a : ℤ) = ellLim x ((a : ℝ) / p) := by
      rw [hx]
      exact ell_eq_ellLim hm (K n) a ha1 ham
    rcases ellLim_eq_qLim_or x ((a : ℝ) / p) with h | h
    · left
      have h' : (ell p (K n) a : ℝ) = (qLim x : ℝ) := by
        have : (ell p (K n) a : ℤ) = qLim x := by rw [e, h]
        exact_mod_cast this
      linarith
    · right
      have h' : (ell p (K n) a : ℝ) = (qLim x : ℝ) + 1 := by
        have : (ell p (K n) a : ℤ) = qLim x + 1 := by rw [e, h]
        exact_mod_cast this
      linarith
  have hcard : ((Icc 1 (mHalf p)).card : ℝ) = mHalf p := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hSl : ∑ a ∈ Icc 1 (mHalf p), (ell p (K n) a : ℝ) = (K n : ℝ) - (mK n p : ℝ) := by
    have h := sum_ell hm (K n)
    have h' : ((∑ a ∈ Icc 1 (mHalf p), ell p (K n) a : ℕ) : ℝ) = ((K n - K n / p : ℕ) : ℝ) := by
      rw [h]
    push_cast at h'
    rw [h', Nat.cast_sub (Nat.div_le_self _ _)]
    rfl
  have hcpdef : ∑ a ∈ Icc 1 (mHalf p), ((ell p (K n) a : ℝ) - qLim x)
      = ∑ a ∈ Icc 1 (mHalf p), (ell p (K n) a : ℝ) - (mHalf p : ℝ) * qLim x := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  have hcpm : ∑ a ∈ Icc 1 (mHalf p), ((ell p (K n) a : ℝ) - qLim x) ≤ mHalf p := by
    calc _ ≤ ∑ a ∈ Icc 1 (mHalf p), (1 : ℝ) :=
          Finset.sum_le_sum fun a ha => by rcases hd01 a ha with h | h <;> linarith
      _ = mHalf p := by rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_one]
  -- the extra rows
  have hsumε : ∑ a ∈ Icc 1 (mHalf p), (ε a : ℝ) = allocE n M p := by
    exact_mod_cast sum_eps hε
  have hεsq : ∀ a ∈ Icc 1 (mHalf p), (ε a : ℝ) * ε a = ε a := by
    intro a ha
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hε.le_one a ha) with h | h <;> simp [h]
  have hmin : ∑ a ∈ Icc 1 (mHalf p), (ε a : ℝ) * ((ell p (K n) a : ℝ) - qLim x)
      = min (allocE n M p : ℝ) (∑ a ∈ Icc 1 (mHalf p), ((ell p (K n) a : ℝ) - qLim x)) := by
    rw [← hsumε]
    refine sum_mul_eq_min (e := fun a => (ε a : ℝ))
      (d := fun a => (ell p (K n) a : ℝ) - qLim x) ?_ hd01 ?_
    · intro a ha
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hε.le_one a ha) with h | h <;> simp [h]
    · intro a ha b hb hea heb
      have hea0 : ((ε a : ℕ) : ℝ) = 0 := hea
      have heb0 : ((ε b : ℕ) : ℝ) = 1 := heb
      have hea' : ε a = 0 := by exact_mod_cast hea0
      have heb' : ε b = 1 := by exact_mod_cast heb0
      have h1 := hε.mono a ha b hb hea' heb'
      have h2 : (ell p (K n) a : ℝ) ≤ ell p (K n) b := by exact_mod_cast h1
      show (ell p (K n) a : ℝ) - qLim x ≤ (ell p (K n) b : ℝ) - qLim x
      linarith
  have hγm : ∑ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) + ε a - bA n p a)
        * ((allocT n M p : ℝ) + ε a + bA n p a - ell p (K n) a - 7)
      = ∑ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) - bA n p a)
          * ((allocT n M p : ℝ) + bA n p a - ell p (K n) a - 7)
        + (allocE n M p : ℝ) * (2 * (allocT n M p : ℝ) - qLim x - 7) + (allocE n M p : ℝ)
        - ∑ a ∈ Icc 1 (mHalf p), (ε a : ℝ) * ((ell p (K n) a : ℝ) - qLim x) := by
    have e1 : ∀ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) + ε a - bA n p a)
        * ((allocT n M p : ℝ) + ε a + bA n p a - ell p (K n) a - 7)
        = ((allocT n M p : ℝ) - bA n p a) * ((allocT n M p : ℝ) + bA n p a - ell p (K n) a - 7)
          + (2 * (allocT n M p : ℝ) - qLim x - 7) * ε a + ε a
          - (ε a : ℝ) * ((ell p (K n) a : ℝ) - qLim x) := by
      intro a ha
      linear_combination hεsq a ha
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hsumε]
    ring
  -- `T` versus `⌊2Hx⌋`
  have hΦ : ∀ t : ℝ, ∑ a ∈ Icc 1 (mHalf p), ((t - 1) - bA n p a)
        * ((t - 1) + bA n p a - ell p (K n) a - 7)
      = ∑ a ∈ Icc 1 (mHalf p), (t - bA n p a) * (t + bA n p a - ell p (K n) a - 7)
        - ((mHalf p : ℝ) * (2 * t - 8) - ∑ a ∈ Icc 1 (mHalf p), (ell p (K n) a : ℝ)) := by
    intro t
    have e1 : ∀ a ∈ Icc 1 (mHalf p), ((t - 1) - bA n p a)
        * ((t - 1) + bA n p a - ell p (K n) a - 7)
        = (t - bA n p a) * (t + bA n p a - ell p (K n) a - 7) - (2 * t - 8)
          + (ell p (K n) a : ℝ) := fun a _ => by ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  have hT : ((allocT n M p : ℝ) = TLim x ∧
        ∑ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) - bA n p a)
          * ((allocT n M p : ℝ) + bA n p a - ell p (K n) a - 7)
        = ∑ a ∈ Icc 1 (mHalf p), ((TLim x : ℝ) - bA n p a)
          * ((TLim x : ℝ) + bA n p a - ell p (K n) a - 7)) ∨
      ((allocT n M p : ℝ) = TLim x - 1 ∧
        ∑ a ∈ Icc 1 (mHalf p), ((allocT n M p : ℝ) - bA n p a)
          * ((allocT n M p : ℝ) + bA n p a - ell p (K n) a - 7)
        = ∑ a ∈ Icc 1 (mHalf p), ((TLim x : ℝ) - bA n p a)
          * ((TLim x : ℝ) + bA n p a - ell p (K n) a - 7)
          - ((mHalf p : ℝ) * (2 * (TLim x : ℝ) - 8)
            - ∑ a ∈ Icc 1 (mHalf p), (ell p (K n) a : ℝ))) := by
    rcases allocT_eq hR hx with h | h
    · left
      have h' : (allocT n M p : ℝ) = TLim x := by exact_mod_cast h
      exact ⟨h', by rw [h']⟩
    · right
      have h' : (allocT n M p : ℝ) = TLim x - 1 := by exact_mod_cast h
      exact ⟨h', by rw [h', hΦ]⟩
  -- the continuum quantities `ps` and `pn₊`
  have hPSeq : (p : ℝ) * sLim x = 49 * n - p * (TLim x : ℝ) / 2 := by
    rw [sLim, bigH_real]
    have e : (p : ℝ) * (49 / 40 * x - (TLim x : ℝ) / 2) = 49 / 40 * (p * x) - p * (TLim x : ℝ) / 2 := by
      ring
    rw [e, hpx]
    ring
  have hPNeq : (p : ℝ) * nPlus x = 40 * n - p * (qLim x : ℝ) / 2 := by
    rw [nPlus]
    have e : (p : ℝ) * ((2 * x - (qLim x : ℝ)) / 2) = p * x - p * (qLim x : ℝ) / 2 := by ring
    rw [e, hpx]
  have hKR : (K n : ℝ) = 40 * n := by simp [K]
  -- the allocation identity `mT + E = h - L_0 + 4(N - m_N)`
  have hdm : mHalf p * allocT n M p + allocE n M p = allocTotal n M p :=
    Nat.div_add_mod (allocTotal n M p) (mHalf p)
  have hdmR : (mHalf p : ℝ) * (allocT n M p : ℝ) + (allocE n M p : ℝ)
      = (allocTotal n M p : ℝ) := by exact_mod_cast hdm
  have htotR : (allocTotal n M p : ℝ) + (6 * M + 10) + 4 * (mN n p : ℝ) = 49 * n := by
    have h : (allocTotal n M p : ℝ) + (L0 M : ℝ) + 4 * (mN n p : ℝ)
        = (hDim n : ℝ) + 4 * (N n : ℝ) := by exact_mod_cast hR.allocTotal_eq
    simp only [L0, hDim, N] at h
    push_cast at h
    linarith
  have hEm : (allocE n M p : ℝ) < mHalf p := by exact_mod_cast (alloc_eq hR).2
  have hAlloc : (mHalf p : ℝ) * (allocT n M p : ℝ) + (allocE n M p : ℝ)
      = (mHalf p : ℝ) * (TLim x : ℝ) + p * sLim x
        + ((TLim x : ℝ) / 2 - (6 * M + 10) - 4 * (mN n p : ℝ)) := by
    rw [hPSeq, hpm]
    linarith
  have hcp : ∑ a ∈ Icc 1 (mHalf p), ((ell p (K n) a : ℝ) - qLim x) - p * nPlus x
      = (qLim x : ℝ) / 2 - mK n p := by
    rw [hcpdef, hSl, hPNeq, hKR, hpm]
    ring
  -- the continuum `p (s - n₊)₊`
  have hν1 : 0 ≤ (p : ℝ) * max (sLim x - nPlus x) 0 :=
    mul_nonneg hpR.le (le_max_right _ _)
  have hν2 : (p : ℝ) * sLim x - p * nPlus x ≤ (p : ℝ) * max (sLim x - nPlus x) 0 := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hpR.le
  have hν3 : (p : ℝ) * max (sLim x - nPlus x) 0 = 0 ∨
      (p : ℝ) * max (sLim x - nPlus x) 0 = p * sLim x - p * nPlus x := by
    rcases max_choice (sLim x - nPlus x) 0 with h | h
    · right
      rw [h, mul_sub]
    · left
      rw [h, mul_zero]
  have hPS : 0 ≤ (p : ℝ) * sLim x := by
    apply mul_nonneg hpR.le
    rw [sLim, bigH_real]
    linarith
  have hPN : 0 ≤ (p : ℝ) * nPlus x := by
    apply mul_nonneg hpR.le
    rw [nPlus]
    linarith
  have hδ : |(TLim x : ℝ) / 2 - (6 * M + 10) - 4 * (mN n p : ℝ)| ≤ 12 * M + 10 := by
    rw [abs_le]
    constructor <;> linarith
  have hδ' : |(qLim x : ℝ) / 2 - mK n p| ≤ 2 * M := by
    rw [abs_le]
    constructor <;> linarith
  have hX : |2 * (TLim x : ℝ) - qLim x - 7| ≤ 7 * M + 7 := by
    rw [abs_le]
    constructor <;> linarith
  rw [hmin] at hγm
  have harith := alloc_arith hγm (min_le_left _ _) (min_le_right _ _) (min_choice _ _)
    hν1 hν2 hν3 (by rw [hcpdef]; ring) hAlloc hcp hT hEm hcpm hPS hPN hδ hδ' hX
  -- assemble
  rw [gammaIn_split hR]
  have hpG : (p : ℝ) * innerGamma x = p * (∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z)
      + (p * sLim x) * (2 * (TLim x : ℝ) - qLim x - 7) + p * max (sLim x - nPlus x) 0 := by
    rw [innerGamma]
    ring
  rw [hpG]
  obtain ⟨b1, b2⟩ := abs_le.mp hW0
  obtain ⟨b3, b4⟩ := abs_le.mp hriem
  obtain ⟨b5, b6⟩ := abs_le.mp harith
  rw [abs_le]
  constructor <;> linarith

end GammaApprox

/-! ## The second formula of (70) -/

section SKApprox

theorem padicValRat_finset_prod {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Legendre's formula (62) for `S_K` when `p ∤ 4` and `K, 2h < p²`:
`v_p(S_K) = 2h⌊K/p⌋ - 16h⌊N/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋`. -/
theorem padicValRat_SK {n p : ℕ} [Fact p.Prime] (h4 : ¬ p ∣ 4) (hsq : 2 * hDim n < p ^ 2)
    (hK : K n < p ^ 2) :
    padicValRat p (SK n) = 2 * hDim n * ((K n / p : ℕ) : ℤ) - 16 * hDim n * ((N n / p : ℕ) : ℤ)
      - 2 * ∑ i ∈ Icc 1 (hDim n - 1), ((2 * i / p : ℕ) : ℤ) := by
  have hfac : ∀ j : ℕ, j < p ^ 2 →
      padicValRat p (Nat.factorial j : ℚ) = ((j / p : ℕ) : ℤ) := by
    intro j hj
    rw [padicValRat.of_nat,
      padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow' (by norm_num) hj),
      Finset.sum_Ico_eq_sum_range]
    simp
  have hN : N n < p ^ 2 := lt_of_le_of_lt (by unfold N K; omega) hK
  have h4' : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd h4]
  have hfne : ∀ j : ℕ, (Nat.factorial j : ℚ) ≠ 0 :=
    fun j => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hprod : (∏ i ∈ Icc 1 (hDim n - 1), (Nat.factorial (2 * i) : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hfne _)
  have h4ne : (4 : ℚ) ^ (hDim n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [SK, padicValRat.div (mul_ne_zero (pow_ne_zero _ (hfne _)) h4ne)
      (mul_ne_zero (pow_ne_zero _ (hfne _)) hprod),
    padicValRat.mul (pow_ne_zero _ (hfne _)) h4ne,
    padicValRat.mul (pow_ne_zero _ (hfne _)) hprod,
    padicValRat.pow, padicValRat.pow, padicValRat.pow, h4', hfac _ hK, hfac _ hN,
    padicValRat_finset_prod (Icc 1 (hDim n - 1)) (fun i => (Nat.factorial (2 * i) : ℚ) ^ 2)
      fun i _ => pow_ne_zero _ (hfne _)]
  have hsum : ∑ i ∈ Icc 1 (hDim n - 1), padicValRat p ((Nat.factorial (2 * i) : ℚ) ^ 2)
      = ∑ i ∈ Icc 1 (hDim n - 1), 2 * ((2 * i / p : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi2 : 2 * i < p ^ 2 :=
      lt_of_le_of_lt (by have := (Finset.mem_Icc.mp hi).2; omega) hsq
    rw [padicValRat.pow, hfac _ hi2]
    push_cast
  rw [hsum, ← Finset.mul_sum]
  push_cast
  ring

/-- `0 ≤ p J(h/p) - ∑_{i<h} ⌊2i/p⌋ ≤ ⌊2h/p⌋`: the `J` correction in (68) matches the
factorial sum in (62). -/
theorem innerJ_sum_bounds {p : ℕ} (hp : 2 ≤ p) (h : ℕ) :
    0 ≤ (p : ℝ) * innerJ ((h : ℝ) / p) - ∑ i ∈ range h, ((2 * i / p : ℕ) : ℝ) ∧
      (p : ℝ) * innerJ ((h : ℝ) / p) - ∑ i ∈ range h, ((2 * i / p : ℕ) : ℝ)
        ≤ ((2 * h / p : ℕ) : ℝ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hJ : ∀ k : ℕ, (p : ℝ) * innerJ ((k : ℝ) / p)
      = ((2 * k / p : ℕ) : ℝ) * k
        - p * ((2 * k / p : ℕ) : ℝ) * (((2 * k / p : ℕ) : ℝ) + 1) / 4 := by
    intro k
    have hfl : ⌊2 * ((k : ℝ) / p)⌋ = ((2 * k / p : ℕ) : ℤ) := by
      rw [show 2 * ((k : ℝ) / p) = ((2 * k : ℕ) : ℝ) / p by push_cast; ring]
      exact floor_natCast_div _ _ hp0
    rw [innerJ, hfl, Int.cast_natCast]
    have hk : (p : ℝ) * ((k : ℝ) / p) = k := mul_div_cancel₀ _ hpR.ne'
    linear_combination ((2 * k / p : ℕ) : ℝ) * hk
  induction h with
  | zero =>
    rw [hJ 0]
    simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [hJ] at ih1 ih2 ⊢
    rw [Finset.sum_range_succ]
    have hA := Nat.div_add_mod (2 * k) p
    have hB := Nat.mod_lt (2 * k) hp0
    have hC := Nat.div_add_mod (2 * (k + 1)) p
    have hmono : 2 * k / p ≤ 2 * (k + 1) / p := Nat.div_le_div_right (by omega)
    have hcase : 2 * (k + 1) / p = 2 * k / p ∨ 2 * (k + 1) / p = 2 * k / p + 1 := by
      have hlt : 2 * (k + 1) / p < 2 * k / p + 2 := by
        by_contra hc
        push_neg at hc
        have h1 := Nat.mul_le_mul_left p hc
        linarith
      omega
    have hA' : (p : ℝ) * ((2 * k / p : ℕ) : ℝ) + ((2 * k % p : ℕ) : ℝ) = 2 * k := by
      exact_mod_cast hA
    have hB' : ((2 * k % p : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hB
    have hC' : (p : ℝ) * ((2 * (k + 1) / p : ℕ) : ℝ) + ((2 * (k + 1) % p : ℕ) : ℝ)
        = 2 * (k + 1) := by exact_mod_cast hC
    have hr0 : (0 : ℝ) ≤ ((2 * k % p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr0' : (0 : ℝ) ≤ ((2 * (k + 1) % p : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases hcase with hc | hc
    · rw [hc] at hC' ⊢
      push_cast
      constructor <;> linarith
    · rw [hc] at hC' ⊢
      push_cast at hC' ⊢
      constructor <;> linarith

/-- **Equation (70), second formula.** For fixed `M`, uniformly in the inner range
`K/M < p ≤ K/3` (`K = 40n ≥ 200M²`, `M ≥ 40`), `v_p(S_K) = p N(K/p) + O_M(1)`. -/
theorem padicValRat_SK_approx (M : ℕ) : ∃ C : ℝ, ∀ n p : ℕ, p.Prime → InnerRange n M p →
    |(padicValRat p (SK n) : ℝ) - p * innerN ((K n : ℝ) / p)| ≤ C := by
  refine ⟨4 * M, fun n p hp hR => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpM := hR.p_gt
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hKlt : 40 * n < M * p := hR.K_lt
  have h4 : ¬ p ∣ 4 := fun h => by
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 := hR.forty_le
    omega
  have hsq : 2 * hDim n < p ^ 2 := by
    have h2 : 200 * M * p < p * p := Nat.mul_lt_mul_of_pos_right hpM hp0
    rw [pow_two]
    unfold hDim
    nlinarith
  have hK2 : K n < p ^ 2 := by
    have : K n ≤ 2 * hDim n := by unfold K hDim; omega
    omega
  rw [padicValRat_SK h4 hsq hK2]
  have hfl1 : ⌊(K n : ℝ) / p⌋ = ((K n / p : ℕ) : ℤ) := floor_natCast_div _ _ hp0
  have hαx : (alpha : ℝ) * ((K n : ℝ) / p) = (N n : ℝ) / p := by
    rw [alpha_real]
    simp only [K, N]
    push_cast
    ring
  have hfl2 : ⌊(alpha : ℝ) * ((K n : ℝ) / p)⌋ = ((N n / p : ℕ) : ℤ) := by
    rw [hαx]
    exact floor_natCast_div _ _ hp0
  have hlamx : (lam : ℝ) * ((K n : ℝ) / p) = (hDim n : ℝ) / p := by
    rw [lam_real]
    simp only [K, hDim]
    push_cast
    ring
  have hplamx : (p : ℝ) * (lam : ℝ) * ((K n : ℝ) / p) = hDim n := by
    rw [mul_assoc, hlamx, mul_div_cancel₀ _ hpR.ne']
  have hpN : (p : ℝ) * innerN ((K n : ℝ) / p) = 2 * (hDim n : ℝ) * ((K n / p : ℕ) : ℝ)
      - 16 * (hDim n : ℝ) * ((N n / p : ℕ) : ℝ) - 2 * ((p : ℝ) * innerJ ((hDim n : ℝ) / p)) := by
    rw [innerN, hfl1, hfl2, hlamx]
    simp only [Int.cast_natCast]
    linear_combination (2 * ((K n / p : ℕ) : ℝ) - 16 * ((N n / p : ℕ) : ℝ)) * hplamx
  obtain ⟨hJ1, hJ2⟩ := innerJ_sum_bounds (p := p) (by omega) (hDim n)
  have hrange : ∑ i ∈ Icc 1 (hDim n - 1), ((2 * i / p : ℕ) : ℝ)
      = ∑ i ∈ range (hDim n), ((2 * i / p : ℕ) : ℝ) := by
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
  have h2h : ((2 * hDim n / p : ℕ) : ℝ) ≤ 2 * M := by
    have : 2 * hDim n / p ≤ 2 * M := by
      apply Nat.div_le_of_le_mul
      unfold hDim
      linarith
    exact_mod_cast this
  rw [hpN]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_sum]
  rw [hrange, abs_le]
  constructor <;> linarith

end SKApprox

end ZetaSeven
