import ZetaSeven.OuterLimiting

/-!
# The exact outer integral (paper Appendix A.2, equation (122) and Table 5, recomputed)

The outer integral (73) of the outer limiting functions,
`I_out = ∫_{1/3}^{2λ} T(y) dy` with
`T(y) = g(y) - 2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+` (`ZetaSeven.outerIntegrand`, by
`ZetaSeven.outerIntegrand_eq`), has the exact value `453803/288000`
(`ZetaSeven.outerIntegral_value`). This is the value recomputed from (54), (58), (59),
(72) and (73) with `γ^out_p = 0` for `p > K`; the printed (122), `-11002997/720000`, and
the nine pieces of Table 5 do not follow from the paper's definitions (source-map
erratum 9).

The proof is a certificate check. With `2λ = 37/20`, the integrand is affine,
`T(y) = b + cy`, on the interior of each of the 11 pieces of `[1/3, 37/20]` cut at
`43/120, 29/80, 37/100, 37/80, 29/60, 1/2, 43/80, 37/60, 37/40, 1`
(`ZetaSeven.outerIntegrand_piece_1`, ..., `ZetaSeven.outerIntegrand_piece_11`): on each
piece the floor `⌊1/y⌋`, the branch of `g`, and every `max`/`min` in `g` and in the
scalar term are constant. The integral splits at the breakpoints, each piece contributes
`b(y_1 - y_0) + c(y_1^2 - y_0^2)/2`, and the eleven contributions sum to
`453803/288000`. `T` jumps at `y = 1/2` and `y = 1`, where `⌊1/y⌋` does
(`ZetaSeven.outerIntegrand_jump_half`, `ZetaSeven.outerIntegrand_jump_one`), which does
not change the integral.
-/

namespace ZetaSeven

open MeasureTheory Filter Topology

/-! ### Helpers -/

private theorem alpha_cast : (alpha : ℝ) = 3 / 40 := by
  norm_num [alpha]

private theorem lam_cast : (lam : ℝ) = 37 / 40 := by
  norm_num [lam]

private theorem two_mul_lam : 2 * (lam : ℝ) = 37 / 20 := by
  norm_num [lam]

private theorem floor_one_div_eq_two {y : ℝ} (h1 : 1 / 3 < y) (h2 : y ≤ 1 / 2) :
    ⌊1 / y⌋ = 2 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hy]
    linarith
  · rw [div_lt_iff₀ hy]
    linarith

private theorem floor_one_div_eq_one {y : ℝ} (h1 : 1 / 2 < y) (h2 : y ≤ 1) :
    ⌊1 / y⌋ = 1 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hy]
    linarith
  · rw [div_lt_iff₀ hy]
    linarith

private theorem floor_one_div_eq_zero {y : ℝ} (h : 1 < y) : ⌊1 / y⌋ = 0 := by
  have hy : 0 < y := by linarith
  rw [Int.floor_eq_zero_iff]
  exact Set.mem_Ico.mpr ⟨div_nonneg zero_le_one hy.le, (div_lt_one hy).mpr h⟩

/-- The sum over `j ∈ [1, 7]` written out. -/
private theorem sum_Icc_one_seven (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) 7, f j = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp only [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

private theorem sum_Icc_one_seven' (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) 7, f j = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h : Finset.Icc (1 : ℕ) 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  rw [h]
  simp [Finset.sum_insert, add_assoc]

/-- The integral of an affine function. -/
private theorem integral_affine (a b B C : ℝ) :
    ∫ y in a..b, (B + C * y) = B * (b - a) + C * ((b ^ 2 - a ^ 2) / 2) := by
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
  have hC : IntervalIntegrable (fun y : ℝ => C * y) volume a b :=
    (by fun_prop : Continuous fun y : ℝ => C * y).intervalIntegrable a b
  rw [intervalIntegral.integral_add hB hC, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

/-- If `T(y) = B + Cy` on `(a, b)`, then `∫_a^b T = B(b - a) + C(b^2 - a^2)/2`. -/
private theorem integral_outerIntegrand_of_affine {a b B C : ℝ} (hab : a ≤ b)
    (h : ∀ y, a < y → y < b → outerIntegrand y = B + C * y) :
    ∫ y in a..b, outerIntegrand y = B * (b - a) + C * ((b ^ 2 - a ^ 2) / 2) := by
  have hEq : Set.EqOn outerIntegrand (fun y => B + C * y) (Set.Ioo a b) := by
    intro y hy
    exact h y hy.1 hy.2
  calc ∫ y in a..b, outerIntegrand y = ∫ y in a..b, (B + C * y) :=
        intervalIntegral.integral_congr_Ioo_of_le hab hEq
    _ = B * (b - a) + C * ((b ^ 2 - a ^ 2) / 2) := integral_affine a b B C

/-- The integrand of (73) is interval integrable on every subinterval of `[1/3, 37/20]`. -/
private theorem intervalIntegrable_outerIntegrand_of_le {a b : ℝ} (ha : 1 / 3 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 37 / 20) : IntervalIntegrable outerIntegrand volume a b := by
  refine intervalIntegrable_outerIntegrand.mono_set ?_
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (show (1 / 3 : ℝ) ≤ 2 * (lam : ℝ) by norm_num [lam])]
  exact Set.Icc_subset_Icc ha (hb.trans_eq two_mul_lam.symm)

/-- Splitting the integral of the integrand of (73) inside `[1/3, 37/20]`. -/
private theorem integral_split {a b c : ℝ} (ha : 1 / 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ 37 / 20) :
    ∫ y in a..c, outerIntegrand y =
      (∫ y in a..b, outerIntegrand y) + ∫ y in b..c, outerIntegrand y :=
  (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerIntegrand_of_le ha hab (hbc.trans hc))
    (intervalIntegrable_outerIntegrand_of_le (ha.trans hab) hbc hc)).symm

/-- If `T(y) = B + Cy` on `(a, x)`, then `T(y) → B + Cx` as `y → x` from the left. -/
private theorem tendsto_nhdsLT_of_affine {a x B C L : ℝ} (hax : a < x) (hL : B + C * x = L)
    (h : ∀ y, a < y → y < x → outerIntegrand y = B + C * y) :
    Tendsto outerIntegrand (𝓝[<] x) (𝓝 L) := by
  have hcont : Continuous fun y : ℝ => B + C * y := by fun_prop
  refine Tendsto.congr' ?_ ((hcont.tendsto' x L hL).mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT hax] with y hy
  exact (h y hy.1 hy.2).symm

/-- If `T(y) = B + Cy` on `(x, b)`, then `T(y) → B + Cx` as `y → x` from the right. -/
private theorem tendsto_nhdsGT_of_affine {x b B C L : ℝ} (hxb : x < b) (hL : B + C * x = L)
    (h : ∀ y, x < y → y < b → outerIntegrand y = B + C * y) :
    Tendsto outerIntegrand (𝓝[>] x) (𝓝 L) := by
  have hcont : Continuous fun y : ℝ => B + C * y := by fun_prop
  refine Tendsto.congr' ?_ ((hcont.tendsto' x L hL).mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
  exact (h y hy.1 hy.2).symm

/-! ### The integrand on the eleven pieces

On `(1/3, 1/2)` we have `⌊1/y⌋ = 2` and the formula `outerGLow`, on `(1/2, 1)`
`⌊1/y⌋ = 1` and the formula `outerGHigh`, and on `(1, 37/20)` `⌊1/y⌋ = 0` and `g = 0`.
Inside each piece every `max` and `min` is resolved by a linear inequality. -/

/-- On `(1/3, 43/120)`, `T(y) = 51/8 - 5y`. -/
theorem outerIntegrand_piece_1 {y : ℝ} (h0 : 1 / 3 < y) (h1 : y < 43 / 120) :
    outerIntegrand y = 51 / 8 - 5 * y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(43/120, 29/80)`, `T(y) = 513/40 - 23y`. -/
theorem outerIntegrand_piece_2 {y : ℝ} (h0 : 43 / 120 < y) (h1 : y < 29 / 80) :
    outerIntegrand y = 513 / 40 - 23 * y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(29/80, 37/100)`, `T(y) = 571/40 - 27y`. -/
theorem outerIntegrand_piece_3 {y : ℝ} (h0 : 29 / 80 < y) (h1 : y < 37 / 100) :
    outerIntegrand y = 571 / 40 - 27 * y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(37/100, 37/80)`, `T(y) = 497/40 - 22y`. -/
theorem outerIntegrand_piece_4 {y : ℝ} (h0 : 37 / 100 < y) (h1 : y < 37 / 80) :
    outerIntegrand y = 497 / 40 - 22 * y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(37/80, 29/60)`, `T(y) = 41/10 - 4y`. -/
theorem outerIntegrand_piece_5 {y : ℝ} (h0 : 37 / 80 < y) (h1 : y < 29 / 60) :
    outerIntegrand y = 41 / 10 - 4 * y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(29/60, 1/2)`, `T(y) = 53/20 - y`. -/
theorem outerIntegrand_piece_6 {y : ℝ} (h0 : 29 / 60 < y) (h1 : y < 1 / 2) :
    outerIntegrand y = 53 / 20 - y := by
  rw [outerIntegrand_eq, outerG_of_le_half (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_two (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGLow, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(1/2, 43/80)`, `T(y) = 7/2 + y`. -/
theorem outerIntegrand_piece_7 {y : ℝ} (h0 : 1 / 2 < y) (h1 : y < 43 / 80) :
    outerIntegrand y = 7 / 2 + y := by
  rw [outerIntegrand_eq, outerG_of_half_lt (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_one (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGHigh, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(43/80, 37/60)`, `T(y) = 121/10 - 15y`. -/
theorem outerIntegrand_piece_8 {y : ℝ} (h0 : 43 / 80 < y) (h1 : y < 37 / 60) :
    outerIntegrand y = 121 / 10 - 15 * y := by
  rw [outerIntegrand_eq, outerG_of_half_lt (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_one (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGHigh, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(37/60, 37/40)`, `T(y) = 41/4 - 12y`. -/
theorem outerIntegrand_piece_9 {y : ℝ} (h0 : 37 / 60 < y) (h1 : y < 37 / 40) :
    outerIntegrand y = 41 / 4 - 12 * y := by
  rw [outerIntegrand_eq, outerG_of_half_lt (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_one (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGHigh, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(37/40, 1)`, `T(y) = 1 - 2y`. -/
theorem outerIntegrand_piece_10 {y : ℝ} (h0 : 37 / 40 < y) (h1 : y < 1) :
    outerIntegrand y = 1 - 2 * y := by
  rw [outerIntegrand_eq, outerG_of_half_lt (y := y) (by linarith) (by linarith), outerScalar,
    floor_one_div_eq_one (y := y) (by linarith) (by linarith), sum_Icc_one_seven]
  simp only [outerGHigh, outerT, outerU, outerV, outerR, alpha_cast, lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right, min_eq_left, min_eq_right]
  ring

/-- On `(1, 37/20)`, where `g = 0`, `T(y) = 37/20 - y`. -/
theorem outerIntegrand_piece_11 {y : ℝ} (h0 : 1 < y) (h1 : y < 37 / 20) :
    outerIntegrand y = 37 / 20 - y := by
  rw [outerIntegrand_eq, outerG_of_one_lt h0, outerScalar, floor_one_div_eq_zero h0,
    sum_Icc_one_seven]
  simp only [lam_cast]
  push_cast
  simp (disch := linarith) only [max_eq_left, max_eq_right]
  ring

/-! ### The eleven contributions -/

private theorem integral_piece_1 :
    ∫ y in (1 / 3 : ℝ)..43 / 120, outerIntegrand y = 223 / 1920 :=
  (integral_outerIntegrand_of_affine (a := 1 / 3) (b := 43 / 120) (B := 51 / 8) (C := -5)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_1 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_2 :
    ∫ y in (43 / 120 : ℝ)..29 / 80, outerIntegrand y = 2177 / 115200 :=
  (integral_outerIntegrand_of_affine (a := 43 / 120) (b := 29 / 80) (B := 513 / 40) (C := -23)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_2 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_3 :
    ∫ y in (29 / 80 : ℝ)..37 / 100, outerIntegrand y = 10527 / 320000 :=
  (integral_outerIntegrand_of_affine (a := 29 / 80) (b := 37 / 100) (B := 571 / 40) (C := -27)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_3 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_4 :
    ∫ y in (37 / 100 : ℝ)..37 / 80, outerIntegrand y = 48359 / 160000 :=
  (integral_outerIntegrand_of_affine (a := 37 / 100) (b := 37 / 80) (B := 497 / 40) (C := -22)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_4 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_5 :
    ∫ y in (37 / 80 : ℝ)..29 / 60, outerIntegrand y = 53 / 1152 :=
  (integral_outerIntegrand_of_affine (a := 37 / 80) (b := 29 / 60) (B := 41 / 10) (C := -4)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_5 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_6 :
    ∫ y in (29 / 60 : ℝ)..1 / 2, outerIntegrand y = 259 / 7200 :=
  (integral_outerIntegrand_of_affine (a := 29 / 60) (b := 1 / 2) (B := 53 / 20) (C := -1)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_6 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_7 :
    ∫ y in (1 / 2 : ℝ)..43 / 80, outerIntegrand y = 1929 / 12800 :=
  (integral_outerIntegrand_of_affine (a := 1 / 2) (b := 43 / 80) (B := 7 / 2) (C := 1)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_7 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_8 :
    ∫ y in (43 / 80 : ℝ)..37 / 60, outerIntegrand y = 10469 / 38400 :=
  (integral_outerIntegrand_of_affine (a := 43 / 80) (b := 37 / 60) (B := 121 / 10) (C := -15)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_8 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_9 :
    ∫ y in (37 / 60 : ℝ)..37 / 40, outerIntegrand y = 37 / 120 :=
  (integral_outerIntegrand_of_affine (a := 37 / 60) (b := 37 / 40) (B := 41 / 4) (C := -12)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_9 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_10 :
    ∫ y in (37 / 40 : ℝ)..1, outerIntegrand y = -111 / 1600 :=
  (integral_outerIntegrand_of_affine (a := 37 / 40) (b := 1) (B := 1) (C := -2)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_10 h0 h1).trans (by ring)).trans
    (by norm_num)

private theorem integral_piece_11 :
    ∫ y in (1 : ℝ)..37 / 20, outerIntegrand y = 289 / 800 :=
  (integral_outerIntegrand_of_affine (a := 1) (b := 37 / 20) (B := 37 / 20) (C := -1)
    (by norm_num) fun _ h0 h1 => (outerIntegrand_piece_11 h0 h1).trans (by ring)).trans
    (by norm_num)

/-! ### The value of `I_out` -/

/-- **Exact outer integral** (Appendix A.2, (122) and Table 5, recomputed as in source-map
erratum 9): `I_out = 453803/288000`. -/
theorem outerIntegral_value : outerIntegral = 453803 / 288000 := by
  rw [outerIntegral, two_mul_lam,
    integral_split (a := 1 / 3) (b := 43 / 120) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_1,
    integral_split (a := 43 / 120) (b := 29 / 80) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_2,
    integral_split (a := 29 / 80) (b := 37 / 100) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_3,
    integral_split (a := 37 / 100) (b := 37 / 80) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_4,
    integral_split (a := 37 / 80) (b := 29 / 60) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_5,
    integral_split (a := 29 / 60) (b := 1 / 2) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_6,
    integral_split (a := 1 / 2) (b := 43 / 80) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_7,
    integral_split (a := 43 / 80) (b := 37 / 60) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_8,
    integral_split (a := 37 / 60) (b := 37 / 40) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_9,
    integral_split (a := 37 / 40) (b := 1) (c := 37 / 20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), integral_piece_10,
    integral_piece_11]
  norm_num

/-! ### The jumps at `y = 1/2` and `y = 1` -/

/-- `T` jumps at `y = 1/2`: its left limit is `43/20` and its right limit is `4`. -/
theorem outerIntegrand_jump_half :
    Tendsto outerIntegrand (𝓝[<] (1 / 2 : ℝ)) (𝓝 (43 / 20)) ∧
      Tendsto outerIntegrand (𝓝[>] (1 / 2 : ℝ)) (𝓝 4) :=
  ⟨tendsto_nhdsLT_of_affine (a := 29 / 60) (B := 53 / 20) (C := -1) (by norm_num) (by norm_num)
      fun _ h0 h1 => (outerIntegrand_piece_6 h0 h1).trans (by ring),
    tendsto_nhdsGT_of_affine (b := 43 / 80) (B := 7 / 2) (C := 1) (by norm_num) (by norm_num)
      fun _ h0 h1 => (outerIntegrand_piece_7 h0 h1).trans (by ring)⟩

/-- `T` jumps at `y = 1`: its left limit is `-1` and its right limit is `17/20`. -/
theorem outerIntegrand_jump_one :
    Tendsto outerIntegrand (𝓝[<] (1 : ℝ)) (𝓝 (-1)) ∧
      Tendsto outerIntegrand (𝓝[>] (1 : ℝ)) (𝓝 (17 / 20)) :=
  ⟨tendsto_nhdsLT_of_affine (a := 37 / 40) (B := 1) (C := -2) (by norm_num) (by norm_num)
      fun _ h0 h1 => (outerIntegrand_piece_10 h0 h1).trans (by ring),
    tendsto_nhdsGT_of_affine (b := 37 / 20) (B := 37 / 20) (C := -1) (by norm_num) (by norm_num)
      fun _ h0 h1 => (outerIntegrand_piece_11 h0 h1).trans (by ring)⟩

end ZetaSeven
