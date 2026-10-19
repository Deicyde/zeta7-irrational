import ZetaSeven.FunctionalMu

/-!
# Outer limiting functions (paper Section 5.3, Definition 5.3, equations (71)-(73))

In the outer range the paper works in the variable `y = p/K ∈ (1/3, 2λ)`, with
`α = 3/40` and `λ = 37/40` (`ZetaSeven.alpha`, `ZetaSeven.lam`). This module defines

* the outer limiting function `g(y)` (`outerG`), by the explicit formula obtained by
  scaling (54), (58) and (59) with `p = yK`, `N = αK`, `h = λK`, and `g(y) = 0` for
  `y > 1`, where `γ^out_p = 0` (Section 5.1, first sentence);
* the zero-weight correction `d(y)` of (72) (`outerD`);
* `R_0 = g + d` (`outerR0`), following the last sentence of Section 5.3 and the
  outer-range step of the proof of Proposition 5.4 rather than (71)
  (source-map erratum 8);
* the scalar term `-2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+` (`outerScalar`), the integrand
  of (73) (`outerIntegrand`) and the outer integral `I_out` (`outerIntegral`).

It proves that the integrand of (73) is `g` plus the scalar term and that it is
interval integrable on `[1/3, 2λ]`, so `I_out` is a genuine integral. The functions
are total in `y : ℝ`; only `y ∈ (1/3, 2λ)` enters `I_out`. That `g(y)` is the limit
of `-γ^out_p/K` is proved in the prime-sum bound, and the value of `I_out` in the
exact outer integral.
-/

namespace ZetaSeven

open MeasureTheory

noncomputable section

/-- `v = 1 - ky`, the quantity `v = K - p⌊K/p⌋` of (58) scaled by `K`,
as a function of `k = ⌊1/y⌋` and `y`. -/
def outerV (k : ℤ) (y : ℝ) : ℝ := 1 - k * y

/-- `u = max(0, α + v - y)`, from (58) scaled by `K`. -/
def outerU (k : ℤ) (y : ℝ) : ℝ := max 0 ((alpha : ℝ) + outerV k y - y)

/-- `t = min(α, v) + u`, from (58) scaled by `K`. -/
def outerT (k : ℤ) (y : ℝ) : ℝ := min (alpha : ℝ) (outerV k y) + outerU k y

/-- `r = min(λ, max(0, 1 + 6α - 3y))`, the rank bound (54) scaled by `K`. -/
def outerR (y : ℝ) : ℝ := min (lam : ℝ) (max 0 (1 + 6 * (alpha : ℝ) - 3 * y))

/-- The formula for `g(y)` on `1/2 < y ≤ 1` (the case `K < 2p` of (59)), as a
function of `k = ⌊1/y⌋` and `y`: `9(1 - y) - 8t + min(r, y - α + u)`. -/
def outerGHigh (k : ℤ) (y : ℝ) : ℝ :=
  9 * (1 - y) - 8 * outerT k y + min (outerR y) (y - (alpha : ℝ) + outerU k y)

/-- The formula for `g(y)` on `1/3 < y ≤ 1/2` (the case `K ≥ 2p` of (59)), as a
function of `k = ⌊1/y⌋` and `y`: `9(1 - y) - 16α - 7t + min(r, y + u)`. -/
def outerGLow (k : ℤ) (y : ℝ) : ℝ :=
  9 * (1 - y) - 16 * (alpha : ℝ) - 7 * outerT k y + min (outerR y) (y + outerU k y)

/-- The outer limiting function `g(y)`, with `k = ⌊1/y⌋`: `outerGLow k y` for
`1/3 < y ≤ 1/2`, `outerGHigh k y` for `1/2 < y ≤ 1`, and `0` otherwise (in
particular for `1 < y < 2λ`, where `γ^out_p = 0`). -/
def outerG (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y ≤ 1 / 2 then outerGLow ⌊1 / y⌋ y
  else if 1 / 2 < y ∧ y ≤ 1 then outerGHigh ⌊1 / y⌋ y
  else 0

/-- The zero-weight correction (72):
`d(y) = (1 + 6α - 3y - (1 + 2α - 3y)_+)_+ · 1_{(1/3,1/2)}(y)`. -/
def outerD (y : ℝ) : ℝ :=
  max (1 + 6 * (alpha : ℝ) - 3 * y - max (1 + 2 * (alpha : ℝ) - 3 * y) 0) 0 *
    (if 1 / 3 < y ∧ y < 1 / 2 then 1 else 0)

/-- The outer limiting function `R_0 = g + d` (Definition 5.3, read as in the last
sentence of Section 5.3: `R_0 - d` is the limit of `-γ^out_p/K`; erratum 8). -/
def outerR0 (y : ℝ) : ℝ := outerG y + outerD y

/-- The scalar term `-2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+` of (73). -/
def outerScalar (y : ℝ) : ℝ :=
  -2 * (lam : ℝ) * ⌊1 / y⌋ + ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * y) 0

/-- The integrand of (73): `R_0(y) - d(y) - 2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+`. -/
def outerIntegrand (y : ℝ) : ℝ :=
  outerR0 y - outerD y - 2 * (lam : ℝ) * ⌊1 / y⌋ +
    ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * y) 0

/-- The outer integral (73):
`I_out = ∫_{1/3}^{2λ} (R_0(y) - d(y) - 2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+) dy`. -/
def outerIntegral : ℝ := ∫ y in (1 / 3 : ℝ)..2 * (lam : ℝ), outerIntegrand y

/-! ### The branches of `g` -/

/-- On `1/3 < y ≤ 1/2`, `g(y)` is given by the formula of the case `K ≥ 2p`. -/
theorem outerG_of_le_half {y : ℝ} (h1 : 1 / 3 < y) (h2 : y ≤ 1 / 2) :
    outerG y = outerGLow ⌊1 / y⌋ y := by
  rw [outerG, if_pos (And.intro h1 h2)]

/-- On `1/2 < y ≤ 1`, `g(y)` is given by the formula of the case `K < 2p`. -/
theorem outerG_of_half_lt {y : ℝ} (h1 : 1 / 2 < y) (h2 : y ≤ 1) :
    outerG y = outerGHigh ⌊1 / y⌋ y := by
  have hlow : ¬(1 / 3 < y ∧ y ≤ 1 / 2) := fun h => by linarith [h.2]
  rw [outerG, if_neg hlow, if_pos (And.intro h1 h2)]

/-- For `y > 1`, `g(y) = 0`. -/
theorem outerG_of_one_lt {y : ℝ} (h : 1 < y) : outerG y = 0 := by
  have hlow : ¬(1 / 3 < y ∧ y ≤ 1 / 2) := fun h' => by linarith [h'.2]
  have hhigh : ¬(1 / 2 < y ∧ y ≤ 1) := fun h' => by linarith [h'.2]
  rw [outerG, if_neg hlow, if_neg hhigh]

/-! ### The integrand of (73) -/

/-- The integrand of (73) is `g(y)` plus the scalar term
`-2λ⌊1/y⌋ + ∑_{j=1}^{7} (2λ - jy)_+`. -/
theorem outerIntegrand_eq (y : ℝ) : outerIntegrand y = outerG y + outerScalar y := by
  rw [outerIntegrand, outerR0, outerScalar]
  ring

/-- `I_out` is the integral of `g` plus the scalar term over `(1/3, 2λ)`. -/
theorem outerIntegral_eq :
    outerIntegral = ∫ y in (1 / 3 : ℝ)..2 * (lam : ℝ), (outerG y + outerScalar y) := by
  rw [outerIntegral]
  exact intervalIntegral.integral_congr fun y _ => outerIntegrand_eq y

/-! ### Integrability

On each of `(1/3, 1/2)`, `(1/2, 1)` and `(1, 2λ)` the floor `⌊1/y⌋` and the branch of
`g` are constant, so `g` and the scalar term agree there with continuous functions. -/

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

private theorem intervalIntegrable_of_eqOn_Ioo {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : Continuous F) (h : Set.EqOn F f (Set.Ioo a b)) :
    IntervalIntegrable f volume a b := by
  have hFi : IntervalIntegrable F volume a b := hF.intervalIntegrable a b
  refine hFi.congr_uIoo ?_
  rw [Set.uIoo_of_le hab]
  exact h

/-- For fixed `k`, the formula `outerGLow k` is continuous in `y`. -/
theorem continuous_outerGLow (k : ℤ) : Continuous (outerGLow k) := by
  unfold outerGLow outerT outerU outerV outerR
  fun_prop

/-- For fixed `k`, the formula `outerGHigh k` is continuous in `y`. -/
theorem continuous_outerGHigh (k : ℤ) : Continuous (outerGHigh k) := by
  unfold outerGHigh outerT outerU outerV outerR
  fun_prop

/-- `g` is interval integrable on `[1/3, 2λ]`. -/
theorem intervalIntegrable_outerG :
    IntervalIntegrable outerG volume (1 / 3) (2 * (lam : ℝ)) := by
  have h1 : IntervalIntegrable outerG volume (1 / 3) (1 / 2) := by
    refine intervalIntegrable_of_eqOn_Ioo (by norm_num) (continuous_outerGLow 2) ?_
    intro y hy
    rw [outerG_of_le_half hy.1 hy.2.le, floor_one_div_eq_two hy.1 hy.2.le]
  have h2 : IntervalIntegrable outerG volume (1 / 2) 1 := by
    refine intervalIntegrable_of_eqOn_Ioo (by norm_num) (continuous_outerGHigh 1) ?_
    intro y hy
    rw [outerG_of_half_lt hy.1 hy.2.le, floor_one_div_eq_one hy.1 hy.2.le]
  have h3 : IntervalIntegrable outerG volume 1 (2 * (lam : ℝ)) := by
    refine intervalIntegrable_of_eqOn_Ioo (F := fun _ => (0 : ℝ)) (by norm_num [lam])
      continuous_const ?_
    intro y hy
    rw [outerG_of_one_lt hy.1]
  exact (h1.trans h2).trans h3

private theorem intervalIntegrable_outerScalar_of_floor {a b : ℝ} {k : ℤ} (hab : a ≤ b)
    (hk : ∀ y ∈ Set.Ioo a b, ⌊1 / y⌋ = k) : IntervalIntegrable outerScalar volume a b := by
  refine intervalIntegrable_of_eqOn_Ioo
    (F := fun y => -2 * (lam : ℝ) * k +
      ∑ j ∈ Finset.Icc (1 : ℕ) 7, max (2 * (lam : ℝ) - (j : ℝ) * y) 0)
    hab (continuous_const.add (continuous_finsetSum _ fun j _ => by fun_prop)) ?_
  intro y hy
  rw [outerScalar, hk y hy]

/-- The scalar term is interval integrable on `[1/3, 2λ]`. -/
theorem intervalIntegrable_outerScalar :
    IntervalIntegrable outerScalar volume (1 / 3) (2 * (lam : ℝ)) := by
  have h1 : IntervalIntegrable outerScalar volume (1 / 3) (1 / 2) :=
    intervalIntegrable_outerScalar_of_floor (by norm_num) fun y hy =>
      floor_one_div_eq_two hy.1 hy.2.le
  have h2 : IntervalIntegrable outerScalar volume (1 / 2) 1 :=
    intervalIntegrable_outerScalar_of_floor (by norm_num) fun y hy =>
      floor_one_div_eq_one hy.1 hy.2.le
  have h3 : IntervalIntegrable outerScalar volume 1 (2 * (lam : ℝ)) :=
    intervalIntegrable_outerScalar_of_floor (by norm_num [lam]) fun y hy =>
      floor_one_div_eq_zero hy.1
  exact (h1.trans h2).trans h3

/-- The integrand of (73) is interval integrable on `[1/3, 2λ]`, so `I_out` is a
genuine integral rather than the junk value `0`. -/
theorem intervalIntegrable_outerIntegrand :
    IntervalIntegrable outerIntegrand volume (1 / 3) (2 * (lam : ℝ)) := by
  have hfun : outerIntegrand = fun y => outerG y + outerScalar y := funext outerIntegrand_eq
  rw [hfun]
  exact intervalIntegrable_outerG.add intervalIntegrable_outerScalar

end

end ZetaSeven
