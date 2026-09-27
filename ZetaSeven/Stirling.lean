import Mathlib

/-!
# Stirling-type estimates for the real bound (paper §6.6, eq. (106)–(107))

This file provides the background factorial estimates used in the real bound:
an elementary upper bound `log (m !) ≤ m * log m - m + log m + 1`
(paper §6.6, the `t = 0` case of eq. (103)), a matching lower bound
`n * log n - n ≤ log (n !)`, the `(2i)!` sum bound of eq. (106), and the
Stirling upper bound for `log S_K` of eq. (107) with the exact
quadratic-log coefficient `2λ - 16αλ - 2λ²` and the `C*` constant, where
`λ = 37/40` and `α = 3/40` (so `h = λK`, `N = αK`).

The normalization factor is `S_K = (K!)^{2h} * 4^{h-1} / ((N!)^{16h} * ∏_{i=1}^{h-1} ((2i)!)^2)`
(cf. the Legendre-formula computation in eq. (62)); sums over `i = 1 .. h-1`
are written as sums over `Finset.range (h - 1)` in the variable `i + 1`.
-/

namespace ZetaSeven
namespace Stirling

open scoped BigOperators

/-- Elementary factorial upper bound: `log (m!) ≤ m log m - m + log m + 1`
for `m ≥ 1` (paper §6.6, the `t = 0` case of eq. (103)).
Proved by induction: the step uses `log (1 + 1/m) ≥ 1/(m+1)`. -/
theorem log_factorial_upper (m : ℕ) (hm : 1 ≤ m) :
    Real.log (Nat.factorial m : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) - m + Real.log (m : ℝ) + 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    norm_num [Nat.factorial_one, Real.log_one]
  | succ n hn ih =>
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1ne : (n : ℝ) + 1 ≠ 0 := ne_of_gt hn1pos
    have hne1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hne2 : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfact : (Nat.factorial (n + 1) : ℝ) = ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hle := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
    rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hn1pos)] at hle
    have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [heq] at hle
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
      rw [Real.log_div (ne_of_gt hn1pos) (ne_of_gt hnpos)]
      linarith [hle]
    have hkey : (1 : ℝ) ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hn1pos)
      rw [mul_one_div_cancel (ne_of_gt hn1pos)] at h2
      rw [Real.log_div (ne_of_gt hn1pos) (ne_of_gt hnpos)] at h2
      exact h2
    rw [hfact, Real.log_mul hne1 hne2]
    push_cast
    linarith [ih, hkey]

/-- Elementary factorial lower bound: `n log n - n ≤ log (n!)` for `n ≥ 1`.
Proved by induction: the step uses `log (1 + 1/n) ≤ 1/n`. -/
theorem log_factorial_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (Nat.factorial n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [Nat.factorial_one, Real.log_one]
  | succ n hn ih =>
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hne1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hne2 : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfact : (Nat.factorial (n + 1) : ℝ) = ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have h2 : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
      calc Real.log (1 + 1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / (n : ℝ) := by ring
    have h3 : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hnpos)
      rw [mul_one_div_cancel (ne_of_gt hnpos)] at hmul
      have heq : (1 : ℝ) + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
        field_simp
      rw [heq, Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < (n : ℝ) + 1))
        (ne_of_gt hnpos)] at hmul
      linarith [hmul]
    rw [hfact, Real.log_mul hne1 hne2]
    push_cast
    linarith [ih, h3]

/-- Summation comparison: with `f(x) = 2x log(2x) - 2x` and `h = n + 1`,
`∑_{i=1}^{h-1} f(i) ≥ h² log(2h) - (3/2)h² - 2h log(2h)`.
Proved by induction on `n`, using `log (1 + 1/m) ≤ 1/m` in the step. -/
theorem sum_integral_compare (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * Real.log (2 * ((n : ℝ) + 1))
        - 3 / 2 * ((n : ℝ) + 1) ^ 2
        - 2 * ((n : ℝ) + 1) * Real.log (2 * ((n : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range n,
        (2 * ((i : ℝ) + 1) * Real.log (2 * ((i : ℝ) + 1)) - 2 * ((i : ℝ) + 1)) := by
  induction n with
  | zero =>
    have h2 : (0 : ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
    simp only [Finset.sum_range_zero, Nat.cast_zero, zero_add, one_pow, mul_one,
      one_mul]
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    set m := (n : ℝ) + 1 with hm_def
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hm : (1 : ℝ) ≤ m := by rw [hm_def]; linarith
    have hmpos : (0 : ℝ) < m := by linarith
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have h2mne : (2 : ℝ) * m ≠ 0 := by positivity
    have hstep :
        ((m + 1) ^ 2 * Real.log (2 * (m + 1)) - 3 / 2 * (m + 1) ^ 2
            - 2 * (m + 1) * Real.log (2 * (m + 1)))
          - (m ^ 2 * Real.log (2 * m) - 3 / 2 * m ^ 2 - 2 * m * Real.log (2 * m))
          ≤ 2 * m * Real.log (2 * m) - 2 * m := by
      have h1 : (2 * (m + 1)) / (2 * m) = 1 + 1 / m := by
        field_simp
      have h2 : Real.log (1 + 1 / m) ≤ 1 / m := by
        calc Real.log (1 + 1 / m) ≤ (1 + 1 / m) - 1 :=
              Real.log_le_sub_one_of_pos (by positivity)
          _ = 1 / m := by ring
      have h3 : (0 : ℝ) ≤ m ^ 2 - 1 := by
        have hmul := mul_nonneg (show (0 : ℝ) ≤ m - 1 by linarith)
          (show (0 : ℝ) ≤ m + 1 by linarith)
        linarith [hmul]
      have h4 : (m ^ 2 - 1) * Real.log ((2 * (m + 1)) / (2 * m)) ≤ m := by
        calc (m ^ 2 - 1) * Real.log ((2 * (m + 1)) / (2 * m))
            = (m ^ 2 - 1) * Real.log (1 + 1 / m) := by rw [h1]
          _ ≤ (m ^ 2 - 1) * (1 / m) := mul_le_mul_of_nonneg_left h2 h3
          _ = (m ^ 2 - 1) / m := by ring
          _ ≤ m := by rw [div_le_iff₀ hmpos]; nlinarith [sq_nonneg m]
      rw [Real.log_div (by positivity) h2mne] at h4
      have hB : (0 : ℝ) ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
      linarith [h4, hB]
    linarith [ih, hstep]

/-- Equation (106): `-2 ∑_{i=1}^{h-1} log((2i)!) ≤ -2h²log(2h) + 3h² + 4h log(2h)`.
Follows from the pointwise lower bound `log_factorial_lower` and
`sumintegral_compare`. -/
theorem stirling_106 (h : ℕ) (hh : 1 ≤ h) :
    -2 * ∑ i ∈ Finset.range (h - 1), Real.log (Nat.factorial (2 * (i + 1)) : ℝ)
      ≤ -2 * (h : ℝ) ^ 2 * Real.log (2 * (h : ℝ))
        + 3 * (h : ℝ) ^ 2 + 4 * (h : ℝ) * Real.log (2 * (h : ℝ)) := by
  have hpt : ∀ i ∈ Finset.range (h - 1),
      2 * ((i : ℝ) + 1) * Real.log (2 * ((i : ℝ) + 1)) - 2 * ((i : ℝ) + 1)
        ≤ Real.log (Nat.factorial (2 * (i + 1)) : ℝ) := by
    intro i _
    have h := log_factorial_lower (2 * (i + 1)) (by omega)
    rw [show ((2 * (i + 1) : ℕ) : ℝ) = 2 * ((i : ℝ) + 1) by push_cast; ring] at h
    linarith [h]
  have hsum := Finset.sum_le_sum hpt
  have hkey := sum_integral_compare (h - 1)
  have hcast : (((h - 1 : ℕ)) : ℝ) + 1 = (h : ℝ) := by
    rw [Nat.cast_sub hh]
    simp
  rw [hcast] at hkey
  linarith [hsum, hkey]

/-- The normalization factor `S_K` (cf. eq. (62)):
`(K!)^{2h} * 4^{h-1} / ((N!)^{16h} * ∏_{i=1}^{h-1} ((2i)!)^2)`. -/
noncomputable def SK (K h N : ℕ) : ℝ :=
  (Nat.factorial K : ℝ) ^ (2 * h)
    / ((Nat.factorial N : ℝ) ^ (16 * h) * ∏ i ∈ Finset.range (h - 1), (Nat.factorial (2 * (i + 1)) : ℝ) ^ 2)
    * 4 ^ (h - 1)

/-- Logarithmic decomposition of `S_K`. -/
theorem log_SK {K h N : ℕ} (_hK : 1 ≤ K) (_hh1 : 1 ≤ h) (_hN1 : 1 ≤ N) :
    Real.log (SK K h N)
      = 2 * (h : ℝ) * Real.log (Nat.factorial K : ℝ) - 16 * (h : ℝ) * Real.log (Nat.factorial N : ℝ)
        - 2 * ∑ i ∈ Finset.range (h - 1), Real.log (Nat.factorial (2 * (i + 1)) : ℝ)
        + ((h - 1 : ℕ) : ℝ) * Real.log 4 := by
  unfold SK
  have hKne : (Nat.factorial K : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  have hNne : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hfine : ∀ i ∈ Finset.range (h - 1), (Nat.factorial (2 * (i + 1)) : ℝ) ≠ 0 := by
    intro i _
    exact_mod_cast Nat.factorial_ne_zero (2 * (i + 1))
  have hpowne : ∀ i ∈ Finset.range (h - 1),
      ((Nat.factorial (2 * (i + 1)) : ℝ) ^ 2) ≠ 0 := by
    intro i hi
    exact pow_ne_zero 2 (hfine i hi)
  have hprodne :
      (∏ i ∈ Finset.range (h - 1), ((Nat.factorial (2 * (i + 1)) : ℝ) ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hpowne
  have hPne : ((Nat.factorial N : ℝ) ^ (16 * h)
      * ∏ i ∈ Finset.range (h - 1), ((Nat.factorial (2 * (i + 1)) : ℝ) ^ 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hNne) hprodne
  have hQne : ((Nat.factorial K : ℝ) ^ (2 * h)
      / ((Nat.factorial N : ℝ) ^ (16 * h)
        * ∏ i ∈ Finset.range (h - 1), ((Nat.factorial (2 * (i + 1)) : ℝ) ^ 2))) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hKne) hPne
  have hRne : ((4 : ℝ) ^ (h - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_mul hQne hRne, Real.log_div (pow_ne_zero _ hKne) hPne,
    Real.log_mul (pow_ne_zero _ hNne) hprodne, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_prod hpowne]
  have h2 : ∀ i ∈ Finset.range (h - 1),
      Real.log ((Nat.factorial (2 * (i + 1)) : ℝ) ^ 2)
        = 2 * Real.log (Nat.factorial (2 * (i + 1)) : ℝ) := by
    intro i _
    rw [Real.log_pow]
    norm_num
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  push_cast
  ring

/-- Numeric bound absorbing the linear remainder into `6h`:
with `λ = 37/40`, `4 * log (2λ) + log 4 ≤ 4`. -/
theorem four_log_two_lam_add_log_four_le :
    4 * Real.log (2 * (37 / 40 : ℝ)) + Real.log 4 ≤ 4 := by
  have hexp := Real.exp_one_gt_d9
  have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [hexp]
  have hpow : (2.7 : ℝ) ^ 4 < (Real.exp 1) ^ 4 :=
    pow_lt_pow_left₀ h27 (by norm_num) (by norm_num)
  have hval : (1874161 / 40000 : ℝ) < (2.7 : ℝ) ^ 4 := by norm_num
  have hlt : (1874161 / 40000 : ℝ) < (Real.exp 1) ^ 4 := lt_trans hval hpow
  have heq : 4 * Real.log (2 * (37 / 40 : ℝ)) + Real.log 4
      = Real.log (1874161 / 40000 : ℝ) := by
    have e1 : (4 : ℝ) * Real.log (2 * (37 / 40 : ℝ))
        = Real.log ((2 * (37 / 40 : ℝ)) ^ 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.log_pow]
    rw [e1, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    norm_num
  rw [heq]
  have hlt4 : Real.log (1874161 / 40000 : ℝ) < 4 := by
    calc Real.log (1874161 / 40000 : ℝ)
        < Real.log ((Real.exp 1) ^ 4) := Real.log_lt_log (by norm_num) hlt
      _ = 4 := by rw [← Real.exp_nat_mul]; simp [Real.log_exp]
  exact le_of_lt hlt4

/-- Equation (107): the Stirling upper bound for `log S_K` with
`λ = 37/40`, `α = 3/40`, the exact quadratic-log coefficient
`2λ - 16αλ - 2λ²`, and `C* = -2λ + 16αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. -/
theorem stirling_107 {K h N : ℕ} (hK : 1 ≤ K)
    (hh : (h : ℝ) = 37 / 40 * (K : ℝ)) (hN : (N : ℝ) = 3 / 40 * (K : ℝ))
    (hN1 : 1 ≤ N) :
    Real.log (SK K h N)
      ≤ (2 * (37 / 40 : ℝ) - 16 * (3 / 40 : ℝ) * (37 / 40 : ℝ)
            - 2 * (37 / 40 : ℝ) ^ 2)
          * (K : ℝ) ^ 2 * Real.log (K : ℝ)
        + (-2 * (37 / 40 : ℝ) + 16 * (3 / 40 : ℝ) * (37 / 40 : ℝ)
              * (1 - Real.log (3 / 40 : ℝ))
            + 3 * (37 / 40 : ℝ) ^ 2
            - 2 * (37 / 40 : ℝ) ^ 2 * Real.log (2 * (37 / 40 : ℝ)))
          * (K : ℝ) ^ 2
        + 6 * (h : ℝ) * Real.log (K : ℝ) + 6 * (h : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hh1 : 1 ≤ h := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    rw [hN] at h1N
    have hK40 : (40 / 3 : ℝ) ≤ (K : ℝ) := by linarith
    have h37 : (37 / 3 : ℝ) ≤ (h : ℝ) := by rw [hh]; linarith
    have h1h : (1 : ℝ) ≤ (h : ℝ) := by linarith
    exact_mod_cast h1h
  rw [log_SK hK hh1 hN1]
  have b1 := log_factorial_upper K hK
  have b2 := log_factorial_lower N hN1
  have b3 := stirling_106 h hh1
  have hsub : ((h - 1 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.sub_le h 1
  have b4 : ((h - 1 : ℕ) : ℝ) * Real.log 4 ≤ (h : ℝ) * Real.log 4 :=
    mul_le_mul_of_nonneg_right hsub (Real.log_nonneg (by norm_num))
  have h2h : (0 : ℝ) ≤ 2 * (h : ℝ) := by positivity
  have h16 : (0 : ℝ) ≤ 16 * (h : ℝ) := by positivity
  have c1 : 2 * (h : ℝ) * Real.log (Nat.factorial K : ℝ)
      ≤ 2 * (h : ℝ)
        * ((K : ℝ) * Real.log (K : ℝ) - (K : ℝ) + Real.log (K : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left b1 h2h
  have c2 : -(16 * (h : ℝ) * Real.log (Nat.factorial N : ℝ))
      ≤ -(16 * (h : ℝ) * ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left b2 h16
    linarith
  have hlogN : Real.log (N : ℝ) = Real.log (K : ℝ) + Real.log (3 / 40 : ℝ) := by
    conv_lhs => rw [hN]
    rw [Real.log_mul (by norm_num) hKne]
    ring
  have hlog2h : Real.log (2 * (h : ℝ))
      = Real.log (K : ℝ) + Real.log (2 * (37 / 40 : ℝ)) := by
    have heq : (2 : ℝ) * (h : ℝ) = 2 * (37 / 40 : ℝ) * (K : ℝ) := by
      rw [hh]
      ring
    conv_lhs => rw [heq]
    rw [Real.log_mul (by norm_num) hKne]
    ring
  rw [hlogN] at c2
  rw [hlog2h] at b3
  have htot :
      2 * (h : ℝ) * Real.log (Nat.factorial K : ℝ) - 16 * (h : ℝ) * Real.log (Nat.factorial N : ℝ)
          - 2 * ∑ i ∈ Finset.range (h - 1), Real.log (Nat.factorial (2 * (i + 1)) : ℝ)
          + ((h - 1 : ℕ) : ℝ) * Real.log 4
        ≤ (2 * (h : ℝ)
              * ((K : ℝ) * Real.log (K : ℝ) - (K : ℝ) + Real.log (K : ℝ) + 1))
          + (-(16 * (h : ℝ)
              * ((N : ℝ) * (Real.log (K : ℝ) + Real.log (3 / 40 : ℝ)) - (N : ℝ))))
          + (-2 * (h : ℝ) ^ 2 * (Real.log (K : ℝ) + Real.log (2 * (37 / 40 : ℝ)))
              + 3 * (h : ℝ) ^ 2
              + 4 * (h : ℝ) * (Real.log (K : ℝ) + Real.log (2 * (37 / 40 : ℝ))))
          + ((h : ℝ) * Real.log 4) := by
    linarith [c1, c2, b3, b4]
  have hid :
      (2 * (h : ℝ)
            * ((K : ℝ) * Real.log (K : ℝ) - (K : ℝ) + Real.log (K : ℝ) + 1))
          + (-(16 * (h : ℝ)
              * ((N : ℝ) * (Real.log (K : ℝ) + Real.log (3 / 40 : ℝ)) - (N : ℝ))))
          + (-2 * (h : ℝ) ^ 2 * (Real.log (K : ℝ) + Real.log (2 * (37 / 40 : ℝ)))
              + 3 * (h : ℝ) ^ 2
              + 4 * (h : ℝ) * (Real.log (K : ℝ) + Real.log (2 * (37 / 40 : ℝ))))
          + ((h : ℝ) * Real.log 4)
        = ((2 * (37 / 40 : ℝ) - 16 * (3 / 40 : ℝ) * (37 / 40 : ℝ)
              - 2 * (37 / 40 : ℝ) ^ 2)
            * (K : ℝ) ^ 2 * Real.log (K : ℝ)
          + (-2 * (37 / 40 : ℝ) + 16 * (3 / 40 : ℝ) * (37 / 40 : ℝ)
                * (1 - Real.log (3 / 40 : ℝ))
              + 3 * (37 / 40 : ℝ) ^ 2
              - 2 * (37 / 40 : ℝ) ^ 2 * Real.log (2 * (37 / 40 : ℝ)))
            * (K : ℝ) ^ 2
          + 6 * (h : ℝ) * Real.log (K : ℝ) + 6 * (h : ℝ))
          + (K : ℝ)
            * ((37 / 40 : ℝ)
                * (2 + 4 * Real.log (2 * (37 / 40 : ℝ)) + Real.log 4)
              - 6 * (37 / 40 : ℝ)) := by
    rw [hh, hN]
    ring
  have hnum := four_log_two_lam_add_log_four_le
  have hR : (37 / 40 : ℝ) * (2 + 4 * Real.log (2 * (37 / 40 : ℝ)) + Real.log 4)
      - 6 * (37 / 40 : ℝ) ≤ 0 := by
    linarith [hnum]
  have hprod : (K : ℝ)
        * ((37 / 40 : ℝ) * (2 + 4 * Real.log (2 * (37 / 40 : ℝ)) + Real.log 4)
          - 6 * (37 / 40 : ℝ)) ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hR (le_of_lt hKpos)
    simpa using hmul
  linarith [htot, hid, hprod]

end Stirling
end ZetaSeven
