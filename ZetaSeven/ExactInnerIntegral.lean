import ZetaSeven.InnerLimiting

/-!
# The exact inner integral (paper Appendix A.1, equations (120)-(121), Tables 2-4)

Prince Anand, "Zeta 7 is Irrational", Appendix A.1. The inner limiting function
`R = -Γ - N` of Definition 5.2 (`ZetaSeven.innerR`) satisfies
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`
(`ZetaSeven.innerIntegral_value`, equation (121)), and `R(x)/x^3` is interval integrable on
`[3, 20]` (`ZetaSeven.intervalIntegrable_innerR_div_cube`).

The proof is a certificate check.

* Closed form of the `z`-integral of (66). Put `n = ⌊x⌋`, `q = ⌊2x⌋`, `m = ⌊αx⌋`,
  `q' = ⌊2αx⌋`, `d_f = min(x - n, n + 1 - x)` and `d_g = min(αx - m, m + 1 - αx)`. Then
  `ℓ(x, z) = 2n + 1` for `0 < z < d_f` and `ℓ(x, z) = 2q - 2n` for `d_f < z < 1/2`
  (`ZetaSeven.ellLim_of_lt_dist`, `ZetaSeven.ellLim_of_dist_lt`), and likewise for `ℓ(αx, z)`
  with `m`, `q'` and `d_g`. So the integrand of (66) is constant on the three intervals cut at
  `d_f` and `d_g`, and the integral is a sum of three constants times interval lengths
  (`ZetaSeven.integral_gammaIntegrand_of_le` if `d_f ≤ d_g`,
  `ZetaSeven.integral_gammaIntegrand_of_ge` if `d_g ≤ d_f`). With `T = ⌊2Hx⌋`, `k = ⌊2λx⌋`,
  the branches of the minima and the branch of `(s - n₊)₊` fixed, `R(x)` is then an explicit
  affine function of `x` (`ZetaSeven.innerR_eq_of_le`, `ZetaSeven.innerR_eq_of_ge`).
* The pieces. The floors, the branches of the minima `d_f` and `d_g`, their order (which flips
  where `(1 ± α)x` is an integer) and the branch of `(s - n₊)₊` (which, with the floors fixed,
  flips where `(9/20)x` is an integer) are constant between consecutive points of `[3, 20]` at
  which `cx` is an integer for some `c ∈ {1, 2, α, 2α, 2H, 2λ, 1 - α, 1 + α, 9/20}`. These
  points cut `[3, 20]` into 131 pieces, each the union of one to four consecutive rows of
  Tables 2-4 with the same coefficients, and `R(x) = ax + b` on the interior of each piece
  (`ZetaSeven.innerRPieces`, `ZetaSeven.innerR_eq_of_mem_innerRPieces`).
* On a piece `(l, u)`, `∫_l^u R(x)/x^3 dx = a(1/l - 1/u) + (b/2)(1/l^2 - 1/u^2)`, and the 131
  contributions sum to (121).

`R` jumps at `x = 4, ..., 19` and at `x = 40/3` (`ZetaSeven.innerR_jump_4`, ...,
`ZetaSeven.innerR_jump_19`, `ZetaSeven.innerR_jump_40_3`), and at the right endpoint
`R(20) = -37` while `R(x) → 0` as `x → 20⁻` (`ZetaSeven.innerR_at_twenty`). So the identities of
Tables 2-4 hold on the open intervals only (source-map erratum 12); the integral is unaffected.
-/

namespace ZetaSeven

open MeasureTheory Filter Topology

/-! ### The class counts `ℓ(x, z)` for fixed floors -/

/-- `d({y}) = min(y - n, n + 1 - y)` lies in `[0, 1/2]` when `⌊y⌋ = n`. -/
private theorem dist_bounds {y : ℝ} {n : ℤ} (hn : ⌊y⌋ = n) :
    0 ≤ min (y - n) (n + 1 - y) ∧ min (y - n) (n + 1 - y) ≤ 1 / 2 := by
  rw [Int.floor_eq_iff] at hn
  refine ⟨le_min (by linarith) (by linarith), ?_⟩
  rcases le_total (y - n) (n + 1 - y) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- `ℓ(x, z) = 2n + 1` for `0 < z < min(x - n, n + 1 - x)` (which forces `n = ⌊x⌋`). -/
theorem ellLim_of_lt_dist {x z : ℝ} {n : ℤ} (hz0 : 0 < z)
    (hz : z < min (x - n) (n + 1 - x)) : ellLim x z = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := lt_min_iff.mp hz
  have e1 : ⌊x - z⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have e2 : ⌊x + z⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  rw [ellLim, e1, e2]
  ring

/-- `ℓ(x, z) = 2q - 2n` for `d({x}) < z < 1/2`, where `n = ⌊x⌋` and `q = ⌊2x⌋`. -/
theorem ellLim_of_dist_lt {x z : ℝ} {n q : ℤ} (hn : ⌊x⌋ = n) (hq : ⌊2 * x⌋ = q)
    (hz : min (x - n) (n + 1 - x) < z) (hz1 : z < 1 / 2) : ellLim x z = 2 * q - 2 * n := by
  rw [Int.floor_eq_iff] at hn hq
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨hq1, hq2⟩ := hq
  rcases min_lt_iff.mp hz with h | h
  · -- `{x} < z < 1/2`, so `{x} < 1/2` and `q = 2n`
    have hq0 : q = 2 * n := by
      have a : (q : ℝ) < 2 * n + 1 := by linarith
      have b : (2 * n : ℝ) < q + 1 := by linarith
      have a' : q < 2 * n + 1 := by exact_mod_cast a
      have b' : 2 * n < q + 1 := by exact_mod_cast b
      omega
    have e1 : ⌊x - z⌋ = n - 1 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have e2 : ⌊x + z⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    rw [ellLim, e1, e2, hq0]
    ring
  · -- `1 - {x} < z < 1/2`, so `{x} > 1/2` and `q = 2n + 1`
    have hq0 : q = 2 * n + 1 := by
      have a : (q : ℝ) < 2 * n + 2 := by linarith
      have b : (2 * n + 1 : ℝ) < q + 1 := by linarith
      have a' : q < 2 * n + 2 := by exact_mod_cast a
      have b' : 2 * n + 1 < q + 1 := by exact_mod_cast b
      omega
    have e1 : ⌊x - z⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    have e2 : ⌊x + z⌋ = n + 1 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [ellLim, e1, e2, hq0]
    ring

/-- The integrand of (66) at a point `z` with `ℓ(x, z) = L` and `ℓ(αx, z) = B`. -/
private theorem gammaIntegrand_eq_of_ell {x z : ℝ} {L B : ℤ} (hL : ellLim x z = L)
    (hB : ellLim ((alpha : ℝ) * x) z = B) :
    gammaIntegrand x z =
      ((TLim x : ℝ) - ((4 * B : ℤ) : ℝ)) * ((TLim x : ℝ) + ((4 * B : ℤ) : ℝ) - (L : ℝ) - 7) := by
  rw [gammaIntegrand, bLim, hL, hB]

/-- The integral over `[a, b]` of a function equal to `c` on `(a, b)`. -/
private theorem integral_eq_mul_of_eqOn {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ z, a < z → z < b → f z = c) : ∫ z in a..b, f z = (b - a) * c := by
  have hEq : Set.EqOn f (fun _ => c) (Set.Ioo a b) := fun z hz => h z hz.1 hz.2
  rw [intervalIntegral.integral_congr_Ioo_of_le hab hEq]
  simp

/-- The integrand of (66) is interval integrable on every subinterval of `[0, 1/2]`. -/
private theorem gammaIntegrand_intervalIntegrable_of_le (x : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1 / 2) : IntervalIntegrable (gammaIntegrand x) volume a b := by
  refine (gammaIntegrand_intervalIntegrable x).mono_set ?_
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact Set.Icc_subset_Icc ha hb

/-! ### The closed form of the `z`-integral of (66) -/

/-- The `z`-integral of (66) when `d({x}) ≤ d({αx})`: the integrand takes the values with
`(ℓ(x, z), ℓ(αx, z)) = (2n + 1, 2m + 1)`, `(2q - 2n, 2m + 1)`, `(2q - 2n, 2q' - 2m)` on
`(0, d_f)`, `(d_f, d_g)`, `(d_g, 1/2)`. -/
theorem integral_gammaIntegrand_of_le {x df dg : ℝ} {n q m q' : ℤ} (hn : ⌊x⌋ = n)
    (hq : ⌊2 * x⌋ = q) (hm : ⌊(alpha : ℝ) * x⌋ = m) (hq' : ⌊2 * ((alpha : ℝ) * x)⌋ = q')
    (hdf : min (x - n) (n + 1 - x) = df)
    (hdg : min ((alpha : ℝ) * x - m) (m + 1 - (alpha : ℝ) * x) = dg) (hle : df ≤ dg) :
    ∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z =
      df * (((TLim x : ℝ) - 4 * (2 * m + 1)) * ((TLim x : ℝ) + 4 * (2 * m + 1) - (2 * n + 1) - 7))
        + (dg - df) * (((TLim x : ℝ) - 4 * (2 * m + 1))
          * ((TLim x : ℝ) + 4 * (2 * m + 1) - (2 * q - 2 * n) - 7))
        + (1 / 2 - dg) * (((TLim x : ℝ) - 4 * (2 * q' - 2 * m))
          * ((TLim x : ℝ) + 4 * (2 * q' - 2 * m) - (2 * q - 2 * n) - 7)) := by
  obtain ⟨hd0, hd1⟩ := dist_bounds hn
  obtain ⟨hg0, hg1⟩ := dist_bounds hm
  rw [hdf] at hd0 hd1
  rw [hdg] at hg0 hg1
  have e1 := integral_eq_mul_of_eqOn hd0 fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * n + 1) (B := 2 * m + 1)
      (ellLim_of_lt_dist (x := x) (n := n) h0 (by rw [hdf]; exact h1))
      (ellLim_of_lt_dist (x := (alpha : ℝ) * x) (n := m) h0 (by rw [hdg]; linarith))
  have e2 := integral_eq_mul_of_eqOn hle fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * q - 2 * n) (B := 2 * m + 1)
      (ellLim_of_dist_lt hn hq (by rw [hdf]; exact h0) (by linarith))
      (ellLim_of_lt_dist (x := (alpha : ℝ) * x) (n := m) (by linarith) (by rw [hdg]; exact h1))
  have e3 := integral_eq_mul_of_eqOn hg1 fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * q - 2 * n) (B := 2 * q' - 2 * m)
      (ellLim_of_dist_lt hn hq (by rw [hdf]; linarith) h1)
      (ellLim_of_dist_lt hm hq' (by rw [hdg]; exact h0) h1)
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (gammaIntegrand_intervalIntegrable_of_le x le_rfl hd0 hd1)
      (gammaIntegrand_intervalIntegrable_of_le x hd0 hd1 le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals
      (gammaIntegrand_intervalIntegrable_of_le x hd0 hle hg1)
      (gammaIntegrand_intervalIntegrable_of_le x hg0 hg1 le_rfl), e1, e2, e3]
  push_cast
  ring

/-- The `z`-integral of (66) when `d({αx}) ≤ d({x})`: the integrand takes the values with
`(ℓ(x, z), ℓ(αx, z)) = (2n + 1, 2m + 1)`, `(2n + 1, 2q' - 2m)`, `(2q - 2n, 2q' - 2m)` on
`(0, d_g)`, `(d_g, d_f)`, `(d_f, 1/2)`. -/
theorem integral_gammaIntegrand_of_ge {x df dg : ℝ} {n q m q' : ℤ} (hn : ⌊x⌋ = n)
    (hq : ⌊2 * x⌋ = q) (hm : ⌊(alpha : ℝ) * x⌋ = m) (hq' : ⌊2 * ((alpha : ℝ) * x)⌋ = q')
    (hdf : min (x - n) (n + 1 - x) = df)
    (hdg : min ((alpha : ℝ) * x - m) (m + 1 - (alpha : ℝ) * x) = dg) (hge : dg ≤ df) :
    ∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z =
      dg * (((TLim x : ℝ) - 4 * (2 * m + 1)) * ((TLim x : ℝ) + 4 * (2 * m + 1) - (2 * n + 1) - 7))
        + (df - dg) * (((TLim x : ℝ) - 4 * (2 * q' - 2 * m))
          * ((TLim x : ℝ) + 4 * (2 * q' - 2 * m) - (2 * n + 1) - 7))
        + (1 / 2 - df) * (((TLim x : ℝ) - 4 * (2 * q' - 2 * m))
          * ((TLim x : ℝ) + 4 * (2 * q' - 2 * m) - (2 * q - 2 * n) - 7)) := by
  obtain ⟨hd0, hd1⟩ := dist_bounds hn
  obtain ⟨hg0, hg1⟩ := dist_bounds hm
  rw [hdf] at hd0 hd1
  rw [hdg] at hg0 hg1
  have e1 := integral_eq_mul_of_eqOn hg0 fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * n + 1) (B := 2 * m + 1)
      (ellLim_of_lt_dist (x := x) (n := n) h0 (by rw [hdf]; linarith))
      (ellLim_of_lt_dist (x := (alpha : ℝ) * x) (n := m) h0 (by rw [hdg]; exact h1))
  have e2 := integral_eq_mul_of_eqOn hge fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * n + 1) (B := 2 * q' - 2 * m)
      (ellLim_of_lt_dist (x := x) (n := n) (by linarith) (by rw [hdf]; exact h1))
      (ellLim_of_dist_lt hm hq' (by rw [hdg]; exact h0) (by linarith))
  have e3 := integral_eq_mul_of_eqOn hd1 fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * q - 2 * n) (B := 2 * q' - 2 * m)
      (ellLim_of_dist_lt hn hq (by rw [hdf]; exact h0) h1)
      (ellLim_of_dist_lt hm hq' (by rw [hdg]; linarith) h1)
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (gammaIntegrand_intervalIntegrable_of_le x le_rfl hg0 hg1)
      (gammaIntegrand_intervalIntegrable_of_le x hg0 hg1 le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals
      (gammaIntegrand_intervalIntegrable_of_le x hg0 hge hd1)
      (gammaIntegrand_intervalIntegrable_of_le x hd0 hd1 le_rfl), e1, e2, e3]
  push_cast
  ring

/-! ### `R` as an affine function once the floors and branches are fixed

With `α = 3/40`, `λ = 37/40`, `H = 49/40`, the floors are `n = ⌊x⌋`, `q = ⌊2x⌋`,
`m = ⌊(3/40)x⌋`, `q' = ⌊(3/20)x⌋`, `T = ⌊(49/20)x⌋`, `k = ⌊(37/20)x⌋`; `S` is the value of
`(s - n₊)₊`. -/

/-- `R(x)` in closed form when `d({x}) ≤ d({αx})`. -/
theorem innerR_eq_of_le {x df dg S : ℝ} {n q m q' T k : ℤ} (hn : ⌊x⌋ = n)
    (hq : ⌊2 * x⌋ = q) (hm : ⌊3 / 40 * x⌋ = m) (hq' : ⌊3 / 20 * x⌋ = q')
    (hT : ⌊49 / 20 * x⌋ = T) (hk : ⌊37 / 20 * x⌋ = k) (hdf : min (x - n) (n + 1 - x) = df)
    (hdg : min (3 / 40 * x - m) (m + 1 - 3 / 40 * x) = dg) (hle : df ≤ dg)
    (hS : max (49 / 40 * x - T / 2 - (2 * x - q) / 2) 0 = S) :
    innerR x =
      -(df * (((T : ℝ) - 8 * m - 4) * (T + 8 * m - 2 * n - 4))
          + (dg - df) * (((T : ℝ) - 8 * m - 4) * (T + 8 * m + 2 * n - 2 * q - 3))
          + (1 / 2 - dg) * (((T : ℝ) + 8 * m - 8 * q') * (T - 8 * m + 8 * q' + 2 * n - 2 * q - 7))
          + (49 / 40 * x - T / 2) * (2 * T - q - 7) + S)
        - (37 / 20 * n * x - 74 / 5 * m * x - 2 * (37 / 40 * k * x - k * (k + 1) / 4)) := by
  have hm' : ⌊(alpha : ℝ) * x⌋ = m := by
    rw [alpha_real]
    exact hm
  have hq'' : ⌊2 * ((alpha : ℝ) * x)⌋ = q' := by
    rw [alpha_real, show (2 : ℝ) * (3 / 40 * x) = 3 / 20 * x by ring]
    exact hq'
  have hdg' : min ((alpha : ℝ) * x - m) (m + 1 - (alpha : ℝ) * x) = dg := by
    rw [alpha_real]
    exact hdg
  have hTL : TLim x = T := by
    rw [TLim, bigH_real, show (2 : ℝ) * (49 / 40) * x = 49 / 20 * x by ring]
    exact hT
  have hqL : qLim x = q := hq
  have hkL : ⌊2 * ((lam : ℝ) * x)⌋ = k := by
    rw [lam_real, show (2 : ℝ) * (37 / 40 * x) = 37 / 20 * x by ring]
    exact hk
  have hS' : max (sLim x - nPlus x) 0 = S := by
    rw [sLim, nPlus, hTL, hqL, bigH_real]
    exact hS
  rw [innerR, innerGamma, integral_gammaIntegrand_of_le hn hq hm' hq'' hdf hdg' hle, hS',
    innerN, innerJ, hkL, hn, hm', sLim, hTL, hqL, lam_real, bigH_real]
  ring

/-- `R(x)` in closed form when `d({αx}) ≤ d({x})`. -/
theorem innerR_eq_of_ge {x df dg S : ℝ} {n q m q' T k : ℤ} (hn : ⌊x⌋ = n)
    (hq : ⌊2 * x⌋ = q) (hm : ⌊3 / 40 * x⌋ = m) (hq' : ⌊3 / 20 * x⌋ = q')
    (hT : ⌊49 / 20 * x⌋ = T) (hk : ⌊37 / 20 * x⌋ = k) (hdf : min (x - n) (n + 1 - x) = df)
    (hdg : min (3 / 40 * x - m) (m + 1 - 3 / 40 * x) = dg) (hge : dg ≤ df)
    (hS : max (49 / 40 * x - T / 2 - (2 * x - q) / 2) 0 = S) :
    innerR x =
      -(dg * (((T : ℝ) - 8 * m - 4) * (T + 8 * m - 2 * n - 4))
          + (df - dg) * (((T : ℝ) + 8 * m - 8 * q') * (T - 8 * m + 8 * q' - 2 * n - 8))
          + (1 / 2 - df) * (((T : ℝ) + 8 * m - 8 * q') * (T - 8 * m + 8 * q' + 2 * n - 2 * q - 7))
          + (49 / 40 * x - T / 2) * (2 * T - q - 7) + S)
        - (37 / 20 * n * x - 74 / 5 * m * x - 2 * (37 / 40 * k * x - k * (k + 1) / 4)) := by
  have hm' : ⌊(alpha : ℝ) * x⌋ = m := by
    rw [alpha_real]
    exact hm
  have hq'' : ⌊2 * ((alpha : ℝ) * x)⌋ = q' := by
    rw [alpha_real, show (2 : ℝ) * (3 / 40 * x) = 3 / 20 * x by ring]
    exact hq'
  have hdg' : min ((alpha : ℝ) * x - m) (m + 1 - (alpha : ℝ) * x) = dg := by
    rw [alpha_real]
    exact hdg
  have hTL : TLim x = T := by
    rw [TLim, bigH_real, show (2 : ℝ) * (49 / 40) * x = 49 / 20 * x by ring]
    exact hT
  have hqL : qLim x = q := hq
  have hkL : ⌊2 * ((lam : ℝ) * x)⌋ = k := by
    rw [lam_real, show (2 : ℝ) * (37 / 40 * x) = 37 / 20 * x by ring]
    exact hk
  have hS' : max (sLim x - nPlus x) 0 = S := by
    rw [sLim, nPlus, hTL, hqL, bigH_real]
    exact hS
  rw [innerR, innerGamma, integral_gammaIntegrand_of_ge hn hq hm' hq'' hdf hdg' hge, hS',
    innerN, innerJ, hkL, hn, hm', sLim, hTL, hqL, lam_real, bigH_real]
  ring

/-- A floor from two bounds. -/
private theorem floor_eq_of_bounds {y : ℝ} {k : ℤ} (h1 : (k : ℝ) ≤ y) (h2 : y < k + 1) :
    ⌊y⌋ = k :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

/-! ### Integrating `R(x)/x^3` over a piece -/

/-- An antiderivative of `(ax + b)/x^3` away from `0`. -/
private theorem hasDerivAt_antideriv (a b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -a * y⁻¹ - b / 2 * (y⁻¹ * y⁻¹)) ((a * x + b) / x ^ 3) x := by
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx
  have h2 : HasDerivAt (fun y : ℝ => y⁻¹ * y⁻¹) (-(x ^ 2)⁻¹ * x⁻¹ + x⁻¹ * -(x ^ 2)⁻¹) x :=
    h1.mul h1
  refine ((h1.const_mul (-a)).sub (h2.const_mul (b / 2))).congr_deriv ?_
  linear_combination (-a * x⁻¹ ^ 2) * mul_inv_cancel₀ hx

/-- `R(x)/x^3` is interval integrable on `[l, u]` and has integral `A` there. -/
private abbrev InnerPiece (l u A : ℝ) : Prop :=
  IntervalIntegrable (fun x => innerR x / x ^ 3) volume l u ∧ ∫ x in l..u, innerR x / x ^ 3 = A

/-- If `R(x) = ax + b` on `(l, u)` with `0 < l ≤ u`, then `R(x)/x^3` is interval integrable on
`[l, u]` with integral `a(1/l - 1/u) + (b/2)(1/l^2 - 1/u^2)`. -/
private theorem innerPiece_of_affine {l u a b A : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (h : ∀ x, l < x → x < u → innerR x = a * x + b)
    (hA : a * (1 / l - 1 / u) + b / 2 * (1 / l ^ 2 - 1 / u ^ 2) = A) : InnerPiece l u A := by
  have hEq : Set.EqOn (fun x : ℝ => (a * x + b) / x ^ 3) (fun x => innerR x / x ^ 3)
      (Set.Ioo l u) := by
    intro x hx
    show (a * x + b) / x ^ 3 = innerR x / x ^ 3
    rw [h x hx.1 hx.2]
  have hcont : ContinuousOn (fun x : ℝ => (a * x + b) / x ^ 3) (Set.uIcc l u) := by
    refine ContinuousOn.div₀ (f := fun x : ℝ => a * x + b) (g := fun x : ℝ => x ^ 3)
      (by fun_prop) (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le hlu] at hx
    exact pow_ne_zero 3 (hl.trans_le hx.1).ne'
  have hint : IntervalIntegrable (fun x : ℝ => (a * x + b) / x ^ 3) volume l u :=
    hcont.intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc l u,
      HasDerivAt (fun y : ℝ => -a * y⁻¹ - b / 2 * (y⁻¹ * y⁻¹)) ((a * x + b) / x ^ 3) x := by
    intro x hx
    rw [Set.uIcc_of_le hlu] at hx
    exact hasDerivAt_antideriv a b (hl.trans_le hx.1).ne'
  refine ⟨hint.congr_uIoo ?_, ?_⟩
  · rw [Set.uIoo_of_le hlu]
    exact hEq
  · rw [← intervalIntegral.integral_congr_Ioo_of_le hlu hEq,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← hA]
    ring

/-- Adjacent pieces combine. -/
private theorem innerPiece_trans {l m u A B C : ℝ} (h1 : InnerPiece l m A)
    (h2 : InnerPiece m u B) (hC : A + B = C) : InnerPiece l u C := by
  obtain ⟨i1, e1⟩ := h1
  obtain ⟨i2, e2⟩ := h2
  exact ⟨i1.trans i2, by rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, e1, e2, hC]⟩

/-- If `R(y) = ay + b` on `(l, c)`, then `R(y) → ac + b` as `y → c` from the left. -/
private theorem tendsto_nhdsLT_of_affine {l c a b L : ℝ} (hlc : l < c) (hL : a * c + b = L)
    (h : ∀ y, l < y → y < c → innerR y = a * y + b) : Tendsto innerR (𝓝[<] c) (𝓝 L) := by
  have hcont : Continuous fun y : ℝ => a * y + b := by fun_prop
  refine Tendsto.congr' ?_ ((hcont.tendsto' c L hL).mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT hlc] with y hy
  exact (h y hy.1 hy.2).symm

/-- If `R(y) = ay + b` on `(c, u)`, then `R(y) → ac + b` as `y → c` from the right. -/
private theorem tendsto_nhdsGT_of_affine {c u a b L : ℝ} (hcu : c < u) (hL : a * c + b = L)
    (h : ∀ y, c < y → y < u → innerR y = a * y + b) : Tendsto innerR (𝓝[>] c) (𝓝 L) := by
  have hcont : Continuous fun y : ℝ => a * y + b := by fun_prop
  refine Tendsto.congr' ?_ ((hcont.tendsto' c L hL).mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT hcu] with y hy
  exact (h y hy.1 hy.2).symm

/-! ### `R` on the 131 pieces

Each piece is cut at consecutive points of `[3, 20]` where `cx` is an integer for some
`c ∈ {1, 2, α, 2α, 2H, 2λ, 1 - α, 1 + α, 9/20}`; the proof fixes the six floors, the branches
of `d_f` and `d_g`, their order, and the branch of `(s - n₊)₊`, each by a linear inequality. -/

/-- On `(3, 120/37)`, `R(x) = (51/20)x + 1` (Tables 2-4, rows 0-1). -/
private theorem innerR_piece_000 (x : ℝ) (h0 : 3 < x) (h1 : x < 120 / 37) :
    innerR x = 51 / 20 * x + 1 := by
  rw [innerR_eq_of_le (x := x) (n := 3) (q := 6) (m := 0) (q' := 0) (T := 7)
    (k := 5) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(120/37, 160/49)`, `R(x) = (81/10)x - 17` (Tables 2-4, rows 2-3). -/
private theorem innerR_piece_001 (x : ℝ) (h0 : 120 / 37 < x) (h1 : x < 160 / 49) :
    innerR x = 81 / 10 * x + -17 := by
  rw [innerR_eq_of_ge (x := x) (n := 3) (q := 6) (m := 0) (q' := 0) (T := 7)
    (k := 6) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(160/49, 7/2)`, `R(x) = (55/8)x - 13` (Tables 2-4, rows 4-6). -/
private theorem innerR_piece_002 (x : ℝ) (h0 : 160 / 49 < x) (h1 : x < 7 / 2) :
    innerR x = 55 / 8 * x + -13 := by
  rw [innerR_eq_of_ge (x := x) (n := 3) (q := 6) (m := 0) (q' := 0) (T := 8)
    (k := 6) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(7/2, 180/49)`, `R(x) = (63/8)x - 33/2` (Tables 2-4, row 7). -/
private theorem innerR_piece_003 (x : ℝ) (h0 : 7 / 2 < x) (h1 : x < 180 / 49) :
    innerR x = 63 / 8 * x + -33 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 3) (q := 7) (m := 0) (q' := 0) (T := 8)
    (k := 6) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(180/49, 160/43)`, `R(x) = (133/20)x - 12` (Tables 2-4, row 8). -/
private theorem innerR_piece_004 (x : ℝ) (h0 : 180 / 49 < x) (h1 : x < 160 / 43) :
    innerR x = 133 / 20 * x + -12 := by
  rw [innerR_eq_of_ge (x := x) (n := 3) (q := 7) (m := 0) (q' := 0) (T := 9)
    (k := 6) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(160/43, 140/37)`, `R(x) = (47/20)x + 4` (Tables 2-4, row 9). -/
private theorem innerR_piece_005 (x : ℝ) (h0 : 160 / 43 < x) (h1 : x < 140 / 37) :
    innerR x = 47 / 20 * x + 4 := by
  rw [innerR_eq_of_le (x := x) (n := 3) (q := 7) (m := 0) (q' := 0) (T := 9)
    (k := 6) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(140/37, 4)`, `R(x) = (21/5)x - 3` (Tables 2-4, rows 10-11). -/
private theorem innerR_piece_006 (x : ℝ) (h0 : 140 / 37 < x) (h1 : x < 4) :
    innerR x = 21 / 5 * x + -3 := by
  rw [innerR_eq_of_le (x := x) (n := 3) (q := 7) (m := 0) (q' := 0) (T := 9)
    (k := 7) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(4, 200/49)`, `R(x) = (67/20)x - 7` (Tables 2-4, row 12). -/
private theorem innerR_piece_007 (x : ℝ) (h0 : 4 < x) (h1 : x < 200 / 49) :
    innerR x = 67 / 20 * x + -7 := by
  rw [innerR_eq_of_le (x := x) (n := 4) (q := 8) (m := 0) (q' := 0) (T := 9)
    (k := 7) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(200/49, 160/37)`, `R(x) = (17/8)x - 2` (Tables 2-4, rows 13-14). -/
private theorem innerR_piece_008 (x : ℝ) (h0 : 200 / 49 < x) (h1 : x < 160 / 37) :
    innerR x = 17 / 8 * x + -2 := by
  rw [innerR_eq_of_le (x := x) (n := 4) (q := 8) (m := 0) (q' := 0) (T := 10)
    (k := 7) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(160/37, 40/9)`, `R(x) = (307/40)x - 26` (Tables 2-4, rows 15-16). -/
private theorem innerR_piece_009 (x : ℝ) (h0 : 160 / 37 < x) (h1 : x < 40 / 9) :
    innerR x = 307 / 40 * x + -26 := by
  rw [innerR_eq_of_ge (x := x) (n := 4) (q := 8) (m := 0) (q' := 0) (T := 10)
    (k := 8) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(40/9, 220/49)`, `R(x) = (149/20)x - 25` (Tables 2-4, row 17). -/
private theorem innerR_piece_010 (x : ℝ) (h0 : 40 / 9 < x) (h1 : x < 220 / 49) :
    innerR x = 149 / 20 * x + -25 := by
  rw [innerR_eq_of_ge (x := x) (n := 4) (q := 8) (m := 0) (q' := 0) (T := 10)
    (k := 8) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(220/49, 9/2)`, `R(x) = (249/40)x - 39/2` (Tables 2-4, row 18). -/
private theorem innerR_piece_011 (x : ℝ) (h0 : 220 / 49 < x) (h1 : x < 9 / 2) :
    innerR x = 249 / 40 * x + -39 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 4) (q := 8) (m := 0) (q' := 0) (T := 11)
    (k := 8) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(9/2, 200/43)`, `R(x) = (289/40)x - 24` (Tables 2-4, row 19). -/
private theorem innerR_piece_012 (x : ℝ) (h0 : 9 / 2 < x) (h1 : x < 200 / 43) :
    innerR x = 289 / 40 * x + -24 := by
  rw [innerR_eq_of_ge (x := x) (n := 4) (q := 9) (m := 0) (q' := 0) (T := 11)
    (k := 8) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(200/43, 180/37)`, `R(x) = (117/40)x - 4` (Tables 2-4, rows 20-21). -/
private theorem innerR_piece_013 (x : ℝ) (h0 : 200 / 43 < x) (h1 : x < 180 / 37) :
    innerR x = 117 / 40 * x + -4 := by
  rw [innerR_eq_of_le (x := x) (n := 4) (q := 9) (m := 0) (q' := 0) (T := 11)
    (k := 8) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(180/37, 240/49)`, `R(x) = (191/40)x - 13` (Tables 2-4, row 22). -/
private theorem innerR_piece_014 (x : ℝ) (h0 : 180 / 37 < x) (h1 : x < 240 / 49) :
    innerR x = 191 / 40 * x + -13 := by
  rw [innerR_eq_of_le (x := x) (n := 4) (q := 9) (m := 0) (q' := 0) (T := 11)
    (k := 9) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(240/49, 5)`, `R(x) = (71/20)x - 7` (Tables 2-4, row 23). -/
private theorem innerR_piece_015 (x : ℝ) (h0 : 240 / 49 < x) (h1 : x < 5) :
    innerR x = 71 / 20 * x + -7 := by
  rw [innerR_eq_of_le (x := x) (n := 4) (q := 9) (m := 0) (q' := 0) (T := 12)
    (k := 9) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(5, 260/49)`, `R(x) = (27/10)x - 12` (Tables 2-4, rows 24-26). -/
private theorem innerR_piece_016 (x : ℝ) (h0 : 5 < x) (h1 : x < 260 / 49) :
    innerR x = 27 / 10 * x + -12 := by
  rw [innerR_eq_of_le (x := x) (n := 5) (q := 10) (m := 0) (q' := 0) (T := 12)
    (k := 9) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(260/49, 200/37)`, `R(x) = (59/40)x - 11/2` (Tables 2-4, row 27). -/
private theorem innerR_piece_017 (x : ℝ) (h0 : 260 / 49 < x) (h1 : x < 200 / 37) :
    innerR x = 59 / 40 * x + -11 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 5) (q := 10) (m := 0) (q' := 0) (T := 13)
    (k := 9) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(200/37, 11/2)`, `R(x) = (281/40)x - 71/2` (Tables 2-4, row 28). -/
private theorem innerR_piece_018 (x : ℝ) (h0 : 200 / 37 < x) (h1 : x < 11 / 2) :
    innerR x = 281 / 40 * x + -71 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 5) (q := 10) (m := 0) (q' := 0) (T := 13)
    (k := 10) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(11/2, 240/43)`, `R(x) = (321/40)x - 41` (Tables 2-4, row 29). -/
private theorem innerR_piece_019 (x : ℝ) (h0 : 11 / 2 < x) (h1 : x < 240 / 43) :
    innerR x = 321 / 40 * x + -41 := by
  rw [innerR_eq_of_ge (x := x) (n := 5) (q := 11) (m := 0) (q' := 0) (T := 13)
    (k := 10) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(240/43, 40/7)`, `R(x) = (149/40)x - 17` (Tables 2-4, rows 30-31). -/
private theorem innerR_piece_020 (x : ℝ) (h0 : 240 / 43 < x) (h1 : x < 40 / 7) :
    innerR x = 149 / 40 * x + -17 := by
  rw [innerR_eq_of_le (x := x) (n := 5) (q := 11) (m := 0) (q' := 0) (T := 13)
    (k := 10) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(40/7, 220/37)`, `R(x) = (5/2)x - 10` (Tables 2-4, row 32). -/
private theorem innerR_piece_021 (x : ℝ) (h0 : 40 / 7 < x) (h1 : x < 220 / 37) :
    innerR x = 5 / 2 * x + -10 := by
  rw [innerR_eq_of_le (x := x) (n := 5) (q := 11) (m := 0) (q' := 0) (T := 14)
    (k := 10) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(220/37, 6)`, `R(x) = (87/20)x - 21` (Tables 2-4, row 33). -/
private theorem innerR_piece_022 (x : ℝ) (h0 : 220 / 37 < x) (h1 : x < 6) :
    innerR x = 87 / 20 * x + -21 := by
  rw [innerR_eq_of_le (x := x) (n := 5) (q := 11) (m := 0) (q' := 0) (T := 14)
    (k := 11) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(6, 300/49)`, `R(x) = (7/2)x - 27` (Tables 2-4, rows 34-36). -/
private theorem innerR_piece_023 (x : ℝ) (h0 : 6 < x) (h1 : x < 300 / 49) :
    innerR x = 7 / 2 * x + -27 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 12) (m := 0) (q' := 0) (T := 14)
    (k := 11) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(300/49, 240/37)`, `R(x) = (91/40)x - 39/2` (Tables 2-4, row 37). -/
private theorem innerR_piece_024 (x : ℝ) (h0 : 300 / 49 < x) (h1 : x < 240 / 37) :
    innerR x = 91 / 40 * x + -39 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 12) (m := 0) (q' := 0) (T := 15)
    (k := 11) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(240/37, 13/2)`, `R(x) = (313/40)x - 111/2` (Tables 2-4, row 38). -/
private theorem innerR_piece_025 (x : ℝ) (h0 : 240 / 37 < x) (h1 : x < 13 / 2) :
    innerR x = 313 / 40 * x + -111 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 6) (q := 12) (m := 0) (q' := 0) (T := 15)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(13/2, 280/43)`, `R(x) = (353/40)x - 62` (Tables 2-4, row 39). -/
private theorem innerR_piece_026 (x : ℝ) (h0 : 13 / 2 < x) (h1 : x < 280 / 43) :
    innerR x = 353 / 40 * x + -62 := by
  rw [innerR_eq_of_ge (x := x) (n := 6) (q := 13) (m := 0) (q' := 0) (T := 15)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(280/43, 320/49)`, `R(x) = (181/40)x - 34` (Tables 2-4, rows 40-41). -/
private theorem innerR_piece_027 (x : ℝ) (h0 : 280 / 43 < x) (h1 : x < 320 / 49) :
    innerR x = 181 / 40 * x + -34 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 13) (m := 0) (q' := 0) (T := 15)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(320/49, 20/3)`, `R(x) = (33/10)x - 26` (Tables 2-4, row 42). -/
private theorem innerR_piece_028 (x : ℝ) (h0 : 320 / 49 < x) (h1 : x < 20 / 3) :
    innerR x = 33 / 10 * x + -26 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 13) (m := 0) (q' := 0) (T := 16)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(20/3, 340/49)`, `R(x) = (219/40)x - 81/2` (Tables 2-4, row 43). -/
private theorem innerR_piece_029 (x : ℝ) (h0 : 20 / 3 < x) (h1 : x < 340 / 49) :
    innerR x = 219 / 40 * x + -81 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 13) (m := 0) (q' := 1) (T := 16)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(340/49, 7)`, `R(x) = (17/4)x - 32` (Tables 2-4, rows 44-46). -/
private theorem innerR_piece_030 (x : ℝ) (h0 : 340 / 49 < x) (h1 : x < 7) :
    innerR x = 17 / 4 * x + -32 := by
  rw [innerR_eq_of_le (x := x) (n := 6) (q := 13) (m := 0) (q' := 1) (T := 17)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(7, 260/37)`, `R(x) = (17/5)x - 39` (Tables 2-4, row 47). -/
private theorem innerR_piece_031 (x : ℝ) (h0 : 7 < x) (h1 : x < 260 / 37) :
    innerR x = 17 / 5 * x + -39 := by
  rw [innerR_eq_of_le (x := x) (n := 7) (q := 14) (m := 0) (q' := 1) (T := 17)
    (k := 12) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(260/37, 360/49)`, `R(x) = (21/4)x - 52` (Tables 2-4, row 48). -/
private theorem innerR_piece_032 (x : ℝ) (h0 : 260 / 37 < x) (h1 : x < 360 / 49) :
    innerR x = 21 / 4 * x + -52 := by
  rw [innerR_eq_of_le (x := x) (n := 7) (q := 14) (m := 0) (q' := 1) (T := 17)
    (k := 13) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(360/49, 320/43)`, `R(x) = (161/40)x - 43` (Tables 2-4, rows 49-50). -/
private theorem innerR_piece_033 (x : ℝ) (h0 : 360 / 49 < x) (h1 : x < 320 / 43) :
    innerR x = 161 / 40 * x + -43 := by
  rw [innerR_eq_of_le (x := x) (n := 7) (q := 14) (m := 0) (q' := 1) (T := 18)
    (k := 13) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(320/43, 15/2)`, `R(x) = (-11/40)x - 11` (Tables 2-4, row 51). -/
private theorem innerR_piece_034 (x : ℝ) (h0 : 320 / 43 < x) (h1 : x < 15 / 2) :
    innerR x = -11 / 40 * x + -11 := by
  rw [innerR_eq_of_ge (x := x) (n := 7) (q := 14) (m := 0) (q' := 1) (T := 18)
    (k := 13) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(15/2, 280/37)`, `R(x) = (29/40)x - 37/2` (Tables 2-4, row 52). -/
private theorem innerR_piece_035 (x : ℝ) (h0 : 15 / 2 < x) (h1 : x < 280 / 37) :
    innerR x = 29 / 40 * x + -37 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 7) (q := 15) (m := 0) (q' := 1) (T := 18)
    (k := 13) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(280/37, 380/49)`, `R(x) = (251/40)x - 121/2` (Tables 2-4, row 53). -/
private theorem innerR_piece_036 (x : ℝ) (h0 : 280 / 37 < x) (h1 : x < 380 / 49) :
    innerR x = 251 / 40 * x + -121 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 7) (q := 15) (m := 0) (q' := 1) (T := 18)
    (k := 14) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(380/49, 8)`, `R(x) = (101/20)x - 51` (Tables 2-4, rows 54-56). -/
private theorem innerR_piece_037 (x : ℝ) (h0 : 380 / 49 < x) (h1 : x < 8) :
    innerR x = 101 / 20 * x + -51 := by
  rw [innerR_eq_of_le (x := x) (n := 7) (q := 15) (m := 0) (q' := 1) (T := 19)
    (k := 14) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(8, 300/37)`, `R(x) = (21/5)x - 59` (Tables 2-4, row 57). -/
private theorem innerR_piece_038 (x : ℝ) (h0 : 8 < x) (h1 : x < 300 / 37) :
    innerR x = 21 / 5 * x + -59 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 16) (m := 0) (q' := 1) (T := 19)
    (k := 14) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(300/37, 400/49)`, `R(x) = (121/20)x - 74` (Tables 2-4, row 58). -/
private theorem innerR_piece_039 (x : ℝ) (h0 : 300 / 37 < x) (h1 : x < 400 / 49) :
    innerR x = 121 / 20 * x + -74 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 16) (m := 0) (q' := 1) (T := 19)
    (k := 15) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(400/49, 360/43)`, `R(x) = (193/40)x - 64` (Tables 2-4, rows 59-61). -/
private theorem innerR_piece_040 (x : ℝ) (h0 : 400 / 49 < x) (h1 : x < 360 / 43) :
    innerR x = 193 / 40 * x + -64 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 16) (m := 0) (q' := 1) (T := 20)
    (k := 15) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(360/43, 17/2)`, `R(x) = (21/40)x - 28` (Tables 2-4, row 62). -/
private theorem innerR_piece_041 (x : ℝ) (h0 : 360 / 43 < x) (h1 : x < 17 / 2) :
    innerR x = 21 / 40 * x + -28 := by
  rw [innerR_eq_of_ge (x := x) (n := 8) (q := 16) (m := 0) (q' := 1) (T := 20)
    (k := 15) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(17/2, 60/7)`, `R(x) = (61/40)x - 73/2` (Tables 2-4, row 63). -/
private theorem innerR_piece_042 (x : ℝ) (h0 : 17 / 2 < x) (h1 : x < 60 / 7) :
    innerR x = 61 / 40 * x + -73 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 8) (q := 17) (m := 0) (q' := 1) (T := 20)
    (k := 15) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(60/7, 320/37)`, `R(x) = (3/10)x - 26` (Tables 2-4, row 64). -/
private theorem innerR_piece_043 (x : ℝ) (h0 : 60 / 7 < x) (h1 : x < 320 / 37) :
    innerR x = 3 / 10 * x + -26 := by
  rw [innerR_eq_of_ge (x := x) (n := 8) (q := 17) (m := 0) (q' := 1) (T := 21)
    (k := 15) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(320/37, 80/9)`, `R(x) = (117/20)x - 74` (Tables 2-4, rows 65-67). -/
private theorem innerR_piece_044 (x : ℝ) (h0 : 320 / 37 < x) (h1 : x < 80 / 9) :
    innerR x = 117 / 20 * x + -74 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 17) (m := 0) (q' := 1) (T := 21)
    (k := 16) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(80/9, 440/49)`, `R(x) = (45/8)x - 72` (Tables 2-4, row 68). -/
private theorem innerR_piece_045 (x : ℝ) (h0 : 80 / 9 < x) (h1 : x < 440 / 49) :
    innerR x = 45 / 8 * x + -72 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 17) (m := 0) (q' := 1) (T := 21)
    (k := 16) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(440/49, 9)`, `R(x) = (22/5)x - 61` (Tables 2-4, row 69). -/
private theorem innerR_piece_046 (x : ℝ) (h0 : 440 / 49 < x) (h1 : x < 9) :
    innerR x = 22 / 5 * x + -61 := by
  rw [innerR_eq_of_le (x := x) (n := 8) (q := 17) (m := 0) (q' := 1) (T := 22)
    (k := 16) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(9, 340/37)`, `R(x) = (71/20)x - 70` (Tables 2-4, rows 70-71). -/
private theorem innerR_piece_047 (x : ℝ) (h0 : 9 < x) (h1 : x < 340 / 37) :
    innerR x = 71 / 20 * x + -70 := by
  rw [innerR_eq_of_le (x := x) (n := 9) (q := 18) (m := 0) (q' := 1) (T := 22)
    (k := 16) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(340/37, 400/43)`, `R(x) = (27/5)x - 87` (Tables 2-4, row 72). -/
private theorem innerR_piece_048 (x : ℝ) (h0 : 340 / 37 < x) (h1 : x < 400 / 43) :
    innerR x = 27 / 5 * x + -87 := by
  rw [innerR_eq_of_le (x := x) (n := 9) (q := 18) (m := 0) (q' := 1) (T := 22)
    (k := 17) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(400/43, 460/49)`, `R(x) = (11/10)x - 47` (Tables 2-4, row 73). -/
private theorem innerR_piece_049 (x : ℝ) (h0 : 400 / 43 < x) (h1 : x < 460 / 49) :
    innerR x = 11 / 10 * x + -47 := by
  rw [innerR_eq_of_ge (x := x) (n := 9) (q := 18) (m := 0) (q' := 1) (T := 22)
    (k := 17) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(460/49, 19/2)`, `R(x) = (-1/8)x - 71/2` (Tables 2-4, row 74). -/
private theorem innerR_piece_050 (x : ℝ) (h0 : 460 / 49 < x) (h1 : x < 19 / 2) :
    innerR x = -1 / 8 * x + -71 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 9) (q := 18) (m := 0) (q' := 1) (T := 23)
    (k := 17) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(19/2, 360/37)`, `R(x) = (7/8)x - 45` (Tables 2-4, rows 75-76). -/
private theorem innerR_piece_051 (x : ℝ) (h0 : 19 / 2 < x) (h1 : x < 360 / 37) :
    innerR x = 7 / 8 * x + -45 := by
  rw [innerR_eq_of_ge (x := x) (n := 9) (q := 19) (m := 0) (q' := 1) (T := 23)
    (k := 17) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(360/37, 480/49)`, `R(x) = (257/40)x - 99` (Tables 2-4, rows 77-78). -/
private theorem innerR_piece_052 (x : ℝ) (h0 : 360 / 37 < x) (h1 : x < 480 / 49) :
    innerR x = 257 / 40 * x + -99 := by
  rw [innerR_eq_of_le (x := x) (n := 9) (q := 19) (m := 0) (q' := 1) (T := 23)
    (k := 18) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(480/49, 10)`, `R(x) = (26/5)x - 87` (Tables 2-4, row 79). -/
private theorem innerR_piece_053 (x : ℝ) (h0 : 480 / 49 < x) (h1 : x < 10) :
    innerR x = 26 / 5 * x + -87 := by
  rw [innerR_eq_of_le (x := x) (n := 9) (q := 19) (m := 0) (q' := 1) (T := 24)
    (k := 18) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(10, 500/49)`, `R(x) = (87/20)x - 97` (Tables 2-4, row 80). -/
private theorem innerR_piece_054 (x : ℝ) (h0 : 10 < x) (h1 : x < 500 / 49) :
    innerR x = 87 / 20 * x + -97 := by
  rw [innerR_eq_of_le (x := x) (n := 10) (q := 20) (m := 0) (q' := 1) (T := 24)
    (k := 18) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(500/49, 440/43)`, `R(x) = (25/8)x - 169/2` (Tables 2-4, row 81). -/
private theorem innerR_piece_055 (x : ℝ) (h0 : 500 / 49 < x) (h1 : x < 440 / 43) :
    innerR x = 25 / 8 * x + -169 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 10) (q := 20) (m := 0) (q' := 1) (T := 25)
    (k := 18) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(440/43, 380/37)`, `R(x) = (-47/40)x - 81/2` (Tables 2-4, row 82). -/
private theorem innerR_piece_056 (x : ℝ) (h0 : 440 / 43 < x) (h1 : x < 380 / 37) :
    innerR x = -47 / 40 * x + -81 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 10) (q := 20) (m := 0) (q' := 1) (T := 25)
    (k := 18) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(380/37, 21/2)`, `R(x) = (27/40)x - 119/2` (Tables 2-4, rows 83-84). -/
private theorem innerR_piece_057 (x : ℝ) (h0 : 380 / 37 < x) (h1 : x < 21 / 2) :
    innerR x = 27 / 40 * x + -119 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 10) (q := 20) (m := 0) (q' := 1) (T := 25)
    (k := 19) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(21/2, 520/49)`, `R(x) = (67/40)x - 70` (Tables 2-4, row 85). -/
private theorem innerR_piece_058 (x : ℝ) (h0 : 21 / 2 < x) (h1 : x < 520 / 49) :
    innerR x = 67 / 40 * x + -70 := by
  rw [innerR_eq_of_ge (x := x) (n := 10) (q := 21) (m := 0) (q' := 1) (T := 25)
    (k := 19) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(520/49, 400/37)`, `R(x) = (9/20)x - 57` (Tables 2-4, rows 86-87). -/
private theorem innerR_piece_059 (x : ℝ) (h0 : 520 / 49 < x) (h1 : x < 400 / 37) :
    innerR x = 9 / 20 * x + -57 := by
  rw [innerR_eq_of_ge (x := x) (n := 10) (q := 21) (m := 0) (q' := 1) (T := 26)
    (k := 19) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(400/37, 11)`, `R(x) = 6x - 117` (Tables 2-4, rows 88-89). -/
private theorem innerR_piece_060 (x : ℝ) (h0 : 400 / 37 < x) (h1 : x < 11) :
    innerR x = 6 * x + -117 := by
  rw [innerR_eq_of_le (x := x) (n := 10) (q := 21) (m := 0) (q' := 1) (T := 26)
    (k := 20) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(11, 540/49)`, `R(x) = (103/20)x - 128` (Tables 2-4, row 90). -/
private theorem innerR_piece_061 (x : ℝ) (h0 : 11 < x) (h1 : x < 540 / 49) :
    innerR x = 103 / 20 * x + -128 := by
  rw [innerR_eq_of_le (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 26)
    (k := 20) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(540/49, 100/9)`, `R(x) = (157/40)x - 229/2` (Tables 2-4, row 91). -/
private theorem innerR_piece_062 (x : ℝ) (h0 : 540 / 49 < x) (h1 : x < 100 / 9) :
    innerR x = 157 / 40 * x + -229 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 27)
    (k := 20) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(100/9, 480/43)`, `R(x) = (37/10)x - 112` (Tables 2-4, row 92). -/
private theorem innerR_piece_063 (x : ℝ) (h0 : 100 / 9 < x) (h1 : x < 480 / 43) :
    innerR x = 37 / 10 * x + -112 := by
  rw [innerR_eq_of_le (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 27)
    (k := 20) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(480/43, 420/37)`, `R(x) = (-3/5)x - 64` (Tables 2-4, rows 93-94). -/
private theorem innerR_piece_064 (x : ℝ) (h0 : 480 / 43 < x) (h1 : x < 420 / 37) :
    innerR x = -3 / 5 * x + -64 := by
  rw [innerR_eq_of_ge (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 27)
    (k := 20) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(420/37, 80/7)`, `R(x) = (5/4)x - 85` (Tables 2-4, row 95). -/
private theorem innerR_piece_065 (x : ℝ) (h0 : 420 / 37 < x) (h1 : x < 80 / 7) :
    innerR x = 5 / 4 * x + -85 := by
  rw [innerR_eq_of_ge (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 27)
    (k := 21) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(80/7, 23/2)`, `R(x) = (1/40)x - 71` (Tables 2-4, row 96). -/
private theorem innerR_piece_066 (x : ℝ) (h0 : 80 / 7 < x) (h1 : x < 23 / 2) :
    innerR x = 1 / 40 * x + -71 := by
  rw [innerR_eq_of_ge (x := x) (n := 11) (q := 22) (m := 0) (q' := 1) (T := 28)
    (k := 21) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(23/2, 580/49)`, `R(x) = (41/40)x - 165/2` (Tables 2-4, rows 97-100). -/
private theorem innerR_piece_067 (x : ℝ) (h0 : 23 / 2 < x) (h1 : x < 580 / 49) :
    innerR x = 41 / 40 * x + -165 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 11) (q := 23) (m := 0) (q' := 1) (T := 28)
    (k := 21) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(580/49, 440/37)`, `R(x) = (-1/5)x - 68` (Tables 2-4, row 101). -/
private theorem innerR_piece_068 (x : ℝ) (h0 : 580 / 49 < x) (h1 : x < 440 / 37) :
    innerR x = -1 / 5 * x + -68 := by
  rw [innerR_eq_of_ge (x := x) (n := 11) (q := 23) (m := 0) (q' := 1) (T := 29)
    (k := 21) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(440/37, 12)`, `R(x) = (107/20)x - 134` (Tables 2-4, row 102). -/
private theorem innerR_piece_069 (x : ℝ) (h0 : 440 / 37 < x) (h1 : x < 12) :
    innerR x = 107 / 20 * x + -134 := by
  rw [innerR_eq_of_le (x := x) (n := 11) (q := 23) (m := 0) (q' := 1) (T := 29)
    (k := 22) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(12, 520/43)`, `R(x) = (9/2)x - 146` (Tables 2-4, row 103). -/
private theorem innerR_piece_070 (x : ℝ) (h0 : 12 < x) (h1 : x < 520 / 43) :
    innerR x = 9 / 2 * x + -146 := by
  rw [innerR_eq_of_le (x := x) (n := 12) (q := 24) (m := 0) (q' := 1) (T := 29)
    (k := 22) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(520/43, 600/49)`, `R(x) = (1/5)x - 94` (Tables 2-4, rows 104-105). -/
private theorem innerR_piece_071 (x : ℝ) (h0 : 520 / 43 < x) (h1 : x < 600 / 49) :
    innerR x = 1 / 5 * x + -94 := by
  rw [innerR_eq_of_ge (x := x) (n := 12) (q := 24) (m := 0) (q' := 1) (T := 29)
    (k := 22) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(600/49, 460/37)`, `R(x) = (-41/40)x - 79` (Tables 2-4, row 106). -/
private theorem innerR_piece_072 (x : ℝ) (h0 : 600 / 49 < x) (h1 : x < 460 / 37) :
    innerR x = -41 / 40 * x + -79 := by
  rw [innerR_eq_of_ge (x := x) (n := 12) (q := 24) (m := 0) (q' := 1) (T := 30)
    (k := 22) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(460/37, 25/2)`, `R(x) = (33/40)x - 102` (Tables 2-4, row 107). -/
private theorem innerR_piece_073 (x : ℝ) (h0 : 460 / 37 < x) (h1 : x < 25 / 2) :
    innerR x = 33 / 40 * x + -102 := by
  rw [innerR_eq_of_ge (x := x) (n := 12) (q := 24) (m := 0) (q' := 1) (T := 30)
    (k := 23) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(25/2, 620/49)`, `R(x) = (73/40)x - 229/2` (Tables 2-4, rows 108-110). -/
private theorem innerR_piece_074 (x : ℝ) (h0 : 25 / 2 < x) (h1 : x < 620 / 49) :
    innerR x = 73 / 40 * x + -229 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 12) (q := 25) (m := 0) (q' := 1) (T := 30)
    (k := 23) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(620/49, 480/37)`, `R(x) = (3/5)x - 99` (Tables 2-4, row 111). -/
private theorem innerR_piece_075 (x : ℝ) (h0 : 620 / 49 < x) (h1 : x < 480 / 37) :
    innerR x = 3 / 5 * x + -99 := by
  rw [innerR_eq_of_ge (x := x) (n := 12) (q := 25) (m := 0) (q' := 1) (T := 31)
    (k := 23) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(480/37, 13)`, `R(x) = (123/20)x - 171` (Tables 2-4, row 112). -/
private theorem innerR_piece_076 (x : ℝ) (h0 : 480 / 37 < x) (h1 : x < 13) :
    innerR x = 123 / 20 * x + -171 := by
  rw [innerR_eq_of_le (x := x) (n := 12) (q := 25) (m := 0) (q' := 1) (T := 31)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(13, 560/43)`, `R(x) = (53/10)x - 184` (Tables 2-4, row 113). -/
private theorem innerR_piece_077 (x : ℝ) (h0 : 13 < x) (h1 : x < 560 / 43) :
    innerR x = 53 / 10 * x + -184 := by
  rw [innerR_eq_of_le (x := x) (n := 13) (q := 26) (m := 0) (q' := 1) (T := 31)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(560/43, 640/49)`, `R(x) = x - 128` (Tables 2-4, rows 114-115). -/
private theorem innerR_piece_078 (x : ℝ) (h0 : 560 / 43 < x) (h1 : x < 640 / 49) :
    innerR x = 1 * x + -128 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 26) (m := 0) (q' := 1) (T := 31)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(640/49, 40/3)`, `R(x) = (-9/40)x - 112` (Tables 2-4, row 116). -/
private theorem innerR_piece_079 (x : ℝ) (h0 : 640 / 49 < x) (h1 : x < 40 / 3) :
    innerR x = -9 / 40 * x + -112 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 26) (m := 0) (q' := 1) (T := 32)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_right (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(40/3, 660/49)`, `R(x) = (67/4)x - 141` (Tables 2-4, row 117). -/
private theorem innerR_piece_080 (x : ℝ) (h0 : 40 / 3 < x) (h1 : x < 660 / 49) :
    innerR x = 67 / 4 * x + -141 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 26) (m := 1) (q' := 2) (T := 32)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(660/49, 27/2)`, `R(x) = (621/40)x - 249/2` (Tables 2-4, rows 118-120). -/
private theorem innerR_piece_081 (x : ℝ) (h0 : 660 / 49 < x) (h1 : x < 27 / 2) :
    innerR x = 621 / 40 * x + -249 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 26) (m := 1) (q' := 2) (T := 33)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(27/2, 500/37)`, `R(x) = (661/40)x - 138` (Tables 2-4, row 121). -/
private theorem innerR_piece_082 (x : ℝ) (h0 : 27 / 2 < x) (h1 : x < 500 / 37) :
    innerR x = 661 / 40 * x + -138 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 27) (m := 1) (q' := 2) (T := 33)
    (k := 24) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(500/37, 680/49)`, `R(x) = (147/8)x - 163` (Tables 2-4, row 122). -/
private theorem innerR_piece_083 (x : ℝ) (h0 : 500 / 37 < x) (h1 : x < 680 / 49) :
    innerR x = 147 / 8 * x + -163 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 27) (m := 1) (q' := 2) (T := 33)
    (k := 25) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(680/49, 600/43)`, `R(x) = (343/20)x - 146` (Tables 2-4, rows 123-124). -/
private theorem innerR_piece_084 (x : ℝ) (h0 : 680 / 49 < x) (h1 : x < 600 / 43) :
    innerR x = 343 / 20 * x + -146 := by
  rw [innerR_eq_of_ge (x := x) (n := 13) (q := 27) (m := 1) (q' := 2) (T := 34)
    (k := 25) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(600/43, 14)`, `R(x) = (257/20)x - 86` (Tables 2-4, row 125). -/
private theorem innerR_piece_085 (x : ℝ) (h0 : 600 / 43 < x) (h1 : x < 14) :
    innerR x = 257 / 20 * x + -86 := by
  rw [innerR_eq_of_le (x := x) (n := 13) (q := 27) (m := 1) (q' := 2) (T := 34)
    (k := 25) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(14, 520/37)`, `R(x) = 12x - 100` (Tables 2-4, row 126). -/
private theorem innerR_piece_086 (x : ℝ) (h0 : 14 < x) (h1 : x < 520 / 37) :
    innerR x = 12 * x + -100 := by
  rw [innerR_eq_of_le (x := x) (n := 14) (q := 28) (m := 1) (q' := 2) (T := 34)
    (k := 25) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(520/37, 100/7)`, `R(x) = (351/20)x - 178` (Tables 2-4, row 127). -/
private theorem innerR_piece_087 (x : ℝ) (h0 : 520 / 37 < x) (h1 : x < 100 / 7) :
    innerR x = 351 / 20 * x + -178 := by
  rw [innerR_eq_of_ge (x := x) (n := 14) (q := 28) (m := 1) (q' := 2) (T := 34)
    (k := 26) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(100/7, 29/2)`, `R(x) = (653/40)x - 321/2` (Tables 2-4, rows 128-130). -/
private theorem innerR_piece_088 (x : ℝ) (h0 : 100 / 7 < x) (h1 : x < 29 / 2) :
    innerR x = 653 / 40 * x + -321 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 14) (q := 28) (m := 1) (q' := 2) (T := 35)
    (k := 26) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(29/2, 540/37)`, `R(x) = (693/40)x - 175` (Tables 2-4, row 131). -/
private theorem innerR_piece_089 (x : ℝ) (h0 : 29 / 2 < x) (h1 : x < 540 / 37) :
    innerR x = 693 / 40 * x + -175 := by
  rw [innerR_eq_of_ge (x := x) (n := 14) (q := 29) (m := 1) (q' := 2) (T := 35)
    (k := 26) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(540/37, 720/49)`, `R(x) = (767/40)x - 202` (Tables 2-4, row 132). -/
private theorem innerR_piece_090 (x : ℝ) (h0 : 540 / 37 < x) (h1 : x < 720 / 49) :
    innerR x = 767 / 40 * x + -202 := by
  rw [innerR_eq_of_ge (x := x) (n := 14) (q := 29) (m := 1) (q' := 2) (T := 35)
    (k := 27) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(720/49, 640/43)`, `R(x) = (359/20)x - 184` (Tables 2-4, rows 133-134). -/
private theorem innerR_piece_091 (x : ℝ) (h0 : 720 / 49 < x) (h1 : x < 640 / 43) :
    innerR x = 359 / 20 * x + -184 := by
  rw [innerR_eq_of_ge (x := x) (n := 14) (q := 29) (m := 1) (q' := 2) (T := 36)
    (k := 27) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(640/43, 15)`, `R(x) = (273/20)x - 120` (Tables 2-4, row 135). -/
private theorem innerR_piece_092 (x : ℝ) (h0 : 640 / 43 < x) (h1 : x < 15) :
    innerR x = 273 / 20 * x + -120 := by
  rw [innerR_eq_of_le (x := x) (n := 14) (q := 29) (m := 1) (q' := 2) (T := 36)
    (k := 27) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(15, 740/49)`, `R(x) = (64/5)x - 135` (Tables 2-4, row 136). -/
private theorem innerR_piece_093 (x : ℝ) (h0 : 15 < x) (h1 : x < 740 / 49) :
    innerR x = 64 / 5 * x + -135 := by
  rw [innerR_eq_of_le (x := x) (n := 15) (q := 30) (m := 1) (q' := 2) (T := 36)
    (k := 27) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(740/49, 560/37)`, `R(x) = (463/40)x - 233/2` (Tables 2-4, row 137). -/
private theorem innerR_piece_094 (x : ℝ) (h0 : 740 / 49 < x) (h1 : x < 560 / 37) :
    innerR x = 463 / 40 * x + -233 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 15) (q := 30) (m := 1) (q' := 2) (T := 37)
    (k := 27) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(560/37, 31/2)`, `R(x) = (137/8)x - 401/2` (Tables 2-4, rows 138-140). -/
private theorem innerR_piece_095 (x : ℝ) (h0 : 560 / 37 < x) (h1 : x < 31 / 2) :
    innerR x = 137 / 8 * x + -401 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 15) (q := 30) (m := 1) (q' := 2) (T := 37)
    (k := 28) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(31/2, 760/49)`, `R(x) = (145/8)x - 216` (Tables 2-4, row 141). -/
private theorem innerR_piece_096 (x : ℝ) (h0 : 31 / 2 < x) (h1 : x < 760 / 49) :
    innerR x = 145 / 8 * x + -216 := by
  rw [innerR_eq_of_ge (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 37)
    (k := 28) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(760/49, 140/9)`, `R(x) = (169/10)x - 197` (Tables 2-4, row 142). -/
private theorem innerR_piece_097 (x : ℝ) (h0 : 760 / 49 < x) (h1 : x < 140 / 9) :
    innerR x = 169 / 10 * x + -197 := by
  rw [innerR_eq_of_ge (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 38)
    (k := 28) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(140/9, 580/37)`, `R(x) = (667/40)x - 387/2` (Tables 2-4, rows 143-144). -/
private theorem innerR_piece_098 (x : ℝ) (h0 : 140 / 9 < x) (h1 : x < 580 / 37) :
    innerR x = 667 / 40 * x + -387 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 38)
    (k := 28) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(580/37, 680/43)`, `R(x) = (741/40)x - 445/2` (Tables 2-4, row 145). -/
private theorem innerR_piece_099 (x : ℝ) (h0 : 580 / 37 < x) (h1 : x < 680 / 43) :
    innerR x = 741 / 40 * x + -445 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 38)
    (k := 29) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(680/43, 780/49)`, `R(x) = (569/40)x - 309/2` (Tables 2-4, row 146). -/
private theorem innerR_piece_100 (x : ℝ) (h0 : 680 / 43 < x) (h1 : x < 780 / 49) :
    innerR x = 569 / 40 * x + -309 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 38)
    (k := 29) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(780/49, 16)`, `R(x) = 13x - 135` (Tables 2-4, row 147). -/
private theorem innerR_piece_101 (x : ℝ) (h0 : 780 / 49 < x) (h1 : x < 16) :
    innerR x = 13 * x + -135 := by
  rw [innerR_eq_of_le (x := x) (n := 15) (q := 31) (m := 1) (q' := 2) (T := 39)
    (k := 29) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(16, 600/37)`, `R(x) = (243/20)x - 151` (Tables 2-4, rows 148-149). -/
private theorem innerR_piece_102 (x : ℝ) (h0 : 16 < x) (h1 : x < 600 / 37) :
    innerR x = 243 / 20 * x + -151 := by
  rw [innerR_eq_of_le (x := x) (n := 16) (q := 32) (m := 1) (q' := 2) (T := 39)
    (k := 29) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(600/37, 800/49)`, `R(x) = (177/10)x - 241` (Tables 2-4, rows 150-151). -/
private theorem innerR_piece_103 (x : ℝ) (h0 : 600 / 37 < x) (h1 : x < 800 / 49) :
    innerR x = 177 / 10 * x + -241 := by
  rw [innerR_eq_of_ge (x := x) (n := 16) (q := 32) (m := 1) (q' := 2) (T := 39)
    (k := 30) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(800/49, 33/2)`, `R(x) = (659/40)x - 221` (Tables 2-4, row 152). -/
private theorem innerR_piece_104 (x : ℝ) (h0 : 800 / 49 < x) (h1 : x < 33 / 2) :
    innerR x = 659 / 40 * x + -221 := by
  rw [innerR_eq_of_ge (x := x) (n := 16) (q := 32) (m := 1) (q' := 2) (T := 40)
    (k := 30) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(33/2, 820/49)`, `R(x) = (699/40)x - 475/2` (Tables 2-4, rows 153-155). -/
private theorem innerR_piece_105 (x : ℝ) (h0 : 33 / 2 < x) (h1 : x < 820 / 49) :
    innerR x = 699 / 40 * x + -475 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 16) (q := 33) (m := 1) (q' := 2) (T := 40)
    (k := 30) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(820/49, 720/43)`, `R(x) = (65/4)x - 217` (Tables 2-4, row 156). -/
private theorem innerR_piece_106 (x : ℝ) (h0 : 820 / 49 < x) (h1 : x < 720 / 43) :
    innerR x = 65 / 4 * x + -217 := by
  rw [innerR_eq_of_ge (x := x) (n := 16) (q := 33) (m := 1) (q' := 2) (T := 41)
    (k := 30) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(720/43, 620/37)`, `R(x) = (239/20)x - 145` (Tables 2-4, row 157). -/
private theorem innerR_piece_107 (x : ℝ) (h0 : 720 / 43 < x) (h1 : x < 620 / 37) :
    innerR x = 239 / 20 * x + -145 := by
  rw [innerR_eq_of_le (x := x) (n := 16) (q := 33) (m := 1) (q' := 2) (T := 41)
    (k := 30) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(620/37, 17)`, `R(x) = (69/5)x - 176` (Tables 2-4, rows 158-159). -/
private theorem innerR_piece_108 (x : ℝ) (h0 : 620 / 37 < x) (h1 : x < 17) :
    innerR x = 69 / 5 * x + -176 := by
  rw [innerR_eq_of_le (x := x) (n := 16) (q := 33) (m := 1) (q' := 2) (T := 41)
    (k := 31) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(17, 120/7)`, `R(x) = (259/20)x - 193` (Tables 2-4, row 160). -/
private theorem innerR_piece_109 (x : ℝ) (h0 : 17 < x) (h1 : x < 120 / 7) :
    innerR x = 259 / 20 * x + -193 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 34) (m := 1) (q' := 2) (T := 41)
    (k := 31) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(120/7, 640/37)`, `R(x) = (469/40)x - 172` (Tables 2-4, rows 161-162). -/
private theorem innerR_piece_110 (x : ℝ) (h0 : 120 / 7 < x) (h1 : x < 640 / 37) :
    innerR x = 469 / 40 * x + -172 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 34) (m := 1) (q' := 2) (T := 42)
    (k := 31) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(640/37, 35/2)`, `R(x) = (691/40)x - 268` (Tables 2-4, rows 163-164). -/
private theorem innerR_piece_111 (x : ℝ) (h0 : 640 / 37 < x) (h1 : x < 35 / 2) :
    innerR x = 691 / 40 * x + -268 := by
  rw [innerR_eq_of_ge (x := x) (n := 17) (q := 34) (m := 1) (q' := 2) (T := 42)
    (k := 32) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(35/2, 860/49)`, `R(x) = (731/40)x - 571/2` (Tables 2-4, row 165). -/
private theorem innerR_piece_112 (x : ℝ) (h0 : 35 / 2 < x) (h1 : x < 860 / 49) :
    innerR x = 731 / 40 * x + -571 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 42)
    (k := 32) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(860/49, 760/43)`, `R(x) = (341/20)x - 264` (Tables 2-4, row 166). -/
private theorem innerR_piece_113 (x : ℝ) (h0 : 860 / 49 < x) (h1 : x < 760 / 43) :
    innerR x = 341 / 20 * x + -264 := by
  rw [innerR_eq_of_ge (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 43)
    (k := 32) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(760/43, 160/9)`, `R(x) = (51/4)x - 188` (Tables 2-4, row 167). -/
private theorem innerR_piece_114 (x : ℝ) (h0 : 760 / 43 < x) (h1 : x < 160 / 9) :
    innerR x = 51 / 4 * x + -188 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 43)
    (k := 32) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(160/9, 660/37)`, `R(x) = (501/40)x - 184` (Tables 2-4, rows 168-169). -/
private theorem innerR_piece_115 (x : ℝ) (h0 : 160 / 9 < x) (h1 : x < 660 / 37) :
    innerR x = 501 / 40 * x + -184 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 43)
    (k := 32) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(660/37, 880/49)`, `R(x) = (115/8)x - 217` (Tables 2-4, row 170). -/
private theorem innerR_piece_116 (x : ℝ) (h0 : 660 / 37 < x) (h1 : x < 880 / 49) :
    innerR x = 115 / 8 * x + -217 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 43)
    (k := 33) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(880/49, 18)`, `R(x) = (263/20)x - 195` (Tables 2-4, row 171). -/
private theorem innerR_piece_117 (x : ℝ) (h0 : 880 / 49 < x) (h1 : x < 18) :
    innerR x = 263 / 20 * x + -195 := by
  rw [innerR_eq_of_le (x := x) (n := 17) (q := 35) (m := 1) (q' := 2) (T := 44)
    (k := 33) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(18, 900/49)`, `R(x) = (123/10)x - 213` (Tables 2-4, rows 172-175). -/
private theorem innerR_piece_118 (x : ℝ) (h0 : 18 < x) (h1 : x < 900 / 49) :
    innerR x = 123 / 10 * x + -213 := by
  rw [innerR_eq_of_le (x := x) (n := 18) (q := 36) (m := 1) (q' := 2) (T := 44)
    (k := 33) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(900/49, 680/37)`, `R(x) = (443/40)x - 381/2` (Tables 2-4, row 176). -/
private theorem innerR_piece_119 (x : ℝ) (h0 : 900 / 49 < x) (h1 : x < 680 / 37) :
    innerR x = 443 / 40 * x + -381 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 18) (q := 36) (m := 1) (q' := 2) (T := 45)
    (k := 33) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(680/37, 37/2)`, `R(x) = (133/8)x - 585/2` (Tables 2-4, row 177). -/
private theorem innerR_piece_120 (x : ℝ) (h0 : 680 / 37 < x) (h1 : x < 37 / 2) :
    innerR x = 133 / 8 * x + -585 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 18) (q := 36) (m := 1) (q' := 2) (T := 45)
    (k := 34) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(37/2, 800/43)`, `R(x) = (141/8)x - 311` (Tables 2-4, row 178). -/
private theorem innerR_piece_121 (x : ℝ) (h0 : 37 / 2 < x) (h1 : x < 800 / 43) :
    innerR x = 141 / 8 * x + -311 := by
  rw [innerR_eq_of_ge (x := x) (n := 18) (q := 37) (m := 1) (q' := 2) (T := 45)
    (k := 34) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(800/43, 920/49)`, `R(x) = (533/40)x - 231` (Tables 2-4, rows 179-180). -/
private theorem innerR_piece_122 (x : ℝ) (h0 : 800 / 43 < x) (h1 : x < 920 / 49) :
    innerR x = 533 / 40 * x + -231 := by
  rw [innerR_eq_of_le (x := x) (n := 18) (q := 37) (m := 1) (q' := 2) (T := 45)
    (k := 34) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(920/49, 700/37)`, `R(x) = (121/10)x - 208` (Tables 2-4, row 181). -/
private theorem innerR_piece_123 (x : ℝ) (h0 : 920 / 49 < x) (h1 : x < 700 / 37) :
    innerR x = 121 / 10 * x + -208 := by
  rw [innerR_eq_of_le (x := x) (n := 18) (q := 37) (m := 1) (q' := 2) (T := 46)
    (k := 34) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(700/37, 19)`, `R(x) = (279/20)x - 243` (Tables 2-4, row 182). -/
private theorem innerR_piece_124 (x : ℝ) (h0 : 700 / 37 < x) (h1 : x < 19) :
    innerR x = 279 / 20 * x + -243 := by
  rw [innerR_eq_of_le (x := x) (n := 18) (q := 37) (m := 1) (q' := 2) (T := 46)
    (k := 35) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(19, 940/49)`, `R(x) = (131/10)x - 262` (Tables 2-4, rows 183-185). -/
private theorem innerR_piece_125 (x : ℝ) (h0 : 19 < x) (h1 : x < 940 / 49) :
    innerR x = 131 / 10 * x + -262 := by
  rw [innerR_eq_of_le (x := x) (n := 19) (q := 38) (m := 1) (q' := 2) (T := 46)
    (k := 35) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(940/49, 720/37)`, `R(x) = (95/8)x - 477/2` (Tables 2-4, row 186). -/
private theorem innerR_piece_126 (x : ℝ) (h0 : 940 / 49 < x) (h1 : x < 720 / 37) :
    innerR x = 95 / 8 * x + -477 / 2 := by
  rw [innerR_eq_of_le (x := x) (n := 19) (q := 38) (m := 1) (q' := 2) (T := 47)
    (k := 35) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(720/37, 39/2)`, `R(x) = (697/40)x - 693/2` (Tables 2-4, row 187). -/
private theorem innerR_piece_127 (x : ℝ) (h0 : 720 / 37 < x) (h1 : x < 39 / 2) :
    innerR x = 697 / 40 * x + -693 / 2 := by
  rw [innerR_eq_of_ge (x := x) (n := 19) (q := 38) (m := 1) (q' := 2) (T := 47)
    (k := 36) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_left (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-- On `(39/2, 840/43)`, `R(x) = (737/40)x - 366` (Tables 2-4, row 188). -/
private theorem innerR_piece_128 (x : ℝ) (h0 : 39 / 2 < x) (h1 : x < 840 / 43) :
    innerR x = 737 / 40 * x + -366 := by
  rw [innerR_eq_of_ge (x := x) (n := 19) (q := 39) (m := 1) (q' := 2) (T := 47)
    (k := 36) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(840/43, 960/49)`, `R(x) = (113/8)x - 282` (Tables 2-4, rows 189-190). -/
private theorem innerR_piece_129 (x : ℝ) (h0 : 840 / 43 < x) (h1 : x < 960 / 49) :
    innerR x = 113 / 8 * x + -282 := by
  rw [innerR_eq_of_le (x := x) (n := 19) (q := 39) (m := 1) (q' := 2) (T := 47)
    (k := 36) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_left (by push_cast; linarith))]
  push_cast
  ring

/-- On `(960/49, 20)`, `R(x) = (129/10)x - 258` (Tables 2-4, row 191). -/
private theorem innerR_piece_130 (x : ℝ) (h0 : 960 / 49 < x) (h1 : x < 20) :
    innerR x = 129 / 10 * x + -258 := by
  rw [innerR_eq_of_le (x := x) (n := 19) (q := 39) (m := 1) (q' := 2) (T := 48)
    (k := 36) (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))
    (min_eq_right (by push_cast; linarith)) (min_eq_left (by push_cast; linarith))
    (by push_cast; linarith) (max_eq_right (by push_cast; linarith))]
  push_cast
  ring

/-! ### The table of pieces -/

/-- The 131 pieces `(l, u, a, b)` of `[3, 20]`, in order: `R(x) = ax + b` for `l < x < u`
(`ZetaSeven.innerR_eq_of_mem_innerRPieces`). Consecutive pieces share an endpoint; the cut points
are the points of `[3, 20]` where `cx` is an integer for some
`c ∈ {1, 2, α, 2α, 2H, 2λ, 1 - α, 1 + α, 9/20}`. Each piece is the union of the rows of
Tables 2-4 noted beside it, which all have these coefficients. -/
noncomputable def innerRPieces : List (ℝ × ℝ × ℝ × ℝ) :=
  [(3, 120 / 37, 51 / 20, 1), -- rows 0-1
   (120 / 37, 160 / 49, 81 / 10, -17), -- rows 2-3
   (160 / 49, 7 / 2, 55 / 8, -13), -- rows 4-6
   (7 / 2, 180 / 49, 63 / 8, -33 / 2), -- row 7
   (180 / 49, 160 / 43, 133 / 20, -12), -- row 8
   (160 / 43, 140 / 37, 47 / 20, 4), -- row 9
   (140 / 37, 4, 21 / 5, -3), -- rows 10-11
   (4, 200 / 49, 67 / 20, -7), -- row 12
   (200 / 49, 160 / 37, 17 / 8, -2), -- rows 13-14
   (160 / 37, 40 / 9, 307 / 40, -26), -- rows 15-16
   (40 / 9, 220 / 49, 149 / 20, -25), -- row 17
   (220 / 49, 9 / 2, 249 / 40, -39 / 2), -- row 18
   (9 / 2, 200 / 43, 289 / 40, -24), -- row 19
   (200 / 43, 180 / 37, 117 / 40, -4), -- rows 20-21
   (180 / 37, 240 / 49, 191 / 40, -13), -- row 22
   (240 / 49, 5, 71 / 20, -7), -- row 23
   (5, 260 / 49, 27 / 10, -12), -- rows 24-26
   (260 / 49, 200 / 37, 59 / 40, -11 / 2), -- row 27
   (200 / 37, 11 / 2, 281 / 40, -71 / 2), -- row 28
   (11 / 2, 240 / 43, 321 / 40, -41), -- row 29
   (240 / 43, 40 / 7, 149 / 40, -17), -- rows 30-31
   (40 / 7, 220 / 37, 5 / 2, -10), -- row 32
   (220 / 37, 6, 87 / 20, -21), -- row 33
   (6, 300 / 49, 7 / 2, -27), -- rows 34-36
   (300 / 49, 240 / 37, 91 / 40, -39 / 2), -- row 37
   (240 / 37, 13 / 2, 313 / 40, -111 / 2), -- row 38
   (13 / 2, 280 / 43, 353 / 40, -62), -- row 39
   (280 / 43, 320 / 49, 181 / 40, -34), -- rows 40-41
   (320 / 49, 20 / 3, 33 / 10, -26), -- row 42
   (20 / 3, 340 / 49, 219 / 40, -81 / 2), -- row 43
   (340 / 49, 7, 17 / 4, -32), -- rows 44-46
   (7, 260 / 37, 17 / 5, -39), -- row 47
   (260 / 37, 360 / 49, 21 / 4, -52), -- row 48
   (360 / 49, 320 / 43, 161 / 40, -43), -- rows 49-50
   (320 / 43, 15 / 2, -11 / 40, -11), -- row 51
   (15 / 2, 280 / 37, 29 / 40, -37 / 2), -- row 52
   (280 / 37, 380 / 49, 251 / 40, -121 / 2), -- row 53
   (380 / 49, 8, 101 / 20, -51), -- rows 54-56
   (8, 300 / 37, 21 / 5, -59), -- row 57
   (300 / 37, 400 / 49, 121 / 20, -74), -- row 58
   (400 / 49, 360 / 43, 193 / 40, -64), -- rows 59-61
   (360 / 43, 17 / 2, 21 / 40, -28), -- row 62
   (17 / 2, 60 / 7, 61 / 40, -73 / 2), -- row 63
   (60 / 7, 320 / 37, 3 / 10, -26), -- row 64
   (320 / 37, 80 / 9, 117 / 20, -74), -- rows 65-67
   (80 / 9, 440 / 49, 45 / 8, -72), -- row 68
   (440 / 49, 9, 22 / 5, -61), -- row 69
   (9, 340 / 37, 71 / 20, -70), -- rows 70-71
   (340 / 37, 400 / 43, 27 / 5, -87), -- row 72
   (400 / 43, 460 / 49, 11 / 10, -47), -- row 73
   (460 / 49, 19 / 2, -1 / 8, -71 / 2), -- row 74
   (19 / 2, 360 / 37, 7 / 8, -45), -- rows 75-76
   (360 / 37, 480 / 49, 257 / 40, -99), -- rows 77-78
   (480 / 49, 10, 26 / 5, -87), -- row 79
   (10, 500 / 49, 87 / 20, -97), -- row 80
   (500 / 49, 440 / 43, 25 / 8, -169 / 2), -- row 81
   (440 / 43, 380 / 37, -47 / 40, -81 / 2), -- row 82
   (380 / 37, 21 / 2, 27 / 40, -119 / 2), -- rows 83-84
   (21 / 2, 520 / 49, 67 / 40, -70), -- row 85
   (520 / 49, 400 / 37, 9 / 20, -57), -- rows 86-87
   (400 / 37, 11, 6, -117), -- rows 88-89
   (11, 540 / 49, 103 / 20, -128), -- row 90
   (540 / 49, 100 / 9, 157 / 40, -229 / 2), -- row 91
   (100 / 9, 480 / 43, 37 / 10, -112), -- row 92
   (480 / 43, 420 / 37, -3 / 5, -64), -- rows 93-94
   (420 / 37, 80 / 7, 5 / 4, -85), -- row 95
   (80 / 7, 23 / 2, 1 / 40, -71), -- row 96
   (23 / 2, 580 / 49, 41 / 40, -165 / 2), -- rows 97-100
   (580 / 49, 440 / 37, -1 / 5, -68), -- row 101
   (440 / 37, 12, 107 / 20, -134), -- row 102
   (12, 520 / 43, 9 / 2, -146), -- row 103
   (520 / 43, 600 / 49, 1 / 5, -94), -- rows 104-105
   (600 / 49, 460 / 37, -41 / 40, -79), -- row 106
   (460 / 37, 25 / 2, 33 / 40, -102), -- row 107
   (25 / 2, 620 / 49, 73 / 40, -229 / 2), -- rows 108-110
   (620 / 49, 480 / 37, 3 / 5, -99), -- row 111
   (480 / 37, 13, 123 / 20, -171), -- row 112
   (13, 560 / 43, 53 / 10, -184), -- row 113
   (560 / 43, 640 / 49, 1, -128), -- rows 114-115
   (640 / 49, 40 / 3, -9 / 40, -112), -- row 116
   (40 / 3, 660 / 49, 67 / 4, -141), -- row 117
   (660 / 49, 27 / 2, 621 / 40, -249 / 2), -- rows 118-120
   (27 / 2, 500 / 37, 661 / 40, -138), -- row 121
   (500 / 37, 680 / 49, 147 / 8, -163), -- row 122
   (680 / 49, 600 / 43, 343 / 20, -146), -- rows 123-124
   (600 / 43, 14, 257 / 20, -86), -- row 125
   (14, 520 / 37, 12, -100), -- row 126
   (520 / 37, 100 / 7, 351 / 20, -178), -- row 127
   (100 / 7, 29 / 2, 653 / 40, -321 / 2), -- rows 128-130
   (29 / 2, 540 / 37, 693 / 40, -175), -- row 131
   (540 / 37, 720 / 49, 767 / 40, -202), -- row 132
   (720 / 49, 640 / 43, 359 / 20, -184), -- rows 133-134
   (640 / 43, 15, 273 / 20, -120), -- row 135
   (15, 740 / 49, 64 / 5, -135), -- row 136
   (740 / 49, 560 / 37, 463 / 40, -233 / 2), -- row 137
   (560 / 37, 31 / 2, 137 / 8, -401 / 2), -- rows 138-140
   (31 / 2, 760 / 49, 145 / 8, -216), -- row 141
   (760 / 49, 140 / 9, 169 / 10, -197), -- row 142
   (140 / 9, 580 / 37, 667 / 40, -387 / 2), -- rows 143-144
   (580 / 37, 680 / 43, 741 / 40, -445 / 2), -- row 145
   (680 / 43, 780 / 49, 569 / 40, -309 / 2), -- row 146
   (780 / 49, 16, 13, -135), -- row 147
   (16, 600 / 37, 243 / 20, -151), -- rows 148-149
   (600 / 37, 800 / 49, 177 / 10, -241), -- rows 150-151
   (800 / 49, 33 / 2, 659 / 40, -221), -- row 152
   (33 / 2, 820 / 49, 699 / 40, -475 / 2), -- rows 153-155
   (820 / 49, 720 / 43, 65 / 4, -217), -- row 156
   (720 / 43, 620 / 37, 239 / 20, -145), -- row 157
   (620 / 37, 17, 69 / 5, -176), -- rows 158-159
   (17, 120 / 7, 259 / 20, -193), -- row 160
   (120 / 7, 640 / 37, 469 / 40, -172), -- rows 161-162
   (640 / 37, 35 / 2, 691 / 40, -268), -- rows 163-164
   (35 / 2, 860 / 49, 731 / 40, -571 / 2), -- row 165
   (860 / 49, 760 / 43, 341 / 20, -264), -- row 166
   (760 / 43, 160 / 9, 51 / 4, -188), -- row 167
   (160 / 9, 660 / 37, 501 / 40, -184), -- rows 168-169
   (660 / 37, 880 / 49, 115 / 8, -217), -- row 170
   (880 / 49, 18, 263 / 20, -195), -- row 171
   (18, 900 / 49, 123 / 10, -213), -- rows 172-175
   (900 / 49, 680 / 37, 443 / 40, -381 / 2), -- row 176
   (680 / 37, 37 / 2, 133 / 8, -585 / 2), -- row 177
   (37 / 2, 800 / 43, 141 / 8, -311), -- row 178
   (800 / 43, 920 / 49, 533 / 40, -231), -- rows 179-180
   (920 / 49, 700 / 37, 121 / 10, -208), -- row 181
   (700 / 37, 19, 279 / 20, -243), -- row 182
   (19, 940 / 49, 131 / 10, -262), -- rows 183-185
   (940 / 49, 720 / 37, 95 / 8, -477 / 2), -- row 186
   (720 / 37, 39 / 2, 697 / 40, -693 / 2), -- row 187
   (39 / 2, 840 / 43, 737 / 40, -366), -- row 188
   (840 / 43, 960 / 49, 113 / 8, -282), -- rows 189-190
   (960 / 49, 20, 129 / 10, -258)] -- row 191

/-- **`R` on the pieces** (Tables 2-4, on open intervals as in source-map erratum 12): for each
piece `(l, u, a, b)` of `ZetaSeven.innerRPieces`, `R(x) = ax + b` for `l < x < u`. -/
theorem innerR_eq_of_mem_innerRPieces {l u a b : ℝ} (hp : (l, u, a, b) ∈ innerRPieces) {x : ℝ}
    (h0 : l < x) (h1 : x < u) : innerR x = a * x + b := by
  have key : ∀ p ∈ innerRPieces, ∀ y : ℝ, p.1 < y → y < p.2.1 →
      innerR y = p.2.2.1 * y + p.2.2.2 := by
    simp only [innerRPieces, List.forall_mem_cons]
    exact ⟨innerR_piece_000, innerR_piece_001, innerR_piece_002, innerR_piece_003, innerR_piece_004,
      innerR_piece_005, innerR_piece_006, innerR_piece_007, innerR_piece_008, innerR_piece_009,
      innerR_piece_010, innerR_piece_011, innerR_piece_012, innerR_piece_013, innerR_piece_014,
      innerR_piece_015, innerR_piece_016, innerR_piece_017, innerR_piece_018, innerR_piece_019,
      innerR_piece_020, innerR_piece_021, innerR_piece_022, innerR_piece_023, innerR_piece_024,
      innerR_piece_025, innerR_piece_026, innerR_piece_027, innerR_piece_028, innerR_piece_029,
      innerR_piece_030, innerR_piece_031, innerR_piece_032, innerR_piece_033, innerR_piece_034,
      innerR_piece_035, innerR_piece_036, innerR_piece_037, innerR_piece_038, innerR_piece_039,
      innerR_piece_040, innerR_piece_041, innerR_piece_042, innerR_piece_043, innerR_piece_044,
      innerR_piece_045, innerR_piece_046, innerR_piece_047, innerR_piece_048, innerR_piece_049,
      innerR_piece_050, innerR_piece_051, innerR_piece_052, innerR_piece_053, innerR_piece_054,
      innerR_piece_055, innerR_piece_056, innerR_piece_057, innerR_piece_058, innerR_piece_059,
      innerR_piece_060, innerR_piece_061, innerR_piece_062, innerR_piece_063, innerR_piece_064,
      innerR_piece_065, innerR_piece_066, innerR_piece_067, innerR_piece_068, innerR_piece_069,
      innerR_piece_070, innerR_piece_071, innerR_piece_072, innerR_piece_073, innerR_piece_074,
      innerR_piece_075, innerR_piece_076, innerR_piece_077, innerR_piece_078, innerR_piece_079,
      innerR_piece_080, innerR_piece_081, innerR_piece_082, innerR_piece_083, innerR_piece_084,
      innerR_piece_085, innerR_piece_086, innerR_piece_087, innerR_piece_088, innerR_piece_089,
      innerR_piece_090, innerR_piece_091, innerR_piece_092, innerR_piece_093, innerR_piece_094,
      innerR_piece_095, innerR_piece_096, innerR_piece_097, innerR_piece_098, innerR_piece_099,
      innerR_piece_100, innerR_piece_101, innerR_piece_102, innerR_piece_103, innerR_piece_104,
      innerR_piece_105, innerR_piece_106, innerR_piece_107, innerR_piece_108, innerR_piece_109,
      innerR_piece_110, innerR_piece_111, innerR_piece_112, innerR_piece_113, innerR_piece_114,
      innerR_piece_115, innerR_piece_116, innerR_piece_117, innerR_piece_118, innerR_piece_119,
      innerR_piece_120, innerR_piece_121, innerR_piece_122, innerR_piece_123, innerR_piece_124,
      innerR_piece_125, innerR_piece_126, innerR_piece_127, innerR_piece_128, innerR_piece_129,
      innerR_piece_130, by simp⟩
  exact key _ hp x h0 h1

/-! ### The integral of `R(x)/x^3` over the pieces -/

private theorem innerPiece_000 : InnerPiece 3 (120 / 37) (689 / 9600) :=
  innerPiece_of_affine (a := 51 / 20) (b := 1) (by norm_num) (by norm_num)
    innerR_piece_000 (by norm_num)

private theorem innerPiece_001 : InnerPiece (120 / 37) (160 / 49) (2761 / 460800) :=
  innerPiece_of_affine (a := 81 / 10) (b := -17) (by norm_num) (by norm_num)
    innerR_piece_001 (by norm_num)

private theorem innerPiece_002 : InnerPiece (160 / 49) (7 / 2) (155963 / 2508800) :=
  innerPiece_of_affine (a := 55 / 8) (b := -13) (by norm_num) (by norm_num)
    innerR_piece_002 (by norm_num)

private theorem innerPiece_003 : InnerPiece (7 / 2) (180 / 49) (93449 / 2116800) :=
  innerPiece_of_affine (a := 63 / 8) (b := -33 / 2) (by norm_num) (by norm_num)
    innerR_piece_003 (by norm_num)

private theorem innerPiece_004 : InnerPiece (180 / 49) (160 / 43) (817 / 69120) :=
  innerPiece_of_affine (a := 133 / 20) (b := -12) (by norm_num) (by norm_num)
    innerR_piece_004 (by norm_num)

private theorem innerPiece_005 : InnerPiece (160 / 43) (140 / 37) (1913 / 125440) :=
  innerPiece_of_affine (a := 47 / 20) (b := 4) (by norm_num) (by norm_num)
    innerR_piece_005 (by norm_num)

private theorem innerPiece_006 : InnerPiece (140 / 37) 4 (12 / 245) :=
  innerPiece_of_affine (a := 21 / 5) (b := -3) (by norm_num) (by norm_num)
    innerR_piece_006 (by norm_num)

private theorem innerPiece_007 : InnerPiece 4 (200 / 49) (647 / 80000) :=
  innerPiece_of_affine (a := 67 / 20) (b := -7) (by norm_num) (by norm_num)
    innerR_piece_007 (by norm_num)

private theorem innerPiece_008 : InnerPiece (200 / 49) (160 / 37) (14509 / 640000) :=
  innerPiece_of_affine (a := 17 / 8) (b := -2) (by norm_num) (by norm_num)
    innerR_piece_008 (by norm_num)

private theorem innerPiece_009 : InnerPiece (160 / 37) (40 / 9) (279 / 25600) :=
  innerPiece_of_affine (a := 307 / 40) (b := -26) (by norm_num) (by norm_num)
    innerR_piece_009 (by norm_num)

private theorem innerPiece_010 : InnerPiece (40 / 9) (220 / 49) (1631 / 387200) :=
  innerPiece_of_affine (a := 149 / 20) (b := -25) (by norm_num) (by norm_num)
    innerR_piece_010 (by norm_num)

private theorem innerPiece_011 : InnerPiece (220 / 49) (9 / 2) (4981 / 5227200) :=
  innerPiece_of_affine (a := 249 / 40) (b := -39 / 2) (by norm_num) (by norm_num)
    innerR_piece_011 (by norm_num)

private theorem innerPiece_012 : InnerPiece (9 / 2) (200 / 43) (15431 / 1080000) :=
  innerPiece_of_affine (a := 289 / 40) (b := -24) (by norm_num) (by norm_num)
    innerR_piece_012 (by norm_num)

private theorem innerPiece_013 : InnerPiece (200 / 43) (180 / 37) (63767 / 3240000) :=
  innerPiece_of_affine (a := 117 / 40) (b := -4) (by norm_num) (by norm_num)
    innerR_piece_013 (by norm_num)

private theorem innerPiece_014 : InnerPiece (180 / 37) (240 / 49) (3041 / 1036800) :=
  innerPiece_of_affine (a := 191 / 40) (b := -13) (by norm_num) (by norm_num)
    innerR_piece_014 (by norm_num)

private theorem innerPiece_015 : InnerPiece (240 / 49) 5 (41 / 4608) :=
  innerPiece_of_affine (a := 71 / 20) (b := -7) (by norm_num) (by norm_num)
    innerR_piece_015 (by norm_num)

private theorem innerPiece_016 : InnerPiece 5 (260 / 49) (18 / 4225) :=
  innerPiece_of_affine (a := 27 / 10) (b := -12) (by norm_num) (by norm_num)
    innerR_piece_016 (by norm_num)

private theorem innerPiece_017 : InnerPiece (260 / 49) (200 / 37) (41931 / 27040000) :=
  innerPiece_of_affine (a := 59 / 40) (b := -11 / 2) (by norm_num) (by norm_num)
    innerR_piece_017 (by norm_num)

private theorem innerPiece_018 : InnerPiece (200 / 37) (11 / 2) (31661 / 19360000) :=
  innerPiece_of_affine (a := 281 / 40) (b := -71 / 2) (by norm_num) (by norm_num)
    innerR_piece_018 (by norm_num)

private theorem innerPiece_019 : InnerPiece (11 / 2) (240 / 43) (23093 / 13939200) :=
  innerPiece_of_affine (a := 321 / 40) (b := -41) (by norm_num) (by norm_num)
    innerR_piece_019 (by norm_num)

private theorem innerPiece_020 : InnerPiece (240 / 43) (40 / 7) (343 / 115200) :=
  innerPiece_of_affine (a := 149 / 40) (b := -17) (by norm_num) (by norm_num)
    innerR_piece_020 (by norm_num)

private theorem innerPiece_021 : InnerPiece (40 / 7) (220 / 37) (207 / 38720) :=
  innerPiece_of_affine (a := 5 / 2) (b := -10) (by norm_num) (by norm_num)
    innerR_piece_021 (by norm_num)

private theorem innerPiece_022 : InnerPiece (220 / 37) 6 (367 / 290400) :=
  innerPiece_of_affine (a := 87 / 20) (b := -21) (by norm_num) (by norm_num)
    innerR_piece_022 (by norm_num)

private theorem innerPiece_023 : InnerPiece 6 (300 / 49) (-191 / 60000) :=
  innerPiece_of_affine (a := 7 / 2) (b := -27) (by norm_num) (by norm_num)
    innerR_piece_023 (by norm_num)

private theorem innerPiece_024 : InnerPiece (300 / 49) (240 / 37) (-14443 / 1920000) :=
  innerPiece_of_affine (a := 91 / 40) (b := -39 / 2) (by norm_num) (by norm_num)
    innerR_piece_024 (by norm_num)

private theorem innerPiece_025 : InnerPiece (240 / 37) (13 / 2) (-601 / 2595840) :=
  innerPiece_of_affine (a := 313 / 40) (b := -111 / 2) (by norm_num) (by norm_num)
    innerR_piece_025 (by norm_num)

private theorem innerPiece_026 : InnerPiece (13 / 2) (280 / 43) (-1283 / 6624800) :=
  innerPiece_of_affine (a := 353 / 40) (b := -62) (by norm_num) (by norm_num)
    innerR_piece_026 (by norm_num)

private theorem innerPiece_027 : InnerPiece (280 / 43) (320 / 49) (-1543 / 5017600) :=
  innerPiece_of_affine (a := 181 / 40) (b := -34) (by norm_num) (by norm_num)
    innerR_piece_027 (by norm_num)

private theorem innerPiece_028 : InnerPiece (320 / 49) (20 / 3) (-41 / 20480) :=
  innerPiece_of_affine (a := 33 / 10) (b := -26) (by norm_num) (by norm_num)
    innerR_piece_028 (by norm_num)

private theorem innerPiece_029 : InnerPiece (20 / 3) (340 / 49) (-327 / 115600) :=
  innerPiece_of_affine (a := 219 / 40) (b := -81 / 2) (by norm_num) (by norm_num)
    innerR_piece_029 (by norm_num)

private theorem innerPiece_030 : InnerPiece (340 / 49) 7 (-2439 / 5664400) :=
  innerPiece_of_affine (a := 17 / 4) (b := -32) (by norm_num) (by norm_num)
    innerR_piece_030 (by norm_num)

private theorem innerPiece_031 : InnerPiece 7 (260 / 37) (-121 / 101920) :=
  innerPiece_of_affine (a := 17 / 5) (b := -39) (by norm_num) (by norm_num)
    innerR_piece_031 (by norm_num)

private theorem innerPiece_032 : InnerPiece (260 / 37) (360 / 49) (-5191 / 421200) :=
  innerPiece_of_affine (a := 21 / 4) (b := -52) (by norm_num) (by norm_num)
    innerR_piece_032 (by norm_num)

private theorem innerPiece_033 : InnerPiece (360 / 49) (320 / 43) (-10313 / 3317760) :=
  innerPiece_of_affine (a := 161 / 40) (b := -43) (by norm_num) (by norm_num)
    innerR_piece_033 (by norm_num)

private theorem innerPiece_034 : InnerPiece (320 / 43) (15 / 2) (-671 / 368640) :=
  innerPiece_of_affine (a := -11 / 40) (b := -11) (by norm_num) (by norm_num)
    innerR_piece_034 (by norm_num)

private theorem innerPiece_035 : InnerPiece (15 / 2) (280 / 37) (-1163 / 564480) :=
  innerPiece_of_affine (a := 29 / 40) (b := -37 / 2) (by norm_num) (by norm_num)
    innerR_piece_035 (by norm_num)

private theorem innerPiece_036 : InnerPiece (280 / 37) (380 / 49) (-587129 / 113209600) :=
  innerPiece_of_affine (a := 251 / 40) (b := -121 / 2) (by norm_num) (by norm_num)
    innerR_piece_036 (by norm_num)

private theorem innerPiece_037 : InnerPiece (380 / 49) 8 (-6501 / 1155200) :=
  innerPiece_of_affine (a := 101 / 20) (b := -51) (by norm_num) (by norm_num)
    innerR_piece_037 (by norm_num)

private theorem innerPiece_038 : InnerPiece 8 (300 / 37) (-3751 / 720000) :=
  innerPiece_of_affine (a := 21 / 5) (b := -59) (by norm_num) (by norm_num)
    innerR_piece_038 (by norm_num)

private theorem innerPiece_039 : InnerPiece (300 / 37) (400 / 49) (-731 / 288000) :=
  innerPiece_of_affine (a := 121 / 20) (b := -74) (by norm_num) (by norm_num)
    innerR_piece_039 (by norm_num)

private theorem innerPiece_040 : InnerPiece (400 / 49) (360 / 43) (-57761 / 6480000) :=
  innerPiece_of_affine (a := 193 / 40) (b := -64) (by norm_num) (by norm_num)
    innerR_piece_040 (by norm_num)

private theorem innerPiece_041 : InnerPiece (360 / 43) (17 / 2) (-188111 / 37454400) :=
  innerPiece_of_affine (a := 21 / 40) (b := -28) (by norm_num) (by norm_num)
    innerR_piece_041 (by norm_num)

private theorem innerPiece_042 : InnerPiece (17 / 2) (60 / 7) (-449 / 166464) :=
  innerPiece_of_affine (a := 61 / 40) (b := -73 / 2) (by norm_num) (by norm_num)
    innerR_piece_042 (by norm_num)

private theorem innerPiece_043 : InnerPiece (60 / 7) (320 / 37) (-2611 / 921600) :=
  innerPiece_of_affine (a := 3 / 10) (b := -26) (by norm_num) (by norm_num)
    innerR_piece_043 (by norm_num)

private theorem innerPiece_044 : InnerPiece (320 / 37) (80 / 9) (-829 / 102400) :=
  innerPiece_of_affine (a := 117 / 20) (b := -74) (by norm_num) (by norm_num)
    innerR_piece_044 (by norm_num)

private theorem innerPiece_045 : InnerPiece (80 / 9) (440 / 49) (-1071 / 387200) :=
  innerPiece_of_affine (a := 45 / 8) (b := -72) (by norm_num) (by norm_num)
    innerR_piece_045 (by norm_num)

private theorem innerPiece_046 : InnerPiece (440 / 49) 9 (-18893 / 31363200) :=
  innerPiece_of_affine (a := 22 / 5) (b := -61) (by norm_num) (by norm_num)
    innerR_piece_046 (by norm_num)

private theorem innerPiece_047 : InnerPiece 9 (340 / 37) (-22211 / 2340900) :=
  innerPiece_of_affine (a := 71 / 20) (b := -70) (by norm_num) (by norm_num)
    innerR_piece_047 (by norm_num)

private theorem innerPiece_048 : InnerPiece (340 / 37) (400 / 43) (-490833 / 92480000) :=
  innerPiece_of_affine (a := 27 / 5) (b := -87) (by norm_num) (by norm_num)
    innerR_piece_048 (by norm_num)

private theorem innerPiece_049 : InnerPiece (400 / 43) (460 / 49) (-650727 / 169280000) :=
  innerPiece_of_affine (a := 11 / 10) (b := -47) (by norm_num) (by norm_num)
    innerR_piece_049 (by norm_num)

private theorem innerPiece_050 : InnerPiece (460 / 49) (19 / 2) (-1493701 / 305550400) :=
  innerPiece_of_affine (a := -1 / 8) (b := -71 / 2) (by norm_num) (by norm_num)
    innerR_piece_050 (by norm_num)

private theorem innerPiece_051 : InnerPiece (19 / 2) (360 / 37) (-19669 / 2079360) :=
  innerPiece_of_affine (a := 7 / 8) (b := -45) (by norm_num) (by norm_num)
    innerR_piece_051 (by norm_num)

private theorem innerPiece_052 : InnerPiece (360 / 37) (480 / 49) (-1189 / 460800) :=
  innerPiece_of_affine (a := 257 / 40) (b := -99) (by norm_num) (by norm_num)
    innerR_piece_052 (by norm_num)

private theorem innerPiece_053 : InnerPiece (480 / 49) 10 (-383 / 51200) :=
  innerPiece_of_affine (a := 26 / 5) (b := -87) (by norm_num) (by norm_num)
    innerR_piece_053 (by norm_num)

private theorem innerPiece_054 : InnerPiece 10 (500 / 49) (-5253 / 500000) :=
  innerPiece_of_affine (a := 87 / 20) (b := -97) (by norm_num) (by norm_num)
    innerR_piece_054 (by norm_num)

private theorem innerPiece_055 : InnerPiece (500 / 49) (440 / 43) (-679071 / 484000000) :=
  innerPiece_of_affine (a := 25 / 8) (b := -169 / 2) (by norm_num) (by norm_num)
    innerR_piece_055 (by norm_num)

private theorem innerPiece_056 : InnerPiece (440 / 43) (380 / 37) (-514209 / 279558400) :=
  innerPiece_of_affine (a := -47 / 40) (b := -81 / 2) (by norm_num) (by norm_num)
    innerR_piece_056 (by norm_num)

private theorem innerPiece_057 : InnerPiece (380 / 37) (21 / 2) (-55981 / 5198400) :=
  innerPiece_of_affine (a := 27 / 40) (b := -119 / 2) (by norm_num) (by norm_num)
    innerR_piece_057 (by norm_num)

private theorem innerPiece_058 : InnerPiece (21 / 2) (520 / 49) (-21263 / 4258800) :=
  innerPiece_of_affine (a := 67 / 40) (b := -70) (by norm_num) (by norm_num)
    innerR_piece_058 (by norm_num)

private theorem innerPiece_059 : InnerPiece (520 / 49) (400 / 37) (-456003 / 54080000) :=
  innerPiece_of_affine (a := 9 / 20) (b := -57) (by norm_num) (by norm_num)
    innerR_piece_059 (by norm_num)

private theorem innerPiece_060 : InnerPiece (400 / 37) 11 (-291333 / 38720000) :=
  innerPiece_of_affine (a := 6) (b := -117) (by norm_num) (by norm_num)
    innerR_piece_060 (by norm_num)

private theorem innerPiece_061 : InnerPiece 11 (540 / 49) (-7693 / 7056720) :=
  innerPiece_of_affine (a := 103 / 20) (b := -128) (by norm_num) (by norm_num)
    innerR_piece_061 (by norm_num)

private theorem innerPiece_062 : InnerPiece (540 / 49) (100 / 9) (-34681 / 7290000) :=
  innerPiece_of_affine (a := 157 / 40) (b := -229 / 2) (by norm_num) (by norm_num)
    innerR_piece_062 (by norm_num)

private theorem innerPiece_063 : InnerPiece (100 / 9) (480 / 43) (-1907 / 720000) :=
  innerPiece_of_affine (a := 37 / 10) (b := -112) (by norm_num) (by norm_num)
    innerR_piece_063 (by norm_num)

private theorem innerPiece_064 : InnerPiece (480 / 43) (420 / 37) (-11 / 1176) :=
  innerPiece_of_affine (a := -3 / 5) (b := -64) (by norm_num) (by norm_num)
    innerR_piece_064 (by norm_num)

private theorem innerPiece_065 : InnerPiece (420 / 37) (80 / 7) (-835 / 225792) :=
  innerPiece_of_affine (a := 5 / 4) (b := -85) (by norm_num) (by norm_num)
    innerR_piece_065 (by norm_num)

private theorem innerPiece_066 : InnerPiece (80 / 7) (23 / 2) (-22699 / 6771200) :=
  innerPiece_of_affine (a := 1 / 40) (b := -71) (by norm_num) (by norm_num)
    innerR_piece_066 (by norm_num)

private theorem innerPiece_067 : InnerPiece (23 / 2) (580 / 49) (-10647813 / 711822400) :=
  innerPiece_of_affine (a := 41 / 40) (b := -165 / 2) (by norm_num) (by norm_num)
    innerR_piece_067 (by norm_num)

private theorem innerPiece_068 : InnerPiece (580 / 49) (440 / 37) (-37843 / 16281760) :=
  innerPiece_of_affine (a := -1 / 5) (b := -68) (by norm_num) (by norm_num)
    innerR_piece_068 (by norm_num)

private theorem innerPiece_069 : InnerPiece (440 / 37) 12 (-1549 / 348480) :=
  innerPiece_of_affine (a := 107 / 20) (b := -134) (by norm_num) (by norm_num)
    innerR_piece_069 (by norm_num)

private theorem innerPiece_070 : InnerPiece 12 (520 / 43) (-11887 / 2433600) :=
  innerPiece_of_affine (a := 9 / 2) (b := -146) (by norm_num) (by norm_num)
    innerR_piece_070 (by norm_num)

private theorem innerPiece_071 : InnerPiece (520 / 43) (600 / 49) (-29347 / 3802500) :=
  innerPiece_of_affine (a := 1 / 5) (b := -94) (by norm_num) (by norm_num)
    innerR_piece_071 (by norm_num)

private theorem innerPiece_072 : InnerPiece (600 / 49) (460 / 37) (-3485221 / 380880000) :=
  innerPiece_of_affine (a := -41 / 40) (b := -79) (by norm_num) (by norm_num)
    innerR_piece_072 (by norm_num)

private theorem innerPiece_073 : InnerPiece (460 / 37) (25 / 2) (-33843 / 10580000) :=
  innerPiece_of_affine (a := 33 / 40) (b := -102) (by norm_num) (by norm_num)
    innerR_piece_073 (by norm_num)

private theorem innerPiece_074 : InnerPiece (25 / 2) (620 / 49) (-270801 / 38440000) :=
  innerPiece_of_affine (a := 73 / 40) (b := -229 / 2) (by norm_num) (by norm_num)
    innerR_piece_074 (by norm_num)

private theorem innerPiece_075 : InnerPiece (620 / 49) (480 / 37) (-683501 / 49203200) :=
  innerPiece_of_affine (a := 3 / 5) (b := -99) (by norm_num) (by norm_num)
    innerR_piece_075 (by norm_num)

private theorem innerPiece_076 : InnerPiece (480 / 37) 13 (-9731 / 8652800) :=
  innerPiece_of_affine (a := 123 / 20) (b := -171) (by norm_num) (by norm_num)
    innerR_piece_076 (by norm_num)

private theorem innerPiece_077 : InnerPiece 13 (560 / 43) (-16091 / 13249600) :=
  innerPiece_of_affine (a := 53 / 10) (b := -184) (by norm_num) (by norm_num)
    innerR_piece_077 (by norm_num)

private theorem innerPiece_078 : InnerPiece (560 / 43) (640 / 49) (-617 / 313600) :=
  innerPiece_of_affine (a := 1) (b := -128) (by norm_num) (by norm_num)
    innerR_piece_078 (by norm_num)

private theorem innerPiece_079 : InnerPiece (640 / 49) (40 / 3) (-697 / 51200) :=
  innerPiece_of_affine (a := -9 / 40) (b := -112) (by norm_num) (by norm_num)
    innerR_piece_079 (by norm_num)

private theorem innerPiece_080 : InnerPiece (40 / 3) (660 / 49) (1827 / 387200) :=
  innerPiece_of_affine (a := 67 / 4) (b := -141) (by norm_num) (by norm_num)
    innerR_piece_080 (by norm_num)

private theorem innerPiece_081 : InnerPiece (660 / 49) (27 / 2) (9967 / 9408960) :=
  innerPiece_of_affine (a := 621 / 40) (b := -249 / 2) (by norm_num) (by norm_num)
    innerR_piece_081 (by norm_num)

private theorem innerPiece_082 : InnerPiece (27 / 2) (500 / 37) (56771 / 121500000) :=
  innerPiece_of_affine (a := 661 / 40) (b := -138) (by norm_num) (by norm_num)
    innerR_piece_082 (by norm_num)

private theorem innerPiece_083 : InnerPiece (500 / 37) (680 / 49) (7260693 / 578000000) :=
  innerPiece_of_affine (a := 147 / 8) (b := -163) (by norm_num) (by norm_num)
    innerR_piece_083 (by norm_num)

private theorem innerPiece_084 : InnerPiece (680 / 49) (600 / 43) (8489 / 3251250) :=
  innerPiece_of_affine (a := 343 / 20) (b := -146) (by norm_num) (by norm_num)
    innerR_piece_084 (by norm_num)

private theorem innerPiece_085 : InnerPiece (600 / 43) 14 (28127 / 17640000) :=
  innerPiece_of_affine (a := 257 / 20) (b := -86) (by norm_num) (by norm_num)
    innerR_piece_085 (by norm_num)

private theorem innerPiece_086 : InnerPiece 14 (520 / 37) (1773 / 1324960) :=
  innerPiece_of_affine (a := 12) (b := -100) (by norm_num) (by norm_num)
    innerR_piece_086 (by norm_num)

private theorem innerPiece_087 : InnerPiece (520 / 37) (100 / 7) (38901 / 6760000) :=
  innerPiece_of_affine (a := 351 / 20) (b := -178) (by norm_num) (by norm_num)
    innerR_piece_087 (by norm_num)

private theorem innerPiece_088 : InnerPiece (100 / 7) (29 / 2) (180021 / 33640000) :=
  innerPiece_of_affine (a := 653 / 40) (b := -321 / 2) (by norm_num) (by norm_num)
    innerR_piece_088 (by norm_num)

private theorem innerPiece_089 : InnerPiece (29 / 2) (540 / 37) (290227 / 122617800) :=
  innerPiece_of_affine (a := 693 / 40) (b := -175) (by norm_num) (by norm_num)
    innerR_piece_089 (by norm_num)

private theorem innerPiece_090 : InnerPiece (540 / 37) (720 / 49) (11623 / 4665600) :=
  innerPiece_of_affine (a := 767 / 40) (b := -202) (by norm_num) (by norm_num)
    innerR_piece_090 (by norm_num)

private theorem innerPiece_091 : InnerPiece (720 / 49) (640 / 43) (7931 / 1658880) :=
  innerPiece_of_affine (a := 359 / 20) (b := -184) (by norm_num) (by norm_num)
    innerR_piece_091 (by norm_num)

private theorem innerPiece_092 : InnerPiece (640 / 43) 15 (899 / 307200) :=
  innerPiece_of_affine (a := 273 / 20) (b := -120) (by norm_num) (by norm_num)
    innerR_piece_092 (by norm_num)

private theorem innerPiece_093 : InnerPiece 15 (740 / 49) (5669 / 3285600) :=
  innerPiece_of_affine (a := 64 / 5) (b := -135) (by norm_num) (by norm_num)
    innerR_piece_093 (by norm_num)

private theorem innerPiece_094 : InnerPiece (740 / 49) (560 / 37) (962049 / 1717273600) :=
  innerPiece_of_affine (a := 463 / 40) (b := -233 / 2) (by norm_num) (by norm_num)
    innerR_piece_094 (by norm_num)

private theorem innerPiece_095 : InnerPiece (560 / 37) (31 / 2) (7562511 / 1205478400) :=
  innerPiece_of_affine (a := 137 / 8) (b := -401 / 2) (by norm_num) (by norm_num)
    innerR_piece_095 (by norm_num)

private theorem innerPiece_096 : InnerPiece (31 / 2) (760 / 49) (98813 / 555073600) :=
  innerPiece_of_affine (a := 145 / 8) (b := -216) (by norm_num) (by norm_num)
    innerR_piece_096 (by norm_num)

private theorem innerPiece_097 : InnerPiece (760 / 49) (140 / 9) (44871 / 56604800) :=
  innerPiece_of_affine (a := 169 / 10) (b := -197) (by norm_num) (by norm_num)
    innerR_piece_097 (by norm_num)

private theorem innerPiece_098 : InnerPiece (140 / 9) (580 / 37) (34781 / 16483600) :=
  innerPiece_of_affine (a := 667 / 40) (b := -387 / 2) (by norm_num) (by norm_num)
    innerR_piece_098 (by norm_num)

private theorem innerPiece_099 : InnerPiece (580 / 37) (680 / 43) (3811797 / 1555513600) :=
  innerPiece_of_affine (a := 741 / 40) (b := -445 / 2) (by norm_num) (by norm_num)
    innerR_piece_099 (by norm_num)

private theorem innerPiece_100 : InnerPiece (680 / 43) (780 / 49) (581779 / 312582400) :=
  innerPiece_of_affine (a := 569 / 40) (b := -309 / 2) (by norm_num) (by norm_num)
    innerR_piece_100 (by norm_num)

private theorem innerPiece_101 : InnerPiece (780 / 49) 16 (1889 / 1297920) :=
  innerPiece_of_affine (a := 13) (b := -135) (by norm_num) (by norm_num)
    innerR_piece_101 (by norm_num)

private theorem innerPiece_102 : InnerPiece 16 (600 / 37) (6661 / 2880000) :=
  innerPiece_of_affine (a := 243 / 20) (b := -151) (by norm_num) (by norm_num)
    innerR_piece_102 (by norm_num)

private theorem innerPiece_103 : InnerPiece (600 / 37) (800 / 49) (2773 / 2304000) :=
  innerPiece_of_affine (a := 177 / 10) (b := -241) (by norm_num) (by norm_num)
    innerR_piece_103 (by norm_num)

private theorem innerPiece_104 : InnerPiece (800 / 49) (33 / 2) (2701691 / 1393920000) :=
  innerPiece_of_affine (a := 659 / 40) (b := -221) (by norm_num) (by norm_num)
    innerR_piece_104 (by norm_num)

private theorem innerPiece_105 : InnerPiece (33 / 2) (820 / 49) (7921637 / 2928974400) :=
  innerPiece_of_affine (a := 699 / 40) (b := -475 / 2) (by norm_num) (by norm_num)
    innerR_piece_105 (by norm_num)

private theorem innerPiece_106 : InnerPiece (820 / 49) (720 / 43) (194041 / 1742860800) :=
  innerPiece_of_affine (a := 65 / 4) (b := -217) (by norm_num) (by norm_num)
    innerR_piece_106 (by norm_num)

private theorem innerPiece_107 : InnerPiece (720 / 43) (620 / 37) (147023 / 996364800) :=
  innerPiece_of_affine (a := 239 / 20) (b := -145) (by norm_num) (by norm_num)
    innerR_piece_107 (by norm_num)

private theorem innerPiece_108 : InnerPiece (620 / 37) 17 (15993 / 5554580) :=
  innerPiece_of_affine (a := 69 / 5) (b := -176) (by norm_num) (by norm_num)
    innerR_piece_108 (by norm_num)

private theorem innerPiece_109 : InnerPiece 17 (120 / 7) (6709 / 8323200) :=
  innerPiece_of_affine (a := 259 / 20) (b := -193) (by norm_num) (by norm_num)
    innerR_piece_109 (by norm_num)

private theorem innerPiece_110 : InnerPiece (120 / 7) (640 / 37) (1667 / 1843200) :=
  innerPiece_of_affine (a := 469 / 40) (b := -172) (by norm_num) (by norm_num)
    innerR_piece_110 (by norm_num)

private theorem innerPiece_111 : InnerPiece (640 / 37) (35 / 2) (12573 / 10035200) :=
  innerPiece_of_affine (a := 691 / 40) (b := -268) (by norm_num) (by norm_num)
    innerR_piece_111 (by norm_num)

private theorem innerPiece_112 : InnerPiece (35 / 2) (860 / 49) (9557 / 28992320) :=
  innerPiece_of_affine (a := 731 / 40) (b := -571 / 2) (by norm_num) (by norm_num)
    innerR_piece_112 (by norm_num)

private theorem innerPiece_113 : InnerPiece (860 / 49) (760 / 43) (437723 / 533991200) :=
  innerPiece_of_affine (a := 341 / 20) (b := -264) (by norm_num) (by norm_num)
    innerR_piece_113 (by norm_num)

private theorem innerPiece_114 : InnerPiece (760 / 43) (160 / 9) (3259 / 4620800) :=
  innerPiece_of_affine (a := 51 / 4) (b := -188) (by norm_num) (by norm_num)
    innerR_piece_114 (by norm_num)

private theorem innerPiece_115 : InnerPiece (160 / 9) (660 / 37) (1447 / 3484800) :=
  innerPiece_of_affine (a := 501 / 40) (b := -184) (by norm_num) (by norm_num)
    innerR_piece_115 (by norm_num)

private theorem innerPiece_116 : InnerPiece (660 / 37) (880 / 49) (2377 / 2787840) :=
  innerPiece_of_affine (a := 115 / 8) (b := -217) (by norm_num) (by norm_num)
    innerR_piece_116 (by norm_num)

private theorem innerPiece_117 : InnerPiece (880 / 49) 18 (12167 / 41817600) :=
  innerPiece_of_affine (a := 263 / 20) (b := -195) (by norm_num) (by norm_num)
    innerR_piece_117 (by norm_num)

private theorem innerPiece_118 : InnerPiece 18 (900 / 49) (13 / 20000) :=
  innerPiece_of_affine (a := 123 / 10) (b := -213) (by norm_num) (by norm_num)
    innerR_piece_118 (by norm_num)

private theorem innerPiece_119 : InnerPiece (900 / 49) (680 / 37) (28823 / 1248480000) :=
  innerPiece_of_affine (a := 443 / 40) (b := -381 / 2) (by norm_num) (by norm_num)
    innerR_piece_119 (by norm_num)

private theorem innerPiece_120 : InnerPiece (680 / 37) (37 / 2) (27603 / 101284096) :=
  innerPiece_of_affine (a := 133 / 8) (b := -585 / 2) (by norm_num) (by norm_num)
    innerR_piece_120 (by norm_num)

private theorem innerPiece_121 : InnerPiece (37 / 2) (800 / 43) (458991 / 1752320000) :=
  innerPiece_of_affine (a := 141 / 8) (b := -311) (by norm_num) (by norm_num)
    innerR_piece_121 (by norm_num)

private theorem innerPiece_122 : InnerPiece (800 / 43) (920 / 49) (319689 / 677120000) :=
  innerPiece_of_affine (a := 533 / 40) (b := -231) (by norm_num) (by norm_num)
    innerR_piece_122 (by norm_num)

private theorem innerPiece_123 : InnerPiece (920 / 49) (700 / 37) (111319 / 259210000) :=
  innerPiece_of_affine (a := 121 / 10) (b := -208) (by norm_num) (by norm_num)
    innerR_piece_123 (by norm_num)

private theorem innerPiece_124 : InnerPiece (700 / 37) 19 (90423 / 353780000) :=
  innerPiece_of_affine (a := 279 / 20) (b := -243) (by norm_num) (by norm_num)
    innerR_piece_124 (by norm_num)

private theorem innerPiece_125 : InnerPiece 19 (940 / 49) (-20043 / 63795920) :=
  innerPiece_of_affine (a := 131 / 10) (b := -262) (by norm_num) (by norm_num)
    innerR_piece_125 (by norm_num)

private theorem innerPiece_126 : InnerPiece (940 / 49) (720 / 37) (-2353 / 6786048) :=
  innerPiece_of_affine (a := 95 / 8) (b := -477 / 2) (by norm_num) (by norm_num)
    innerR_piece_126 (by norm_num)

private theorem innerPiece_127 : InnerPiece (720 / 37) (39 / 2) (-503 / 12979200) :=
  innerPiece_of_affine (a := 697 / 40) (b := -693 / 2) (by norm_num) (by norm_num)
    innerR_piece_127 (by norm_num)

private theorem innerPiece_128 : InnerPiece (39 / 2) (840 / 43) (-149 / 4968600) :=
  innerPiece_of_affine (a := 737 / 40) (b := -366) (by norm_num) (by norm_num)
    innerR_piece_128 (by norm_num)

private theorem innerPiece_129 : InnerPiece (840 / 43) (960 / 49) (-649 / 15052800) :=
  innerPiece_of_affine (a := 113 / 8) (b := -282) (by norm_num) (by norm_num)
    innerR_piece_129 (by norm_num)

private theorem innerPiece_130 : InnerPiece (960 / 49) 20 (-43 / 307200) :=
  innerPiece_of_affine (a := 129 / 10) (b := -258) (by norm_num) (by norm_num)
    innerR_piece_130 (by norm_num)

private theorem innerPiece_block_00 :
    InnerPiece 3 (40 / 9) (1216783 / 4032000) := by
  have h := innerPiece_trans innerPiece_000 innerPiece_001 (C := 35833 / 460800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_002 (C := 789871 / 5644800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_003 (C := 89063 / 483840)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_004 (C := 15797 / 80640)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_005 (C := 47675 / 225792)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_006 (C := 41953 / 161280)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_007 (C := 5407169 / 20160000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_008 (C := 2345681 / 8064000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_009 (C := 1216783 / 4032000)
    (by norm_num)
  exact h

private theorem innerPiece_block_01 :
    InnerPiece (40 / 9) (240 / 43) (4947689 / 82368000) := by
  have h := innerPiece_trans innerPiece_010 innerPiece_011 (C := 4909 / 950400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_012 (C := 154069 / 7920000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_013 (C := 557899 / 14256000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_014 (C := 266539 / 6336000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_015 (C := 53819 / 1056000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_016 (C := 9855731 / 178464000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_017 (C := 1948553 / 34320000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_018 (C := 8820589 / 151008000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_019 (C := 4947689 / 82368000)
    (by norm_num)
  exact h

private theorem innerPiece_block_02 :
    InnerPiece (240 / 43) (340 / 49) (-2226793207 / 333260928000) := by
  have h := innerPiece_trans innerPiece_020 innerPiece_021 (C := 116023 / 13939200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_022 (C := 12149 / 1267200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_023 (C := 202877 / 31680000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_024 (C := -14173 / 12672000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_025 (C := -1445531 / 1070784000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_026 (C := -6230183 / 4036032000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_027 (C := -8538667 / 4612608000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_028 (C := -4443223 / 1153152000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_029 (C := -2226793207 / 333260928000)
    (by norm_num)
  exact h

private theorem innerPiece_block_03 :
    InnerPiece (340 / 49) (400 / 49) (-14208321721 / 359770320000) := by
  have h := innerPiece_trans innerPiece_030 innerPiece_031 (C := -34037 / 21039200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_032 (C := -23759783 / 1704175200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_033 (C := -826512487 / 48474316800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_034 (C := -28585801 / 1514822400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_035 (C := -110973781 / 5301878400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_036 (C := -14282237537 / 546850886400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_037 (C := -913668101 / 28781625600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_038 (C := -26590309387 / 719540640000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_039 (C := -14208321721 / 359770320000)
    (by norm_num)
  exact h

private theorem innerPiece_block_04 :
    InnerPiece (400 / 49) (460 / 49) (-14122522213 / 284898240000) := by
  have h := innerPiece_trans innerPiece_040 innerPiece_041 (C := -2899831 / 208080000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_042 (C := -203593 / 12240000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_043 (C := -7624651 / 391680000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_044 (C := -1349447 / 48960000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_045 (C := -179669387 / 5924160000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_046 (C := -149922053 / 4847040000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_047 (C := -370055789 / 9155520000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_048 (C := -384787 / 8415000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_049 (C := -14122522213 / 284898240000)
    (by norm_num)
  exact h

private theorem innerPiece_block_05 :
    InnerPiece (460 / 49) (400 / 37) (-20073970997 / 321953632000) := by
  have h := innerPiece_trans innerPiece_050 innerPiece_051 (C := -4153217 / 289468800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_052 (C := -26134037 / 1543833600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_053 (C := -9420659 / 385958400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_054 (C := -8422211219 / 241224000000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_055 (C := -42401584529 / 1167524160000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_056 (C := -76948417291 / 2016632640000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_057 (C := -15578733667 / 318415680000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_058 (C := -2256703195829 / 41853972160000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_059 (C := -20073970997 / 321953632000)
    (by norm_num)
  exact h

private theorem innerPiece_block_06 :
    InnerPiece (400 / 37) 12 (-2184505769 / 40340160000) := by
  have h := innerPiece_trans innerPiece_060 innerPiece_061 (C := -22104887 / 2566080000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_062 (C := -1270837 / 95040000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_063 (C := -1522561 / 95040000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_064 (C := -118165489 / 4656960000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_065 (C := -4835263 / 166320000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_066 (C := -11411197033 / 351933120000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_067 (C := -609746841311 / 12868511040000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_068 (C := -242628355049 / 4881159360000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_069 (C := -2184505769 / 40340160000)
    (by norm_num)
  exact h

private theorem innerPiece_block_07 :
    InnerPiece 12 (40 / 3) (-9538617359 / 149490432000) := by
  have h := innerPiece_trans innerPiece_070 innerPiece_071 (C := -58979 / 4680000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_072 (C := -21541531 / 990288000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_073 (C := -5371573 / 215280000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_074 (C := -1323906527 / 41376816000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_075 (C := -979968077 / 21355776000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_076 (C := -1631475517 / 34703136000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_077 (C := -6308263021 / 130804128000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_078 (C := -468972629 / 9343152000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_079 (C := -9538617359 / 149490432000)
    (by norm_num)
  exact h

private theorem innerPiece_block_08 :
    InnerPiece (40 / 3) (540 / 37) (272143929623 / 7195127940000) := by
  have h := innerPiece_trans innerPiece_080 innerPiece_081 (C := 49421 / 8553600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_082 (C := 3709561 / 594000000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_083 (C := 64569779 / 3433320000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_084 (C := 4325539 / 201960000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_085 (C := 113865329 / 4948020000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_086 (C := 1454444659 / 59729670000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_087 (C := 553281283 / 18378360000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_088 (C := 274010913821 / 7728100380000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_089 (C := 272143929623 / 7195127940000)
    (by norm_num)
  exact h

private theorem innerPiece_block_09 :
    InnerPiece (540 / 37) (680 / 43) (57954443583641 / 2386043698429440) := by
  have h := innerPiece_trans innerPiece_090 innerPiece_091 (C := 542863 / 74649600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_092 (C := 19033 / 1866240)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_093 (C := 152321957 / 12774412800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_094 (C := 422402311 / 33834931200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_095 (C := 43565159291 / 2322526348800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_096 (C := 102427602289 / 5409238786560)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_097 (C := 196581261053 / 9964387238400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_098 (C := 26143864629971 / 1197149952499200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_099 (C := 57954443583641 / 2386043698429440)
    (by norm_num)
  exact h

private theorem innerPiece_block_10 :
    InnerPiece (680 / 43) (120 / 7) (466536830833 / 30255331392000) := by
  have h := innerPiece_trans innerPiece_100 innerPiece_101 (C := 478483 / 144268800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_102 (C := 30455801 / 5410080000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_103 (C := 98579071 / 14426880000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_104 (C := 2296722793 / 261847872000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_105 (C := 153068321921 / 13338371904000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_106 (C := 50889516511 / 4391902944000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_107 (C := 11006137192883 / 937915273152000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_108 (C := 442149213293 / 30255331392000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_109 (C := 466536830833 / 30255331392000)
    (by norm_num)
  exact h

private theorem innerPiece_block_11 :
    InnerPiece (120 / 7) (680 / 37) (130772170889 / 20944167552000) := by
  have h := innerPiece_trans innerPiece_110 innerPiece_111 (C := 4871 / 2257920)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_112 (C := 1483241 / 596413440)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_113 (C := 82783711 / 25035494400)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_114 (C := 5286367 / 1317657600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_115 (C := 235284517 / 53145523200)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_116 (C := 841794181 / 159436569600)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_117 (C := 242231699 / 43482700800)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_118 (C := 6762386363 / 1087067520000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_119 (C := 130772170889 / 20944167552000)
    (by norm_num)
  exact h

private theorem innerPiece_block_12 :
    InnerPiece (680 / 37) (960 / 49) (4029643337729 / 4385442587136000) := by
  have h := innerPiece_trans innerPiece_120 innerPiece_121 (C := 7315227 / 13687040000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_122 (C := 182204739 / 181011104000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_123 (C := 2768935049 / 1928161760000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_124 (C := 33642682579 / 19887611296000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_125 (C := 3184973197969 / 2312196492256000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_126 (C := 608486869399 / 590348040576000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_127 (C := 8247317394633 / 8314068238112000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_128 (C := 12919833877201 / 13430417923104000)
    (by norm_num)
  have h := innerPiece_trans h innerPiece_129 (C := 4029643337729 / 4385442587136000)
    (by norm_num)
  exact h

private theorem innerPiece_block_13 :
    InnerPiece (960 / 49) 20 (-43 / 307200) := by
  exact innerPiece_130

private theorem innerPiece_all :
    InnerPiece 3 20 (120667538150827615739401 / 708353029541942104320000) := by
  have h := innerPiece_trans innerPiece_block_00 innerPiece_block_01
    (C := 3259903 / 9009000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_02
    (C := 118363538569 / 333260928000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_03
    (C := 45222641867 / 143256960000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_04
    (C := 1344412442599 / 5052195456000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_05
    (C := 581837898713 / 2855588736000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_06
    (C := 557498183891783 / 3726543300480000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_07
    (C := 2831775664143043 / 33006526375680000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_08
    (C := 771156564657613111 / 6238233485003520000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_09
    (C := 3070706675359451171 / 20761105090302720000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_10
    (C := 743446785457769893 / 4551900046536960000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_11
    (C := 43446142638939166357681 / 256212797919425867520000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_12
    (C := 241533378256540019958527 / 1416706059083884208640000) (by norm_num)
  have h := innerPiece_trans h innerPiece_block_13
    (C := 120667538150827615739401 / 708353029541942104320000) (by norm_num)
  exact h

/-! ### The value of the inner integral -/

/-- `R(x)/x^3` is interval integrable on `[3, 20]`. -/
theorem intervalIntegrable_innerR_div_cube :
    IntervalIntegrable (fun x => innerR x / x ^ 3) volume 3 20 :=
  innerPiece_all.1

/-- **Exact inner integral** (Appendix A.1, (121)):
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`. -/
theorem innerIntegral_value :
    ∫ x in (3 : ℝ)..20, innerR x / x ^ 3 =
      120667538150827615739401 / 708353029541942104320000 :=
  innerPiece_all.2

/-! ### The jumps of `R` (source-map erratum 12) -/

/-- `R` jumps at `x = 4`: left limit `69/5`, right limit `32/5`. -/
theorem innerR_jump_4 :
    Tendsto innerR (𝓝[<] (4 : ℝ)) (𝓝 (69 / 5)) ∧
      Tendsto innerR (𝓝[>] (4 : ℝ)) (𝓝 (32 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 140 / 37) (a := 21 / 5) (b := -3) (by norm_num)
      (by norm_num) innerR_piece_006,
    tendsto_nhdsGT_of_affine (u := 200 / 49) (a := 67 / 20) (b := -7) (by norm_num)
      (by norm_num) innerR_piece_007⟩

/-- `R` jumps at `x = 5`: left limit `43/4`, right limit `3/2`. -/
theorem innerR_jump_5 :
    Tendsto innerR (𝓝[<] (5 : ℝ)) (𝓝 (43 / 4)) ∧
      Tendsto innerR (𝓝[>] (5 : ℝ)) (𝓝 (3 / 2)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 240 / 49) (a := 71 / 20) (b := -7) (by norm_num)
      (by norm_num) innerR_piece_015,
    tendsto_nhdsGT_of_affine (u := 260 / 49) (a := 27 / 10) (b := -12) (by norm_num)
      (by norm_num) innerR_piece_016⟩

/-- `R` jumps at `x = 6`: left limit `51/10`, right limit `-6`. -/
theorem innerR_jump_6 :
    Tendsto innerR (𝓝[<] (6 : ℝ)) (𝓝 (51 / 10)) ∧
      Tendsto innerR (𝓝[>] (6 : ℝ)) (𝓝 (-6)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 220 / 37) (a := 87 / 20) (b := -21) (by norm_num)
      (by norm_num) innerR_piece_022,
    tendsto_nhdsGT_of_affine (u := 300 / 49) (a := 7 / 2) (b := -27) (by norm_num)
      (by norm_num) innerR_piece_023⟩

/-- `R` jumps at `x = 7`: left limit `-9/4`, right limit `-76/5`. -/
theorem innerR_jump_7 :
    Tendsto innerR (𝓝[<] (7 : ℝ)) (𝓝 (-9 / 4)) ∧
      Tendsto innerR (𝓝[>] (7 : ℝ)) (𝓝 (-76 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 340 / 49) (a := 17 / 4) (b := -32) (by norm_num)
      (by norm_num) innerR_piece_030,
    tendsto_nhdsGT_of_affine (u := 260 / 37) (a := 17 / 5) (b := -39) (by norm_num)
      (by norm_num) innerR_piece_031⟩

/-- `R` jumps at `x = 8`: left limit `-53/5`, right limit `-127/5`. -/
theorem innerR_jump_8 :
    Tendsto innerR (𝓝[<] (8 : ℝ)) (𝓝 (-53 / 5)) ∧
      Tendsto innerR (𝓝[>] (8 : ℝ)) (𝓝 (-127 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 380 / 49) (a := 101 / 20) (b := -51) (by norm_num)
      (by norm_num) innerR_piece_037,
    tendsto_nhdsGT_of_affine (u := 300 / 37) (a := 21 / 5) (b := -59) (by norm_num)
      (by norm_num) innerR_piece_038⟩

/-- `R` jumps at `x = 9`: left limit `-107/5`, right limit `-761/20`. -/
theorem innerR_jump_9 :
    Tendsto innerR (𝓝[<] (9 : ℝ)) (𝓝 (-107 / 5)) ∧
      Tendsto innerR (𝓝[>] (9 : ℝ)) (𝓝 (-761 / 20)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 440 / 49) (a := 22 / 5) (b := -61) (by norm_num)
      (by norm_num) innerR_piece_046,
    tendsto_nhdsGT_of_affine (u := 340 / 37) (a := 71 / 20) (b := -70) (by norm_num)
      (by norm_num) innerR_piece_047⟩

/-- `R` jumps at `x = 10`: left limit `-35`, right limit `-107/2`. -/
theorem innerR_jump_10 :
    Tendsto innerR (𝓝[<] (10 : ℝ)) (𝓝 (-35)) ∧
      Tendsto innerR (𝓝[>] (10 : ℝ)) (𝓝 (-107 / 2)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 480 / 49) (a := 26 / 5) (b := -87) (by norm_num)
      (by norm_num) innerR_piece_053,
    tendsto_nhdsGT_of_affine (u := 500 / 49) (a := 87 / 20) (b := -97) (by norm_num)
      (by norm_num) innerR_piece_054⟩

/-- `R` jumps at `x = 11`: left limit `-51`, right limit `-1427/20`. -/
theorem innerR_jump_11 :
    Tendsto innerR (𝓝[<] (11 : ℝ)) (𝓝 (-51)) ∧
      Tendsto innerR (𝓝[>] (11 : ℝ)) (𝓝 (-1427 / 20)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 400 / 37) (a := 6) (b := -117) (by norm_num)
      (by norm_num) innerR_piece_060,
    tendsto_nhdsGT_of_affine (u := 540 / 49) (a := 103 / 20) (b := -128) (by norm_num)
      (by norm_num) innerR_piece_061⟩

/-- `R` jumps at `x = 12`: left limit `-349/5`, right limit `-92`. -/
theorem innerR_jump_12 :
    Tendsto innerR (𝓝[<] (12 : ℝ)) (𝓝 (-349 / 5)) ∧
      Tendsto innerR (𝓝[>] (12 : ℝ)) (𝓝 (-92)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 440 / 37) (a := 107 / 20) (b := -134) (by norm_num)
      (by norm_num) innerR_piece_069,
    tendsto_nhdsGT_of_affine (u := 520 / 43) (a := 9 / 2) (b := -146) (by norm_num)
      (by norm_num) innerR_piece_070⟩

/-- `R` jumps at `x = 13`: left limit `-1821/20`, right limit `-1151/10`. -/
theorem innerR_jump_13 :
    Tendsto innerR (𝓝[<] (13 : ℝ)) (𝓝 (-1821 / 20)) ∧
      Tendsto innerR (𝓝[>] (13 : ℝ)) (𝓝 (-1151 / 10)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 480 / 37) (a := 123 / 20) (b := -171) (by norm_num)
      (by norm_num) innerR_piece_076,
    tendsto_nhdsGT_of_affine (u := 560 / 43) (a := 53 / 10) (b := -184) (by norm_num)
      (by norm_num) innerR_piece_077⟩

/-- `R` jumps at `x = 40/3`: left limit `-115`, right limit `247/3`. -/
theorem innerR_jump_40_3 :
    Tendsto innerR (𝓝[<] (40 / 3 : ℝ)) (𝓝 (-115)) ∧
      Tendsto innerR (𝓝[>] (40 / 3 : ℝ)) (𝓝 (247 / 3)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 640 / 49) (a := -9 / 40) (b := -112) (by norm_num)
      (by norm_num) innerR_piece_079,
    tendsto_nhdsGT_of_affine (u := 660 / 49) (a := 67 / 4) (b := -141) (by norm_num)
      (by norm_num) innerR_piece_080⟩

/-- `R` jumps at `x = 14`: left limit `939/10`, right limit `68`. -/
theorem innerR_jump_14 :
    Tendsto innerR (𝓝[<] (14 : ℝ)) (𝓝 (939 / 10)) ∧
      Tendsto innerR (𝓝[>] (14 : ℝ)) (𝓝 68) :=
  ⟨tendsto_nhdsLT_of_affine (l := 600 / 43) (a := 257 / 20) (b := -86) (by norm_num)
      (by norm_num) innerR_piece_085,
    tendsto_nhdsGT_of_affine (u := 520 / 37) (a := 12) (b := -100) (by norm_num)
      (by norm_num) innerR_piece_086⟩

/-- `R` jumps at `x = 15`: left limit `339/4`, right limit `57`. -/
theorem innerR_jump_15 :
    Tendsto innerR (𝓝[<] (15 : ℝ)) (𝓝 (339 / 4)) ∧
      Tendsto innerR (𝓝[>] (15 : ℝ)) (𝓝 57) :=
  ⟨tendsto_nhdsLT_of_affine (l := 640 / 43) (a := 273 / 20) (b := -120) (by norm_num)
      (by norm_num) innerR_piece_092,
    tendsto_nhdsGT_of_affine (u := 740 / 49) (a := 64 / 5) (b := -135) (by norm_num)
      (by norm_num) innerR_piece_093⟩

/-- `R` jumps at `x = 16`: left limit `73`, right limit `217/5`. -/
theorem innerR_jump_16 :
    Tendsto innerR (𝓝[<] (16 : ℝ)) (𝓝 73) ∧
      Tendsto innerR (𝓝[>] (16 : ℝ)) (𝓝 (217 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 780 / 49) (a := 13) (b := -135) (by norm_num)
      (by norm_num) innerR_piece_101,
    tendsto_nhdsGT_of_affine (u := 600 / 37) (a := 243 / 20) (b := -151) (by norm_num)
      (by norm_num) innerR_piece_102⟩

/-- `R` jumps at `x = 17`: left limit `293/5`, right limit `543/20`. -/
theorem innerR_jump_17 :
    Tendsto innerR (𝓝[<] (17 : ℝ)) (𝓝 (293 / 5)) ∧
      Tendsto innerR (𝓝[>] (17 : ℝ)) (𝓝 (543 / 20)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 620 / 37) (a := 69 / 5) (b := -176) (by norm_num)
      (by norm_num) innerR_piece_108,
    tendsto_nhdsGT_of_affine (u := 120 / 7) (a := 259 / 20) (b := -193) (by norm_num)
      (by norm_num) innerR_piece_109⟩

/-- `R` jumps at `x = 18`: left limit `417/10`, right limit `42/5`. -/
theorem innerR_jump_18 :
    Tendsto innerR (𝓝[<] (18 : ℝ)) (𝓝 (417 / 10)) ∧
      Tendsto innerR (𝓝[>] (18 : ℝ)) (𝓝 (42 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 880 / 49) (a := 263 / 20) (b := -195) (by norm_num)
      (by norm_num) innerR_piece_117,
    tendsto_nhdsGT_of_affine (u := 900 / 49) (a := 123 / 10) (b := -213) (by norm_num)
      (by norm_num) innerR_piece_118⟩

/-- `R` jumps at `x = 19`: left limit `441/20`, right limit `-131/10`. -/
theorem innerR_jump_19 :
    Tendsto innerR (𝓝[<] (19 : ℝ)) (𝓝 (441 / 20)) ∧
      Tendsto innerR (𝓝[>] (19 : ℝ)) (𝓝 (-131 / 10)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 700 / 37) (a := 279 / 20) (b := -243) (by norm_num)
      (by norm_num) innerR_piece_124,
    tendsto_nhdsGT_of_affine (u := 940 / 49) (a := 131 / 10) (b := -262) (by norm_num)
      (by norm_num) innerR_piece_125⟩

/-- At the right endpoint `x = 20`, `R(x) → 0` as `x → 20` from the left, but `R(20) = -37`
(`⌊x⌋`, `⌊2x⌋`, `⌊2Hx⌋` and `⌊2λx⌋` all jump at `x = 20`). -/
theorem innerR_at_twenty : Tendsto innerR (𝓝[<] (20 : ℝ)) (𝓝 0) ∧ innerR 20 = -37 := by
  refine ⟨tendsto_nhdsLT_of_affine (l := 960 / 49) (a := 129 / 10) (b := -258) (by norm_num)
      (by norm_num) innerR_piece_130, ?_⟩
  rw [innerR_eq_of_le (x := 20) (n := 20) (q := 40) (m := 1) (q' := 3) (T := 49) (k := 37)
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (floor_eq_of_bounds (by norm_num) (by norm_num))
    (min_eq_left (by norm_num)) (min_eq_left (by norm_num)) (by norm_num)
    (max_eq_left (by norm_num))]
  norm_num

end ZetaSeven
