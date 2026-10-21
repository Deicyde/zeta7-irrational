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
  (`ZetaSeven.innerR_piece_000`, ..., `ZetaSeven.innerR_piece_130`).
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

/-- `ℓ(x, z) = 2n + 1` for `0 < z < d({x})`, where `n = ⌊x⌋`. -/
theorem ellLim_of_lt_dist {x z : ℝ} {n : ℤ} (hn : ⌊x⌋ = n) (hz0 : 0 < z)
    (hz : z < min (x - n) (n + 1 - x)) : ellLim x z = 2 * n + 1 := by
  rw [Int.floor_eq_iff] at hn
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
      (ellLim_of_lt_dist hn h0 (by rw [hdf]; exact h1))
      (ellLim_of_lt_dist hm h0 (by rw [hdg]; linarith))
  have e2 := integral_eq_mul_of_eqOn hle fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * q - 2 * n) (B := 2 * m + 1)
      (ellLim_of_dist_lt hn hq (by rw [hdf]; exact h0) (by linarith))
      (ellLim_of_lt_dist hm (by linarith) (by rw [hdg]; exact h1))
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
      (ellLim_of_lt_dist hn h0 (by rw [hdf]; linarith))
      (ellLim_of_lt_dist hm h0 (by rw [hdg]; exact h1))
  have e2 := integral_eq_mul_of_eqOn hge fun z h0 h1 =>
    gammaIntegrand_eq_of_ell (L := 2 * n + 1) (B := 2 * q' - 2 * m)
      (ellLim_of_lt_dist hn (by linarith) (by rw [hdf]; exact h1))
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
theorem innerR_piece_000 {x : ℝ} (h0 : 3 < x) (h1 : x < 120 / 37) :
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
theorem innerR_piece_001 {x : ℝ} (h0 : 120 / 37 < x) (h1 : x < 160 / 49) :
    innerR x = 81 / 10 * x - 17 := by
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
theorem innerR_piece_002 {x : ℝ} (h0 : 160 / 49 < x) (h1 : x < 7 / 2) :
    innerR x = 55 / 8 * x - 13 := by
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
theorem innerR_piece_003 {x : ℝ} (h0 : 7 / 2 < x) (h1 : x < 180 / 49) :
    innerR x = 63 / 8 * x - 33 / 2 := by
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
theorem innerR_piece_004 {x : ℝ} (h0 : 180 / 49 < x) (h1 : x < 160 / 43) :
    innerR x = 133 / 20 * x - 12 := by
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
theorem innerR_piece_005 {x : ℝ} (h0 : 160 / 43 < x) (h1 : x < 140 / 37) :
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
theorem innerR_piece_006 {x : ℝ} (h0 : 140 / 37 < x) (h1 : x < 4) :
    innerR x = 21 / 5 * x - 3 := by
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
theorem innerR_piece_007 {x : ℝ} (h0 : 4 < x) (h1 : x < 200 / 49) :
    innerR x = 67 / 20 * x - 7 := by
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

/-- On `(20/3, 340/49)`, `R(x) = (219/40)x - 81/2` (Tables 2-4, row 43). -/
theorem innerR_piece_029 {x : ℝ} (h0 : 20 / 3 < x) (h1 : x < 340 / 49) :
    innerR x = 219 / 40 * x - 81 / 2 := by
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

/-- On `(60/7, 320/37)`, `R(x) = (3/10)x - 26` (Tables 2-4, row 64). -/
theorem innerR_piece_043 {x : ℝ} (h0 : 60 / 7 < x) (h1 : x < 320 / 37) :
    innerR x = 3 / 10 * x - 26 := by
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

/-- On `(960/49, 20)`, `R(x) = (129/10)x - 258` (Tables 2-4, row 191). -/
theorem innerR_piece_130 {x : ℝ} (h0 : 960 / 49 < x) (h1 : x < 20) :
    innerR x = 129 / 10 * x - 258 := by
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

/-! ### Round-1 checks (temporary) -/

private theorem innerPiece_000 : InnerPiece 3 (120 / 37) (689 / 9600) :=
  innerPiece_of_affine (a := 51 / 20) (b := 1) (by norm_num) (by norm_num)
    (fun _ h0 h1 => (innerR_piece_000 h0 h1).trans (by ring)) (by norm_num)

private theorem innerPiece_001 : InnerPiece (120 / 37) (160 / 49) (2761 / 460800) :=
  innerPiece_of_affine (a := 81 / 10) (b := -17) (by norm_num) (by norm_num)
    (fun _ h0 h1 => (innerR_piece_001 h0 h1).trans (by ring)) (by norm_num)

private theorem innerPiece_test01 : InnerPiece 3 (160 / 49) (689 / 9600 + 2761 / 460800) :=
  innerPiece_trans innerPiece_000 innerPiece_001 rfl

/-- `R` jumps at `x = 4`: left limit `69/5`, right limit `32/5`. -/
theorem innerR_jump_4 :
    Tendsto innerR (𝓝[<] (4 : ℝ)) (𝓝 (69 / 5)) ∧
      Tendsto innerR (𝓝[>] (4 : ℝ)) (𝓝 (32 / 5)) :=
  ⟨tendsto_nhdsLT_of_affine (l := 140 / 37) (a := 21 / 5) (b := -3) (by norm_num)
      (by norm_num) fun _ h0 h1 => (innerR_piece_006 h0 h1).trans (by ring),
    tendsto_nhdsGT_of_affine (u := 200 / 49) (a := 67 / 20) (b := -7) (by norm_num)
      (by norm_num) fun _ h0 h1 => (innerR_piece_007 h0 h1).trans (by ring)⟩

/-- At the right endpoint `x = 20`, `R(x) → 0` as `x → 20` from the left, but `R(20) = -37`
(`⌊x⌋`, `⌊2x⌋`, `⌊2Hx⌋` and `⌊2λx⌋` all jump at `x = 20`). -/
theorem innerR_at_twenty : Tendsto innerR (𝓝[<] (20 : ℝ)) (𝓝 0) ∧ innerR 20 = -37 := by
  refine ⟨tendsto_nhdsLT_of_affine (l := 960 / 49) (a := 129 / 10) (b := -258) (by norm_num)
      (by norm_num) fun _ h0 h1 => (innerR_piece_130 h0 h1).trans (by ring), ?_⟩
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
