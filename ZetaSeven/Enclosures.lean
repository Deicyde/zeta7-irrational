import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Elementary enclosures (appendix A.2, equations (111)-(112))

Rigorous Taylor enclosures for `log` and `arctan` with explicit remainders,
argument reductions, the Machin-like formula for `π`, and square-root enclosure
by adjacent multiples of `2⁻¹⁴⁴`.

## English proofs

**(111) Log enclosure.** For `1 ≤ x ≤ 2` put `z = (x-1)/(x+1)`, so
`0 ≤ z ≤ 1/3` and `x = (1+z)/(1-z)`. Then
`log x = log (1+z) - log (1-z) = 2 ∑_{k≥0} z^{2k+1}/(2k+1)`
(`Real.hasSum_log_sub_log_of_abs_lt_one`). All summands are nonnegative, so
truncated sums lie below the total (lower bound `0`). The tail term satisfies
`2 z^{2(m+i)+1}/(2(m+i)+1) ≤ C (z²)^i` with `C = 2 z^{2m+1}/(2m+1)`, since
`z^{2(m+i)+1} = z^{2m+1} (z²)^i` and `2(m+i)+1 ≥ 2m+1`; summing the geometric
majorant gives the upper bound `C/(1-z²)`.

**(112) Arctan enclosure.** For `0 ≤ z ≤ 1/2`,
`arctan z = ∑_{k≥0} (-1)^k z^{2k+1}/(2k+1)`
(`Real.hasSum_arctan`). The absolute terms `f k = z^{2k+1}/(2k+1)` are antitone
(`z ≤ 1`, denominators grow) and summable (dominated by the geometric sequence
`z (z²)^k`), so the Leibniz estimate (`alternating_series_error_bound`) gives
`|error| ≤ f m`.

**Reciprocal reduction.** `arctan x = π/2 - arctan x⁻¹` for `x > 1` is
`Real.arctan_inv_of_pos` rearranged.

**Half-angle reduction.** For `0 ≤ x ≤ 1`, with `s = √(1+x²)` and
`t = x/(1+s) ∈ [0,1)`, the identity `2t/(1-t²) = x` follows from
`(1+s)² - x² = 2(1+s)` (using `s² = 1+x²`); then `Real.two_mul_arctan` gives
`2 arctan t = arctan x`.

**Machin formula.** `π = 16 arctan(1/5) - 4 arctan(1/239)` is four times
`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`.

**Square-root enclosure.** `k = ⌊√x · 2^144⌋₊` gives
`k/2^144 ≤ √x < (k+1)/2^144` by `Nat.floor_le` / `Nat.lt_floor_add_one`;
squaring gives the enclosure of `x` itself.

**Remainder bounds.** At `m = 64` the (111) bound is increasing in `z`, and its
value at `z = 1/3` is below `2⁻¹⁴⁴` (checked by `norm_num`). At `m = 80` the
(112) bound satisfies `z^161/161 ≤ (1/2)^161 < 2⁻¹⁴⁴`.
-/

namespace ZetaSeven

/-- Equation (111): Taylor enclosure for `log` on `[1,2]`. -/
theorem log_taylor_enclosure {x z : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2)
    (hz : z = (x - 1) / (x + 1)) (m : ℕ) :
    0 ≤ Real.log x - 2 * ∑ k ∈ Finset.range m, z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
    ∧ Real.log x - 2 * ∑ k ∈ Finset.range m, z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
      ≤ 2 * z ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - z ^ 2)) := by
  have hz0 : 0 ≤ z := by
    rw [hz]
    exact div_nonneg (by linarith) (by linarith)
  have hz1 : z ≤ 1 / 3 := by
    have hden : (0 : ℝ) < x + 1 := by linarith
    rw [hz, le_div_iff₀ (by norm_num : (0 : ℝ) < 3), div_mul_eq_mul_div,
      div_le_iff₀ hden]
    linarith [hx2]
  have habs : |z| < 1 := by
    rw [abs_of_nonneg hz0]
    linarith [hz1]
  have hz2 : z ^ 2 < 1 := by
    calc z ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz1 2
    _ < 1 := by norm_num
  have h1pz : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith [hz0] : (0 : ℝ) < 1 + z)
  have h1mz : (1 : ℝ) - z ≠ 0 := ne_of_gt (by linarith [hz1] : (0 : ℝ) < 1 - z)
  have hfrac : (1 + z) / (1 - z) = x := by
    have hden : (x : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < x + 1)
    have e1 : (1 : ℝ) + z = 2 * x / (x + 1) := by
      rw [hz]
      have h : (1 : ℝ) + (x - 1) / (x + 1) = ((x + 1) + (x - 1)) / (x + 1) := by
        rw [add_div, div_self hden]
      rw [h]
      congr 1
      ring
    have e2 : (1 : ℝ) - z = 2 / (x + 1) := by
      rw [hz]
      have h : ((x + 1) - (x - 1)) / (x + 1) = (1 : ℝ) - (x - 1) / (x + 1) := by
        rw [sub_div, div_self hden]
      rw [← h]
      congr 1
      ring
    have h2 : (2 : ℝ) / (x + 1) ≠ 0 := div_ne_zero (by norm_num) hden
    rw [e1, e2, div_eq_iff h2, ← mul_div_assoc]
    congr 1
    ring
  have hlim : Real.log (1 + z) - Real.log (1 - z) = Real.log x := by
    rw [← hfrac, Real.log_div h1pz h1mz]
  have hsum : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1))
      (Real.log x) := by
    have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := z) habs
    rw [hlim] at h
    exact h
  have hsum2 : HasSum (fun k : ℕ => 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
      (Real.log x) := by
    have hfun : (fun k : ℕ => 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
        = fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1) := by
      ext k
      show 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
        = (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)
      push_cast
      ring
    rw [hfun]
    exact hsum
  have hsumm : Summable
      (fun k : ℕ => 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))) := hsum2.summable
  have hnonneg : ∀ k : ℕ, 0 ≤ 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    intro k
    positivity
  have hle : (∑ k ∈ Finset.range m, 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
      ≤ Real.log x := by
    have h := Summable.sum_le_tsum (Finset.range m) (fun i _ => hnonneg i) hsumm
    rw [hsum2.tsum_eq] at h
    exact h
  have htail : (∑ k ∈ Finset.range m, 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
      + (∑' i : ℕ, 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ)))
      = Real.log x := by
    have h := Summable.sum_add_tsum_nat_add m hsumm
    rw [hsum2.tsum_eq] at h
    exact h
  rw [← Finset.mul_sum] at hle htail
  set C : ℝ := 2 * z ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ) with hC
  have hbound : ∀ i : ℕ, 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ))
      ≤ C * (z ^ 2) ^ i := by
    intro i
    have e1 : 2 * (i + m) + 1 = (2 * m + 1) + 2 * i := by ring
    have hexp : z ^ (2 * (i + m) + 1) = z ^ (2 * m + 1) * (z ^ 2) ^ i := by
      rw [e1, pow_add, pow_mul]
    have hP : (0 : ℝ) ≤ z ^ (2 * m + 1) * (z ^ 2) ^ i := by positivity
    have hD0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
    have hD1 : (0 : ℝ) < ((2 * (i + m) + 1 : ℕ) : ℝ) := by positivity
    have hDle : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * (i + m) + 1 : ℕ) : ℝ) := by
      have h : 2 * m + 1 ≤ 2 * (i + m) + 1 := by omega
      exact_mod_cast h
    have hstep : z ^ (2 * m + 1) * (z ^ 2) ^ i / ((2 * (i + m) + 1 : ℕ) : ℝ)
        ≤ z ^ (2 * m + 1) * (z ^ 2) ^ i / ((2 * m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hP hD0 hDle
    rw [hexp, hC]
    calc 2 * (z ^ (2 * m + 1) * (z ^ 2) ^ i / ((2 * (i + m) + 1 : ℕ) : ℝ))
          ≤ 2 * (z ^ (2 * m + 1) * (z ^ 2) ^ i / ((2 * m + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 * z ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ) * (z ^ 2) ^ i := by ring
  have hmaj_summ : Summable (fun i : ℕ => C * (z ^ 2) ^ i) :=
    Summable.mul_left C (summable_geometric_of_lt_one (by positivity) hz2)
  have hmin_summ : Summable
      (fun i : ℕ => 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hbound hmaj_summ
  have htail_le : (∑' i : ℕ, 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ)))
      ≤ ∑' i : ℕ, C * (z ^ 2) ^ i :=
    Summable.tsum_le_tsum hbound hmin_summ hmaj_summ
  have hgeo_val : (∑' i : ℕ, C * (z ^ 2) ^ i) = C * (1 - z ^ 2)⁻¹ := by
    rw [tsum_mul_left, (hasSum_geometric_of_lt_one (by positivity) hz2).tsum_eq]
  have hdecomp : Real.log x
      - 2 * ∑ k ∈ Finset.range m, z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
      = ∑' i : ℕ, 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ)) := by
    linarith [htail]
  refine ⟨?_, ?_⟩
  · linarith [hle]
  · rw [hdecomp]
    calc (∑' i : ℕ, 2 * (z ^ (2 * (i + m) + 1) / ((2 * (i + m) + 1 : ℕ) : ℝ)))
          ≤ ∑' i : ℕ, C * (z ^ 2) ^ i := htail_le
      _ = C * (1 - z ^ 2)⁻¹ := hgeo_val
      _ = 2 * z ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - z ^ 2)) := by
          rw [hC, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
          ring

/-- Equation (112): Taylor enclosure for `arctan` on `[0,1/2]`. -/
theorem arctan_taylor_enclosure {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (m : ℕ) :
    |Real.arctan z - ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)|
      ≤ z ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ) := by
  have hz01 : z ≤ 1 := by linarith [hz1]
  have habs : ‖z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hz0]
    linarith [hz1]
  have hz2 : z ^ 2 < 1 := by
    calc z ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz1 2
    _ < 1 := by norm_num
  set f : ℕ → ℝ := fun k => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) with hf
  have hanti : Antitone f := by
    intro a b hab
    have hpow : z ^ (2 * b + 1) ≤ z ^ (2 * a + 1) :=
      pow_le_pow_of_le_one hz0 hz01 (by omega : 2 * a + 1 ≤ 2 * b + 1)
    have hdiv : (1 : ℝ) / ((2 * b + 1 : ℕ) : ℝ) ≤ 1 / ((2 * a + 1 : ℕ) : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h : 2 * a + 1 ≤ 2 * b + 1 := by omega
      exact_mod_cast h
    have h1 : (0 : ℝ) ≤ 1 / ((2 * b + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ z ^ (2 * a + 1) := by positivity
    have hmul := mul_le_mul hpow hdiv h1 h2
    simp only [hf]
    calc z ^ (2 * b + 1) / ((2 * b + 1 : ℕ) : ℝ)
          = z ^ (2 * b + 1) * (1 / ((2 * b + 1 : ℕ) : ℝ)) := by ring
      _ ≤ z ^ (2 * a + 1) * (1 / ((2 * a + 1 : ℕ) : ℝ)) := hmul
      _ = z ^ (2 * a + 1) / ((2 * a + 1 : ℕ) : ℝ) := by ring
  have hsumm : Summable f := by
    have hgeo : Summable (fun i : ℕ => z * (z ^ 2) ^ i) :=
      Summable.mul_left z (summable_geometric_of_lt_one (by positivity) hz2)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hgeo
    · simp only [hf]
      positivity
    · simp only [hf]
      show z ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) ≤ z * (z ^ 2) ^ i
      have hexp : z ^ (2 * i + 1) = z * (z ^ 2) ^ i := by
        rw [pow_succ', pow_mul]
      rw [hexp]
      have hA : (0 : ℝ) ≤ z * (z ^ 2) ^ i := by positivity
      have hD : (1 : ℝ) ≤ ((2 * i + 1 : ℕ) : ℝ) := by
        have h1 : 1 ≤ 2 * i + 1 := by omega
        exact_mod_cast h1
      have hD0 : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by linarith [hD]
      rw [div_le_iff₀ hD0]
      have hle := mul_le_mul_of_nonneg_left hD hA
      simpa using hle
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n) (Real.arctan z) := by
    have h := Real.hasSum_arctan (x := z) habs
    have hfun : (fun n : ℕ => (-1 : ℝ) ^ n * f n)
        = fun n : ℕ => (-1 : ℝ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
      ext n
      simp only [hf]
      ring
    rw [hfun]
    exact h
  have herr := alternating_series_error_bound f hanti hsumm m
  rw [hsum.tsum_eq] at herr
  have hsum_eq : (∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * f i)
      = ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hf]
    ring
  rw [hsum_eq] at herr
  have hfm : f m = z ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ) := rfl
  rw [hfm] at herr
  exact herr

/-- Large-argument reduction: `arctan x = π/2 - arctan (1/x)` for `x > 1`. -/
theorem arctan_inv_reduction {x : ℝ} (hx : 1 < x) :
    Real.arctan x = Real.pi / 2 - Real.arctan x⁻¹ := by
  have h := Real.arctan_inv_of_pos (show (0 : ℝ) < x by linarith)
  linarith

/-- Small-argument reduction: half-angle formula for `arctan` on `[0,1]`. -/
theorem arctan_half_reduction {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arctan x = 2 * Real.arctan (x / (1 + Real.sqrt (1 + x ^ 2))) := by
  set s := Real.sqrt (1 + x ^ 2) with hs_def
  set t := x / (1 + s) with ht_def
  have hs : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : (1 : ℝ) ≤ s := by
    have h : (1 : ℝ) ^ 2 ≤ 1 + x ^ 2 := by
      calc (1 : ℝ) ^ 2 = 1 := by norm_num
      _ ≤ 1 + x ^ 2 := by
          have h2 := sq_nonneg x
          linarith
    exact Real.le_sqrt_of_sq_le h
  have h1s : (0 : ℝ) < 1 + s := by linarith [hs1]
  have h1sne : (1 : ℝ) + s ≠ 0 := ne_of_gt h1s
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one h1s]
    linarith [hx1, hs1]
  have htan : 2 * t / (1 - t ^ 2) = x := by
    have e : (1 + s) ^ 2 - x ^ 2 = 2 * (1 + s) := by
      have hsq : (1 + s) ^ 2 = 1 + 2 * s + s ^ 2 := by ring
      rw [hsq]
      linarith [hs]
    have ht2 : t ^ 2 = x ^ 2 / (1 + s) ^ 2 := by rw [ht_def, div_pow]
    have hden : (1 : ℝ) - t ^ 2 = 2 * (1 + s) / (1 + s) ^ 2 := by
      have hsq : ((1 + s) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h1sne
      have hform : (1 : ℝ) - x ^ 2 / (1 + s) ^ 2
          = ((1 + s) ^ 2 - x ^ 2) / (1 + s) ^ 2 := by
        rw [sub_div, div_self hsq]
      rw [ht2, hform, e]
    have hsq : ((1 + s) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h1sne
    have hBne : (2 : ℝ) * (1 + s) / (1 + s) ^ 2 ≠ 0 :=
      div_ne_zero (ne_of_gt (by linarith [h1s] : (0 : ℝ) < 2 * (1 + s))) hsq
    rw [hden, ht_def]
    field_simp
  have h2 := Real.two_mul_arctan (show (-1 : ℝ) < t by linarith [div_nonneg hx0 (le_of_lt h1s)]) ht1
  rw [htan] at h2
  exact h2.symm

/-- Machin-like formula: `π = 16 arctan(1/5) - 4 arctan(1/239)`. -/
theorem machin_pi_formula :
    Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  simp only [one_div] at h ⊢
  linarith

/-- Square roots are enclosed by adjacent multiples of `2⁻¹⁴⁴`. -/
theorem sqrt_enclosure {x : ℝ} (hx : 0 ≤ x) :
    ∃ k : ℕ, (k : ℝ) / 2 ^ 144 ≤ Real.sqrt x
      ∧ Real.sqrt x < ((k : ℝ) + 1) / 2 ^ 144 := by
  have h2 : (0 : ℝ) < 2 ^ 144 := by positivity
  refine ⟨Nat.floor (Real.sqrt x * 2 ^ 144), ?_, ?_⟩
  · rw [div_le_iff₀ h2]
    exact Nat.floor_le (by positivity)
  · rw [lt_div_iff₀ h2]
    exact Nat.lt_floor_add_one (Real.sqrt x * 2 ^ 144)

/-- Squared form: `x` lies between adjacent multiples' squares. -/
theorem sqrt_enclosure_sq {x : ℝ} (hx : 0 ≤ x) :
    ∃ k : ℕ, ((k : ℝ) / 2 ^ 144) ^ 2 ≤ x
      ∧ x < (((k : ℝ) + 1) / 2 ^ 144) ^ 2 := by
  obtain ⟨k, hk1, hk2⟩ := sqrt_enclosure hx
  refine ⟨k, ?_, ?_⟩
  · rw [← Real.sq_sqrt hx]
    exact pow_le_pow_left₀ (by positivity) hk1 2
  · rw [← Real.sq_sqrt hx]
    exact pow_lt_pow_left₀ hk2 (by positivity) (by decide : (2 : ℕ) ≠ 0)

/-- The (111) remainder at `m = 64` is below `2⁻¹⁴⁴`. -/
theorem log_remainder_m64 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 3) :
    2 * z ^ (2 * 64 + 1) / ((((2 * 64 + 1 : ℕ) : ℝ)) * (1 - z ^ 2)) < 1 / 2 ^ 144 := by
  have e64 : 2 * 64 + 1 = 129 := rfl
  rw [e64]
  have hnum : z ^ 129 ≤ (1 / 3 : ℝ) ^ 129 := pow_le_pow_left₀ hz0 hz1 129
  have hsq : z ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz1 2
  have hD0 : (0 : ℝ) < ((129 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2) := by norm_num
  have hD1 : (0 : ℝ) < ((129 : ℕ) : ℝ) * (1 - z ^ 2) := by
    have hz2 : z ^ 2 < 1 := by
      calc z ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := hsq
      _ < 1 := by norm_num
    have h129 : (0 : ℝ) < ((129 : ℕ) : ℝ) := by norm_num
    have h1 : (0 : ℝ) < 1 - z ^ 2 := by linarith
    exact mul_pos h129 h1
  have hden_le : ((129 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)
      ≤ ((129 : ℕ) : ℝ) * (1 - z ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ ((129 : ℕ) : ℝ))
    linarith [hsq]
  have hmono : 2 * z ^ 129 / (((129 : ℕ) : ℝ) * (1 - z ^ 2))
      ≤ 2 * (1 / 3 : ℝ) ^ 129 / (((129 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) := by
    have hAB : 2 * z ^ 129 ≤ 2 * (1 / 3 : ℝ) ^ 129 := by linarith [hnum]
    exact div_le_div₀ (by positivity) hAB hD0 hden_le
  have hnum2 : 2 * (1 / 3 : ℝ) ^ 129 / (((129 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2))
      < 1 / 2 ^ 144 := by
    norm_num
  exact lt_of_le_of_lt hmono hnum2

/-- The (112) remainder at `m = 80` is below `2⁻¹⁴⁴`. -/
theorem arctan_remainder_m80 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    z ^ (2 * 80 + 1) / (((2 * 80 + 1 : ℕ) : ℝ)) < 1 / 2 ^ 144 := by
  have e80 : 2 * 80 + 1 = 161 := rfl
  rw [e80]
  have hpow : z ^ 161 ≤ (1 / 2 : ℝ) ^ 161 := pow_le_pow_left₀ hz0 hz1 161
  have h161 : (1 / 2 : ℝ) ^ 161 < 1 / 2 ^ 144 := by norm_num
  calc z ^ 161 / (((161 : ℕ) : ℝ))
      ≤ (1 / 2 : ℝ) ^ 161 / (((161 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ ((161 : ℕ) : ℝ))
    _ ≤ (1 / 2 : ℝ) ^ 161 := by
        have hA : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 161 := by positivity
        have hD : (1 : ℝ) ≤ ((161 : ℕ) : ℝ) := by norm_num
        have hD0 : (0 : ℝ) < ((161 : ℕ) : ℝ) := by norm_num
        rw [div_le_iff₀ hD0]
        have hle := mul_le_mul_of_nonneg_left hD hA
        rw [mul_one] at hle
        exact hle
    _ < 1 / 2 ^ 144 := h161

end ZetaSeven
