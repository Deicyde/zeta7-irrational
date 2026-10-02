import Mathlib.NumberTheory.ZetaValues

open Polynomial Finset

namespace ZetaSeven

/-- Bernoulli multiplication formula as a polynomial identity over `ℚ`
(DLMF 24.4.18, needed for Lemma 3.7):
`∑_{a=0}^{m-1} Bₙ(X + a/m) = (m/mⁿ) * Bₙ(m*X)`.
Follows from the real-valued `bernoulliFun_mul` by polynomial extensionality. -/
theorem bernoulli_mul {n m : ℕ} (hm : m ≠ 0) :
    (∑ a ∈ Finset.range m, (Polynomial.bernoulli n).comp (X + C ((a : ℚ) / (m : ℚ))))
      = C ((m : ℚ) / (m : ℚ) ^ n) * (Polynomial.bernoulli n).comp (C (m : ℚ) * X) := by
  have hmap : Function.Injective (Polynomial.map (algebraMap ℚ ℝ) : ℚ[X] → ℝ[X]) :=
    Polynomial.map_injective _ (RingHom.injective _)
  apply hmap
  refine Polynomial.funext fun x => ?_
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hLHS : Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
          (∑ a ∈ Finset.range m, (Polynomial.bernoulli n).comp (X + C ((a : ℚ) / (m : ℚ)))))
        = ∑ a ∈ Finset.range m, bernoulliFun n (x + (a : ℝ) / (m : ℝ)) := by
    rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Polynomial.map_comp, Polynomial.eval_comp, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      map_div₀, map_natCast, bernoulliFun]
  have hRHS : Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
          (C ((m : ℚ) / (m : ℚ) ^ n) * (Polynomial.bernoulli n).comp (C (m : ℚ) * X)))
        = ((m : ℝ) / (m : ℝ) ^ n) * bernoulliFun n ((m : ℝ) * x) := by
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_X,
      Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_X, Polynomial.eval_natCast, map_div₀, map_pow, map_natCast, bernoulliFun]
  rw [hLHS, hRHS]
  have hmul := bernoulliFun_mul n hm x
  have hpow : (m : ℝ) ^ n ≠ 0 := pow_ne_zero n hmR
  have hcd : ((m : ℝ) / (m : ℝ) ^ n) * ((m : ℝ) ^ n / (m : ℝ)) = 1 := by
    field_simp
  rw [hmul, ← mul_assoc, hcd, one_mul]

/-- Bernoulli multiplication formula with the `m ^ (1 - n)` (zpow) coefficient,
matching the `p ^ (1-n)` form in the roadmap article. -/
theorem bernoulli_mul_zpow {n m : ℕ} (hm : m ≠ 0) :
    (∑ a ∈ Finset.range m, (Polynomial.bernoulli n).comp (X + C ((a : ℚ) / (m : ℚ))))
      = C ((m : ℚ) ^ ((1 : ℤ) - (n : ℤ))) * (Polynomial.bernoulli n).comp (C (m : ℚ) * X) := by
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hcoeff : ((m : ℚ) / (m : ℚ) ^ n) = (m : ℚ) ^ ((1 : ℤ) - (n : ℤ)) := by
    rw [zpow_sub₀ hmQ, zpow_one, zpow_natCast]
  rw [← hcoeff]
  exact bernoulli_mul hm

end ZetaSeven
