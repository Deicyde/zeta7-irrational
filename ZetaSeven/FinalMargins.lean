import ZetaSeven.PrimeSumBound
import ZetaSeven.ExactInnerIntegral
import ZetaSeven.ExactOuterIntegral

/-!
# Final rational margins (paper Section 5.5, (87)-(89); Section B.1, (118)-(119))

Prince Anand, "Zeta 7 is Irrational". With `A_0`, `B_0` and `A_M` of (87)-(89)
(`ZetaSeven.primeSumA0`, `ZetaSeven.primeSumB0`, `ZetaSeven.primeSumA`) and `U = 44/25`, the
constant of the real bound (Proposition 6.3, `ZetaSeven.real_bound`), this module records with
exact arithmetic that the paper's final margin fails (source map, open question 5):

* `B_0 = 166929451792375913959739/54488694580149392640000`, about `3.0636`
  (`ZetaSeven.primeSumB0_value`, `ZetaSeven.primeSumB0_approx`);
* `A_200 + U = 6626902387705935050696033/1362217364503734816000000`, about `4.8648`
  (`ZetaSeven.primeSumA_two_hundred_add_U`, `ZetaSeven.primeSumA_two_hundred_add_U_approx`);
* `A_M > B_0` for every integer `M > 0` (`ZetaSeven.primeSumB0_lt_primeSumA`);
* `B_0 + U > 0` (`ZetaSeven.primeSumB0_add_U_pos`), so `A_M + U > 0` for every integer `M > 0`
  (`ZetaSeven.primeSumA_add_U_pos`);
* hence the margin `A_200 + U < -95/8` (that is, `1600(A_200 + U) < -19000`), the paper's (118),
  `A_200 + U < -11`, and its (119), `A_100000 + U < -12`, all fail
  (`ZetaSeven.final_margins_fail`).

The hypothesis `M > 0` is needed: Lean's `x / 0 = 0` makes `primeSumA 0 = primeSumB0`.

## Proof

`B_0` is (88) with the exact outer integral `I_out = 453803/288000`
(`ZetaSeven.outerIntegral_value`; source-map errata 8-9, not the printed (122)) and the exact
inner integral `∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`
(`ZetaSeven.innerIntegral_value`), and (89) with `λ = 37/40` then gives `A_200`. For `M > 0`,
`A_M - B_0 = (9λM^2 - 11549M/720 + 44)/M^3`, and the numerator is positive for every real `M`
(`ZetaSeven.primeSumA_numerator_pos`): its leading coefficient `9λ = 333/40` is positive and
its discriminant `(11549/720)^2 - 4·(333/40)·44 = -626180279/518400` is negative.
-/

namespace ZetaSeven

/-! ## The exact constants -/

/-- `B_0 = 166929451792375913959739/54488694580149392640000`: (88) with the exact outer
integral `453803/288000` and the exact inner integral (121). -/
theorem primeSumB0_value :
    primeSumB0 = 166929451792375913959739 / 54488694580149392640000 := by
  rw [primeSumB0, primeSumA0, outerIntegral_value, innerIntegral_value]
  norm_num

/-- `B_0` is about `3.0636`: `|B_0 - 3.0636| < 5 · 10⁻⁵`. -/
theorem primeSumB0_approx : |primeSumB0 - 30636 / 10000| < 5 / 100000 := by
  rw [primeSumB0_value, abs_lt]
  constructor <;> norm_num

/-- (89) at `M = 200` with `U = 44/25`:
`A_200 + U = 6626902387705935050696033/1362217364503734816000000`. -/
theorem primeSumA_two_hundred_add_U :
    primeSumA 200 + 44 / 25 = 6626902387705935050696033 / 1362217364503734816000000 := by
  rw [primeSumA, primeSumB0_value, lam_real]
  norm_num

/-- `A_200 + U` is about `4.8648`: `|A_200 + U - 4.8648| < 5 · 10⁻⁵`. -/
theorem primeSumA_two_hundred_add_U_approx :
    |primeSumA 200 + 44 / 25 - 48648 / 10000| < 5 / 100000 := by
  rw [primeSumA_two_hundred_add_U, abs_lt]
  constructor <;> norm_num

/-! ## `A_M > B_0` for every `M > 0` -/

/-- The numerator `9λx^2 - 11549x/720 + 44` of `A_M - B_0 = (9λM^2 - 11549M/720 + 44)/M^3` is
positive for every real `x`: its leading coefficient `9λ = 333/40` is positive and its
discriminant `-626180279/518400` is negative. -/
theorem primeSumA_numerator_pos (x : ℝ) : 0 < 9 * (lam : ℝ) * x ^ 2 - 11549 / 720 * x + 44 := by
  rw [lam_real]
  nlinarith [sq_nonneg (x - 11549 / 11988)]

/-- `A_M > B_0` for every integer `M > 0`. -/
theorem primeSumB0_lt_primeSumA {M : ℕ} (hM : 0 < M) : primeSumB0 < primeSumA M := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h2 : (0 : ℝ) < 720 * (M : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hM' 2)
  have h3 : (0 : ℝ) < (M : ℝ) ^ 3 := pow_pos hM' 3
  have key : 0 < 9 * (lam : ℝ) / M - 11549 / (720 * (M : ℝ) ^ 2) + 44 / (M : ℝ) ^ 3 := by
    rw [div_sub_div _ _ hM'.ne' h2.ne', div_add_div _ _ (mul_pos hM' h2).ne' h3.ne']
    refine div_pos ?_ (mul_pos (mul_pos hM' h2) h3)
    nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 720) h3) (primeSumA_numerator_pos M)]
  rw [primeSumA]
  linarith

/-! ## The margins fail -/

/-- `B_0 + U > 0` with `U = 44/25`. -/
theorem primeSumB0_add_U_pos : 0 < primeSumB0 + 44 / 25 := by
  rw [primeSumB0_value]
  norm_num

/-- `A_M + U > 0` with `U = 44/25`, for every integer `M > 0`. -/
theorem primeSumA_add_U_pos {M : ℕ} (hM : 0 < M) : 0 < primeSumA M + 44 / 25 := by
  linarith [primeSumB0_lt_primeSumA hM, primeSumB0_add_U_pos]

/-- The final margins fail: with `U = 44/25`, neither `A_200 + U < -95/8` (that is,
`1600(A_200 + U) < -19000`), nor the paper's (118), `A_200 + U < -11`, nor its (119),
`A_100000 + U < -12`, holds. -/
theorem final_margins_fail :
    ¬primeSumA 200 + 44 / 25 < -95 / 8 ∧ ¬1600 * (primeSumA 200 + 44 / 25) < -19000 ∧
      ¬primeSumA 200 + 44 / 25 < -11 ∧ ¬primeSumA 100000 + 44 / 25 < -12 := by
  have h200 := primeSumA_add_U_pos (M := 200) (by norm_num)
  have h100000 := primeSumA_add_U_pos (M := 100000) (by norm_num)
  exact ⟨not_lt.mpr (by linarith), not_lt.mpr (by linarith), not_lt.mpr (by linarith),
    not_lt.mpr (by linarith)⟩

end ZetaSeven
