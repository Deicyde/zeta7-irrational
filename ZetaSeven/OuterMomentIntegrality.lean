import ZetaSeven.Completion

/-!
# Outer moment integrality (paper Section 3.3 and Section 4.2.1)

Prince Anand, "Zeta 7 is Irrational". Fix a prime `p ≥ 7`. The polynomial moment
`μ(t^e) = μ_X(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)(2e+6)(2e+7)/720` (equation (5),
`ZetaSeven.muMonomial`; `muFunctional_X_pow` identifies it with `μ_X(t^e)`) satisfies

* `v_p(μ(t^e)) ≥ -1` for every `e` (`muMonomial_padicValRat_ge`): by (5) and (24),
  `μ(t^e) = (-1)^e κ_{2e+7}` (`muMonomial_eq_kappa`), and Lemma 3.4 bounds `κ_d`;
* `v_p(μ(t^e)) ≥ 0` for `e < 3p - 4` (`muMonomial_padicValRat_nonneg`), Section 4.2.1,
  first paragraph: von Staudt-Clausen makes `B_{2e+2}` `p`-integral unless
  `2e + 2 = k(p - 1)`, and then `1 ≤ k ≤ 5` and the factor `2e + 2 + k = kp` cancels the
  denominator `p` of `B_{2e+2}`.

`outer_moment_integrality` records both clauses. Valuations are `padicValRat p`; the paper's
`v_p(0) = +∞` and Mathlib's `padicValRat p 0 = 0` both satisfy the two bounds, so the
statements agree with the paper for every `e`. The proofs go through `p`-adic norms, as in
`ZetaSeven.norm_kappa_le` and `ZetaSeven.norm_kappa_le_one`.
-/

namespace ZetaSeven

open Polynomial

/-- `μ_X(t^e)` is the constant polynomial `μ(t^e)` of equation (5). -/
theorem muFunctional_X_pow (e : ℕ) : muFunctional (X ^ e) 0 = C (muMonomial e) := by
  unfold muFunctional
  rw [X_pow_eq_monomial, sum_monomial_index _ _ (by simp), Finsupp.sum_zero_index, add_zero,
    C_1, one_mul]

/-- Equations (5) and (24): `μ(t^e) = (-1)^e κ_{2e+7}`. -/
theorem muMonomial_eq_kappa (e : ℕ) : muMonomial e = (-1) ^ e * kappa (2 * e + 7) := by
  rw [kappa_eq, show 2 * e + 7 = 2 * e + 2 + 5 by ring, Nat.add_sub_cancel,
    descFactorial_add_five]
  unfold muMonomial
  push_cast
  ring

/-- Section 4.2.1: if `2e + 2 = k(p - 1)` and `e < 3p - 4`, then `1 ≤ k ≤ 5` and the factor
`2e + 2 + k = kp` of `(2e+3)⋯(2e+7)` is divisible by `p`. -/
theorem dvd_descFactorial_of_sub_one_dvd {p e : ℕ} (he : e < 3 * p - 4)
    (hn : (p - 1) ∣ (2 * e + 2)) : p ∣ (2 * e + 7).descFactorial 5 := by
  obtain ⟨k, hk⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  have hk5 : k ≤ 5 := by
    by_contra hcon
    have h6 := Nat.mul_le_mul_left (p - 1) (show 6 ≤ k by omega)
    omega
  have hfac : p * k = 2 * e + 7 - (5 - k) := by
    interval_cases k <;> omega
  have hmem : 5 - k ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  rw [Nat.descFactorial_eq_prod_range]
  exact dvd_trans (Dvd.intro k hfac) (Finset.dvd_prod_of_mem (fun i => 2 * e + 7 - i) hmem)

variable {p : ℕ} [Fact p.Prime]

theorem norm_muMonomial_eq (e : ℕ) :
    ‖((muMonomial e : ℚ) : ℚ_[p])‖ = ‖((kappa (2 * e + 7) : ℚ) : ℚ_[p])‖ := by
  rw [muMonomial_eq_kappa, Rat.cast_mul, norm_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- First clause in norm form: `|μ(t^e)|_p ≤ p`, from Lemma 3.4. -/
theorem norm_muMonomial_le (hp7 : 7 ≤ p) (e : ℕ) :
    ‖((muMonomial e : ℚ) : ℚ_[p])‖ ≤ p := by
  rw [norm_muMonomial_eq]
  exact norm_kappa_le hp7 _

/-- Second clause in norm form: `|μ(t^e)|_p ≤ 1` for `e < 3p - 4`. -/
theorem norm_muMonomial_le_one (hp7 : 7 ≤ p) {e : ℕ} (he : e < 3 * p - 4) :
    ‖((muMonomial e : ℚ) : ℚ_[p])‖ ≤ 1 := by
  rw [norm_muMonomial_eq, norm_kappa_eq hp7, show 2 * e + 7 - 5 = 2 * e + 2 by omega]
  by_cases hn : (p - 1) ∣ (2 * e + 2)
  · obtain ⟨c, hc⟩ := dvd_descFactorial_of_sub_one_dvd he hn
    rw [hc, Nat.cast_mul, norm_mul, Padic.norm_p]
    have h1 := padic_norm_natCast_le_one (p := p) c
    have h2 := norm_bernoulli_le (p := p) (by omega) (2 * e + 2)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc _ ≤ (p : ℝ)⁻¹ * 1 * p := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hp0.le)) h2
            (norm_nonneg _)
          positivity
      _ = 1 := by rw [mul_one, inv_mul_cancel₀ hp0.ne']
  · exact real_mul_le_one (padic_norm_natCast_le_one _) (norm_nonneg _)
      (norm_bernoulli_le_one (by omega) hn)

/-- First clause: `v_p(μ(t^e)) ≥ -1` for every `e`. -/
theorem muMonomial_padicValRat_ge (hp7 : 7 ≤ p) (e : ℕ) :
    -1 ≤ padicValRat p (muMonomial e) := by
  have h := neg_le_padicValRat_of_norm_le (p := p) (q := muMonomial e) (n := 1)
    (by rw [pow_one]; exact norm_muMonomial_le hp7 e)
  simpa using h

/-- Second clause: `v_p(μ(t^e)) ≥ 0` for `e < 3p - 4`. -/
theorem muMonomial_padicValRat_nonneg (hp7 : 7 ≤ p) {e : ℕ} (he : e < 3 * p - 4) :
    0 ≤ padicValRat p (muMonomial e) := by
  have h := neg_le_padicValRat_of_norm_le (p := p) (q := muMonomial e) (n := 0)
    (by rw [pow_zero]; exact norm_muMonomial_le_one hp7 he)
  simpa using h

/-- **Outer moment integrality** (Section 3.3, Lemma 3.4 with (24); Section 4.2.1). For a
prime `p ≥ 7` and every `e`, `v_p(μ(t^e)) ≥ -1`, and `v_p(μ(t^e)) ≥ 0` when `e < 3p - 4`. -/
theorem outer_moment_integrality (hp7 : 7 ≤ p) (e : ℕ) :
    -1 ≤ padicValRat p (muMonomial e) ∧
      (e < 3 * p - 4 → 0 ≤ padicValRat p (muMonomial e)) :=
  ⟨muMonomial_padicValRat_ge hp7 e, fun he => muMonomial_padicValRat_nonneg hp7 he⟩

end ZetaSeven
