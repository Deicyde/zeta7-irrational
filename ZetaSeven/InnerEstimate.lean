import ZetaSeven.MatrixDet
import ZetaSeven.DistributionFormula

/-!
# Inner range estimate (paper Section 4.1, Proposition 4.4, equations (42)-(51))

Prince Anand, "Zeta 7 is Irrational", Section 4.1. Fix `M ≥ 40`, `K = 40n ≥ 200 M²` and a
prime `p` with `K/M < p ≤ K/3` (hypothesis (44)).

## The class-local residue bound

The proof of Proposition 4.4 applies the distribution formula (Lemma 3.7) to each entry of the
Gram matrix in the `E`-basis and bounds every residue-class term `τ^ext_Y(g(a + p z))`
separately; the paper defers this step ((50)-(51)) to the `ζ(5)` predecessor. It is proved here
in general (`tauExt_subst_norm_le`): write `g = P + ∑_{r ∈ den} d_r/(x - r)` and
`Num = P D + ∑_r d_r D/(x - r)` with `D = ∏_{r ∈ den} (x - r)`. If after `x = a + p z` the
numerator has class degree `n` (`ClassDeg`: coefficients divisible by `p^n`, and by `p^{n+1}`
above degree `n`), the `t` poles `r ≡ a (mod p)` are pairwise incongruent modulo `p²`, and
`n ≤ p + 4 + t`, then `τ^ext_Y(g(a + p z)) ∈ p^{n-t} ℤ_p[X]`. The analytic part is controlled by
the identity `p^{-t} D(a + p z) · g(a + p z)^{an} = p^{-t}(Num(a + p z) - ∑_{r ≡ a} d_r ⋯)` and a
top-coefficient argument, since `p^{-t} D(a + p z)` is a unit times a monic polynomial of degree
`t` modulo `p`.
-/

namespace ZetaSeven

open Polynomial Finset Filter Topology

/-! ## Class degree after the substitution `x = a + p z` -/

section ClassLocal

variable {p : ℕ} [Fact p.Prime]

theorem prime_cast_pos_real : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

theorem prime_cast_one_lt_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

theorem norm_ratCast_zero_le (e : ℤ) : ‖((0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ e := by
  rw [Rat.cast_zero, norm_zero]
  exact zpow_nonneg (Nat.cast_nonneg p) e

/-- Class degree `n` at the residue `a`: after the substitution `x = a + p z` every coefficient
of `Q` has `p`-adic norm at most `p^{-n}`, and the coefficients of degree above `n` have norm at
most `p^{-n-1}`. For a product of linear factors `x - r` (`r ∈ ℤ`), `n` is the number of roots
`r ≡ a (mod p)` (`classDeg_prod_X_sub_C`). -/
def ClassDeg (p : ℕ) [Fact p.Prime] (a n : ℕ) (Q : ℚ[X]) : Prop :=
  ∀ k, ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff k : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ∧
    (n < k → ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff k : ℚ) : ℚ_[p])‖
      ≤ (p : ℝ) ^ (-(n : ℤ) - 1))

theorem ClassDeg.one (a : ℕ) : ClassDeg p a 0 (1 : ℚ[X]) := by
  intro k
  rw [one_comp, coeff_one]
  split_ifs with hk
  · subst hk
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    simp
  · exact ⟨norm_ratCast_zero_le _, fun _ => norm_ratCast_zero_le _⟩

theorem ClassDeg.neg {a n : ℕ} {Q : ℚ[X]} (hQ : ClassDeg p a n Q) : ClassDeg p a n (-Q) := by
  intro k
  rw [neg_comp, coeff_neg, Rat.cast_neg, norm_neg]
  exact hQ k

theorem ClassDeg.mul {a n m : ℕ} {Q R : ℚ[X]} (hQ : ClassDeg p a n Q) (hR : ClassDeg p a m R) :
    ClassDeg p a (n + m) (Q * R) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hnn : ∀ e : ℤ, (0 : ℝ) ≤ (p : ℝ) ^ e := fun e => zpow_nonneg (Nat.cast_nonneg p) e
  intro k
  rw [mul_comp, coeff_mul, Rat.cast_sum]
  have hterm : ∀ x ∈ antidiagonal k,
      ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.1
          * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.2 : ℚ) : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-((n + m : ℕ) : ℤ)) ∧
      (n + m < k → ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.1
          * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.2 : ℚ) : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-((n + m : ℕ) : ℤ) - 1)) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Rat.cast_mul, norm_mul]
    refine ⟨?_, fun hk => ?_⟩
    · calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) :=
            mul_le_mul (hQ x.1).1 (hR x.2).1 (norm_nonneg _) (hnn _)
        _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
    · by_cases h1 : n < x.1
      · calc _ ≤ (p : ℝ) ^ (-(n : ℤ) - 1) * (p : ℝ) ^ (-(m : ℤ)) :=
              mul_le_mul ((hQ x.1).2 h1) (hR x.2).1 (norm_nonneg _) (hnn _)
          _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
      · have h2 : m < x.2 := by omega
        calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * (p : ℝ) ^ (-(m : ℤ) - 1) :=
              mul_le_mul (hQ x.1).1 ((hR x.2).2 h2) (norm_nonneg _) (hnn _)
          _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
  exact ⟨IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hnn _) fun x hx => (hterm x hx).1,
    fun hk => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hnn _)
      fun x hx => (hterm x hx).2 hk⟩

theorem ClassDeg.pow {a n : ℕ} {Q : ℚ[X]} (hQ : ClassDeg p a n Q) (e : ℕ) :
    ClassDeg p a (n * e) (Q ^ e) := by
  induction e with
  | zero => simpa using ClassDeg.one (p := p) a
  | succ e ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hQ

theorem ClassDeg.prod {ι : Type*} (s : Finset ι) {a : ℕ} (n : ι → ℕ) (Q : ι → ℚ[X])
    (h : ∀ i ∈ s, ClassDeg p a (n i) (Q i)) :
    ClassDeg p a (∑ i ∈ s, n i) (∏ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ClassDeg.one (p := p) a
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fact p.Prime] in
theorem comp_affine_X_sub_C' (a : ℕ) (r : ℤ) :
    (X - C (r : ℚ)).comp (C (a : ℚ) + C (p : ℚ) * X) = C (((a - r : ℤ) : ℚ)) + C (p : ℚ) * X := by
  rw [sub_comp, X_comp, C_comp, Int.cast_sub, Int.cast_natCast, C_sub]
  ring

theorem norm_ratCast_p : ‖(((p : ℚ)) : ℚ_[p])‖ = (p : ℝ) ^ (-1 : ℤ) := by
  rw [Rat.cast_natCast, Padic.norm_p, zpow_neg_one]

/-- A linear factor `x - r` has class degree `1` at `a` if `r ≡ a (mod p)` and `0` otherwise. -/
theorem classDeg_X_sub_C (a : ℕ) (r : ℤ) :
    ClassDeg p a (if (p : ℤ) ∣ r - a then 1 else 0) (X - C (r : ℚ)) := by
  have hp1 := prime_cast_one_lt_real (p := p)
  have hint : ‖((((a - r : ℤ) : ℚ)) : ℚ_[p])‖ ≤ 1 := by
    rw [Rat.cast_intCast]; exact Padic.norm_int_le_one _
  intro k
  rw [comp_affine_X_sub_C']
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]
      split_ifs with h
      · have h' : (p : ℤ) ^ 1 ∣ ((a : ℤ) - r) := by
          rw [pow_one, show (a : ℤ) - r = -(r - a) by ring]; exact dvd_neg.mpr h
        have h1 := (Padic.norm_int_le_pow_iff_dvd (p := p) ((a : ℤ) - r) 1).mpr h'
        refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
        rw [Rat.cast_intCast]
        simpa using h1
      · refine ⟨?_, fun h0 => absurd h0 (lt_irrefl 0)⟩
        simpa using hint
    · rw [coeff_add, coeff_C_of_ne_zero one_ne_zero, coeff_C_mul, coeff_X_one, mul_one, zero_add]
      split_ifs with h
      · refine ⟨?_, fun h0 => absurd h0 (lt_irrefl 1)⟩
        rw [norm_ratCast_p]; norm_num
      · refine ⟨?_, fun _ => ?_⟩
        · rw [norm_ratCast_p]; exact zpow_le_zpow_right₀ hp1.le (by norm_num)
        · rw [norm_ratCast_p]; norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [coeff_add, coeff_C_of_ne_zero (by omega), coeff_C_mul, coeff_X_of_ne_one (by omega),
      mul_zero, add_zero]
    exact ⟨norm_ratCast_zero_le _, fun _ => norm_ratCast_zero_le _⟩

/-- The leading class coefficient of `x - r`: the coefficient of degree equal to the class degree
has norm exactly `p^{-class degree}`. -/
theorem norm_lead_X_sub_C (a : ℕ) (r : ℤ) :
    ‖((((X - C (r : ℚ)).comp (C (a : ℚ) + C (p : ℚ) * X)).coeff
        (if (p : ℤ) ∣ r - a then 1 else 0) : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((if (p : ℤ) ∣ r - a then 1 else 0 : ℕ) : ℤ)) := by
  rw [comp_affine_X_sub_C']
  split_ifs with h
  · rw [coeff_add, coeff_C_of_ne_zero one_ne_zero, coeff_C_mul, coeff_X_one, mul_one, zero_add,
      norm_ratCast_p]
    norm_num
  · rw [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero, Rat.cast_intCast]
    have hnd : ¬ (p : ℤ) ∣ ((a : ℤ) - r) := fun h' => h (by
      rw [show r - (a : ℤ) = -((a : ℤ) - r) by ring]; exact dvd_neg.mpr h')
    rw [le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnd (Padic.norm_intCast_lt_one_iff.mp hlt))]
    simp

/-- Exactness of the leading class coefficient is multiplicative. -/
theorem ClassDeg.mul_lead {a n m : ℕ} {Q R : ℚ[X]} (hQ : ClassDeg p a n Q)
    (hR : ClassDeg p a m R)
    (hQn : ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff n : ℚ) : ℚ_[p])‖ = (p : ℝ) ^ (-(n : ℤ)))
    (hRm : ‖(((R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff m : ℚ) : ℚ_[p])‖ = (p : ℝ) ^ (-(m : ℤ))) :
    ‖((((Q * R).comp (C (a : ℚ) + C (p : ℚ) * X)).coeff (n + m) : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((n + m : ℕ) : ℤ)) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hp1 := prime_cast_one_lt_real (p := p)
  have hnn : ∀ e : ℤ, (0 : ℝ) ≤ (p : ℝ) ^ e := fun e => zpow_nonneg (Nat.cast_nonneg p) e
  rw [mul_comp, coeff_mul, Rat.cast_sum, ← Finset.add_sum_erase _ _ (show (n, m) ∈ antidiagonal
    (n + m) from Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)]
  dsimp only
  have hmain : ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff n
        * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff m : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((n + m : ℕ) : ℤ)) := by
    rw [Rat.cast_mul, norm_mul, hQn, hRm, ← zpow_add₀ hp0]; congr 1; push_cast; ring
  have hrest : ‖∑ x ∈ (antidiagonal (n + m)).erase (n, m),
        (((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.1
          * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.2 : ℚ) : ℚ_[p])‖
      ≤ (p : ℝ) ^ (-((n + m : ℕ) : ℤ) - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hnn _) fun x hx => ?_
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Rat.cast_mul, norm_mul]
    by_cases h1 : n < x.1
    · calc _ ≤ (p : ℝ) ^ (-(n : ℤ) - 1) * (p : ℝ) ^ (-(m : ℤ)) :=
            mul_le_mul ((hQ x.1).2 h1) (hR x.2).1 (norm_nonneg _) (hnn _)
        _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
    · have h2 : m < x.2 := by
        rcases Nat.lt_or_ge m x.2 with h | h
        · exact h
        · exact absurd (Prod.ext (by show x.1 = n; omega) (by show x.2 = m; omega)) hne
      calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * (p : ℝ) ^ (-(m : ℤ) - 1) :=
            mul_le_mul (hQ x.1).1 ((hR x.2).2 h2) (norm_nonneg _) (hnn _)
        _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
  have hlt : ‖∑ x ∈ (antidiagonal (n + m)).erase (n, m),
        (((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.1
          * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff x.2 : ℚ) : ℚ_[p])‖
      < ‖(((Q.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff n
        * (R.comp (C (a : ℚ) + C (p : ℚ) * X)).coeff m : ℚ) : ℚ_[p])‖ :=
    hrest.trans_lt (by rw [hmain]; exact zpow_lt_zpow_right₀ hp1 (by omega))
  rw [Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, hmain]

theorem ClassDeg.prod_lead {ι : Type*} (s : Finset ι) {a : ℕ} (n : ι → ℕ) (Q : ι → ℚ[X])
    (h : ∀ i ∈ s, ClassDeg p a (n i) (Q i))
    (hl : ∀ i ∈ s, ‖((((Q i).comp (C (a : ℚ) + C (p : ℚ) * X)).coeff (n i) : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-(n i : ℤ))) :
    ‖((((∏ i ∈ s, Q i).comp (C (a : ℚ) + C (p : ℚ) * X)).coeff (∑ i ∈ s, n i) : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((∑ i ∈ s, n i : ℕ) : ℤ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul_lead
      (ClassDeg.prod s n Q fun j hj => h j (Finset.mem_insert_of_mem hj))
      (hl i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
        fun j hj => hl j (Finset.mem_insert_of_mem hj))

/-- A product of linear factors `x - r` over `r ∈ s` has class degree equal to the number of
roots `r ≡ a (mod p)`. -/
theorem classDeg_prod_X_sub_C (a : ℕ) (s : Finset ℤ) :
    ClassDeg p a (s.filter fun r => (p : ℤ) ∣ r - a).card (∏ r ∈ s, (X - C (r : ℚ))) := by
  rw [card_filter]
  exact ClassDeg.prod s _ _ fun r _ => classDeg_X_sub_C a r

theorem norm_lead_prod_X_sub_C (a : ℕ) (s : Finset ℤ) :
    ‖((((∏ r ∈ s, (X - C (r : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X)).coeff
        (s.filter fun r => (p : ℤ) ∣ r - a).card : ℚ) : ℚ_[p])‖
      = (p : ℝ) ^ (-((s.filter fun r => (p : ℤ) ∣ r - a).card : ℤ)) := by
  rw [card_filter]
  exact ClassDeg.prod_lead s _ _ (fun r _ => classDeg_X_sub_C a r)
    fun r _ => norm_lead_X_sub_C a r

/-! ## Partial fractions and the residue bound -/

/-- The numerator `Num = P · D + ∑_{r ∈ den} d_r D/(x - r)` of `g = P + ∑_{r ∈ den} d_r/(x - r)`
over `D = ∏_{r ∈ den} (x - r)`, so that `g = Num/D`. -/
noncomputable def pfNum (P : ℚ[X]) (d : ℤ →₀ ℚ) (den : Finset ℤ) : ℚ[X] :=
  P * ∏ r ∈ den, (X - C (r : ℚ)) + ∑ r ∈ den, C (d r) * ∏ j ∈ den.erase r, (X - C (j : ℚ))

/-- Evaluating the numerator at a pole `r ∈ den` isolates `d_r`. -/
theorem eval_pfNum (P : ℚ[X]) (d : ℤ →₀ ℚ) (den : Finset ℤ) {r : ℤ} (hr : r ∈ den) :
    (pfNum P d den).eval (r : ℚ) = d r * ∏ j ∈ den.erase r, ((r : ℚ) - j) := by
  have h0 : ∏ j ∈ den, eval (r : ℚ) (X - C (j : ℚ)) = 0 :=
    Finset.prod_eq_zero hr (by simp)
  rw [pfNum, eval_add, eval_mul, eval_prod, h0, mul_zero, zero_add, eval_finsetSum,
    Finset.sum_eq_single r]
  · rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro j _ hjr
    rw [eval_mul, eval_prod]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hjr, hr⟩) (by simp))
  · intro h
    exact absurd hr h

/-- A polynomial of class degree `n` at `a` takes values in `p^n ℤ_p` on `a + p ℤ`. -/
theorem norm_eval_affine_le {Q : ℚ[X]} {a n : ℕ} (hQ : ClassDeg p a n Q) (s : ℤ) :
    ‖((Q.eval ((a : ℚ) + p * s) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have h : Q.eval ((a : ℚ) + p * s) = (Q.comp (C (a : ℚ) + C (p : ℚ) * X)).eval (s : ℚ) := by
    rw [eval_comp]
    simp
  rw [h, eval_eq_sum_range, Rat.cast_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (zpow_nonneg (Nat.cast_nonneg p) _) fun i _ => ?_
  rw [Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow, Rat.cast_intCast]
  calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
        mul_le_mul (hQ i).1 (pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one s))
          (by positivity) (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = _ := mul_one _

/-- At a pole `r ≡ a (mod p)` whose class-mates are incongruent to it modulo `p²`,
`|∏_{j ≠ r} (r - j)|_p ≥ p^{-(t - 1)}`, where `t` is the number of poles `≡ a (mod p)`. -/
theorem norm_prod_sub_ge {den : Finset ℤ} {a : ℕ} {r : ℤ} (hr : r ∈ den)
    (hra : (p : ℤ) ∣ r - a)
    (hinc : ∀ j ∈ den, r ≠ j → (p : ℤ) ∣ j - a → ¬ (p : ℤ) ^ 2 ∣ r - j) :
    (p : ℝ) ^ (-(((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1)) ≤
      ‖((∏ j ∈ den.erase r, ((r : ℚ) - j) : ℚ) : ℚ_[p])‖ := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hrS : r ∈ den.filter fun j => (p : ℤ) ∣ j - a := Finset.mem_filter.mpr ⟨hr, hra⟩
  have ht : 1 ≤ (den.filter fun j => (p : ℤ) ∣ j - a).card := Finset.card_pos.mpr ⟨r, hrS⟩
  have hcast : ∀ j : ℤ, (((r : ℚ) - j : ℚ) : ℚ_[p]) = ((r - j : ℤ) : ℚ_[p]) := fun j => by
    norm_cast
  rw [Rat.cast_prod, norm_prod,
    ← Finset.prod_filter_mul_prod_filter_not (den.erase r) (fun j => (p : ℤ) ∣ j - a)]
  have hin : ∀ j ∈ (den.erase r).filter (fun j => (p : ℤ) ∣ j - a),
      (p : ℝ)⁻¹ ≤ ‖(((r : ℚ) - j : ℚ) : ℚ_[p])‖ := by
    intro j hj
    obtain ⟨hj, hja⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjr, hj⟩ := Finset.mem_erase.mp hj
    rw [hcast]
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have h2 : ‖((r - j : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((2 : ℕ) : ℤ)) := by
      rw [show (-((2 : ℕ) : ℤ)) = -2 by norm_num, Padic.norm_le_pow_iff_norm_lt_pow_add_one,
        show (-2 : ℤ) + 1 = -1 by norm_num, zpow_neg_one]
      exact hlt
    exact hinc j hj (Ne.symm hjr) hja ((Padic.norm_int_le_pow_iff_dvd _ 2).mp h2)
  have hout : ∀ j ∈ (den.erase r).filter (fun j => ¬ (p : ℤ) ∣ j - a),
      ‖(((r : ℚ) - j : ℚ) : ℚ_[p])‖ = 1 := by
    intro j hj
    obtain ⟨-, hja⟩ := Finset.mem_filter.mp hj
    rw [hcast]
    have hnd : ¬ (p : ℤ) ∣ r - j := fun h => hja (by
      have h' := dvd_sub hra h
      rwa [show r - (a : ℤ) - (r - j) = j - a by ring] at h')
    exact le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnd (Padic.norm_intCast_lt_one_iff.mp hlt))
  rw [Finset.prod_eq_one hout, mul_one]
  have hcard : ((den.erase r).filter fun j => (p : ℤ) ∣ j - a).card
      = (den.filter fun j => (p : ℤ) ∣ j - a).card - 1 := by
    rw [Finset.filter_erase, Finset.card_erase_of_mem hrS]
  have hexp : (-(((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1))
      = -((((den.filter fun j => (p : ℤ) ∣ j - a).card - 1 : ℕ)) : ℤ) := by omega
  calc (p : ℝ) ^ (-(((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1))
      = ∏ _j ∈ (den.erase r).filter (fun j => (p : ℤ) ∣ j - a), (p : ℝ)⁻¹ := by
        rw [hexp, zpow_neg, zpow_natCast, Finset.prod_const, hcard, inv_pow]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) hin

/-- **Residue bound.** At a pole `r ≡ a (mod p)`, `|d_r|_p ≤ p^{t - 1 - n}`. -/
theorem norm_residue_le (P : ℚ[X]) (d : ℤ →₀ ℚ) {den : Finset ℤ} {a n : ℕ}
    (hN : ClassDeg p a n (pfNum P d den)) {r : ℤ} (hr : r ∈ den) (hra : (p : ℤ) ∣ r - a)
    (hinc : ∀ j ∈ den, r ≠ j → (p : ℤ) ∣ j - a → ¬ (p : ℤ) ^ 2 ∣ r - j) :
    ‖((d r : ℚ) : ℚ_[p])‖
      ≤ (p : ℝ) ^ (((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1 - n) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  obtain ⟨s, hs⟩ := hra
  have hr' : (r : ℚ) = (a : ℚ) + p * s := by
    have h : r = (a : ℤ) + p * s := by linarith
    exact_mod_cast h
  have hnum := norm_eval_affine_le hN s
  rw [← hr', eval_pfNum P d den hr, Rat.cast_mul, norm_mul] at hnum
  have hlow := norm_prod_sub_ge hr ⟨s, hs⟩ hinc
  rw [show ((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1 - n
      = -(n : ℤ) - (-(((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1)) by ring,
    zpow_sub₀ hp0, le_div_iff₀ (zpow_pos prime_cast_pos_real _)]
  exact (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)).trans hnum

/-- The principal parts of `g(a + p z)` lie in `p^{t - n} ℤ_p`. -/
theorem norm_substPrincipal_le (P : ℚ[X]) (d : ℤ →₀ ℚ) {den : Finset ℤ}
    (hsupp : d.support ⊆ den) {a n : ℕ} (hN : ClassDeg p a n (pfNum P d den))
    (hinc : ∀ r ∈ den, ∀ j ∈ den, r ≠ j → (p : ℤ) ∣ r - a → (p : ℤ) ∣ j - a →
      ¬ (p : ℤ) ^ 2 ∣ r - j)
    {s : ℤ} (hs : s ∈ substPoles p a d) :
    ‖((substPrincipal p a d s : ℚ) : ℚ_[p])‖
      ≤ (p : ℝ) ^ (((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - n) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hrs, hra⟩ := Finset.mem_filter.mp hr
  have hra' : (a : ℤ) + p * ((r - a) / p) = r := by
    rw [Int.mul_ediv_cancel' hra]; ring
  have hrd := hsupp hrs
  have hres := norm_residue_le P d hN hrd hra fun j hj hrj hja => hinc r hrd j hj hrj hra hja
  rw [substPrincipal, hra', Rat.cast_div, norm_div, norm_ratCast_p, zpow_neg_one, div_inv_eq_mul]
  calc ‖((d r : ℚ) : ℚ_[p])‖ * p
      ≤ (p : ℝ) ^ (((den.filter fun j => (p : ℤ) ∣ j - a).card : ℤ) - 1 - n)
          * (p : ℝ) ^ (1 : ℤ) := by
        rw [zpow_one]; exact mul_le_mul_of_nonneg_right hres (Nat.cast_nonneg p)
    _ = _ := by rw [← zpow_add₀ hp0]; congr 1; ring

/-! ## The top-coefficient argument -/

/-- Let `W` be a polynomial whose coefficient of degree `t` is a unit, with integral coefficients
and coefficients above `t` divisible by `p`, and let `G` be a restricted power series. If
`W G ∈ p^e ℤ_p⟦z⟧` with coefficients above degree `D` in `p^{e+1} ℤ_p`, then `G ∈ p^e ℤ_p⟦z⟧`
with coefficients above degree `D - t` in `p^{e+1} ℤ_p` (compare the coefficient of `W G` at
`m + t`, for `m` the largest index of a coefficient of maximal norm). -/
theorem top_coeff_bound {W : Polynomial ℚ_[p]} {G : PowerSeries ℚ_[p]} {t D : ℕ} {e : ℤ}
    (hG : G.IsRestricted 1) (hWt : ‖W.coeff t‖ = 1) (hW1 : ∀ i, ‖W.coeff i‖ ≤ 1)
    (hWp : ∀ i, t < i → ‖W.coeff i‖ ≤ (p : ℝ)⁻¹)
    (hR : ∀ k, ‖PowerSeries.coeff k ((W : PowerSeries ℚ_[p]) * G)‖ ≤ (p : ℝ) ^ e)
    (hRD : ∀ k, D < k → ‖PowerSeries.coeff k ((W : PowerSeries ℚ_[p]) * G)‖ ≤ (p : ℝ) ^ (e - 1)) :
    (∀ j, ‖PowerSeries.coeff j G‖ ≤ (p : ℝ) ^ e) ∧
      ∀ j, D < j + t → ‖PowerSeries.coeff j G‖ ≤ (p : ℝ) ^ (e - 1) := by
  have hp1 := prime_cast_one_lt_real (p := p)
  -- the coefficient of `W G` at `m + t` for a last coefficient `G_m` of maximal norm
  have key : ∀ m, (∀ j, ‖PowerSeries.coeff j G‖ ≤ ‖PowerSeries.coeff m G‖) →
      (∀ j, m < j → ‖PowerSeries.coeff j G‖ < ‖PowerSeries.coeff m G‖) →
      0 < ‖PowerSeries.coeff m G‖ →
      ‖PowerSeries.coeff (m + t) ((W : PowerSeries ℚ_[p]) * G)‖ = ‖PowerSeries.coeff m G‖ := by
    intro m hmax hlt hpos
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ (show (t, m) ∈ antidiagonal (m + t) from
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_comm t m))]
    dsimp only
    have hmain : ‖PowerSeries.coeff t (W : PowerSeries ℚ_[p]) * PowerSeries.coeff m G‖
        = ‖PowerSeries.coeff m G‖ := by
      rw [norm_mul, Polynomial.coeff_coe, hWt, one_mul]
    have hrest : ‖∑ x ∈ (antidiagonal (m + t)).erase (t, m),
          PowerSeries.coeff x.1 (W : PowerSeries ℚ_[p]) * PowerSeries.coeff x.2 G‖
        < ‖PowerSeries.coeff m G‖ := by
      rcases Finset.eq_empty_or_nonempty ((antidiagonal (m + t)).erase (t, m)) with he | hne
      · rw [he, Finset.sum_empty, norm_zero]
        exact hpos
      · obtain ⟨x, hx, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
          (fun x : ℕ × ℕ => PowerSeries.coeff x.1 (W : PowerSeries ℚ_[p]) * PowerSeries.coeff x.2 G)
        refine hle.trans_lt ?_
        obtain ⟨hxne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        dsimp only
        rw [norm_mul, Polynomial.coeff_coe]
        rcases lt_trichotomy x.1 t with h | h | h
        · have h2 : m < x.2 := by omega
          calc ‖W.coeff x.1‖ * ‖PowerSeries.coeff x.2 G‖ ≤ 1 * ‖PowerSeries.coeff x.2 G‖ :=
                mul_le_mul_of_nonneg_right (hW1 _) (norm_nonneg _)
            _ < ‖PowerSeries.coeff m G‖ := by rw [one_mul]; exact hlt _ h2
        · exact absurd (Prod.ext h (by show x.2 = m; omega)) hxne
        · calc ‖W.coeff x.1‖ * ‖PowerSeries.coeff x.2 G‖
              ≤ (p : ℝ)⁻¹ * ‖PowerSeries.coeff m G‖ :=
                mul_le_mul (hWp _ h) (hmax _) (norm_nonneg _) (by positivity)
            _ < 1 * ‖PowerSeries.coeff m G‖ := mul_lt_mul_of_pos_right inv_prime_lt_one hpos
            _ = _ := one_mul _
    have hne : ‖PowerSeries.coeff t (W : PowerSeries ℚ_[p]) * PowerSeries.coeff m G‖ ≠
        ‖∑ x ∈ (antidiagonal (m + t)).erase (t, m),
          PowerSeries.coeff x.1 (W : PowerSeries ℚ_[p]) * PowerSeries.coeff x.2 G‖ := by
      rw [hmain]; exact ne_of_gt hrest
    rw [Padic.add_eq_max_of_ne hne, hmain, max_eq_left hrest.le]
  -- a last coefficient of maximal norm above any positive level that is attained
  rw [PowerSeries.isRestricted_iff'] at hG
  simp only [one_pow, mul_one] at hG
  have hmaxex : ∀ γ : ℝ, 0 < γ → ∀ j0, γ ≤ ‖PowerSeries.coeff j0 G‖ →
      ∃ m, (∀ j, ‖PowerSeries.coeff j G‖ ≤ ‖PowerSeries.coeff m G‖) ∧
        (∀ j, m < j → ‖PowerSeries.coeff j G‖ < ‖PowerSeries.coeff m G‖) ∧
        (∀ j, ‖PowerSeries.coeff j G‖ = ‖PowerSeries.coeff m G‖ → j ≤ m) ∧
        γ ≤ ‖PowerSeries.coeff m G‖ := by
    intro γ hγ j0 hj0
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hG γ hγ
    have hsmall : ∀ j, N0 ≤ j → ‖PowerSeries.coeff j G‖ < γ := fun j hj => by
      have := hN0 j hj
      rwa [Real.dist_eq, sub_zero, abs_norm] at this
    set S := (range N0).filter fun j => γ ≤ ‖PowerSeries.coeff j G‖ with hS
    have hmemS : ∀ j, γ ≤ ‖PowerSeries.coeff j G‖ → j ∈ S := fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        by_contra hjN
        exact absurd hj (not_le.mpr (hsmall j (not_lt.mp hjN)))), hj⟩
    obtain ⟨m0, hm0S, hm0⟩ :=
      Finset.exists_max_image S (fun j => ‖PowerSeries.coeff j G‖) ⟨j0, hmemS j0 hj0⟩
    have hγm0 : γ ≤ ‖PowerSeries.coeff m0 G‖ := (Finset.mem_filter.mp hm0S).2
    have hall : ∀ j, ‖PowerSeries.coeff j G‖ ≤ ‖PowerSeries.coeff m0 G‖ := fun j => by
      by_cases hj : γ ≤ ‖PowerSeries.coeff j G‖
      · exact hm0 j (hmemS j hj)
      · exact (not_le.mp hj).le.trans hγm0
    set S' := S.filter fun j => ‖PowerSeries.coeff j G‖ = ‖PowerSeries.coeff m0 G‖ with hS'
    have hne' : S'.Nonempty := ⟨m0, Finset.mem_filter.mpr ⟨hm0S, rfl⟩⟩
    have hmS' := Finset.max'_mem S' hne'
    have hmeq : ‖PowerSeries.coeff (S'.max' hne') G‖ = ‖PowerSeries.coeff m0 G‖ :=
      (Finset.mem_filter.mp hmS').2
    have hle' : ∀ j, ‖PowerSeries.coeff j G‖ = ‖PowerSeries.coeff m0 G‖ → j ≤ S'.max' hne' :=
      fun j hj => Finset.le_max' S' j (Finset.mem_filter.mpr ⟨hmemS j (hγm0.trans hj.ge), hj⟩)
    refine ⟨S'.max' hne', fun j => (hall j).trans hmeq.ge, fun j hj => ?_,
      fun j hj => hle' j (hj.trans hmeq), hγm0.trans hmeq.ge⟩
    rw [hmeq]
    exact lt_of_le_of_ne (hall j) fun heq => absurd (hle' j heq) (not_le.mpr hj)
  have hpos : ∀ e' : ℤ, (0 : ℝ) < (p : ℝ) ^ e' := fun e' => zpow_pos prime_cast_pos_real e'
  have part1 : ∀ j, ‖PowerSeries.coeff j G‖ ≤ (p : ℝ) ^ e := by
    intro j0
    by_contra hbig'
    have hbig := not_le.mp hbig'
    obtain ⟨m, hm1, hm2, -, hm4⟩ := hmaxex _ ((hpos e).trans hbig) j0 le_rfl
    have := key m hm1 hm2 (((hpos e).trans hbig).trans_le hm4)
    have h5 := hR (m + t)
    rw [this] at h5
    exact absurd (hbig.trans_le hm4) (not_lt.mpr h5)
  refine ⟨part1, fun j0 hj0 => ?_⟩
  by_contra hbig
  have hge : (p : ℝ) ^ e ≤ ‖PowerSeries.coeff j0 G‖ := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel] at hbig
    exact not_lt.mp hbig
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hmaxex _ (hpos e) j0 hge
  have hmB : ‖PowerSeries.coeff m G‖ = (p : ℝ) ^ e := le_antisymm (part1 m) (hge.trans (hm1 j0))
  have hj0m : j0 ≤ m := hm3 j0 (by rw [hmB]; exact le_antisymm (part1 j0) hge)
  have := key m hm1 hm2 (by rw [hmB]; exact hpos e)
  have h5 := hRD (m + t) (by omega)
  rw [this, hmB] at h5
  exact absurd h5 (not_le.mpr (zpow_lt_zpow_right₀ hp1 (by omega)))

/-! ## The analytic part of `g(a + p z)` -/

theorem finset_sum_comp' {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (q : ℚ[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  have h := map_sum (Polynomial.compRingHom q) f s
  simp only [coe_compRingHom_apply] at h
  exact h

theorem coe_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    ((∑ i ∈ s, f i : ℚ[X]) : PowerSeries ℚ) = ∑ i ∈ s, (f i : PowerSeries ℚ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) f s
  simp only [Polynomial.coeToPowerSeries.ringHom_apply] at h
  exact h

theorem norm_inv_p_pow (t : ℕ) : ‖((((p : ℚ) ^ t)⁻¹ : ℚ) : ℚ_[p])‖ = (p : ℝ) ^ (t : ℤ) := by
  rw [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, norm_inv, norm_pow, Padic.norm_p, inv_pow,
    inv_inv, zpow_natCast]

/-- `W = p^{-t} D(a + p z)`, with `D = ∏_{r ∈ den} (x - r)` and `t` the number of poles
`r ≡ a (mod p)`. Modulo `p` it is a unit times a monic polynomial of degree `t`. -/
noncomputable def wPoly (p a : ℕ) (den : Finset ℤ) : ℚ[X] :=
  C (((p : ℚ) ^ (den.filter fun r => (p : ℤ) ∣ r - a).card)⁻¹)
    * (∏ r ∈ den, (X - C (r : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X)

/-- `p^{-t} (Num(a + p z) - ∑_{r ≡ a} d_r D_r(a + p z))`, with `D_r = D/(x - r)`: the product of
`wPoly` with the analytic part of `g(a + p z)` (`W_mul_substAnalytic`). -/
noncomputable def rPoly (p a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) (den : Finset ℤ) : ℚ[X] :=
  C (((p : ℚ) ^ (den.filter fun r => (p : ℤ) ∣ r - a).card)⁻¹)
    * ((pfNum P d den).comp (C (a : ℚ) + C (p : ℚ) * X)
      - ∑ r ∈ den.filter (fun r => (p : ℤ) ∣ r - a),
          C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X))

theorem norm_coeff_wPoly (a : ℕ) (den : Finset ℤ) (i : ℕ) :
    ‖(((wPoly p a den).coeff i : ℚ) : ℚ_[p])‖ ≤ 1 ∧
      ((den.filter fun r => (p : ℤ) ∣ r - a).card < i →
        ‖(((wPoly p a den).coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹) ∧
      (i = (den.filter fun r => (p : ℤ) ∣ r - a).card →
        ‖(((wPoly p a den).coeff i : ℚ) : ℚ_[p])‖ = 1) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hc := classDeg_prod_X_sub_C (p := p) a den
  have hl := norm_lead_prod_X_sub_C (p := p) a den
  rw [wPoly, coeff_C_mul, Rat.cast_mul, norm_mul, norm_inv_p_pow]
  set t := (den.filter fun r => (p : ℤ) ∣ r - a).card with ht
  refine ⟨?_, fun hi => ?_, fun hi => ?_⟩
  · calc _ ≤ (p : ℝ) ^ (t : ℤ) * (p : ℝ) ^ (-(t : ℤ)) :=
          mul_le_mul_of_nonneg_left (hc i).1 (zpow_nonneg (Nat.cast_nonneg p) _)
      _ = 1 := by rw [← zpow_add₀ hp0, add_neg_cancel, zpow_zero]
  · calc _ ≤ (p : ℝ) ^ (t : ℤ) * (p : ℝ) ^ (-(t : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left ((hc i).2 hi) (zpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ)⁻¹ := by
          rw [← zpow_add₀ hp0, show (t : ℤ) + (-(t : ℤ) - 1) = -1 by ring, zpow_neg_one]
  · subst hi
    rw [hl, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero]

/-- The identity behind the analytic bound: `p^{-t} D(a + p z)` times the analytic part of
`g(a + p z)` is the polynomial `rPoly`. Each pole `r ≢ a` contributes
`(d_r/p) · 1/(z - (r - a)/p)`, and `D(a + p z) = p (z - (r - a)/p) D_r(a + p z)`. -/
theorem W_mul_substAnalytic (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) {den : Finset ℤ}
    (hsupp : d.support ⊆ den) :
    ((wPoly p a den : ℚ[X]) : PowerSeries ℚ) * substAnalytic p a P d
      = ((rPoly p a P d den : ℚ[X]) : PowerSeries ℚ) := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [wPoly, rPoly]
  set c : ℚ := ((p : ℚ) ^ (den.filter fun r => (p : ℤ) ∣ r - a).card)⁻¹ with hc
  have hpole : ∀ r ∈ den, ¬ (p : ℤ) ∣ r - a →
      ((C c * (∏ j ∈ den, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X])
          : PowerSeries ℚ) * (PowerSeries.C (d r / p) * poleSeries (((r - a : ℤ) : ℚ) / p))
        = ((C c * (C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
            (C (a : ℚ) + C (p : ℚ) * X)) : ℚ[X]) : PowerSeries ℚ) := by
    intro r hr hra
    have hσ : (((r - a : ℤ) : ℚ) / p) ≠ 0 := by
      have h1 : (r - a : ℤ) ≠ 0 := fun h => hra (by rw [h]; exact dvd_zero _)
      exact div_ne_zero (by exact_mod_cast h1) hp
    have hprod : (∏ j ∈ den, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X)
        = C (p : ℚ) * (X - C (((r - a : ℤ) : ℚ) / p))
          * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X) := by
      rw [← Finset.mul_prod_erase den (fun j : ℤ => X - C (j : ℚ)) hr, mul_comp,
        comp_affine_X_sub_C hp a r]
    have hpm := poleSeries_mul hσ
    have hC : PowerSeries.C (p : ℚ) * PowerSeries.C (d r / p) = PowerSeries.C (d r) := by
      rw [← map_mul, mul_div_cancel₀ _ hp]
    rw [hprod]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_sub, Polynomial.coe_X]
    linear_combination (PowerSeries.C c * PowerSeries.C (d r / p) * PowerSeries.C (p : ℚ)
        * (((∏ j ∈ den.erase r, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X])
          : PowerSeries ℚ)) * hpm
      + (PowerSeries.C c * (((∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
          (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X]) : PowerSeries ℚ)) * hC
  have hsum : ∑ r ∈ d.support,
      ((C c * (∏ j ∈ den, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X])
          : PowerSeries ℚ)
        * (if (p : ℤ) ∣ r - a then 0
          else PowerSeries.C (d r / p) * poleSeries (((r - a : ℤ) : ℚ) / p))
      = ∑ r ∈ den.filter (fun r => ¬ (p : ℤ) ∣ r - a),
          ((C c * (C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
            (C (a : ℚ) + C (p : ℚ) * X)) : ℚ[X]) : PowerSeries ℚ) := by
    rw [Finset.sum_filter, ← Finset.sum_subset hsupp]
    · refine Finset.sum_congr rfl fun r hr => ?_
      by_cases hq : (p : ℤ) ∣ r - a
      · rw [if_pos hq, if_neg (not_not.mpr hq), mul_zero]
      · rw [if_neg hq, if_pos hq, hpole r (hsupp hr) hq]
    · intro r _ hrs
      rw [Finsupp.notMem_support_iff.mp hrs]
      simp
  have hnum : (pfNum P d den).comp (C (a : ℚ) + C (p : ℚ) * X)
      = P.comp (C (a : ℚ) + C (p : ℚ) * X)
          * (∏ j ∈ den, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X)
        + ∑ r ∈ den, C (d r)
          * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X) := by
    rw [pfNum, add_comp, mul_comp, finset_sum_comp']
    simp only [mul_comp, C_comp]
  have hsplit := Finset.sum_filter_add_sum_filter_not den (fun r => (p : ℤ) ∣ r - a)
    (fun r => C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X))
  have hpoly : C c * (∏ j ∈ den, (X - C (j : ℚ))).comp (C (a : ℚ) + C (p : ℚ) * X)
        * P.comp (C (a : ℚ) + C (p : ℚ) * X)
      + ∑ r ∈ den.filter (fun r => ¬ (p : ℤ) ∣ r - a),
          C c * (C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
            (C (a : ℚ) + C (p : ℚ) * X))
      = C c * ((pfNum P d den).comp (C (a : ℚ) + C (p : ℚ) * X)
          - ∑ r ∈ den.filter (fun r => (p : ℤ) ∣ r - a),
              C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
                (C (a : ℚ) + C (p : ℚ) * X)) := by
    rw [hnum, ← hsplit, ← Finset.mul_sum]
    ring
  rw [substAnalytic, mul_add, Finset.mul_sum, hsum, ← hpoly]
  simp only [Polynomial.coe_add, Polynomial.coe_mul, coe_finset_sum']

/-- Coefficient bounds for `rPoly`: all in `p^{t - n} ℤ_p`, and in `p^{t - n + 1} ℤ_p` above
degree `max(n, t - 1)`. -/
theorem norm_coeff_rPoly_le (P : ℚ[X]) (d : ℤ →₀ ℚ) {den : Finset ℤ} {a n : ℕ}
    (hN : ClassDeg p a n (pfNum P d den))
    (hinc : ∀ r ∈ den, ∀ j ∈ den, r ≠ j → (p : ℤ) ∣ r - a → (p : ℤ) ∣ j - a →
      ¬ (p : ℤ) ^ 2 ∣ r - j) (k : ℕ) :
    ‖(((rPoly p a P d den).coeff k : ℚ) : ℚ_[p])‖
        ≤ (p : ℝ) ^ (((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - n) ∧
      (max n ((den.filter fun r => (p : ℤ) ∣ r - a).card - 1) < k →
        ‖(((rPoly p a P d den).coeff k : ℚ) : ℚ_[p])‖
          ≤ (p : ℝ) ^ (((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - n - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hnn : ∀ e : ℤ, (0 : ℝ) ≤ (p : ℝ) ^ e := fun e => zpow_nonneg (Nat.cast_nonneg p) e
  have hterm : ∀ r ∈ den.filter (fun r => (p : ℤ) ∣ r - a),
      ‖(((C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
          (C (a : ℚ) + C (p : ℚ) * X)).coeff k : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ∧
      ((den.filter fun r => (p : ℤ) ∣ r - a).card - 1 < k →
        ‖(((C (d r) * (∏ j ∈ den.erase r, (X - C (j : ℚ))).comp
          (C (a : ℚ) + C (p : ℚ) * X)).coeff k : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ) - 1)) := by
    intro r hr
    obtain ⟨hrd, hra⟩ := Finset.mem_filter.mp hr
    have hres := norm_residue_le P d hN hrd hra fun j hj hrj hja => hinc r hrd j hj hrj hra hja
    have hcd := classDeg_prod_X_sub_C (p := p) a (den.erase r)
    have hcard : ((den.erase r).filter fun j => (p : ℤ) ∣ j - a).card
        = (den.filter fun r => (p : ℤ) ∣ r - a).card - 1 := by
      rw [Finset.filter_erase, Finset.card_erase_of_mem hr]
    rw [hcard] at hcd
    have ht1 : 1 ≤ (den.filter fun r => (p : ℤ) ∣ r - a).card := Finset.card_pos.mpr ⟨r, hr⟩
    rw [coeff_C_mul, Rat.cast_mul, norm_mul]
    refine ⟨?_, fun hk => ?_⟩
    · calc _ ≤ (p : ℝ) ^ (((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - 1 - n)
            * (p : ℝ) ^ (-(((den.filter fun r => (p : ℤ) ∣ r - a).card - 1 : ℕ) : ℤ)) :=
            mul_le_mul hres (hcd k).1 (norm_nonneg _) (hnn _)
        _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast [ht1]; ring
    · calc _ ≤ (p : ℝ) ^ (((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - 1 - n)
            * (p : ℝ) ^ (-(((den.filter fun r => (p : ℤ) ∣ r - a).card - 1 : ℕ) : ℤ) - 1) :=
            mul_le_mul hres ((hcd k).2 hk) (norm_nonneg _) (hnn _)
        _ = _ := by rw [← zpow_add₀ hp0]; congr 1; push_cast [ht1]; ring
  have hsub : ∀ {x y : ℚ_[p]} {B : ℝ}, ‖x‖ ≤ B → ‖y‖ ≤ B → ‖x - y‖ ≤ B := fun hx hy => by
    rw [sub_eq_add_neg]
    exact (Padic.nonarchimedean _ _).trans (max_le hx (by rwa [norm_neg]))
  rw [rPoly, coeff_C_mul, coeff_sub, finsetSum_coeff, Rat.cast_mul, norm_mul, norm_inv_p_pow,
    Rat.cast_sub, Rat.cast_sum]
  refine ⟨?_, fun hk => ?_⟩
  · calc _ ≤ (p : ℝ) ^ ((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) * (p : ℝ) ^ (-(n : ℤ)) :=
          mul_le_mul_of_nonneg_left (hsub (hN k).1
            (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hnn _)
              fun r hr => (hterm r hr).1)) (hnn _)
      _ = _ := by rw [← zpow_add₀ hp0]; congr 1; ring
  · have hkn : n < k := lt_of_le_of_lt (le_max_left _ _) hk
    have hkt : (den.filter fun r => (p : ℤ) ∣ r - a).card - 1 < k :=
      lt_of_le_of_lt (le_max_right _ _) hk
    calc _ ≤ (p : ℝ) ^ ((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ)
          * (p : ℝ) ^ (-(n : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left (hsub ((hN k).2 hkn)
            (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hnn _)
              fun r hr => (hterm r hr).2 hkt)) (hnn _)
      _ = _ := by rw [← zpow_add₀ hp0]; congr 1; ring

/-- `|τ(G)|_p ≤ p^e` for `G ∈ p^e ℤ_p⟦z⟧` whose coefficients above degree `D ≤ p + 4` lie in
`p^{e+1} ℤ_p` (Lemma 3.4: `κ_d ∈ ℤ_p` for `d ≤ p + 4` and `v_p(κ_d) ≥ -1` always). -/
theorem norm_tateTau_le_of_coeff (hp7 : 7 ≤ p) {G : PowerSeries ℚ_[p]} {e : ℤ} {D : ℕ}
    (hD : D ≤ p + 4) (h1 : ∀ j, ‖PowerSeries.coeff j G‖ ≤ (p : ℝ) ^ e)
    (h2 : ∀ j, D < j → ‖PowerSeries.coeff j G‖ ≤ (p : ℝ) ^ (e - 1)) :
    ‖tateTau G‖ ≤ (p : ℝ) ^ e := by
  have hp0 : (p : ℝ) ≠ 0 := prime_cast_pos_real.ne'
  have hnn : ∀ e' : ℤ, (0 : ℝ) ≤ (p : ℝ) ^ e' := fun e' => zpow_nonneg (Nat.cast_nonneg p) e'
  unfold tateTau
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (hnn e) fun j => ?_
  rw [norm_mul]
  by_cases hj : j ≤ p + 4
  · calc _ ≤ (p : ℝ) ^ e * 1 :=
          mul_le_mul (h1 j) (norm_kappa_le_one hp7 hj) (norm_nonneg _) (hnn e)
      _ = _ := mul_one _
  · calc _ ≤ (p : ℝ) ^ (e - 1) * p :=
          mul_le_mul (h2 j (by omega)) (norm_kappa_le hp7 j) (norm_nonneg _) (hnn _)
      _ = _ := by rw [zpow_sub_one₀ hp0, mul_assoc, inv_mul_cancel₀ hp0, mul_one]

theorem norm_coeff_C_sub_distY_le (hp11 : 11 ≤ p) {h : ℚ_[p]} (hh : ‖h‖ ≤ 1) (k : ℕ) :
    ‖(C h - distY p).coeff k‖ ≤ 1 := by
  have hcP : ‖cP p‖ ≤ 1 :=
    (norm_cP_le hp11).trans (pow_le_one₀ (by positivity) inv_prime_lt_one.le)
  have hp7 : ‖(p : ℚ_[p]) ^ 7‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) inv_prime_lt_one.le
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [distY, coeff_sub, coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add,
        coeff_C_zero, coeff_C_zero, sub_eq_add_neg]
      exact (Padic.nonarchimedean _ _).trans (max_le hh (by rwa [norm_neg]))
    · rw [distY, coeff_sub, coeff_add, coeff_C_mul, coeff_X_one, mul_one,
        coeff_C_of_ne_zero one_ne_zero, coeff_C_of_ne_zero one_ne_zero, add_zero, zero_sub,
        norm_neg]
      exact hp7
  · rw [distY, coeff_sub, coeff_add, coeff_C_mul, coeff_X_of_ne_one (by omega), mul_zero,
      zero_add, coeff_C_of_ne_zero (by omega), coeff_C_of_ne_zero (by omega), sub_zero, norm_zero]
    exact zero_le_one

/-- Coefficients of `τ^ext_Y(f + ∑_s c_s/(z - s))` for `Y = p⁷ X + C_p`, given `τ(f)` and the
principal parts in `p^e ℤ_p` and `d(s) < p`. -/
theorem norm_coeff_tauExt_le (hp11 : 11 ≤ p) {S : Finset ℤ} (hS : ∀ s ∈ S, dIndex s < p)
    {f : PowerSeries ℚ_[p]} {c : ℤ → ℚ_[p]} {e : ℤ} (hf : ‖tateTau f‖ ≤ (p : ℝ) ^ e)
    (hc : ∀ s ∈ S, ‖c s‖ ≤ (p : ℝ) ^ e) (k : ℕ) :
    ‖(tauExt (distY p) S f c).coeff k‖ ≤ (p : ℝ) ^ e := by
  have he : (0 : ℝ) ≤ (p : ℝ) ^ e := zpow_nonneg (Nat.cast_nonneg p) e
  rw [tauExt, coeff_add, finsetSum_coeff]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · rw [coeff_C]
    split_ifs
    · exact hf
    · rw [norm_zero]; exact he
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he fun s hs => ?_
    rw [coeff_C_mul, norm_mul]
    calc _ ≤ (p : ℝ) ^ e * 1 :=
          mul_le_mul (hc s hs) (norm_coeff_C_sub_distY_le hp11 (norm_H7_le_one (hS s hs)) k)
            (norm_nonneg _) he
      _ = _ := mul_one _

/-- **Class-local residue bound** (the content of (50)-(51)). Let `g = P + ∑_r d_r/(x - r)` have
its simple poles in `den`, and let `t` be the number of poles `r ≡ a (mod p)`. If the numerator
`pfNum P d den` has class degree `n ≤ p + 4` at `a` and the poles `≡ a (mod p)` are pairwise
incongruent modulo `p²` with `d((r - a)/p) < p`, then `τ^ext_Y(g(a + p z)) ∈ p^{n - t} ℤ_p[X]`
for `Y = p⁷ X + C_p` (`distY`), with `g(a + p z)` the element of `B_T` of the distribution
formula. -/
theorem tauExt_subst_norm_le (hp11 : 11 ≤ p) (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) (den : Finset ℤ)
    (hsupp : d.support ⊆ den) {n : ℕ} (hN : ClassDeg p a n (pfNum P d den))
    (hinc : ∀ r ∈ den, ∀ j ∈ den, r ≠ j → (p : ℤ) ∣ r - a → (p : ℤ) ∣ j - a →
      ¬ (p : ℤ) ^ 2 ∣ r - j)
    (hd : ∀ r ∈ den, (p : ℤ) ∣ r - a → dIndex ((r - a) / p) < p) (hdeg : n ≤ p + 4)
    (k : ℕ) :
    ‖(tauExt (distY p) (substPoles p a d)
        (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
        (fun s => (substPrincipal p a d s : ℚ_[p]))).coeff k‖
      ≤ (p : ℝ) ^ (-((n : ℤ) - (den.filter fun r => (p : ℤ) ∣ r - a).card)) := by
  have hp7 : 7 ≤ p := by omega
  have hexp : -((n : ℤ) - (den.filter fun r => (p : ℤ) ∣ r - a).card)
      = ((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - n := by ring
  rw [hexp]
  have hres := substAnalytic_isRestricted (p := p) a P d
  have hidp : (((wPoly p a den).map (Rat.castHom ℚ_[p]) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])
      * PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d)
      = (((rPoly p a P d den).map (Rat.castHom ℚ_[p]) : Polynomial ℚ_[p])
          : PowerSeries ℚ_[p]) := by
    rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul,
      W_mul_substAnalytic a P d hsupp]
  have hcW : ∀ i, ((wPoly p a den).map (Rat.castHom ℚ_[p])).coeff i
      = (((wPoly p a den).coeff i : ℚ) : ℚ_[p]) := fun i => by
    rw [coeff_map, Rat.coe_castHom]
  have hcR : ∀ k, PowerSeries.coeff k
      ((((wPoly p a den).map (Rat.castHom ℚ_[p]) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])
        * PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
      = (((rPoly p a P d den).coeff k : ℚ) : ℚ_[p]) := fun k => by
    rw [hidp, Polynomial.coeff_coe, coeff_map, Rat.coe_castHom]
  obtain ⟨hb1, hb2⟩ := top_coeff_bound (t := (den.filter fun r => (p : ℤ) ∣ r - a).card)
    (D := n + (den.filter fun r => (p : ℤ) ∣ r - a).card)
    (e := ((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - n) hres
    (by rw [hcW]; exact (norm_coeff_wPoly a den _).2.2 rfl)
    (fun i => by rw [hcW]; exact (norm_coeff_wPoly a den i).1)
    (fun i hi => by rw [hcW]; exact (norm_coeff_wPoly a den i).2.1 hi)
    (fun k => by rw [hcR]; exact (norm_coeff_rPoly_le P d hN hinc k).1)
    (fun k hk => by
      rw [hcR]
      exact (norm_coeff_rPoly_le P d hN hinc k).2 (max_lt (by omega) (by omega)))
  have htau : ‖tateTau (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))‖
      ≤ (p : ℝ) ^ (((den.filter fun r => (p : ℤ) ∣ r - a).card : ℤ) - n) :=
    norm_tateTau_le_of_coeff hp7 hdeg hb1 fun j hj => hb2 j (by omega)
  refine norm_coeff_tauExt_le hp11 ?_ htau ?_ k
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hrs, hra⟩ := Finset.mem_filter.mp hr
    exact hd r (hsupp hrs) hra
  · intro s hs
    exact norm_substPrincipal_le P d hsupp hN hinc hs

end ClassLocal

end ZetaSeven
