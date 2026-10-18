import ZetaSeven.MatrixDet
import ZetaSeven.DistributionFormula

/-!
# Inner range estimate (paper Section 4.1, Proposition 4.4, equations (42)-(51))

Prince Anand, "Zeta 7 is Irrational", Section 4.1. Fix `M ≥ 40`, `K = 40n ≥ 200 M²` and a
prime `p` with `K/M < p ≤ K/3` (hypothesis (44), `InnerRange`).

## Main results

* The statement data (42)-(49): `mHalf`, `mN`, `mK`, the class counts `ell` (43), the dimension
  allocation `L0`, `bA`, `allocT`, `allocE`, `allocZ`, `allocL` (Definition 4.1, (45)), the
  extra rows `ExtraRows` (classes ordered by decreasing `ℓ_K`, ties broken arbitrarily; such a
  choice exists, `exists_extraRows`), the `E`-basis `eBasis` (Definition 4.2, (46)), the
  half-weights `weight2` (doubled, (47)-(48)) and the exponent `gammaIn` (49).
* Definition 4.1: `L_a ≥ 1` (`bA_lt_allocT`) and (45) (`alloc_eq`); the allocation fills
  `R[t]_{<h}` (`card_eIdx`, `eBasis_natDegree_lt`).
* Definition 4.2: the `E`-basis is `ℤ_p`-unimodular (`eBasis_unimodular`).
* **Proposition 4.4** (`inner_estimate`): every nonzero coefficient of `Δ_K(X)` has `p`-adic
  valuation at least `γ^in_p`, for every admissible choice of extra rows.

## The class-local residue bound

The proof of Proposition 4.4 applies the distribution formula (Lemma 3.7) to each entry of the
Gram matrix in the `E`-basis and bounds every residue-class term `τ^ext_Y(g(a + p z))`
separately; the paper defers this step ((50)-(51)) to the `ζ(5)` predecessor. It is proved here
in general (`tauExt_subst_norm_le`): write `g = P + ∑_{r ∈ den} d_r/(x - r)` and
`Num = P D + ∑_r d_r D/(x - r)` with `D = ∏_{r ∈ den} (x - r)`. If after `x = a + p z` the
numerator has class degree `n ≤ p + 4` (`ClassDeg`: coefficients divisible by `p^n`, and by
`p^{n+1}` above degree `n`) and the `t` poles `r ≡ a (mod p)` are pairwise incongruent modulo
`p²`, then `τ^ext_Y(g(a + p z)) ∈ p^{n-t} ℤ_p[X]`. The analytic part is controlled by the
identity `p^{-t} D(a + p z) · g(a + p z)^{an} = p^{-t}(Num(a + p z) - ∑_{r ≡ a} d_r ⋯)` and a
top-coefficient argument, since `p^{-t} D(a + p z)` is a unit times a monic polynomial of degree
`t` modulo `p`. For the Gram entries `x⁷ (D_N⁷ E_{a,i} E_{b,j})(-x²)` the class degrees and pole
counts give exactly the exponents (50)-(51) (`numDeg_sub`), and the comparison with the
half-weights covers cases (i)-(iv) and the mixed cases with a zero-class row (`comparison`).
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

theorem finset_sum_comp' {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (q : R[X]) :
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
      · rw [ite_eq_left hq, ite_eq_right (not_not.mpr hq), mul_zero]
      · rw [ite_eq_right hq, ite_eq_left hq, hpole r (hsupp hr) hq]
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
      _ = _ := by rw [← zpow_add₀ hp0]; congr 1
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

/-! ## Statement data: equations (42)-(49) -/

section Data

/-- Hypothesis (44) of Section 4.1 together with `M ≥ 40` (Section 4 preamble):
`K = 40n ≥ 200 M²` and `K/M < p ≤ K/3`, written `K < M p` and `3 p ≤ K`. -/
structure InnerRange (n M p : ℕ) : Prop where
  forty_le : 40 ≤ M
  K_ge : 200 * M ^ 2 ≤ K n
  K_lt : K n < M * p
  three_mul_le : 3 * p ≤ K n

/-- (42): `m = (p - 1)/2`. -/
def mHalf (p : ℕ) : ℕ := (p - 1) / 2

/-- (42): `m_N = ⌊N/p⌋`. -/
def mN (n p : ℕ) : ℕ := N n / p

/-- (42): `m_K = ⌊K/p⌋`. -/
def mK (n p : ℕ) : ℕ := K n / p

/-- (43): `ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ a or j ≡ -a (mod p)}`. -/
def ell (p A a : ℕ) : ℕ :=
  ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - a ∨ (p : ℤ) ∣ (j : ℤ) + a).card

/-- Definition 4.1: `L_0 = 6M + 10`. -/
def L0 (M : ℕ) : ℕ := 6 * M + 10

/-- Definition 4.1: `b_a = 4 ℓ_N(a)`. -/
def bA (n p a : ℕ) : ℕ := 4 * ell p (N n) a

/-- The right side of (45): `h - L_0 + 4(N - m_N)` (no truncation under (44)). -/
def allocTotal (n M p : ℕ) : ℕ := hDim n - L0 M + 4 * (N n - mN n p)

/-- (45): `T`, with `m T + E = h - L_0 + 4(N - m_N)` and `0 ≤ E < m`. -/
def allocT (n M p : ℕ) : ℕ := allocTotal n M p / mHalf p

/-- (45): `E`, with `m T + E = h - L_0 + 4(N - m_N)` and `0 ≤ E < m`. -/
def allocE (n M p : ℕ) : ℕ := allocTotal n M p % mHalf p

/-- Definition 4.1: the extra rows `ε`. The paper orders the classes `1 ≤ a ≤ m` by decreasing
`ℓ_K(a)` (ties broken arbitrarily) and sets `ε_a = 1` for the first `E` of them and `ε_a = 0`
otherwise. The functions arising from such an order are exactly those with values in `{0, 1}`
on the classes, with exactly `E` classes of value `1`, and with `ℓ_K(a) ≤ ℓ_K(b)` whenever
`ε_a = 0` and `ε_b = 1`. -/
structure ExtraRows (n M p : ℕ) (ε : ℕ → ℕ) : Prop where
  le_one : ∀ a ∈ Icc 1 (mHalf p), ε a ≤ 1
  card_eq : ((Icc 1 (mHalf p)).filter fun a => ε a = 1).card = allocE n M p
  mono : ∀ a ∈ Icc 1 (mHalf p), ∀ b ∈ Icc 1 (mHalf p), ε a = 0 → ε b = 1 →
    ell p (K n) a ≤ ell p (K n) b

/-- Definition 4.1: `Z_a = T + ε_a`. -/
def allocZ (n M p : ℕ) (ε : ℕ → ℕ) (a : ℕ) : ℕ := allocT n M p + ε a

/-- Definition 4.1: `L_a = T - b_a + ε_a` for `1 ≤ a ≤ m` (no truncation under (44):
`bA_lt_allocZ`), and `L_0 = 6M + 10`. -/
def allocL (n M p : ℕ) (ε : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a = 0 then L0 M else allocZ n M p ε a - bA n p a

/-- Definition 4.2: `E_{a,i}(t) = ∏_{0 ≤ c ≤ m, c ≠ a} (t + c²)^{L_c} · (t + a²)^i`, over any
commutative ring `R`. -/
noncomputable def eBasis (R : Type*) [CommRing R] (n M p : ℕ) (ε : ℕ → ℕ) (a i : ℕ) : R[X] :=
  (∏ c ∈ (range (mHalf p + 1)).erase a, (X + C ((c : R) ^ 2)) ^ allocL n M p ε c)
    * (X + C ((a : R) ^ 2)) ^ i

/-- The index set `{(a, i) : 0 ≤ a ≤ m, 0 ≤ i < L_a}` of the `E`-basis. -/
abbrev eIdx (n M p : ℕ) (ε : ℕ → ℕ) : Type :=
  Σ a : Fin (mHalf p + 1), Fin (allocL n M p ε a)

/-- (47)-(48), doubled to keep them integral: `2 w_{a,i}`. For `1 ≤ a ≤ m`,
`2 w_{a,i} = 2i + 8 ℓ_N(a) - ℓ_K(a) - 6` (47); for `a = 0`,
`2 w_{0,i} = min(4i + 16 m_N - 2 m_K + 1, min_{1 ≤ c ≤ m} (2 Z_c - ℓ_K(c) - 6))` (48). -/
def weight2 (n M p : ℕ) (ε : ℕ → ℕ) (a i : ℕ) : ℤ :=
  if a = 0 then
    (Icc 1 (mHalf p)).fold min (4 * (i : ℤ) + 16 * mN n p - 2 * mK n p + 1)
      fun c => 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6
  else 2 * (i : ℤ) + 8 * ell p (N n) a - ell p (K n) a - 6

/-- (49): `γ^in_p = 2 ∑_{a=0}^m ∑_{i < L_a} w_{a,i}`. -/
def gammaIn (n M p : ℕ) (ε : ℕ → ℕ) : ℤ :=
  ∑ a ∈ range (mHalf p + 1), ∑ i ∈ range (allocL n M p ε a), weight2 n M p ε a i

end Data

/-! ## Class counts and the dimension allocation -/

section Counts

variable {p : ℕ}

/-- `#{1 ≤ j ≤ A : j ≡ v (mod p)} = ⌊(A + 1)/p⌋ + [v < (A + 1) mod p]` for `1 ≤ v < p`. -/
theorem card_filter_dvd_sub (A v : ℕ) (hv1 : 1 ≤ v) (hvp : v < p) :
    ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - v).card
      = (A + 1) / p + if v < (A + 1) % p then 1 else 0 := by
  have hp : 0 < p := by omega
  have h := Nat.count_modEq_card (A + 1) hp v
  rw [Nat.mod_eq_of_lt hvp, Nat.count_eq_card_filter_range] at h
  rw [← h]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.modEq_iff_dvd]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, by rw [dvd_sub_comm]; exact h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨?_, by omega⟩, by rw [dvd_sub_comm]; exact h3⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exfalso
      have h4 : (p : ℤ) ∣ (v : ℤ) := by simpa using h3
      have := Int.le_of_dvd (by omega) h4
      omega
    · exact hj

/-- For an odd prime `p` and `1 ≤ c ≤ m`, `ℓ_A(c)` splits over the residues `c` and `p - c`. -/
theorem ell_eq_add (hp : 2 * mHalf p + 1 = p) (A c : ℕ) (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ell p A c = ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c).card
      + ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - (p - c : ℕ)).card := by
  have hplus : ∀ j : ℕ, (p : ℤ) ∣ (j : ℤ) + c ↔ (p : ℤ) ∣ (j : ℤ) - (p - c : ℕ) := fun j => by
    have h : (j : ℤ) + c = (j : ℤ) - (p - c : ℕ) + p := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [h, dvd_add_left (dvd_refl _)]
  rw [ell, ← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, hplus j]
    tauto
  · rw [Finset.disjoint_filter]
    intro j _ h1 h2
    have h3 := dvd_sub h2 h1
    rw [show (j : ℤ) - (p - c : ℕ) - (j - c) = -((p : ℤ) - 2 * c) by
      rw [Nat.cast_sub (by omega)]; ring, dvd_neg] at h3
    have h4 : (p : ℤ) ∣ 2 * c := by
      have := dvd_sub (dvd_refl (p : ℤ)) h3
      rwa [sub_sub_cancel] at this
    have := Int.le_of_dvd (by omega) h4
    omega

/-- The class counts `ℓ_A(c)` for `1 ≤ c ≤ m` in terms of `(A + 1) = q p + s`. -/
theorem ell_eq_count (hp : 2 * mHalf p + 1 = p) (A c : ℕ) (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ell p A c = 2 * ((A + 1) / p) + (if c < (A + 1) % p then 1 else 0)
      + (if p - c < (A + 1) % p then 1 else 0) := by
  rw [ell_eq_add hp A c hc1 hcm, card_filter_dvd_sub A c hc1 (by omega),
    card_filter_dvd_sub A (p - c) (by omega) (by omega)]
  ring

/-- In the inner range the class counts `ℓ_A(a)`, `1 ≤ a ≤ m`, differ by at most one. -/
theorem ell_le_ell_add_one (hp : 2 * mHalf p + 1 = p) (A : ℕ) {a b : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) (hb1 : 1 ≤ b) (hbm : b ≤ mHalf p) : ell p A a ≤ ell p A b + 1 := by
  have hs : (A + 1) % p < p := Nat.mod_lt _ (by omega)
  rw [ell_eq_count hp A a ha1 ham, ell_eq_count hp A b hb1 hbm]
  split_ifs <;> omega

/-- `p ℓ_A(c) ≤ 2A + p + 2` for `1 ≤ c ≤ m`. -/
theorem mul_ell_le (hp : 2 * mHalf p + 1 = p) (A c : ℕ) (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    p * ell p A c ≤ 2 * A + p + 2 := by
  have hs : (A + 1) % p < p := Nat.mod_lt _ (by omega)
  have hdm := Nat.div_add_mod (A + 1) p
  rw [ell_eq_count hp A c hc1 hcm]
  set q := (A + 1) / p
  set s := (A + 1) % p
  split_ifs <;> first | omega | nlinarith |
    (have hs2 : mHalf p + 2 ≤ s := (by omega); nlinarith)

end Counts

section Alloc

variable {n M p : ℕ} {ε : ℕ → ℕ}

theorem int_eq_zero_of_dvd_of_lt {q : ℕ} {x : ℤ} (h : (q : ℤ) ∣ x) (h1 : -(q : ℤ) < x)
    (h2 : x < q) : x = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k = 0 := by
    by_contra hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · nlinarith
    · nlinarith
  rw [hk, mul_zero]

/-- Every `j ∈ [1, A]` prime to `p` lies in exactly one class `±a`, `1 ≤ a ≤ m`, so
`∑_{a=1}^m ℓ_A(a) = A - ⌊A/p⌋`. -/
theorem sum_ell (hp : 2 * mHalf p + 1 = p) (A : ℕ) :
    ∑ a ∈ Icc 1 (mHalf p), ell p A a = A - A / p := by
  have hp0 : 0 < p := by omega
  have h1 : ∑ a ∈ Icc 1 (mHalf p), ell p A a
      = ∑ j ∈ Icc 1 A, ((Icc 1 (mHalf p)).filter
          fun a : ℕ => (p : ℤ) ∣ (j : ℤ) - a ∨ (p : ℤ) ∣ (j : ℤ) + a).card := by
    simp only [ell, Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∀ j ∈ Icc 1 A, ((Icc 1 (mHalf p)).filter
      fun a : ℕ => (p : ℤ) ∣ (j : ℤ) - a ∨ (p : ℤ) ∣ (j : ℤ) + a).card
        = if p ∣ j then 0 else 1 := by
    intro j _
    have hjr : (p : ℤ) ∣ (j : ℤ) - (j % p : ℕ) := by
      have h := Nat.div_add_mod j p
      refine ⟨(j / p : ℕ), ?_⟩
      have h' : (j : ℤ) = p * (j / p : ℕ) + (j % p : ℕ) := by exact_mod_cast h.symm
      rw [h']; ring
    have hrp : j % p < p := Nat.mod_lt _ hp0
    split_ifs with hpj
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha h
      obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
      have hpj' : (p : ℤ) ∣ (j : ℤ) := Int.natCast_dvd_natCast.mpr hpj
      have hpa : (p : ℤ) ∣ (a : ℤ) := by
        rcases h with h | h
        · have h' := dvd_sub hpj' h
          rwa [sub_sub_cancel] at h'
        · have h' := dvd_sub h hpj'
          rwa [add_sub_cancel_left] at h'
      have := Int.le_of_dvd (by omega) hpa
      omega
    · have hr0 : 0 < j % p := Nat.pos_of_ne_zero fun h => hpj (Nat.dvd_of_mod_eq_zero h)
      rw [Finset.card_eq_one]
      by_cases hrm : j % p ≤ mHalf p
      · refine ⟨j % p, ?_⟩
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨ha1, ham⟩, h⟩
          rcases h with h | h
          · have h' := dvd_sub hjr h
            have h0 := int_eq_zero_of_dvd_of_lt (q := p)
              (x := (a : ℤ) - (j % p : ℕ)) (by rw [show (a : ℤ) - (j % p : ℕ)
                = (j - (j % p : ℕ)) - (j - a) by ring]; exact h') (by omega) (by omega)
            omega
          · have h' := dvd_sub h hjr
            have h0 := int_eq_zero_of_dvd_of_lt (q := p)
              (x := (a : ℤ) + (j % p : ℕ)) (by rw [show (a : ℤ) + (j % p : ℕ)
                = (j + a) - (j - (j % p : ℕ)) by ring]; exact h') (by omega) (by omega)
            omega
        · rintro rfl
          exact ⟨⟨hr0, hrm⟩, Or.inl hjr⟩
      · refine ⟨p - j % p, ?_⟩
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨ha1, ham⟩, h⟩
          rcases h with h | h
          · have h' := dvd_sub hjr h
            have h0 := int_eq_zero_of_dvd_of_lt (q := p)
              (x := (a : ℤ) - (j % p : ℕ)) (by rw [show (a : ℤ) - (j % p : ℕ)
                = (j - (j % p : ℕ)) - (j - a) by ring]; exact h') (by omega) (by omega)
            omega
          · have h' := dvd_sub h hjr
            have h0 := int_eq_zero_of_dvd_of_lt (q := p)
              (x := (a : ℤ) + (j % p : ℕ) - p) (by
                rw [show (a : ℤ) + (j % p : ℕ) - p = (j + a) - (j - (j % p : ℕ)) - p by ring]
                exact dvd_sub h' (dvd_refl _)) (by omega) (by omega)
            omega
        · rintro rfl
          refine ⟨⟨by omega, by omega⟩, Or.inr ?_⟩
          have h' := dvd_add hjr (dvd_refl (p : ℤ))
          rwa [show (j : ℤ) - (j % p : ℕ) + p = j + (p - j % p : ℕ) by
            rw [Nat.cast_sub hrp.le]; ring] at h'
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, smul_eq_mul, mul_one]
  have hc := Finset.card_filter_add_card_filter_not (s := Icc 1 A) (fun j => p ∣ j)
  have hdiv : ((Icc 1 A).filter fun j => p ∣ j).card = A / p := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div A p, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  rw [Nat.card_Icc] at hc
  omega

theorem InnerRange.M_pos (hR : InnerRange n M p) : 0 < M := by
  have := hR.forty_le
  omega

theorem InnerRange.p_gt (hR : InnerRange n M p) : 200 * M < p := by
  have h1 : M * (200 * M) < M * p :=
    calc M * (200 * M) = 200 * M ^ 2 := by ring
      _ ≤ K n := hR.K_ge
      _ < M * p := hR.K_lt
  exact Nat.lt_of_mul_lt_mul_left h1

theorem InnerRange.n_ge (hR : InnerRange n M p) : 5 * M ^ 2 ≤ n := by
  have := hR.K_ge
  simp only [K] at this
  linarith

theorem InnerRange.M_le_sq (hR : InnerRange n M p) : 40 * M ≤ M ^ 2 := by
  have := hR.forty_le
  nlinarith

theorem InnerRange.two_mul_mHalf (hR : InnerRange n M p) [hp : Fact p.Prime] :
    2 * mHalf p + 1 = p := by
  have h1 := hR.p_gt
  have h2 := hR.forty_le
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · unfold mHalf
    omega

theorem InnerRange.mK_lt (hR : InnerRange n M p) [Fact p.Prime] : mK n p < M := by
  unfold mK
  rw [Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos]
  exact hR.K_lt

theorem mN_le_mK (n p : ℕ) : mN n p ≤ mK n p :=
  Nat.div_le_div_right (by unfold N K; omega)

theorem InnerRange.L0_le (hR : InnerRange n M p) : L0 M ≤ hDim n := by
  have h1 := hR.n_ge
  have h2 := hR.M_le_sq
  have h3 := hR.forty_le
  unfold L0 hDim
  nlinarith

theorem InnerRange.allocTotal_eq (hR : InnerRange n M p) :
    allocTotal n M p + L0 M + 4 * mN n p = hDim n + 4 * N n := by
  have h1 := hR.L0_le
  have h2 : mN n p ≤ N n := Nat.div_le_self _ _
  unfold allocTotal
  omega

/-- (45): `m T + E = h - L_0 + 4(N - m_N)` with `0 ≤ E < m`. -/
theorem alloc_eq (hR : InnerRange n M p) [Fact p.Prime] :
    mHalf p * allocT n M p + allocE n M p = hDim n - L0 M + 4 * (N n - mN n p) ∧
      allocE n M p < mHalf p := by
  have hm := hR.two_mul_mHalf
  have hp := hR.p_gt
  have hM := hR.forty_le
  exact ⟨Nat.div_add_mod _ _, Nat.mod_lt _ (by omega)⟩

/-- Definition 4.1: `b_a < T`, so `L_a = T - b_a + ε_a ≥ 1` without truncation. -/
theorem bA_lt_allocT (hR : InnerRange n M p) [Fact p.Prime] {a : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) : bA n p a < allocT n M p := by
  have hm := hR.two_mul_mHalf
  have hp := hR.p_gt
  have hM := hR.forty_le
  have hn := hR.n_ge
  have hMM := hR.M_le_sq
  have h3p := hR.three_mul_le
  have hmK := hR.mK_lt
  have hmN := mN_le_mK n p
  have htot := hR.allocTotal_eq
  have hm0 : 0 < mHalf p := by omega
  have hQlt : allocTotal n M p < mHalf p * (allocTotal n M p / mHalf p) + mHalf p := by
    have h := Nat.lt_mul_div_succ (allocTotal n M p) hm0
    rwa [Nat.mul_add, Nat.mul_one] at h
  have hell := mul_ell_le hm (N n) a ha1 ham
  unfold bA allocT
  by_contra hcon
  have hle : allocTotal n M p / mHalf p ≤ 4 * ell p (N n) a := not_lt.mp hcon
  have h5 : p * (allocTotal n M p / mHalf p) ≤ 4 * (p * ell p (N n) a) :=
    calc p * (allocTotal n M p / mHalf p) ≤ p * (4 * ell p (N n) a) := Nat.mul_le_mul_left p hle
      _ = 4 * (p * ell p (N n) a) := by ring
  have hpT : p * (allocTotal n M p / mHalf p)
      = 2 * (mHalf p * (allocTotal n M p / mHalf p)) + allocTotal n M p / mHalf p := by
    rw [show 2 * (mHalf p * (allocTotal n M p / mHalf p)) + allocTotal n M p / mHalf p
      = (2 * mHalf p + 1) * (allocTotal n M p / mHalf p) by ring, hm]
  have hNn : N n = 3 * n := rfl
  have hKn : K n = 40 * n := rfl
  have hhn : hDim n = 37 * n := rfl
  have hLM : L0 M = 6 * M + 10 := rfl
  generalize allocTotal n M p / mHalf p = T at *
  generalize ell p (N n) a = l at *
  generalize mN n p = q at *
  generalize mK n p = q' at *
  linarith

/-- `T < 3M`. -/
theorem allocT_lt (hR : InnerRange n M p) [Fact p.Prime] : allocT n M p < 3 * M := by
  have hm := hR.two_mul_mHalf
  have hp := hR.p_gt
  have hM := hR.forty_le
  have hKlt := hR.K_lt
  have htot := hR.allocTotal_eq
  have hdm := Nat.mul_div_le (allocTotal n M p) (mHalf p)
  unfold allocT
  by_contra hcon
  have hle : 3 * M ≤ allocTotal n M p / mHalf p := not_lt.mp hcon
  have h5 : 3 * (mHalf p * M) ≤ mHalf p * (allocTotal n M p / mHalf p) :=
    calc 3 * (mHalf p * M) = mHalf p * (3 * M) := by ring
      _ ≤ mHalf p * (allocTotal n M p / mHalf p) := Nat.mul_le_mul_left _ hle
  have hMp : M * p = 2 * (mHalf p * M) + M := by
    rw [show 2 * (mHalf p * M) + M = M * (2 * mHalf p + 1) by ring, hm]
  have hmM : 3 * M ≤ mHalf p * M := Nat.mul_le_mul_right M (by omega)
  have hNn : N n = 3 * n := rfl
  have hKn : K n = 40 * n := rfl
  have hhn : hDim n = 37 * n := rfl
  have hLM : L0 M = 6 * M + 10 := rfl
  generalize allocTotal n M p / mHalf p = T at *
  generalize mN n p = q at *
  linarith

/-- `∑_{a=1}^m ε_a = E`. -/
theorem sum_eps (hε : ExtraRows n M p ε) : ∑ a ∈ Icc 1 (mHalf p), ε a = allocE n M p := by
  rw [← hε.card_eq, Finset.card_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  have := hε.le_one a ha
  split_ifs with h
  · exact h
  · omega

/-- The dimension count: `∑_{a=0}^m L_a = h`. -/
theorem sum_allocL (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε) :
    ∑ a ∈ range (mHalf p + 1), allocL n M p ε a = hDim n := by
  have hm := hR.two_mul_mHalf
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < mHalf p + 1),
    Finset.Ico_add_one_right_eq_Icc]
  have hL : ∀ a ∈ Icc 1 (mHalf p), allocL n M p ε a = allocZ n M p ε a - bA n p a := by
    intro a ha
    rw [allocL, ite_eq_right (by have := (Finset.mem_Icc.mp ha).1; omega)]
  have hL0 : allocL n M p ε 0 = L0 M := by rw [allocL, ite_eq_left rfl]
  rw [Finset.sum_congr rfl hL, Finset.sum_tsub_distrib _ fun a ha => by
    have h := bA_lt_allocT hR (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
    unfold allocZ; omega]
  rw [hL0]
  simp only [allocZ, bA, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
    ← Finset.mul_sum, sum_eps hε, sum_ell hm, Nat.add_sub_cancel]
  have htot := hR.allocTotal_eq
  have hdm := Nat.div_add_mod (allocTotal n M p) (mHalf p)
  have hL0le := hR.L0_le
  have h2 : N n / p ≤ N n := Nat.div_le_self _ _
  unfold allocT allocE
  unfold mN at htot
  generalize allocTotal n M p / mHalf p = T at *
  generalize allocTotal n M p % mHalf p = r at *
  generalize N n / p = q at *
  generalize allocTotal n M p = Q at *
  omega

end Alloc

/-! ## The `E`-basis is unimodular (Definition 4.2) -/

section Unimodular

variable {n M p : ℕ} {ε : ℕ → ℕ}

theorem eBasis_map (R : Type*) [CommRing R] (n M p : ℕ) (ε : ℕ → ℕ) (a i : ℕ) :
    (eBasis ℤ n M p ε a i).map (Int.castRingHom R) = eBasis R n M p ε a i := by
  simp only [eBasis, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_X, map_pow, map_natCast, Polynomial.map_natCast]

/-- The `E`-basis lies in `R[t]_{<h}`. -/
theorem eBasis_natDegree_lt (R : Type*) [CommRing R] [Nontrivial R] (hR : InnerRange n M p)
    [Fact p.Prime] (hε : ExtraRows n M p ε) (ρ : eIdx n M p ε) :
    (eBasis R n M p ε ρ.1 ρ.2).natDegree < hDim n := by
  have hsum := sum_allocL hR hε
  have hmem : (ρ.1 : ℕ) ∈ range (mHalf p + 1) := Finset.mem_range.mpr ρ.1.isLt
  rw [← Finset.add_sum_erase _ _ hmem] at hsum
  have hi : (ρ.2 : ℕ) < allocL n M p ε ρ.1 := ρ.2.isLt
  calc (eBasis R n M p ε ρ.1 ρ.2).natDegree
      ≤ (∑ c ∈ (range (mHalf p + 1)).erase ρ.1, allocL n M p ε c) + ρ.2 := by
        unfold eBasis
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          refine natDegree_pow_le.trans ?_
          rw [natDegree_X_add_C, mul_one]
        · refine natDegree_pow_le.trans ?_
          rw [natDegree_X_add_C, mul_one]
    _ < hDim n := by omega

/-- The squares `c²`, `0 ≤ c ≤ m`, are distinct modulo `p`. -/
theorem natCast_sq_ne (hR : InnerRange n M p) [Fact p.Prime] {a c : ℕ} (ha : a ≤ mHalf p)
    (hc : c ≤ mHalf p) (hac : c ≠ a) : ((c : ZMod p) ^ 2) ≠ (a : ZMod p) ^ 2 := by
  have hm := hR.two_mul_mHalf
  intro h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h'
    exact hac h'
  · have h2 : ((c + a : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add, h', neg_add_cancel]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega

theorem isCoprime_X_add_C_sq (hR : InnerRange n M p) [Fact p.Prime] {a c : ℕ}
    (ha : a ≤ mHalf p) (hc : c ≤ mHalf p) (hac : c ≠ a) :
    IsCoprime (X + C ((a : ZMod p) ^ 2)) (X + C ((c : ZMod p) ^ 2)) := by
  rw [← sub_neg_eq_add, ← sub_neg_eq_add X, ← C_neg, ← C_neg]
  apply isCoprime_X_sub_C_of_isUnit_sub
  rw [sub_eq_add_neg, neg_neg]
  exact isUnit_iff_ne_zero.mpr fun h => natCast_sq_ne hR ha hc hac (by linear_combination h)

/-- Definition 4.2: modulo `p` the `E`-basis is linearly independent (the Chinese remainder
decomposition by the pairwise coprime powers of `t + c²`). -/
theorem eBasis_linearIndependent (hR : InnerRange n M p) [Fact p.Prime] :
    LinearIndependent (ZMod p) fun ρ : eIdx n M p ε => eBasis (ZMod p) n M p ε ρ.1 ρ.2 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg ρ0
  obtain ⟨a0, i0⟩ := ρ0
  rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at hg
  dsimp only at hg
  have hdvd : (X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ allocL n M p ε a0 ∣
      ∑ a ∈ Finset.univ.erase a0, ∑ i : Fin (allocL n M p ε a),
        g ⟨a, i⟩ • eBasis (ZMod p) n M p ε a i := by
    refine Finset.dvd_sum fun a ha => Finset.dvd_sum fun i _ => ?_
    rw [Polynomial.smul_eq_C_mul]
    refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem
      (fun c : ℕ => (X + C ((c : ZMod p) ^ 2)) ^ allocL n M p ε c) ?_) _) _
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h.symm),
      Finset.mem_range.mpr a0.isLt⟩
  have hsplit : ∑ i : Fin (allocL n M p ε a0), g ⟨a0, i⟩ • eBasis (ZMod p) n M p ε a0 i
      = (∏ c ∈ (range (mHalf p + 1)).erase a0,
          (X + C ((c : ZMod p) ^ 2)) ^ allocL n M p ε c)
        * ∑ i : Fin (allocL n M p ε a0),
            g ⟨a0, i⟩ • (X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ (i : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eBasis, mul_smul_comm]
  have hdvd2 : (X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ allocL n M p ε a0 ∣
      (∏ c ∈ (range (mHalf p + 1)).erase a0,
          (X + C ((c : ZMod p) ^ 2)) ^ allocL n M p ε c)
        * ∑ i : Fin (allocL n M p ε a0),
            g ⟨a0, i⟩ • (X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ (i : ℕ) := by
    rw [← hsplit, eq_neg_of_add_eq_zero_left hg]
    exact (dvd_neg).mpr hdvd
  have hcop : IsCoprime ((X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ allocL n M p ε a0)
      (∏ c ∈ (range (mHalf p + 1)).erase a0,
          (X + C ((c : ZMod p) ^ 2)) ^ allocL n M p ε c) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun c hc => IsCoprime.pow_right ?_)
    obtain ⟨hca, hcr⟩ := Finset.mem_erase.mp hc
    exact isCoprime_X_add_C_sq hR (by have := a0.isLt; omega)
      (by have := Finset.mem_range.mp hcr; omega) hca
  have hQdvd := hcop.dvd_of_dvd_mul_left hdvd2
  have hmonic : (X + C (((a0 : ℕ) : ZMod p) ^ 2)).Monic := monic_X_add_C _
  have hL1 : 1 ≤ allocL n M p ε a0 := by have := i0.isLt; omega
  have hQ0 : ∑ i : Fin (allocL n M p ε a0),
      g ⟨a0, i⟩ • (X + C (((a0 : ℕ) : ZMod p) ^ 2)) ^ (i : ℕ) = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hQdvd ?_
    rw [hmonic.natDegree_pow, natDegree_X_add_C, mul_one]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := allocL n M p ε a0 - 1)
      fun i _ => ?_) (by omega)
    refine (natDegree_smul_le _ _).trans (natDegree_pow_le.trans ?_)
    rw [natDegree_X_add_C, mul_one]
    have := i.isLt
    omega
  have hcomp := congrArg
    (fun q : (ZMod p)[X] => (q.comp (X - C (((a0 : ℕ) : ZMod p) ^ 2))).coeff i0) hQ0
  simp only [finset_sum_comp', smul_comp, pow_comp, add_comp, X_comp, C_comp, sub_add_cancel,
    finsetSum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Fin.val_inj, zero_comp, coeff_zero] at hcomp
  rwa [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i0)] at hcomp

/-- The coefficient matrix of the `E`-basis modulo `p` is invertible. -/
theorem eBasis_det_ne_zero (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (e : eIdx n M p ε ≃ Fin (hDim n)) :
    (Matrix.of fun k l : Fin (hDim n) =>
      (eBasis (ZMod p) n M p ε (e.symm k).1 (e.symm k).2).coeff l).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro g hg k
  have hli := Fintype.linearIndependent_iff.mp (eBasis_linearIndependent (ε := ε) hR) (fun ρ => g (e ρ))
  have hzero : ∑ ρ : eIdx n M p ε, g (e ρ) • eBasis (ZMod p) n M p ε ρ.1 ρ.2 = 0 := by
    ext l
    rw [finsetSum_coeff, coeff_zero]
    by_cases hl : l < hDim n
    · have h := congrFun hg ⟨l, hl⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, Matrix.of_apply, smul_eq_mul,
        Pi.zero_apply] at h
      rw [← h, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [coeff_smul, smul_eq_mul, Equiv.symm_apply_apply]
    · refine Finset.sum_eq_zero fun ρ _ => ?_
      rw [coeff_smul, coeff_eq_zero_of_natDegree_lt
        (by have := eBasis_natDegree_lt (ZMod p) hR hε ρ; omega), smul_zero]
  have := hli hzero (e.symm k)
  rwa [Equiv.apply_symm_apply] at this

/-- **Definition 4.2** (`ℤ_p`-unimodularity of the `E`-basis). For every enumeration `e` of the
index set `{(a, i)}` (of size `h`, `card_eIdx`), the integer matrix of coefficients of the
`E_{a,i}` in the monomial basis `1, t, …, t^{h-1}` has determinant prime to `p`. -/
theorem eBasis_unimodular (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (e : eIdx n M p ε ≃ Fin (hDim n)) :
    ¬ (p : ℤ) ∣ (Matrix.of fun k l : Fin (hDim n) =>
      (eBasis ℤ n M p ε (e.symm k).1 (e.symm k).2).coeff l).det := by
  intro hdvd
  apply eBasis_det_ne_zero hR hε e
  have hmap : (Int.castRingHom (ZMod p)).mapMatrix (Matrix.of fun k l : Fin (hDim n) =>
      (eBasis ℤ n M p ε (e.symm k).1 (e.symm k).2).coeff l)
      = Matrix.of fun k l : Fin (hDim n) =>
        (eBasis (ZMod p) n M p ε (e.symm k).1 (e.symm k).2).coeff l := by
    ext k l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [← eBasis_map (ZMod p), coeff_map]
  rw [← hmap, ← RingHom.map_det, eq_intCast, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd]

/-- The `E`-basis has `h` elements. -/
theorem card_eIdx (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε) :
    Fintype.card (eIdx n M p ε) = hDim n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun a => allocL n M p ε a) (mHalf p + 1)]
  exact sum_allocL hR hε

end Unimodular

/-! ## The Gram matrix in the `E`-basis -/

section Gram

variable {n M p : ℕ} {ε : ℕ → ℕ}

/-- `μ_X(Q/D_tail)` for a polynomial `Q`, computed as in `ZetaSeven.Gentry`: polynomial part
`Q div D_tail` and simple-pole residues `Q(-a²)/D_tail'(-a²)` at `N < a ≤ K`. The entries of
`G_K` are `Gentry n i j = muTail n (D_N⁷ t^{i+j})`, and in the `E`-basis the Gram entries are
`muTail n (D_N⁷ E_{a,i} E_{b,j})`. -/
noncomputable def muTail (n : ℕ) (Q : ℚ[X]) : ℚ[X] :=
  muFunctional (Q.div (Dtail n))
    (∑ a ∈ Icc (N n + 1) (K n), Finsupp.single a
      (Q.eval (-(a : ℚ) ^ 2) / (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)))

theorem Gentry_eq_muTail (n i j : ℕ) : Gentry n i j = muTail n (Rnum n i j) := rfl

theorem Dtail_monic (n : ℕ) : (Dtail n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem div_Dtail (n : ℕ) (Q : ℚ[X]) : Q.div (Dtail n) = Q /ₘ Dtail n :=
  (divByMonic_eq_div Q (Dtail_monic n)).symm

theorem muFunctional_add (P₁ P₂ : ℚ[X]) (c₁ c₂ : ℕ →₀ ℚ) :
    muFunctional (P₁ + P₂) (c₁ + c₂) = muFunctional P₁ c₁ + muFunctional P₂ c₂ := by
  unfold muFunctional
  rw [Polynomial.sum_add_index _ _ _ (fun i => by simp) (fun a b₁ b₂ => by rw [C_add, add_mul]),
    Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by rw [C_add, add_mul])]
  ring

theorem muFunctional_smul (r : ℚ) (P : ℚ[X]) (c : ℕ →₀ ℚ) :
    muFunctional (r • P) (r • c) = C r * muFunctional P c := by
  unfold muFunctional
  rw [Polynomial.sum_smul_index _ _ _ (fun i => by simp),
    Finsupp.sum_smul_index' (fun i => by simp)]
  simp only [Polynomial.sum_def, Finsupp.sum, mul_add, Finset.mul_sum, smul_eq_mul, C_mul,
    mul_assoc]

theorem muTail_add (n : ℕ) (Q₁ Q₂ : ℚ[X]) : muTail n (Q₁ + Q₂) = muTail n Q₁ + muTail n Q₂ := by
  unfold muTail
  rw [← muFunctional_add]
  congr 1
  · rw [div_Dtail, div_Dtail, div_Dtail, add_divByMonic]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finsupp.single_add, eval_add, add_div]

theorem muTail_smul (n : ℕ) (r : ℚ) (Q : ℚ[X]) : muTail n (r • Q) = C r * muTail n Q := by
  unfold muTail
  rw [← muFunctional_smul]
  congr 1
  · rw [div_Dtail, div_Dtail, smul_divByMonic]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.smul_single, eval_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc]

/-- `muTail n` is `ℚ`-linear. -/
noncomputable def muTailLin (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := muTail n
  map_add' := muTail_add n
  map_smul' r Q := by rw [muTail_smul, RingHom.id_apply, smul_eq_C_mul]

theorem eBasis_eq_sum (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (ρ : eIdx n M p ε) :
    eBasis ℚ n M p ε ρ.1 ρ.2
      = ∑ i : Fin (hDim n), C ((eBasis ℚ n M p ε ρ.1 ρ.2).coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' _ (eBasis_natDegree_lt ℚ hR hε ρ)]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => C ((eBasis ℚ n M p ε ρ.1 ρ.2).coeff i) * X ^ i)]

/-- The Gram entries in the `E`-basis are the bilinear combinations of the entries of `G_K`. -/
theorem gram_entry (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (ρ σ : eIdx n M p ε) :
    muTail n (Dpoly (N n) ^ 7 * eBasis ℚ n M p ε ρ.1 ρ.2 * eBasis ℚ n M p ε σ.1 σ.2)
      = ∑ i : Fin (hDim n), ∑ j : Fin (hDim n),
          C ((eBasis ℚ n M p ε ρ.1 ρ.2).coeff i * (eBasis ℚ n M p ε σ.1 σ.2).coeff j)
            * Gentry n i j := by
  have h : Dpoly (N n) ^ 7 * eBasis ℚ n M p ε ρ.1 ρ.2 * eBasis ℚ n M p ε σ.1 σ.2
      = ∑ i : Fin (hDim n), ∑ j : Fin (hDim n),
          ((eBasis ℚ n M p ε ρ.1 ρ.2).coeff i * (eBasis ℚ n M p ε σ.1 σ.2).coeff j)
            • Rnum n i j := by
    conv_lhs => rw [eBasis_eq_sum hR hε ρ, eBasis_eq_sum hR hε σ, mul_assoc,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, Rnum, C_mul, pow_add]
    ring
  rw [h]
  change muTailLin n _ = _
  simp only [map_sum, map_smul]
  simp only [smul_eq_C_mul]
  rfl

/-- The `E`-basis coefficient matrix (over `ℚ`, as constant polynomials). -/
noncomputable def eMat (n M p : ℕ) (ε : ℕ → ℕ) (e : eIdx n M p ε ≃ Fin (hDim n)) :
    Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun k i => (eBasis ℚ n M p ε (e.symm k).1 (e.symm k).2).coeff i

/-- Change of basis: the Gram matrix in the `E`-basis is `C G_K Cᵀ`. -/
theorem gram_matrix (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (e : eIdx n M p ε ≃ Fin (hDim n)) :
    (Matrix.of fun k l : Fin (hDim n) => muTail n (Dpoly (N n) ^ 7
        * eBasis ℚ n M p ε (e.symm k).1 (e.symm k).2 * eBasis ℚ n M p ε (e.symm l).1 (e.symm l).2))
      = (eMat n M p ε e).map C * Gmat n * Matrix.transpose ((eMat n M p ε e).map C) := by
  refine Matrix.ext fun k l => ?_
  rw [Matrix.of_apply, gram_entry hR hε, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, eMat, Matrix.of_apply,
    Gmat, Finset.sum_mul]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [C_mul]
  ring

/-- `det(C G_K Cᵀ) = det(C)² Δ_K`. -/
theorem det_gram (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (e : eIdx n M p ε ≃ Fin (hDim n)) :
    (Matrix.of fun k l : Fin (hDim n) => muTail n (Dpoly (N n) ^ 7
        * eBasis ℚ n M p ε (e.symm k).1 (e.symm k).2
        * eBasis ℚ n M p ε (e.symm l).1 (e.symm l).2)).det
      = C ((eMat n M p ε e).det ^ 2) * DeltaK n := by
  have hC : ((eMat n M p ε e).map C).det = C (eMat n M p ε e).det :=
    (RingHom.map_det C (eMat n M p ε e)).symm
  rw [gram_matrix hR hε e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, DeltaK, hC,
    C_pow]
  ring

/-- `det C` is a `p`-adic unit (Definition 4.2). -/
theorem norm_det_eMat (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (e : eIdx n M p ε ≃ Fin (hDim n)) : ‖(((eMat n M p ε e).det : ℚ) : ℚ_[p])‖ = 1 := by
  have h := eBasis_unimodular hR hε e
  have hmap : eMat n M p ε e = (Int.castRingHom ℚ).mapMatrix (Matrix.of fun k l : Fin (hDim n) =>
      (eBasis ℤ n M p ε (e.symm k).1 (e.symm k).2).coeff l) := by
    ext k l
    simp only [eMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [← eBasis_map ℚ, coeff_map]
  rw [hmap, ← RingHom.map_det, eq_intCast, Rat.cast_intCast]
  exact le_antisymm (Padic.norm_int_le_one _)
    (not_lt.mp fun hlt => h (Padic.norm_intCast_lt_one_iff.mp hlt))

end Gram

/-! ## The pullback numerator `x⁷ Q(-x²)` -/

section Numerator

/-- Partial fractions over a nodal polynomial (as in `ZetaSeven.partialFraction_spec`). -/
theorem lagrange_spec_aux (s : Finset ℕ) (v : ℕ → ℚ) (hinj : Set.InjOn v s) (U : ℚ[X]) :
    U = U /ₘ Lagrange.nodal s v * Lagrange.nodal s v
      + ∑ r ∈ s, C (U.eval (v r) / (derivative (Lagrange.nodal s v)).eval (v r))
          * Lagrange.nodal (s.erase r) v := by
  have hmonic : (Lagrange.nodal s v).Monic := Lagrange.nodal_monic
  have hrem := Lagrange.eq_interpolate hinj
    ((degree_modByMonic_lt U hmonic).trans_eq Lagrange.degree_nodal)
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C] at hrem
  have hsum : ∀ i ∈ s, C (Lagrange.nodalWeight s v i)
        * (Lagrange.nodal s v / (X - C (v i)))
        * C (eval (v i) (U %ₘ Lagrange.nodal s v))
      = C (U.eval (v i) / (derivative (Lagrange.nodal s v)).eval (v i))
          * Lagrange.nodal (s.erase i) v := by
    intro i hi
    rw [← Lagrange.nodal_erase_eq_nodal_div hi, Lagrange.nodalWeight_eq_eval_derivative_nodal hi,
      modByMonic_eq_sub_mul_div, eval_sub, eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul,
      sub_zero, div_eq_mul_inv, C_mul]
    ring
  conv_lhs => rw [← modByMonic_add_div U (Lagrange.nodal s v)]
  rw [hrem, Finset.sum_congr rfl hsum]
  ring

/-- The residues `Q(-a²)/D_tail'(-a²)` of `Q/D_tail`. -/
noncomputable def tailRes (n : ℕ) (Q : ℚ[X]) (a : ℕ) : ℚ :=
  Q.eval (-(a : ℚ) ^ 2) / (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)

/-- The pole coefficients of `Q/D_tail`, supported on `N < a ≤ K`. -/
noncomputable def tailCoeffs (n : ℕ) (Q : ℚ[X]) : ℕ →₀ ℚ :=
  ∑ a ∈ Icc (N n + 1) (K n), Finsupp.single a (tailRes n Q a)

theorem muTail_eq (n : ℕ) (Q : ℚ[X]) :
    muTail n Q = muFunctional (Q.div (Dtail n)) (tailCoeffs n Q) := rfl

theorem Dtail_eq_nodal (n : ℕ) :
    Dtail n = Lagrange.nodal (Icc (N n + 1) (K n)) fun j : ℕ => -((j : ℚ) ^ 2) := by
  unfold Dtail Lagrange.nodal
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [C_neg, sub_neg_eq_add]

/-- Partial fractions over `D_tail` (proof of Lemma 2.3, (11)). -/
theorem muTail_lagrange (n : ℕ) (Q : ℚ[X]) :
    Q = Q.div (Dtail n) * Dtail n + ∑ a ∈ Icc (N n + 1) (K n),
      C (tailRes n Q a) * ∏ j ∈ (Icc (N n + 1) (K n)).erase a, (X + C ((j : ℚ) ^ 2)) := by
  have hinj : Set.InjOn (fun j : ℕ => -((j : ℚ) ^ 2)) (Icc (N n + 1) (K n)) := by
    intro x _ y _ h
    have h' : (x : ℚ) ^ 2 = (y : ℚ) ^ 2 := neg_inj.mp h
    exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg x) (Nat.cast_nonneg y)).mp h'
  have h := lagrange_spec_aux _ _ hinj Q
  have herase : ∀ a, Lagrange.nodal ((Icc (N n + 1) (K n)).erase a)
      (fun j : ℕ => -((j : ℚ) ^ 2)) = ∏ j ∈ (Icc (N n + 1) (K n)).erase a, (X + C ((j : ℚ) ^ 2)) :=
    fun a => by
      unfold Lagrange.nodal
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [C_neg, sub_neg_eq_add]
  rw [← Dtail_eq_nodal] at h
  simp only [herase] at h
  rw [div_Dtail]
  exact h

/-- The poles `±j`, `N < j ≤ K`, of `x⁷ R(-x²)`. -/
noncomputable def denSet (n : ℕ) : Finset ℤ :=
  (Icc (N n + 1) (K n)).image (fun j : ℕ => (j : ℤ))
    ∪ (Icc (N n + 1) (K n)).image (fun j : ℕ => -(j : ℤ))

theorem denSet_disjoint (n : ℕ) :
    Disjoint ((Icc (N n + 1) (K n)).image fun j : ℕ => (j : ℤ))
      ((Icc (N n + 1) (K n)).image fun j : ℕ => -(j : ℤ)) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨j', hj', h⟩ := Finset.mem_image.mp hr'
  have h1 := (Finset.mem_Icc.mp hj).1
  have h2 := (Finset.mem_Icc.mp hj').1
  omega

/-- `∏_{r ∈ den} (x - r) = (-1)^h D_tail(-x²)`. -/
theorem prod_denSet (n : ℕ) :
    ∏ r ∈ denSet n, (X - C (r : ℚ)) = (-1) ^ hDim n * (Dtail n).comp (-X ^ 2) := by
  have hcard : (Icc (N n + 1) (K n)).card = hDim n := by
    rw [Nat.card_Icc]; unfold N K hDim; omega
  rw [denSet, Finset.prod_union (denSet_disjoint n),
    Finset.prod_image (fun x _ y _ h => by exact_mod_cast h),
    Finset.prod_image (fun x _ y _ h => by simpa using h), ← Finset.prod_mul_distrib, Dtail,
    Polynomial.prod_comp, ← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [add_comp, X_comp, C_comp]
  simp only [Int.cast_natCast, Int.cast_neg, C_neg, C_pow]
  ring

/-- Clearing the denominators of `g = P + ∑_r d_r/(x - r)`. -/
theorem algebraMap_pfNum (P : ℚ[X]) (d : ℤ →₀ ℚ) {den : Finset ℤ} (hsupp : d.support ⊆ den) :
    algebraMap ℚ[X] (RatFunc ℚ) (pfNum P d den)
      = algebraMap ℚ[X] (RatFunc ℚ) (∏ r ∈ den, (X - C (r : ℚ))) * tauRatFunc P d := by
  unfold tauRatFunc pfNum
  rw [Finsupp.sum_of_support_subset d hsupp _ (fun r _ => by simp), mul_add, Finset.mul_sum,
    map_add, map_mul, map_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hne : algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _)
    rw [← Finset.mul_prod_erase den (fun j : ℤ => X - C (j : ℚ)) hr, map_mul, map_mul]
    field_simp

/-- `∏_{r ∈ den} (x - r) · x⁷ R(-x²) = (-1)^h x⁷ Q(-x²)` for `R = Q/D_tail`. -/
theorem algebraMap_mul_pullbackRatFunc (n : ℕ) (Q : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) (∏ r ∈ denSet n, (X - C (r : ℚ)))
        * pullbackRatFunc (Q.div (Dtail n)) (tailCoeffs n Q)
      = algebraMap ℚ[X] (RatFunc ℚ) ((-1) ^ hDim n * (X ^ 7 * Q.comp (-X ^ 2))) := by
  have hQ : Q.comp (-X ^ 2) = (Q.div (Dtail n)).comp (-X ^ 2) * (Dtail n).comp (-X ^ 2)
      + ∑ a ∈ Icc (N n + 1) (K n), C (tailRes n Q a)
        * (∏ j ∈ (Icc (N n + 1) (K n)).erase a, (X + C ((j : ℚ) ^ 2))).comp (-X ^ 2) := by
    conv_lhs => rw [muTail_lagrange n Q]
    rw [add_comp, mul_comp, finset_sum_comp']
    simp only [mul_comp, C_comp]
  have hne : ∀ a : ℕ, algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((a : ℚ) ^ 2)) ≠ 0 := by
    intro a
    refine RatFunc.algebraMap_ne_zero fun h => ?_
    have h2 : (-X ^ 2 + C ((a : ℚ) ^ 2) : ℚ[X]).coeff 2 = 0 := by rw [h, coeff_zero]
    rw [coeff_add, coeff_neg, coeff_X_pow, coeff_C] at h2
    norm_num at h2
  have hterm : ∀ a ∈ Icc (N n + 1) (K n),
      algebraMap ℚ[X] (RatFunc ℚ) ((Dtail n).comp (-X ^ 2))
        * (algebraMap ℚ[X] (RatFunc ℚ) (C (tailRes n Q a))
          / algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((a : ℚ) ^ 2)))
      = algebraMap ℚ[X] (RatFunc ℚ) (C (tailRes n Q a)
          * (∏ j ∈ (Icc (N n + 1) (K n)).erase a, (X + C ((j : ℚ) ^ 2))).comp (-X ^ 2)) := by
    intro a ha
    have hL := hne a
    rw [Dtail, ← Finset.mul_prod_erase _ _ ha, mul_comp, add_comp, X_comp, C_comp, map_mul,
      map_mul]
    field_simp
  rw [prod_denSet, hQ]
  unfold pullbackRatFunc tailCoeffs
  rw [← Finsupp.sum_finsetSum_index (fun j => by simp)
    (fun j b₁ b₂ => by rw [C_add, map_add, add_div])]
  simp only [Finsupp.sum_single_index, map_zero, zero_div]
  calc algebraMap ℚ[X] (RatFunc ℚ) ((-1) ^ hDim n * (Dtail n).comp (-X ^ 2))
        * (algebraMap ℚ[X] (RatFunc ℚ) X ^ 7
          * (algebraMap ℚ[X] (RatFunc ℚ) ((Q.div (Dtail n)).comp (-X ^ 2))
            + ∑ a ∈ Icc (N n + 1) (K n), algebraMap ℚ[X] (RatFunc ℚ) (C (tailRes n Q a))
              / algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((a : ℚ) ^ 2))))
      = algebraMap ℚ[X] (RatFunc ℚ) ((-1) ^ hDim n) * algebraMap ℚ[X] (RatFunc ℚ) X ^ 7
          * (algebraMap ℚ[X] (RatFunc ℚ) ((Dtail n).comp (-X ^ 2))
              * algebraMap ℚ[X] (RatFunc ℚ) ((Q.div (Dtail n)).comp (-X ^ 2))
            + ∑ a ∈ Icc (N n + 1) (K n), algebraMap ℚ[X] (RatFunc ℚ) ((Dtail n).comp (-X ^ 2))
              * (algebraMap ℚ[X] (RatFunc ℚ) (C (tailRes n Q a))
                / algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((a : ℚ) ^ 2)))) := by
        rw [map_mul, ← Finset.mul_sum]
        ring
    _ = algebraMap ℚ[X] (RatFunc ℚ) ((-1) ^ hDim n) * algebraMap ℚ[X] (RatFunc ℚ) X ^ 7
          * (algebraMap ℚ[X] (RatFunc ℚ) ((Dtail n).comp (-X ^ 2))
              * algebraMap ℚ[X] (RatFunc ℚ) ((Q.div (Dtail n)).comp (-X ^ 2))
            + ∑ a ∈ Icc (N n + 1) (K n), algebraMap ℚ[X] (RatFunc ℚ) (C (tailRes n Q a)
              * (∏ j ∈ (Icc (N n + 1) (K n)).erase a, (X + C ((j : ℚ) ^ 2))).comp (-X ^ 2))) := by
        rw [Finset.sum_congr rfl hterm]
    _ = _ := by
        simp only [map_mul, map_add, map_sum, map_pow]
        ring

theorem tailCoeffs_support (n : ℕ) (Q : ℚ[X]) : (tailCoeffs n Q).support ⊆ Icc (N n + 1) (K n) := by
  intro a ha
  have h := Finsupp.support_finsetSum ha
  simp only [Finset.mem_biUnion] at h
  obtain ⟨b, hb, hab⟩ := h
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hab)]
  exact hb

theorem pullbackPoles_support_subset (n : ℕ) (Q : ℚ[X]) :
    (pullbackPoles (tailCoeffs n Q)).support ⊆ denSet n := by
  intro r hr
  unfold pullbackPoles at hr
  have h2 := Finsupp.support_sum hr
  simp only [Finset.mem_biUnion] at h2
  obtain ⟨j, hj, hrj⟩ := h2
  have hj' := tailCoeffs_support n Q hj
  rcases Finset.mem_union.mp (Finsupp.support_add hrj) with h | h
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj')
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj')

/-- The numerator of `x⁷ R(-x²)` over `∏_{r ∈ den} (x - r)`, for `R = Q/D_tail`, is
`(-1)^h x⁷ Q(-x²)`. -/
theorem pfNum_pullback (n : ℕ) (Q : ℚ[X]) :
    pfNum (pullbackPoly (Q.div (Dtail n)) (tailCoeffs n Q)) (pullbackPoles (tailCoeffs n Q))
        (denSet n)
      = (-1) ^ hDim n * (X ^ 7 * Q.comp (-X ^ 2)) := by
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  rw [algebraMap_pfNum _ _ (pullbackPoles_support_subset n Q), tauRatFunc_pullbackData,
    algebraMap_mul_pullbackRatFunc]

end Numerator

/-! ## Class degrees of the pullback numerator -/

section ClassNumer

variable {p : ℕ} [Fact p.Prime]

/-- `[r ≡ a] + [-r ≡ a] (mod p)`: the class degree at `a` of `-x² + r²`. -/
def classMult (p a : ℕ) (r : ℤ) : ℕ :=
  (if (p : ℤ) ∣ r - a then 1 else 0) + (if (p : ℤ) ∣ -r - a then 1 else 0)

theorem ClassDeg.of_eq {a n n' : ℕ} {Q : ℚ[X]} (h : ClassDeg p a n Q) (hn : n = n') :
    ClassDeg p a n' Q := hn ▸ h

theorem ClassDeg.neg_one_pow_mul {a n : ℕ} {Q : ℚ[X]} (hQ : ClassDeg p a n Q) (k : ℕ) :
    ClassDeg p a n ((-1) ^ k * Q) := by
  rcases neg_one_pow_eq_or ℚ[X] k with h | h
  · rw [h, one_mul]; exact hQ
  · rw [h, neg_one_mul]; exact hQ.neg

theorem classDeg_negSq (a : ℕ) (r : ℤ) :
    ClassDeg p a (classMult p a r) (-X ^ 2 + C ((r : ℚ) ^ 2)) := by
  have h : (-X ^ 2 + C ((r : ℚ) ^ 2) : ℚ[X]) = -((X - C (r : ℚ)) * (X - C ((-r : ℤ) : ℚ))) := by
    rw [Int.cast_neg, C_neg, C_pow]; ring
  rw [h]
  exact ((classDeg_X_sub_C a r).mul (classDeg_X_sub_C a (-r))).neg

theorem classDeg_negSq_nat (a c : ℕ) :
    ClassDeg p a (classMult p a c) (-X ^ 2 + C ((c : ℚ) ^ 2)) := by
  have h := classDeg_negSq (p := p) a (c : ℤ)
  rwa [Int.cast_natCast] at h

theorem classDeg_X (a : ℕ) : ClassDeg p a (if (p : ℤ) ∣ 0 - a then 1 else 0) (X : ℚ[X]) := by
  have h := classDeg_X_sub_C (p := p) a 0
  rwa [Int.cast_zero, C_0, sub_zero] at h

theorem classDeg_Dpoly_comp (a m : ℕ) :
    ClassDeg p a (∑ j ∈ range m, classMult p a ((j : ℤ) + 1)) ((Dpoly m).comp (-X ^ 2)) := by
  rw [Dpoly, Polynomial.prod_comp]
  refine ClassDeg.prod _ _ _ fun j _ => ?_
  rw [add_comp, X_comp, C_comp]
  have h := classDeg_negSq_nat (p := p) a (j + 1)
  push_cast at h
  exact h

/-- The class degree of `E_{b,i}(-x²)` at `a`. -/
def eDeg (n M p : ℕ) (ε : ℕ → ℕ) (b i a : ℕ) : ℕ :=
  (∑ c ∈ (range (mHalf p + 1)).erase b, classMult p a c * allocL n M p ε c)
    + classMult p a b * i

theorem classDeg_eBasis_comp (a n M : ℕ) (ε : ℕ → ℕ) (b i : ℕ) :
    ClassDeg p a (eDeg n M p ε b i a) ((eBasis ℚ n M p ε b i).comp (-X ^ 2)) := by
  rw [eBasis, mul_comp, Polynomial.prod_comp]
  refine (ClassDeg.prod _ _ _ fun c _ => ?_).mul ?_
  · rw [pow_comp, add_comp, X_comp, C_comp]
    exact (classDeg_negSq_nat a c).pow _
  · rw [pow_comp, add_comp, X_comp, C_comp]
    exact (classDeg_negSq_nat a b).pow _

/-- The class degree at `a` of the numerator `(-1)^h x⁷ (D_N⁷ E_{b,i} E_{b',i'})(-x²)`. -/
def numDeg (n M p : ℕ) (ε : ℕ → ℕ) (b i b' i' a : ℕ) : ℕ :=
  7 * (if (p : ℤ) ∣ 0 - a then 1 else 0)
    + 7 * (∑ j ∈ range (N n), classMult p a ((j : ℤ) + 1))
    + eDeg n M p ε b i a + eDeg n M p ε b' i' a

theorem classDeg_numer (a n M : ℕ) (ε : ℕ → ℕ) (b i b' i' : ℕ) :
    ClassDeg p a (numDeg n M p ε b i b' i' a) ((-1) ^ hDim n * (X ^ 7
      * (Dpoly (N n) ^ 7 * eBasis ℚ n M p ε b i * eBasis ℚ n M p ε b' i').comp (-X ^ 2))) := by
  refine ClassDeg.neg_one_pow_mul ?_ _
  rw [mul_comp, mul_comp, pow_comp]
  refine (((classDeg_X a).pow 7).mul ((((classDeg_Dpoly_comp a (N n)).pow 7).mul
    (classDeg_eBasis_comp a n M ε b i)).mul (classDeg_eBasis_comp a n M ε b' i'))).of_eq ?_
  unfold numDeg
  ring

end ClassNumer

/-! ## Class arithmetic -/

section ClassArith

variable {p : ℕ}

/-- The class `c ∈ [0, m]` of a residue `a ∈ [0, p)`, with `a ≡ ±c (mod p)`. -/
def cls (p a : ℕ) : ℕ := if a ≤ mHalf p then a else p - a

theorem cls_le (hp : 2 * mHalf p + 1 = p) {a : ℕ} (ha : a < p) : cls p a ≤ mHalf p := by
  unfold cls
  split_ifs <;> omega

theorem dvd_iff_eq_zero_of_lt {q : ℕ} {x : ℤ} (h1 : -(q : ℤ) < x) (h2 : x < q) :
    (q : ℤ) ∣ x ↔ x = 0 :=
  ⟨fun h => int_eq_zero_of_dvd_of_lt h h1 h2, fun h => h ▸ dvd_zero _⟩

theorem classMult_eq (hp : 2 * mHalf p + 1 = p) {a c : ℕ} (ha : a < p) (hc : c ≤ mHalf p) :
    classMult p a c = if c = cls p a then (if a = 0 then 2 else 1) else 0 := by
  unfold classMult cls
  by_cases ham : a ≤ mHalf p
  · have hD1 : (p : ℤ) ∣ (c : ℤ) - a ↔ c = a := by
      rw [dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
    have hD2 : (p : ℤ) ∣ -(c : ℤ) - a ↔ c = 0 ∧ a = 0 := by
      rw [dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
    simp only [hD1, hD2, ham, ite_true]
    split_ifs <;> omega
  · have hD1 : ¬ (p : ℤ) ∣ (c : ℤ) - a := by
      rw [dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
    have hD2 : (p : ℤ) ∣ -(c : ℤ) - a ↔ c = p - a := by
      rw [← dvd_add_left (dvd_refl (p : ℤ)), dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
    simp only [hD1, hD2, ham, ite_false]
    split_ifs <;> omega

/-- For `1 ≤ c ≤ m`, `ℓ_A(c)` counts the residues `c` and `-c` separately. -/
theorem ell_eq_card_add (hp : 2 * mHalf p + 1 = p) (A c : ℕ) (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ell p A c = ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c).card
      + ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) + c).card := by
  rw [ell, Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro j _ h1 h2
  have h3 := dvd_sub h2 h1
  rw [show (j : ℤ) + c - (j - c) = 2 * c by ring] at h3
  have := Int.le_of_dvd (by omega) h3
  omega

theorem sum_classMult_eq_card (s : Finset ℕ) (a : ℕ) :
    ∑ j ∈ s, classMult p a j = (s.filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - a).card
      + (s.filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) + a).card := by
  unfold classMult
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (p : ℤ) ∣ -(j : ℤ) - a ↔ (p : ℤ) ∣ (j : ℤ) + a := by
    rw [show -(j : ℤ) - a = -((j : ℤ) + a) by ring, dvd_neg]
  simp only [h]

/-- The class counts in terms of `classMult`: `∑_{j=1}^A ([j ≡ a] + [-j ≡ a])` is `2⌊A/p⌋` for
`a = 0` and `ℓ_A(c)` for `a ≡ ±c`, `1 ≤ c ≤ m`. -/
theorem sum_classMult_Icc (hp : 2 * mHalf p + 1 = p) (A : ℕ) {a : ℕ} (ha : a < p) :
    ∑ j ∈ Icc 1 A, classMult p a j = if a = 0 then 2 * (A / p) else ell p A (cls p a) := by
  rw [sum_classMult_eq_card]
  split_ifs with h0
  · subst h0
    have hdiv : ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - ((0 : ℕ) : ℤ)).card = A / p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div A p, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
      congr 1
      ext j
      simp only [Finset.mem_filter, Nat.cast_zero, sub_zero, Int.natCast_dvd_natCast]
    have hdiv' : ((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) + ((0 : ℕ) : ℤ)).card
        = A / p := by
      rw [← hdiv]
      congr 1
    rw [hdiv, hdiv']
    ring
  · unfold cls
    by_cases ham : a ≤ mHalf p
    · rw [ite_eq_left ham, ell_eq_card_add hp A a (by omega) ham]
    · rw [ite_eq_right ham, ell_eq_card_add hp A (p - a) (by omega) (by omega), add_comm]
      congr 2
      · ext j
        have h : ∀ x : ℕ, (p : ℤ) ∣ (x : ℤ) + a ↔ (p : ℤ) ∣ (x : ℤ) - (p - a : ℕ) := fun x => by
          rw [Nat.cast_sub ha.le, show (x : ℤ) - (p - a) = (x : ℤ) + a - p by ring,
            dvd_sub_self_right]
        simp only [Finset.mem_filter, h]
      · ext j
        have h : ∀ x : ℕ, (p : ℤ) ∣ (x : ℤ) - a ↔ (p : ℤ) ∣ (x : ℤ) + (p - a : ℕ) := fun x => by
          rw [Nat.cast_sub ha.le, show (x : ℤ) + (p - a) = (x : ℤ) - a + p by ring,
            dvd_add_self_right]
        simp only [Finset.mem_filter, h]

theorem sum_range_classMult (A a : ℕ) :
    ∑ j ∈ range A, classMult p a ((j : ℤ) + 1) = ∑ j ∈ Icc 1 A, classMult p a j := by
  have h := Finset.sum_Ico_add' (fun j : ℕ => classMult p a (j : ℤ)) 0 A 1
  simp only [zero_add, Nat.cast_add, Nat.cast_one, Finset.Ico_add_one_right_eq_Icc] at h
  rw [Finset.range_eq_Ico, h]

/-- The number `t` of poles `r ∈ den` with `r ≡ a (mod p)`. -/
theorem card_denSet_filter (n a : ℕ) :
    ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card
      = ∑ j ∈ Icc (N n + 1) (K n), classMult p a j := by
  rw [sum_classMult_eq_card, denSet, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (denSet_disjoint n)),
    Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
  congr 1
  congr 1
  ext j
  have h : (p : ℤ) ∣ -(j : ℤ) - a ↔ (p : ℤ) ∣ (j : ℤ) + a := by
    rw [show -(j : ℤ) - a = -((j : ℤ) + a) by ring, dvd_neg]
  simp only [Finset.mem_filter, h]

theorem sum_Icc_split (f : ℕ → ℕ) {N' K' : ℕ} (h : N' ≤ K') :
    ∑ j ∈ Icc 1 K', f j = ∑ j ∈ Icc 1 N', f j + ∑ j ∈ Icc (N' + 1) K', f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_consecutive _ (by omega) (by omega)]

end ClassArith

/-! ## The comparison cases (i)-(iv) -/

section Comparison

variable {n M p : ℕ} {ε : ℕ → ℕ}

theorem weight2_of_ne {a : ℕ} (ha : a ≠ 0) (i : ℕ) :
    weight2 n M p ε a i = 2 * (i : ℤ) + 8 * ell p (N n) a - ell p (K n) a - 6 := by
  unfold weight2
  rw [ite_eq_right ha]

theorem weight2_zero_le (i : ℕ) :
    weight2 n M p ε 0 i ≤ 4 * (i : ℤ) + 16 * mN n p - 2 * mK n p + 1 := by
  unfold weight2
  rw [ite_eq_left rfl]
  exact (Finset.fold_min_le _).mpr (Or.inl le_rfl)

theorem weight2_zero_le' (i : ℕ) {c : ℕ} (hc : c ∈ Icc 1 (mHalf p)) :
    weight2 n M p ε 0 i ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6 := by
  unfold weight2
  rw [ite_eq_left rfl]
  exact (Finset.fold_min_le _).mpr (Or.inr ⟨c, hc, le_rfl⟩)

theorem allocL_eq (hR : InnerRange n M p) [Fact p.Prime] {a : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) :
    (allocL n M p ε a : ℤ) = allocT n M p + ε a - 4 * ell p (N n) a := by
  have h := bA_lt_allocT hR ha1 ham
  unfold allocL allocZ
  unfold bA at h ⊢
  rw [ite_eq_right (by omega)]
  omega

/-- **Comparison** (proof of Proposition 4.4, cases (i)-(iv) and the mixed cases with a
zero-class row): for rows `(a, i)`, `(b, j)` and every source class `0 ≤ c ≤ m`, twice the
residue exponent `(50)`/`(51)` dominates `2 w_{a,i} + 2 w_{b,j}`. Here `ν` is the vanishing order
at `-c²` (`i` if the row belongs to class `c`, `L_c` otherwise). -/
theorem comparison (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    {a i b j c : ℕ} (ha : a ≤ mHalf p) (hi : i < allocL n M p ε a)
    (hb : b ≤ mHalf p) (hj : j < allocL n M p ε b) (hc : c ≤ mHalf p) :
    weight2 n M p ε a i + weight2 n M p ε b j
      ≤ 2 * (if c = 0 then 1 + 16 * (mN n p : ℤ) - 2 * mK n p
            + 2 * ((if a = c then i else allocL n M p ε c : ℕ) : ℤ)
            + 2 * ((if b = c then j else allocL n M p ε c : ℕ) : ℤ)
          else 8 * (ell p (N n) c : ℤ) - ell p (K n) c
            + ((if a = c then i else allocL n M p ε c : ℕ) : ℤ)
            + ((if b = c then j else allocL n M p ε c : ℕ) : ℤ) - 6) := by
  have hm := hR.two_mul_mHalf
  have hT := allocT_lt hR
  have hmK := hR.mK_lt
  have hM := hR.forty_le
  have hL0 : allocL n M p ε 0 = 6 * M + 10 := by
    unfold allocL L0
    rw [ite_eq_left rfl]
  have hmono : ∀ x y, 1 ≤ x → x ≤ mHalf p → 1 ≤ y → y ≤ mHalf p →
      ε x ≠ 0 ∨ ε y ≠ 1 ∨ ell p (K n) x ≤ ell p (K n) y := by
    intro x y hx1 hx2 hy1 hy2
    by_cases h1 : ε x = 0
    · by_cases h2 : ε y = 1
      · exact Or.inr (Or.inr (hε.mono x (Finset.mem_Icc.mpr ⟨hx1, hx2⟩) y
          (Finset.mem_Icc.mpr ⟨hy1, hy2⟩) h1 h2))
      · exact Or.inr (Or.inl h2)
    · exact Or.inl h1
  have hrow : ∀ x k, x ≤ mHalf p → k < allocL n M p ε x → x ≠ 0 →
      weight2 n M p ε x k = 2 * (k : ℤ) + 8 * ell p (N n) x - ell p (K n) x - 6 ∧
      (k : ℤ) < allocT n M p + ε x - 4 * ell p (N n) x ∧ ε x ≤ 1 := by
    intro x k hx hk hx0
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    refine ⟨weight2_of_ne hx0 k, ?_, hε.le_one x (Finset.mem_Icc.mpr ⟨hx1, hx⟩)⟩
    have := allocL_eq (ε := ε) hR hx1 hx
    omega
  by_cases hc0 : c = 0
  · rw [ite_eq_left hc0]
    subst hc0
    rw [hL0]
    by_cases ha0 : a = 0
    · rw [ite_eq_left ha0]
      have hWa : weight2 n M p ε a i ≤ 4 * (i : ℤ) + 16 * mN n p - 2 * mK n p + 1 := by
        rw [ha0]; exact weight2_zero_le i
      by_cases hb0 : b = 0
      · rw [ite_eq_left hb0]
        have hWb : weight2 n M p ε b j ≤ 4 * (j : ℤ) + 16 * mN n p - 2 * mK n p + 1 := by
          rw [hb0]; exact weight2_zero_le j
        omega
      · rw [ite_eq_right hb0]
        obtain ⟨hWb, hjb, hεb⟩ := hrow b j hb hj hb0
        omega
    · rw [ite_eq_right ha0]
      obtain ⟨hWa, hia, hεa⟩ := hrow a i ha hi ha0
      by_cases hb0 : b = 0
      · rw [ite_eq_left hb0]
        have hWb : weight2 n M p ε b j ≤ 4 * (j : ℤ) + 16 * mN n p - 2 * mK n p + 1 := by
          rw [hb0]; exact weight2_zero_le j
        omega
      · rw [ite_eq_right hb0]
        obtain ⟨hWb, hjb, hεb⟩ := hrow b j hb hj hb0
        omega
  · rw [ite_eq_right hc0]
    have hc1 : 1 ≤ c := Nat.pos_of_ne_zero hc0
    have hcI : c ∈ Icc 1 (mHalf p) := Finset.mem_Icc.mpr ⟨hc1, hc⟩
    have hLc := allocL_eq (ε := ε) hR hc1 hc
    have hεc := hε.le_one c hcI
    have hZc : (allocZ n M p ε c : ℤ) = allocT n M p + ε c := by unfold allocZ; omega
    by_cases hac : a = c
    · rw [ite_eq_left hac]
      have hWa : weight2 n M p ε a i
          = 2 * (i : ℤ) + 8 * ell p (N n) c - ell p (K n) c - 6 := by
        rw [hac]; exact weight2_of_ne hc0 i
      by_cases hbc : b = c
      · rw [ite_eq_left hbc]
        have hWb : weight2 n M p ε b j
            = 2 * (j : ℤ) + 8 * ell p (N n) c - ell p (K n) c - 6 := by
          rw [hbc]; exact weight2_of_ne hc0 j
        omega
      · rw [ite_eq_right hbc]
        by_cases hb0 : b = 0
        · have hWb : weight2 n M p ε b j ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6 := by
            rw [hb0]; exact weight2_zero_le' j hcI
          omega
        · obtain ⟨hWb, hjb, hεb⟩ := hrow b j hb hj hb0
          have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
          have h1 := ell_le_ell_add_one hm (K n) hb1 hb hc1 hc
          have h2 := ell_le_ell_add_one hm (K n) hc1 hc hb1 hb
          have h3 := hmono c b hc1 hc hb1 hb
          omega
    · rw [ite_eq_right hac]
      by_cases ha0 : a = 0
      · have hWa : weight2 n M p ε a i ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6 := by
          rw [ha0]; exact weight2_zero_le' i hcI
        by_cases hbc : b = c
        · rw [ite_eq_left hbc]
          have hWb : weight2 n M p ε b j
              = 2 * (j : ℤ) + 8 * ell p (N n) c - ell p (K n) c - 6 := by
            rw [hbc]; exact weight2_of_ne hc0 j
          omega
        · rw [ite_eq_right hbc]
          by_cases hb0 : b = 0
          · have hWb : weight2 n M p ε b j
                ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6 := by
              rw [hb0]; exact weight2_zero_le' j hcI
            omega
          · obtain ⟨hWb, hjb, hεb⟩ := hrow b j hb hj hb0
            have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
            have h1 := ell_le_ell_add_one hm (K n) hb1 hb hc1 hc
            have h2 := ell_le_ell_add_one hm (K n) hc1 hc hb1 hb
            have h3 := hmono c b hc1 hc hb1 hb
            omega
      · obtain ⟨hWa, hia, hεa⟩ := hrow a i ha hi ha0
        have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
        have h1 := ell_le_ell_add_one hm (K n) ha1 ha hc1 hc
        have h2 := ell_le_ell_add_one hm (K n) hc1 hc ha1 ha
        have h3 := hmono c a hc1 hc ha1 ha
        by_cases hbc : b = c
        · rw [ite_eq_left hbc]
          have hWb : weight2 n M p ε b j
              = 2 * (j : ℤ) + 8 * ell p (N n) c - ell p (K n) c - 6 := by
            rw [hbc]; exact weight2_of_ne hc0 j
          omega
        · rw [ite_eq_right hbc]
          by_cases hb0 : b = 0
          · have hWb : weight2 n M p ε b j
                ≤ 2 * (allocZ n M p ε c : ℤ) - ell p (K n) c - 6 := by
              rw [hb0]; exact weight2_zero_le' j hcI
            omega
          · obtain ⟨hWb, hjb, hεb⟩ := hrow b j hb hj hb0
            have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
            have h4 := ell_le_ell_add_one hm (K n) hb1 hb hc1 hc
            have h5 := ell_le_ell_add_one hm (K n) hc1 hc hb1 hb
            have h6 := hmono c b hc1 hc hb1 hb
            have h7 := ell_le_ell_add_one hm (K n) ha1 ha hb1 hb
            have h8 := ell_le_ell_add_one hm (K n) hb1 hb ha1 ha
            omega

end Comparison

/-! ## Entry valuations, the determinant bound and Proposition 4.4 -/

section Assembly

variable {n M p : ℕ} {ε : ℕ → ℕ}

/-- `‖P_k‖_p² ≤ p^{-u}` for every coefficient: the Gauss valuation of `P` is at least `u/2`. -/
def NormSqLe (p : ℕ) [Fact p.Prime] (u : ℤ) (P : ℚ[X]) : Prop :=
  ∀ k, ‖((P.coeff k : ℚ) : ℚ_[p])‖ ^ 2 ≤ (p : ℝ) ^ (-u)

theorem NormSqLe.mul [Fact p.Prime] {u v : ℤ} {P Q : ℚ[X]} (hP : NormSqLe p u P)
    (hQ : NormSqLe p v Q) : NormSqLe p (u + v) (P * Q) := by
  intro k
  rw [coeff_mul, Rat.cast_sum]
  obtain ⟨x, _, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    ⟨(0, k), Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add k)⟩
    (fun x : ℕ × ℕ => ((P.coeff x.1 * Q.coeff x.2 : ℚ) : ℚ_[p]))
  calc _ ≤ ‖((P.coeff x.1 * Q.coeff x.2 : ℚ) : ℚ_[p])‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖((P.coeff x.1 : ℚ) : ℚ_[p])‖ ^ 2 * ‖((Q.coeff x.2 : ℚ) : ℚ_[p])‖ ^ 2 := by
        rw [Rat.cast_mul, norm_mul, mul_pow]
    _ ≤ (p : ℝ) ^ (-u) * (p : ℝ) ^ (-v) :=
        mul_le_mul (hP _) (hQ _) (by positivity) (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = _ := by rw [← zpow_add₀ prime_cast_pos_real.ne']; congr 1; ring

theorem NormSqLe.prod [Fact p.Prime] {ι : Type*} (s : Finset ι) (u : ι → ℤ) (P : ι → ℚ[X])
    (h : ∀ i ∈ s, NormSqLe p (u i) (P i)) : NormSqLe p (∑ i ∈ s, u i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [Finset.prod_empty, Finset.sum_empty, neg_zero, zpow_zero, coeff_one]
    split_ifs <;> simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem NormSqLe.sum [Fact p.Prime] {ι : Type*} (s : Finset ι) {u : ℤ} (P : ι → ℚ[X])
    (h : ∀ i ∈ s, NormSqLe p u (P i)) : NormSqLe p u (∑ i ∈ s, P i) := by
  intro k
  rw [finsetSum_coeff, Rat.cast_sum]
  rcases Finset.eq_empty_or_nonempty s with he | hne
  · rw [he, Finset.sum_empty, norm_zero]
    simpa using zpow_nonneg (Nat.cast_nonneg (α := ℝ) p) (-u)
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i => (((P i).coeff k : ℚ) : ℚ_[p]))
    exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans (h i hi k)

theorem NormSqLe.intCast_mul [Fact p.Prime] {u : ℤ} {P : ℚ[X]} (hP : NormSqLe p u P) (z : ℤˣ) :
    NormSqLe p u (((z : ℤ) : ℚ[X]) * P) := by
  intro k
  rw [← C_eq_intCast, coeff_C_mul, Rat.cast_mul, norm_mul, mul_pow]
  have hz : ‖(((z : ℤ) : ℚ) : ℚ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or z with h | h <;> simp [h]
  rw [hz, one_pow, one_mul]
  exact hP k

/-- Leibniz expansion: if `v^G_p(A_{ij}) ≥ (w_i + w_j)/2` then `v^G_p(det A) ≥ ∑ w_i`. -/
theorem normSqLe_det [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (w : ι → ℤ) (hA : ∀ i j, NormSqLe p (w i + w j) (A i j)) :
    NormSqLe p (2 * ∑ i, w i) A.det := by
  rw [Matrix.det_apply']
  refine NormSqLe.sum _ _ fun σ _ => ?_
  have h := NormSqLe.prod Finset.univ (fun i => w (σ i) + w i) (fun i => A (σ i) i)
    fun i _ => hA (σ i) i
  beta_reduce at h
  have hsum : ∑ i, (w (σ i) + w i) = 2 * ∑ i, w i := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ w]
    ring
  rw [hsum] at h
  exact h.intCast_mul _

theorem mem_denSet_bound {r : ℤ} (hr : r ∈ denSet n) : -(K n : ℤ) ≤ r ∧ r ≤ K n := by
  rcases Finset.mem_union.mp hr with h | h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have := (Finset.mem_Icc.mp hj).2
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have := (Finset.mem_Icc.mp hj).2
    omega

/-- Distinct poles are incongruent modulo `p²` (since `p² > 2K`). -/
theorem denSet_not_dvd (hR : InnerRange n M p) [Fact p.Prime] {r j : ℤ} (hr : r ∈ denSet n)
    (hj : j ∈ denSet n) (hrj : r ≠ j) : ¬ (p : ℤ) ^ 2 ∣ r - j := by
  intro hdvd
  obtain ⟨hr1, hr2⟩ := mem_denSet_bound hr
  obtain ⟨hj1, hj2⟩ := mem_denSet_bound hj
  have hK := hR.K_lt
  have hpM := hR.p_gt
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : 2 * (K n : ℤ) < (p : ℤ) ^ 2 := by
    have h1 : 200 * K n < p * p := by nlinarith
    have h2 : 2 * K n < p ^ 2 := by nlinarith
    exact_mod_cast h2
  have h0 := int_eq_zero_of_dvd_of_lt (q := p ^ 2) (x := r - j) (by exact_mod_cast hdvd)
    (by push_cast; linarith) (by push_cast; linarith)
  omega

/-- `d((r - a)/p) < p` for the poles `r ≡ a (mod p)`. -/
theorem dIndex_lt_of_mem (hR : InnerRange n M p) [Fact p.Prime] {a : ℕ} (ha : a < p) {r : ℤ}
    (hr : r ∈ denSet n) (hra : (p : ℤ) ∣ r - a) : dIndex ((r - a) / p) < p := by
  obtain ⟨hr1, hr2⟩ := mem_denSet_bound hr
  obtain ⟨s, hs⟩ := hra
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [hs, Int.mul_ediv_cancel_left _ hp0]
  have hK : (K n : ℤ) < M * p := by exact_mod_cast hR.K_lt
  have hpM : (200 * M : ℤ) < p := by exact_mod_cast hR.p_gt
  have ha' : (a : ℤ) < p := by exact_mod_cast ha
  have h1 : (p : ℤ) * s < p * (M + 1) := by nlinarith
  have h2 : (p : ℤ) * (-(M + 1)) < p * s := by nlinarith
  have h3 : s < M + 1 := lt_of_mul_lt_mul_left h1 hpp.le
  have h4 : -((M : ℤ) + 1) < s := lt_of_mul_lt_mul_left h2 hpp.le
  unfold dIndex
  split_ifs <;> omega

theorem eDeg_eq (hR : InnerRange n M p) [Fact p.Prime] {b i a : ℕ} (hb : b ≤ mHalf p)
    (ha : a < p) :
    eDeg n M p ε b i a = (if a = 0 then 2 else 1)
      * (if b = cls p a then i else allocL n M p ε (cls p a)) := by
  have hm := hR.two_mul_mHalf
  have hcl := cls_le hm ha
  unfold eDeg
  have hsum : ∑ c ∈ (range (mHalf p + 1)).erase b, classMult p a c * allocL n M p ε c
      = ∑ c ∈ (range (mHalf p + 1)).erase b,
          (if c = cls p a then (if a = 0 then 2 else 1) else 0) * allocL n M p ε c :=
    Finset.sum_congr rfl fun c hc => by
      rw [classMult_eq hm ha (by
        have := Finset.mem_range.mp (Finset.mem_of_mem_erase hc); omega)]
  rw [hsum, classMult_eq hm ha hb]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  by_cases hbc : b = cls p a
  · rw [ite_eq_right (by simp only [Finset.mem_erase, Finset.mem_range]; omega :
      cls p a ∉ (range (mHalf p + 1)).erase b), ite_eq_left hbc, ite_eq_left hbc]
    ring
  · rw [ite_eq_left (by simp only [Finset.mem_erase, Finset.mem_range]; omega :
      cls p a ∈ (range (mHalf p + 1)).erase b), ite_eq_right hbc, ite_eq_right hbc]
    ring

/-- The residue exponent of class `a`: `n - t - 6` is `(51)` for `a = 0` and `(50)` otherwise,
with `ν` the vanishing orders at `-c²`, `c = cls a`. -/
theorem numDeg_sub (hR : InnerRange n M p) [Fact p.Prime] {b i b' i' a : ℕ}
    (hb : b ≤ mHalf p) (hb' : b' ≤ mHalf p) (ha : a < p) :
    (numDeg n M p ε b i b' i' a : ℤ) - ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card - 6
      = if cls p a = 0 then 1 + 16 * (mN n p : ℤ) - 2 * mK n p
            + 2 * ((if b = cls p a then i else allocL n M p ε (cls p a) : ℕ) : ℤ)
            + 2 * ((if b' = cls p a then i' else allocL n M p ε (cls p a) : ℕ) : ℤ)
          else 8 * (ell p (N n) (cls p a) : ℤ) - ell p (K n) (cls p a)
            + ((if b = cls p a then i else allocL n M p ε (cls p a) : ℕ) : ℤ)
            + ((if b' = cls p a then i' else allocL n M p ε (cls p a) : ℕ) : ℤ) - 6 := by
  have hm := hR.two_mul_mHalf
  have hNK : N n ≤ K n := by unfold N K; omega
  have hsplit := sum_Icc_split (fun j => classMult p a j) hNK
  beta_reduce at hsplit
  have hSN := sum_classMult_Icc hm (N n) ha
  have hSK := sum_classMult_Icc hm (K n) ha
  have hcls0 : cls p a = 0 ↔ a = 0 := by unfold cls; split_ifs <;> omega
  have hdvd0 : (p : ℤ) ∣ 0 - a ↔ a = 0 := by
    rw [dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
  rw [card_denSet_filter, numDeg, eDeg_eq hR hb ha, eDeg_eq hR hb' ha, sum_range_classMult]
  simp only [hcls0, hdvd0]
  generalize (if b = cls p a then i else allocL n M p ε (cls p a)) = νb
  generalize (if b' = cls p a then i' else allocL n M p ε (cls p a)) = νb'
  unfold mN mK
  split_ifs at hSN hSK ⊢ <;> omega

/-- The class degree satisfies the degree condition `n ≤ p + 4` of the residue bound. -/
theorem numDeg_le (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    {b i b' i' a : ℕ} (hb : b ≤ mHalf p) (hi : i < allocL n M p ε b) (hb' : b' ≤ mHalf p)
    (hi' : i' < allocL n M p ε b') (ha : a < p) : numDeg n M p ε b i b' i' a ≤ p + 4 := by
  have hm := hR.two_mul_mHalf
  have hT := allocT_lt hR
  have hpM := hR.p_gt
  have hM := hR.forty_le
  have hmK := hR.mK_lt
  have hmN := mN_le_mK n p
  have hSN := sum_classMult_Icc hm (N n) ha
  have hcl := cls_le hm ha
  have hcls0 : cls p a = 0 ↔ a = 0 := by unfold cls; split_ifs <;> omega
  have hdvd0 : (p : ℤ) ∣ 0 - a ↔ a = 0 := by
    rw [dvd_iff_eq_zero_of_lt (by omega) (by omega)]; omega
  have hνb : (if b = cls p a then i else allocL n M p ε (cls p a)) ≤ allocL n M p ε (cls p a) := by
    split_ifs with h
    · rw [← h]; exact hi.le
    · exact le_rfl
  have hνb' : (if b' = cls p a then i' else allocL n M p ε (cls p a))
      ≤ allocL n M p ε (cls p a) := by
    split_ifs with h
    · rw [← h]; exact hi'.le
    · exact le_rfl
  rw [numDeg, eDeg_eq hR hb ha, eDeg_eq hR hb' ha, sum_range_classMult, hSN]
  simp only [hdvd0]
  generalize (if b = cls p a then i else allocL n M p ε (cls p a)) = νb at hνb ⊢
  generalize (if b' = cls p a then i' else allocL n M p ε (cls p a)) = νb' at hνb' ⊢
  by_cases ha0 : a = 0
  · have hL0 : allocL n M p ε (cls p a) = 6 * M + 10 := by
      rw [hcls0.mpr ha0]; unfold allocL L0; rw [ite_eq_left rfl]
    rw [hL0] at hνb hνb'
    simp only [ha0, ↓reduceIte]
    unfold mN at hmN
    omega
  · have hc1 : 1 ≤ cls p a := Nat.pos_of_ne_zero fun h => ha0 (hcls0.mp h)
    have hLc := allocL_eq (ε := ε) hR hc1 hcl
    have hεc := hε.le_one (cls p a) (Finset.mem_Icc.mpr ⟨hc1, hcl⟩)
    simp only [ha0, ↓reduceIte]
    omega

/-- **Residue bounds (50)-(51) and the comparison**: every entry of the Gram matrix in the
`E`-basis has Gauss valuation at least `w_ρ + w_σ`. -/
theorem normSqLe_gram (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (ρ σ : eIdx n M p ε) :
    NormSqLe p (weight2 n M p ε ρ.1 ρ.2 + weight2 n M p ε σ.1 σ.2)
      (muTail n (Dpoly (N n) ^ 7 * eBasis ℚ n M p ε ρ.1 ρ.2 * eBasis ℚ n M p ε σ.1 σ.2)) := by
  intro k
  have hp11 : 11 ≤ p := by have := hR.p_gt; have := hR.forty_le; omega
  have hm := hR.two_mul_mHalf
  have hp1 := prime_cast_one_lt_real (p := p)
  have hρ : (ρ.1 : ℕ) ≤ mHalf p := Nat.lt_succ_iff.mp ρ.1.isLt
  have hσ : (σ.1 : ℕ) ≤ mHalf p := Nat.lt_succ_iff.mp σ.1.isLt
  set Q := Dpoly (N n) ^ 7 * eBasis ℚ n M p ε ρ.1 ρ.2 * eBasis ℚ n M p ε σ.1 σ.2
  set P := pullbackPoly (Q.div (Dtail n)) (tailCoeffs n Q) with hP
  set d := pullbackPoles (tailCoeffs n Q) with hd
  have h1 := congrArg (fun F : Polynomial ℚ_[p] => F.coeff k) (distribution_formula hp11 P d)
  simp only [coeff_map, Rat.coe_castHom, coeff_C_mul, finsetSum_coeff] at h1
  have hmu : muTail n Q = tauFunctional P d := by
    rw [muTail_eq, hP, hd, tauFunctional_pullbackData]
  rw [hmu, h1, norm_mul, Padic.norm_p_zpow, neg_neg]
  have hsupp : d.support ⊆ denSet n := pullbackPoles_support_subset n Q
  have hpf : pfNum P d (denSet n) = (-1) ^ hDim n * (X ^ 7 * Q.comp (-X ^ 2)) :=
    pfNum_pullback n Q
  have hterm : ∀ a ∈ range p, ‖(tauExt (distY p) (substPoles p a d)
      (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
      (fun s => (substPrincipal p a d s : ℚ_[p]))).coeff k‖
        ≤ (p : ℝ) ^ (-((numDeg n M p ε ρ.1 ρ.2 σ.1 σ.2 a : ℤ)
          - ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card)) := by
    intro a ha
    have ha' := Finset.mem_range.mp ha
    refine tauExt_subst_norm_le hp11 a P d (denSet n) hsupp ?_
      (fun r hr j hj hrj _ _ => denSet_not_dvd hR hr hj hrj)
      (fun r hr hra => dIndex_lt_of_mem hR ha' hr hra)
      (numDeg_le hR hε hρ ρ.2.isLt hσ σ.2.isLt ha') k
    rw [hpf]
    exact classDeg_numer a n M ε ρ.1 ρ.2 σ.1 σ.2
  obtain ⟨a, ha, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr (Fact.out : p.Prime).ne_zero)
    (fun a => (tauExt (distY p) (substPoles p a d)
      (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
      (fun s => (substPrincipal p a d s : ℚ_[p]))).coeff k)
  have ha' := Finset.mem_range.mp ha
  have hcmp := comparison hR hε hρ ρ.2.isLt hσ σ.2.isLt (cls_le hm ha')
  have hns := numDeg_sub (ε := ε) hR hρ hσ ha' (i := ρ.2) (i' := σ.2)
  have hexp : (6 + -((numDeg n M p ε ρ.1 ρ.2 σ.1 σ.2 a : ℤ)
      - ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card)) * ((2 : ℕ) : ℤ)
      ≤ -(weight2 n M p ε ρ.1 ρ.2 + weight2 n M p ε σ.1 σ.2) := by
    push_cast
    linarith
  calc ((p : ℝ) ^ (6 : ℤ) * ‖∑ a ∈ range p, (tauExt (distY p) (substPoles p a d)
        (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
        (fun s => (substPrincipal p a d s : ℚ_[p]))).coeff k‖) ^ 2
      ≤ ((p : ℝ) ^ (6 : ℤ) * (p : ℝ) ^ (-((numDeg n M p ε ρ.1 ρ.2 σ.1 σ.2 a : ℤ)
          - ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (zpow_nonneg (Nat.cast_nonneg p) _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hle.trans (hterm a ha))
            (zpow_nonneg (Nat.cast_nonneg p) _)) 2
    _ = (p : ℝ) ^ ((6 + -((numDeg n M p ε ρ.1 ρ.2 σ.1 σ.2 a : ℤ)
          - ((denSet n).filter fun r => (p : ℤ) ∣ r - a).card)) * ((2 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ prime_cast_pos_real.ne', zpow_mul, zpow_natCast]
    _ ≤ _ := zpow_le_zpow_right₀ hp1.le hexp

/-- **Proposition 4.4** (inner estimate). Assume (44) with `M ≥ 40`, and let `ε` be any choice
of extra rows allowed by Definition 4.1 (classes ordered by decreasing `ℓ_K`, ties broken
arbitrarily). Then `v^G_p(Δ_K) ≥ γ^in_p`: every nonzero coefficient of `Δ_K(X)` has `p`-adic
valuation at least `γ^in_p`. -/
theorem inner_estimate (hR : InnerRange n M p) [Fact p.Prime] (hε : ExtraRows n M p ε)
    (k : ℕ) (hk : (DeltaK n).coeff k ≠ 0) :
    gammaIn n M p ε ≤ padicValRat p ((DeltaK n).coeff k) := by
  obtain ⟨e⟩ : Nonempty (eIdx n M p ε ≃ Fin (hDim n)) :=
    ⟨Fintype.equivFinOfCardEq (card_eIdx hR hε)⟩
  have hbound := normSqLe_det (p := p) (Matrix.of fun k l : Fin (hDim n) =>
    muTail n (Dpoly (N n) ^ 7 * eBasis ℚ n M p ε (e.symm k).1 (e.symm k).2
      * eBasis ℚ n M p ε (e.symm l).1 (e.symm l).2))
    (fun k => weight2 n M p ε (e.symm k).1 (e.symm k).2)
    (fun k l => normSqLe_gram hR hε (e.symm k) (e.symm l)) k
  beta_reduce at hbound
  rw [det_gram hR hε e, coeff_C_mul, Rat.cast_mul, norm_mul, mul_pow, Rat.cast_pow, norm_pow,
    norm_det_eMat hR hε e, one_pow, one_pow, one_mul] at hbound
  have hsum : ∑ k : Fin (hDim n), weight2 n M p ε (e.symm k).1 (e.symm k).2
      = gammaIn n M p ε := by
    calc ∑ k : Fin (hDim n), weight2 n M p ε (e.symm k).1 (e.symm k).2
        = ∑ ρ : eIdx n M p ε, weight2 n M p ε ρ.1 ρ.2 :=
          Equiv.sum_comp e.symm (fun ρ : eIdx n M p ε => weight2 n M p ε ρ.1 ρ.2)
      _ = ∑ a : Fin (mHalf p + 1), ∑ i : Fin (allocL n M p ε a), weight2 n M p ε a i :=
          Fintype.sum_sigma _
      _ = gammaIn n M p ε := by
          unfold gammaIn
          rw [← Fin.sum_univ_eq_sum_range
            (fun a => ∑ i ∈ range (allocL n M p ε a), weight2 n M p ε a i)]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Fin.sum_univ_eq_sum_range (fun i => weight2 n M p ε a i) _
  rw [hsum] at hbound
  rw [Padic.norm_eq_zpow_neg_valuation (x := (((DeltaK n).coeff k : ℚ) : ℚ_[p]))
      (by exact_mod_cast hk), Padic.valuation_ratCast,
    ← zpow_natCast, ← zpow_mul] at hbound
  have := (zpow_le_zpow_iff_right₀ prime_cast_one_lt_real).mp hbound
  push_cast at this
  omega

/-- Definition 4.1 is not vacuous: admissible extra rows exist (order the classes by decreasing
`ℓ_K` and give the first `E` of them an extra row). -/
theorem exists_extraRows (hR : InnerRange n M p) [Fact p.Prime] : ∃ ε, ExtraRows n M p ε := by
  have hE := (alloc_eq hR).2
  have key : ∀ e ≤ mHalf p, ∃ S ⊆ Icc 1 (mHalf p), S.card = e ∧
      ∀ a ∈ Icc 1 (mHalf p), a ∉ S → ∀ b ∈ S, ell p (K n) a ≤ ell p (K n) b := by
    intro e he
    induction e with
    | zero => exact ⟨∅, Finset.empty_subset _, rfl, fun a _ _ b hb => by simp at hb⟩
    | succ e ih =>
      obtain ⟨S, hS, hcard, hmono⟩ := ih (by omega)
      have hne : ((Icc 1 (mHalf p)).filter fun a => a ∉ S).Nonempty := by
        by_contra hne
        have hsub : Icc 1 (mHalf p) ⊆ S := fun a ha => by
          by_contra haS
          exact hne ⟨a, Finset.mem_filter.mpr ⟨ha, haS⟩⟩
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        omega
      obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image _ (fun a => ell p (K n) a) hne
      obtain ⟨hxI, hxS⟩ := Finset.mem_filter.mp hx
      refine ⟨insert x S, Finset.insert_subset hxI hS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hxS, hcard]
      · intro a ha haS b hb
        have haS' : a ∉ S := fun h => haS (Finset.mem_insert_of_mem h)
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hxmax a (Finset.mem_filter.mpr ⟨ha, haS'⟩)
        · exact hmono a ha haS' b hb
  obtain ⟨S, hS, hcard, hmono⟩ := key (allocE n M p) hE.le
  refine ⟨fun a => if a ∈ S then 1 else 0, fun a _ => ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · rw [← hcard]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      by_contra haS
      rw [ite_eq_right haS] at h
      omega
    · intro h
      exact ⟨hS h, by rw [ite_eq_left h]⟩
  · intro a ha b hb ha0 hb1
    have haS : a ∉ S := fun h => by rw [ite_eq_left h] at ha0; omega
    have hbS : b ∈ S := by
      by_contra h
      rw [ite_eq_right h] at hb1
      omega
    exact hmono a ha haS b hbS

end Assembly

end ZetaSeven
