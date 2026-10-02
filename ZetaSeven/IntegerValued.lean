import Mathlib

/-!
# Integer-valued polynomial estimates (Zeta 7, Lemma 3.8 prerequisites)

This file proves the two integer-valued-polynomial facts imported from the
predecessor paper's Section 3.3, as used in the proof of Zeta 7 Lemma 3.8
(`Small-prime estimate`):

* **(I1)** `intValued_lipschitz`: for integer-valued `A` of degree `≤ d`,
  `v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1,d)⌋`.
* **(I2)** `bernoulli_functional_bound`: for `P` with values in `p⁻ᴬℤ_p`
  and `deg P ≤ d`, `v_p(L(P)) ≥ -A - 5*⌊log_p(d+1)⌋ - v_p(720)`,
  where `L` is the Bernoulli functional `L(C(x,k)) = (-1)^k/(k+1)`.
* **Derivative loss** `deriv_loss`: the `r`-th derivative of `C(x,k)` is
  integer-valued up to a loss of `r*⌊log_p(d+1)⌋` (used with `r = 5`).

## Formalization strategy

Mathlib's `p`-adic API is over `ℕ`, so everything is phrased
valuation-theoretically over `ℚ`: polynomials are represented by their
binomial-basis coefficient functions `c : ℕ → ℚ`, and "integer-valued of
degree `≤ d`" becomes "`∀ k ≤ d, v_p(c k) ≥ 0`" via `padicValRat`.
Evaluation is on `ℕ` (`evalBinom`), where `Nat.choose` identities and
Vandermonde (`Nat.add_choose_eq`) apply directly.

Two documented gaps between these `ℕ`/`ℚ` shadows and the `ℤ_p` statements:
(i) the step "values in `p⁻ᴬℤ_p` imply binomial coefficients have
`v_p ≥ -A`" (forward differences at `0`, needs `ℤ_p` API) is taken as the
hypothesis `hc`; (ii) `intValued_lipschitz` requires the evaluated
difference to be nonzero, since `padicValRat p 0 = 0` (junk value) while the
true valuation of `0` is `+∞` (e.g. constant `A` with `v_p(t)` large would
otherwise be a false instance).

Note on the constant in (I2): the literal finite-sum bound
`v_p(Σ c_k (-1)^k/(k+1)) ≥ -A - ⌊log_p(d+1)⌋` (factor 1) is proved and then
weakened to the stated factor-5-plus-`v_p(720)` form. The factor 5 in the
paper comes from the five derivatives in `τ(P) = L(P⁽⁵⁾)/720` via
`deriv_loss_five`; the full `τ`-bound with constant exactly 5 needs a
cancellation argument beyond naive per-term counting (which gives 6) and is
not attempted here. It is numerically verified (see `/tmp/intvalued_probe.py`
run during development) that the factor-5 `τ`-bound holds on basis elements
for `p ∈ {2,3,5}`, `d ≤ 29`, and that (I1) holds and is sharp.
-/

namespace ZetaSeven.IntegerValued

open Finset
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- Binomial-basis evaluation on `ℕ`: `A(m) = Σ_{k ≤ d} c_k * C(m,k)`. -/
noncomputable def evalBinom (c : ℕ → ℚ) (d : ℕ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (d + 1), c k * (m.choose k : ℚ)

/-- The Bernoulli functional on a binomial expansion:
`L(P) = Σ_{k ≤ d} c_k * (-1)^k/(k+1)`. -/
noncomputable def bernFunctional (c : ℕ → ℚ) (d : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (d + 1), c k * ((-1 : ℚ) ^ k / ((k : ℚ) + 1))

/-- The binomial-basis polynomial `C(X,k)` over `ℚ`. -/
noncomputable def binomPoly (k : ℕ) : Polynomial ℚ :=
  (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (i : ℚ)))
    * Polynomial.C ((Nat.factorial k : ℚ)⁻¹)

/-- `r! * [X^r]C(X,i)`: the `r`-th derivative of `C(X,i)` at `0`. -/
noncomputable def derivCoeff (r i : ℕ) : ℚ :=
  (Nat.factorial r : ℚ) * (binomPoly i).coeff r

/-- The cofactor sum from the Vandermonde difference:
`C(n+t,k) - C(n,k) = t * vandermondeQuot n t k` (for `t ≥ 1`). -/
noncomputable def vandermondeQuot (n t k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    ((n.choose i * (t - 1).choose (k - i - 1) : ℕ) : ℚ) / ((k - i : ℕ) : ℚ)

section ValuationHelpers

/-- Finite-sum ultrametric bound over `ℚ` for nonpositive `B`
(no nonvanishing hypothesis needed since `padicValRat p 0 = 0 ≥ B`). -/
theorem padicValRat_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℤ)
    (hB : B ≤ 0) (h : ∀ i ∈ s, B ≤ padicValRat p (f i)) :
    B ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa [padicValRat.zero] using hB
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    by_cases hsum : f a + ∑ i ∈ s, f i = 0
    · rw [hsum, padicValRat.zero]
      exact hB
    · have h1 : B ≤ padicValRat p (f a) := h a (Finset.mem_insert_self a s)
      have h2 : B ≤ padicValRat p (∑ i ∈ s, f i) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hmin := le_trans (min_le_min h1 h2) (padicValRat.min_le_padicValRat_add hsum)
      simpa using hmin

/-- Finite-product lower bound over `ℚ` for `B₁ + B₂ ≤ 0`. -/
theorem padicValRat_mul_ge (a b : ℚ) (B₁ B₂ : ℤ)
    (ha : B₁ ≤ padicValRat p a) (hb : B₂ ≤ padicValRat p b)
    (hB : B₁ + B₂ ≤ 0) :
    B₁ + B₂ ≤ padicValRat p (a * b) := by
  by_cases hab : a * b = 0
  · rw [hab, padicValRat.zero]
    exact hB
  · have ha' : a ≠ 0 := fun h => hab (by simp [h])
    have hb' : b ≠ 0 := fun h => hab (by simp [h])
    rw [padicValRat.mul ha' hb']
    exact add_le_add ha hb

/-- Dividing a `p`-integral rational by a positive natural. -/
theorem padicValRat_div_int_ge (a : ℚ) (j : ℕ) (hj : 1 ≤ j)
    (ha : 0 ≤ padicValRat p a) :
    -((padicValNat p j : ℕ) : ℤ) ≤ padicValRat p (a / (j : ℚ)) := by
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  by_cases ha0 : a = 0
  · rw [ha0, zero_div, padicValRat.zero]
    have hnn : (0 : ℤ) ≤ ((padicValNat p j : ℕ) : ℤ) := by positivity
    linarith
  · rw [padicValRat.div ha0 hj0, padicValRat.of_nat]
    linarith [ha]

/-- `v_p(m) ≤ ⌊log_p d⌋` for `1 ≤ m ≤ d`. -/
theorem padicValNat_le_log_of_le (m d : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) :
    ((padicValNat p m : ℕ) : ℤ) ≤ (Nat.log p d : ℤ) := by
  have h := le_trans (padicValNat_le_nat_log (p := p) m) (Nat.log_mono_right hmd)
  have _ : Fact p.Prime := inferInstance
  have _ := hm
  exact_mod_cast h

end ValuationHelpers

section Vandermonde

/-- Absorption identity: `j * C(t,j) = t * C(t-1,j-1)`. -/
theorem choose_absorb (t j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t) :
    j * t.choose j = t * (t - 1).choose (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [mul_comm (k + 1) _]
  exact (Nat.add_one_mul_choose_eq n k).symm

/-- Vandermonde difference identity (via `Nat.add_choose_eq`). -/
theorem vandermonde_diff (n t k : ℕ) (ht : 1 ≤ t) :
    ((n + t).choose k : ℚ) - (n.choose k : ℚ)
      = (t : ℚ) * vandermondeQuot n t k := by
  have hsum : ((n + t).choose k : ℚ)
      = (∑ i ∈ Finset.range k, ((n.choose i * t.choose (k - i) : ℕ) : ℚ))
        + (n.choose k : ℚ) := by
    have h1 : (n + t).choose k
        = ∑ i ∈ Finset.range (k + 1), n.choose i * t.choose (k - i) := by
      have h0 := Nat.add_choose_eq n t k
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h0
      exact h0
    rw [h1]
    push_cast
    rw [Finset.sum_range_succ]
    congr 1
    simp [Nat.choose_zero_right]
  have hterm : ∀ i ∈ Finset.range k,
      ((n.choose i * t.choose (k - i) : ℕ) : ℚ)
        = (t : ℚ) * ((((n.choose i * (t - 1).choose (k - i - 1) : ℕ)) : ℚ)
          / ((k - i : ℕ) : ℚ)) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hji : 1 ≤ k - i := by omega
    have hne : ((k - i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : k - i ≠ 0)
    by_cases hle : k - i ≤ t
    · have habs := choose_absorb t (k - i) hji hle
      have habsQ := congrArg (Nat.cast : ℕ → ℚ) habs
      push_cast at habsQ
      have hsingle : ((t.choose (k - i) : ℕ) : ℚ)
          = (t : ℚ) * ((((t - 1).choose (k - i - 1) : ℕ)) : ℚ)
            / ((k - i : ℕ) : ℚ) := by
        field_simp [hne]
        linear_combination habsQ
      calc ((n.choose i * t.choose (k - i) : ℕ) : ℚ)
          = (n.choose i : ℚ) * (t.choose (k - i) : ℚ) := Nat.cast_mul _ _
        _ = (n.choose i : ℚ) * ((t : ℚ)
              * ((((t - 1).choose (k - i - 1) : ℕ)) : ℚ) / ((k - i : ℕ) : ℚ)) := by
            rw [hsingle]
        _ = (t : ℚ) * ((((n.choose i * (t - 1).choose (k - i - 1) : ℕ)) : ℚ)
            / ((k - i : ℕ) : ℚ)) := by push_cast; ring
    · have h1 : t.choose (k - i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : (t - 1).choose (k - i - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h1, h2]
      simp
  rw [hsum, add_sub_cancel_right]
  unfold vandermondeQuot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hterm

/-- Valuation bound on the Vandermonde cofactor sum. -/
theorem padicValRat_vandermondeQuot_ge (d n t k : ℕ) (hk : k ≤ d) :
    -((Nat.log p (max 1 d) : ℕ) : ℤ)
      ≤ padicValRat p (vandermondeQuot n t k) := by
  have hlog : (0 : ℤ) ≤ ((Nat.log p (max 1 d) : ℕ) : ℤ) := by positivity
  unfold vandermondeQuot
  apply padicValRat_le_sum
  · linarith
  · intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hji : 1 ≤ k - i := by omega
    have h1 := padicValRat_div_int_ge (p := p)
      (((n.choose i * (t - 1).choose (k - i - 1) : ℕ)) : ℚ) (k - i) hji
      (zero_le_padicValRat_of_nat _)
    have h2 := padicValNat_le_log_of_le (p := p) (k - i) (max 1 d) hji (by omega)
    linarith [h1, h2]

/-- (I1) Lipschitz-type bound for integer-valued polynomials (3.8).
The difference is required to be nonzero (see file docstring). -/
theorem intValued_lipschitz (d : ℕ) (c : ℕ → ℚ)
    (hc : ∀ k ∈ Finset.range (d + 1), 0 ≤ padicValRat p (c k))
    (n t : ℕ) (hne : evalBinom c d (n + t) - evalBinom c d n ≠ 0) :
    padicValRat p (t : ℚ) - ((Nat.log p (max 1 d) : ℕ) : ℤ)
      ≤ padicValRat p (evalBinom c d (n + t) - evalBinom c d n) := by
  have hlog : (0 : ℤ) ≤ ((Nat.log p (max 1 d) : ℕ) : ℤ) := by positivity
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [Nat.add_zero, sub_self] at hne
    exact (hne rfl).elim
  · have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
    have hdiff : evalBinom c d (n + t) - evalBinom c d n
        = ∑ k ∈ Finset.range (d + 1), c k * ((t : ℚ) * vandermondeQuot n t k) := by
      unfold evalBinom
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_sub, vandermonde_diff n t k ht]
    have hfactor : (∑ k ∈ Finset.range (d + 1), c k * ((t : ℚ) * vandermondeQuot n t k))
        = (t : ℚ) * ∑ k ∈ Finset.range (d + 1), c k * vandermondeQuot n t k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hdiff, hfactor]
    have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht0
    have hne' : (t : ℚ) * ∑ k ∈ Finset.range (d + 1), c k * vandermondeQuot n t k ≠ 0 := by
      rw [← hfactor, ← hdiff]
      exact hne
    have hS0 : ∑ k ∈ Finset.range (d + 1), c k * vandermondeQuot n t k ≠ 0 :=
      fun h => hne' (by simp [h])
    rw [padicValRat.mul htQ hS0]
    have hS : -(((Nat.log p (max 1 d) : ℕ)) : ℤ)
        ≤ padicValRat p (∑ k ∈ Finset.range (d + 1), c k * vandermondeQuot n t k) := by
      apply padicValRat_le_sum
      · linarith
      · intro k hk
        have hc0 := hc k hk
        have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
        have hV := padicValRat_vandermondeQuot_ge (p := p) d n t k hkd
        have h := padicValRat_mul_ge (c k) (vandermondeQuot n t k) 0
          (-(((Nat.log p (max 1 d) : ℕ)) : ℤ)) hc0 hV (by linarith)
        simpa using h
    linarith [hS]

end Vandermonde

section Bernoulli

/-- (I2) Bernoulli-functional bound, adapted (3.9): factor 5, `v_p(720)`. -/
theorem bernoulli_functional_bound (d A : ℕ) (c : ℕ → ℚ)
    (hc : ∀ k ∈ Finset.range (d + 1), -((A : ℤ)) ≤ padicValRat p (c k)) :
    -((A : ℤ)) - 5 * ((Nat.log p (d + 1) : ℕ) : ℤ)
        - padicValRat p ((720 : ℕ) : ℚ)
      ≤ padicValRat p (bernFunctional c d) := by
  have hA : (0 : ℤ) ≤ ((A : ℕ) : ℤ) := by positivity
  have hL : (0 : ℤ) ≤ ((Nat.log p (d + 1) : ℕ) : ℤ) := by positivity
  have h720 : (0 : ℤ) ≤ padicValRat p ((720 : ℕ) : ℚ) := zero_le_padicValRat_of_nat 720
  have _ : Fact p.Prime := inferInstance
  have hU : ∀ k ∈ Finset.range (d + 1),
      -(((Nat.log p (d + 1) : ℕ)) : ℤ)
        ≤ padicValRat p ((-1 : ℚ) ^ k / ((k : ℚ) + 1)) := by
    intro k hk
    have hcast : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := (Nat.cast_add_one k).symm
    rw [hcast]
    have hneg1 : padicValRat p (-1 : ℚ) = 0 := by
      rw [padicValRat.neg, padicValRat.one]
    have hpow : padicValRat p ((-1 : ℚ) ^ k) = 0 := by
      rw [padicValRat.pow, hneg1, mul_zero]
    have hdiv := padicValRat_div_int_ge ((-1 : ℚ) ^ k) (k + 1)
      (Nat.le_add_left 1 k) (le_of_eq hpow.symm)
    have hle := padicValNat_le_log_of_le (p := p) (k + 1) (d + 1)
      (Nat.le_add_left 1 k) (by have := Finset.mem_range.mp hk; omega)
    linarith [hdiv, hle]
  have hmain : -((A : ℤ)) - (((Nat.log p (d + 1) : ℕ)) : ℤ)
      ≤ padicValRat p (bernFunctional c d) := by
    unfold bernFunctional
    apply padicValRat_le_sum
    · linarith
    · intro k hk
      have hck := hc k hk
      have huk := hU k hk
      have h := padicValRat_mul_ge (c k) ((-1 : ℚ) ^ k / ((k : ℚ) + 1))
        (-((A : ℤ))) (-(((Nat.log p (d + 1) : ℕ)) : ℤ)) hck huk (by linarith)
      rw [sub_eq_add_neg]
      exact h
  linarith [hmain]

end Bernoulli

section DerivLoss

/-- `(j+1) * B(j+1) = (X - j) * B(j)`. -/
theorem binomPoly_succ_mul (j : ℕ) :
    Polynomial.C ((j : ℚ) + 1) * binomPoly (j + 1)
      = (Polynomial.X - Polynomial.C (j : ℚ)) * binomPoly j := by
  have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have hjf : (((Nat.factorial j : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hC : Polynomial.C ((j : ℚ) + 1)
        * Polynomial.C ((((j : ℚ) + 1) * ((Nat.factorial j : ℕ) : ℚ))⁻¹)
      = Polynomial.C ((((Nat.factorial j : ℕ) : ℚ))⁻¹) := by
    rw [← Polynomial.C_mul]
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hj1, one_mul]
  unfold binomPoly
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  linear_combination
    (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℚ)))
      * (Polynomial.X - Polynomial.C (j : ℚ)) * hC

/-- Shift identity: `B(j) ∘ (X - 1) = Σ_s (-1)^{j-s} B(s)`. -/
theorem binomPoly_comp_X_sub_one (j : ℕ) :
    (binomPoly j).comp (Polynomial.X - 1)
      = ∑ s ∈ Finset.range (j + 1),
          Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s := by
  have main : ∀ j, ((binomPoly j).comp (Polynomial.X - 1)
        = ∑ s ∈ Finset.range (j + 1),
            Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s)
      ∧ (Polynomial.X * (∑ s ∈ Finset.range (j + 1),
            Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s)
        = Polynomial.C (((j + 1 : ℕ)) : ℚ) * binomPoly (j + 1)) := by
    intro j
    induction j with
    | zero =>
      constructor <;> simp [binomPoly]
    | succ j ih =>
      obtain ⟨ihF, ihX⟩ := ih
      have hcast : ((j : ℚ) + 1) = (((j + 1 : ℕ)) : ℚ) := (Nat.cast_add_one j).symm
      have hGrec : (∑ s ∈ Finset.range (j + 1 + 1),
            Polynomial.C ((-1 : ℚ) ^ (j + 1 - s)) * binomPoly s)
          = binomPoly (j + 1) - (∑ s ∈ Finset.range (j + 1),
            Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s) := by
        rw [Finset.sum_range_succ]
        have hlast : Polynomial.C ((-1 : ℚ) ^ (j + 1 - (j + 1))) * binomPoly (j + 1)
            = binomPoly (j + 1) := by
          rw [Nat.sub_self, pow_zero, Polynomial.C_1, one_mul]
        have hneg : (∑ s ∈ Finset.range (j + 1),
              Polynomial.C ((-1 : ℚ) ^ (j + 1 - s)) * binomPoly s)
            = -(∑ s ∈ Finset.range (j + 1),
              Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro s hs
          have hsj : s ≤ j := by have := Finset.mem_range.mp hs; omega
          have hexp : j + 1 - s = (j - s) + 1 := by omega
          have hCm1 : Polynomial.C (-1 : ℚ) = -1 := by
            rw [Polynomial.C_neg, Polynomial.C_1]
          rw [hexp, pow_succ, Polynomial.C_mul, hCm1]
          ring
        rw [hlast, hneg]
        ring
      have hF : Polynomial.C (((j + 1 : ℕ)) : ℚ)
            * (binomPoly (j + 1)).comp (Polynomial.X - 1)
          = (Polynomial.X - Polynomial.C (((j + 1 : ℕ)) : ℚ))
            * (binomPoly j).comp (Polynomial.X - 1) := by
        have hsm := binomPoly_succ_mul j
        have hFc := congrArg (fun P => P.comp (Polynomial.X - 1)) hsm
        simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp,
          Polynomial.X_comp] at hFc
        have hX : (Polynomial.X - 1 - Polynomial.C (j : ℚ))
            = Polynomial.X - Polynomial.C (((j + 1 : ℕ)) : ℚ) := by
          rw [← hcast, Polynomial.C_add, Polynomial.C_1]
          ring
        rw [hcast, hX] at hFc
        exact hFc
      have hcancel : Polynomial.C (((j + 1 : ℕ)) : ℚ) ≠ 0 := by
        have h1 : (((j + 1 : ℕ)) : ℚ) ≠ 0 := by positivity
        exact mt Polynomial.C_eq_zero.mp h1
      have goal1 : (binomPoly (j + 1)).comp (Polynomial.X - 1)
          = ∑ s ∈ Finset.range (j + 1 + 1),
              Polynomial.C ((-1 : ℚ) ^ (j + 1 - s)) * binomPoly s := by
        apply mul_left_cancel₀ hcancel
        rw [hF, hGrec, ihF]
        linear_combination ihX
      have hsm2 := binomPoly_succ_mul (j + 1)
      have hcast2 : (((j + 1 : ℕ)) : ℚ) + 1 = (((j + 1 + 1 : ℕ)) : ℚ) :=
        (Nat.cast_add_one (j + 1)).symm
      rw [hcast2] at hsm2
      have goal2 : Polynomial.X * (∑ s ∈ Finset.range (j + 1 + 1),
              Polynomial.C ((-1 : ℚ) ^ (j + 1 - s)) * binomPoly s)
          = Polynomial.C (((j + 1 + 1 : ℕ)) : ℚ) * binomPoly (j + 1 + 1) := by
        rw [hGrec]
        linear_combination -hsm2 - ihX
      exact ⟨goal1, goal2⟩
  exact (main j).1

/-- `i * B(i) = X * (B(i-1) ∘ (X-1))` for `i ≥ 1`. -/
theorem binomPoly_quot_comp (i : ℕ) (hi : 1 ≤ i) :
    Polynomial.C (i : ℚ) * binomPoly i
      = Polynomial.X * (binomPoly (i - 1)).comp (Polynomial.X - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hprod : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℚ),
      (∏ x ∈ s, f x).comp (Polynomial.X - 1)
        = ∏ x ∈ s, (f x).comp (Polynomial.X - 1) := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, Polynomial.mul_comp, ih]
  have hfact : ∀ s ∈ Finset.range j,
      (Polynomial.X - Polynomial.C (s : ℚ)).comp (Polynomial.X - 1)
        = Polynomial.X - Polynomial.C ((s : ℚ) + 1) := by
    intro s hs
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      Polynomial.C_add, Polynomial.C_1]
    ring
  have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have hC : Polynomial.C ((j : ℚ) + 1)
        * Polynomial.C ((((j : ℚ) + 1) * ((Nat.factorial j : ℕ) : ℚ))⁻¹)
      = Polynomial.C ((((Nat.factorial j : ℕ) : ℚ))⁻¹) := by
    rw [← Polynomial.C_mul]
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hj1, one_mul]
  have hprod2 : (∏ x ∈ Finset.range j,
        (Polynomial.X - Polynomial.C (x : ℚ)).comp (Polynomial.X - 1))
      = ∏ x ∈ Finset.range j, (Polynomial.X - Polynomial.C ((x : ℚ) + 1)) :=
    Finset.prod_congr rfl hfact
  unfold binomPoly
  rw [Finset.prod_range_succ', Nat.factorial_succ]
  push_cast
  rw [Polynomial.mul_comp, hprod, hprod2]
  simp only [Polynomial.C_comp, Polynomial.C_0, sub_zero]
  linear_combination
    (∏ x ∈ Finset.range j, (Polynomial.X - Polynomial.C ((x : ℚ) + 1)))
      * Polynomial.X * hC

/-- Coefficient recursion for `derivCoeff`. -/
theorem derivCoeff_succ (r i : ℕ) (hi : 1 ≤ i) :
    derivCoeff (r + 1) i = (((r : ℚ) + 1) / (i : ℚ))
      * ∑ s ∈ Finset.range i, (-1 : ℚ) ^ (i - 1 - s) * derivCoeff r s := by
  have hq := binomPoly_quot_comp i hi
  rw [binomPoly_comp_X_sub_one (i - 1)] at hq
  have hi1 : i - 1 + 1 = i := by omega
  rw [hi1] at hq
  have hcoeff := congrArg (fun P => Polynomial.coeff P (r + 1)) hq
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
    Polynomial.finsetSum_coeff] at hcoeff
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hS : (∑ s ∈ Finset.range i,
        (-1 : ℚ) ^ (i - 1 - s) * ((Nat.factorial r : ℚ) * (binomPoly s).coeff r))
      = (Nat.factorial r : ℚ) * ∑ s ∈ Finset.range i,
        (-1 : ℚ) ^ (i - 1 - s) * (binomPoly s).coeff r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  unfold derivCoeff
  rw [Nat.factorial_succ]
  push_cast
  rw [hS, ← hcoeff, div_eq_mul_inv]
  have hinv : (i : ℚ) * (i : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hi0
  linear_combination
    (-(((r : ℚ) + 1) * (Nat.factorial r : ℚ) * (binomPoly i).coeff (r + 1))) * hinv

/-- `D(r+1, 0) = 0`. -/
theorem derivCoeff_succ_zero (r : ℕ) : derivCoeff (r + 1) 0 = 0 := by
  have hB0 : binomPoly 0 = 1 := by simp [binomPoly]
  have hcoeff : (1 : Polynomial ℚ).coeff (r + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_one]; omega)
  unfold derivCoeff
  rw [hB0, hcoeff, mul_zero]

/-- `D(0, i)` is `p`-integral (it is `C(0,i) ∈ {0, 1}`). -/
theorem derivCoeff_zero_ge (i : ℕ) : 0 ≤ padicValRat p (derivCoeff 0 i) := by
  have _ : Fact p.Prime := inferInstance
  rcases eq_or_ne i 0 with rfl | hi
  · have hB0 : binomPoly 0 = 1 := by simp [binomPoly]
    have h1 : (1 : Polynomial ℚ).coeff 0 = 1 := by simp
    have hD : derivCoeff 0 0 = 1 := by
      unfold derivCoeff
      rw [hB0, h1]
      simp
    rw [hD]
    exact le_of_eq padicValRat.one.symm
  · have h0 : (binomPoly i).coeff 0 = 0 := by
      unfold binomPoly
      rw [Polynomial.coeff_mul_C]
      have hP : (∏ s ∈ Finset.range i,
          (Polynomial.X - Polynomial.C (s : ℚ))).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.pos_of_ne_zero hi))
        show (Polynomial.X - Polynomial.C ((0 : ℕ) : ℚ)).eval 0 = 0
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          Nat.cast_zero, sub_zero]
      rw [hP, zero_mul]
    unfold derivCoeff
    rw [h0, mul_zero]
    exact le_of_eq padicValRat.zero.symm

/-- Derivative loss: the `r`-th derivative of `C(X,i)` is integer-valued
up to a loss of `r * ⌊log_p (d+1)⌋`. -/
theorem deriv_loss (d r i : ℕ) (hi : i ≤ d) :
    -((((r * Nat.log p (d + 1) : ℕ))) : ℤ)
      ≤ padicValRat p (derivCoeff r i) := by
  have hL : (0 : ℤ) ≤ (((Nat.log p (d + 1) : ℕ)) : ℤ) := by positivity
  have main : ∀ (r : ℕ) (i : ℕ), i ≤ d →
      -((((r * Nat.log p (d + 1) : ℕ))) : ℤ)
        ≤ padicValRat p (derivCoeff r i) := by
    intro r
    induction r with
    | zero =>
      intro i hi
      simpa using derivCoeff_zero_ge i
    | succ r ih =>
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · rw [derivCoeff_succ_zero, padicValRat.zero]
        have hnn : (0 : ℤ) ≤ (((((r + 1) * Nat.log p (d + 1) : ℕ))) : ℤ) := by
          positivity
        linarith
      · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        rw [derivCoeff_succ r i hi1]
        have hcast : ((r : ℚ) + 1) = (((r + 1 : ℕ)) : ℚ) := (Nat.cast_add_one r).symm
        rw [hcast]
        have hfrac : -(((Nat.log p (d + 1) : ℕ)) : ℤ)
            ≤ padicValRat p ((((r + 1 : ℕ)) : ℚ) / ((i : ℕ) : ℚ)) := by
          have h1 := padicValRat_div_int_ge (p := p) (((r + 1 : ℕ)) : ℚ) i hi1
            (zero_le_padicValRat_of_nat (r + 1))
          have h2 := padicValNat_le_log_of_le (p := p) i (d + 1) hi1 (by omega)
          linarith [h1, h2]
        have hsum : -((((r * Nat.log p (d + 1) : ℕ))) : ℤ)
            ≤ padicValRat p (∑ s ∈ Finset.range i,
              (-1 : ℚ) ^ (i - 1 - s) * derivCoeff r s) := by
          apply padicValRat_le_sum
          · have hnn : (0 : ℤ) ≤ ((((r * Nat.log p (d + 1) : ℕ))) : ℤ) := by
              positivity
            linarith
          · intro s hs
            have hsr : s ≤ d := by have := Finset.mem_range.mp hs; omega
            have ihs := ih s hsr
            have hpow : (0 : ℤ) ≤ padicValRat p ((-1 : ℚ) ^ (i - 1 - s)) := by
              have hneg1 : padicValRat p (-1 : ℚ) = 0 := by
                rw [padicValRat.neg, padicValRat.one]
              have h0 : padicValRat p ((-1 : ℚ) ^ (i - 1 - s)) = 0 := by
                rw [padicValRat.pow, hneg1, mul_zero]
              exact le_of_eq h0.symm
            have h := padicValRat_mul_ge ((-1 : ℚ) ^ (i - 1 - s)) (derivCoeff r s) 0
              (-((((r * Nat.log p (d + 1) : ℕ))) : ℤ)) hpow ihs (by
                have hnn : (0 : ℤ) ≤ ((((r * Nat.log p (d + 1) : ℕ))) : ℤ) := by
                  positivity
                linarith)
            simpa using h
        have hmul := padicValRat_mul_ge ((((r + 1 : ℕ)) : ℚ) / ((i : ℕ) : ℚ))
          (∑ s ∈ Finset.range i, (-1 : ℚ) ^ (i - 1 - s) * derivCoeff r s)
          (-(((Nat.log p (d + 1) : ℕ)) : ℤ)) (-((((r * Nat.log p (d + 1) : ℕ))) : ℤ))
          hfrac hsum (by
            have hnn : (0 : ℤ) ≤ ((((r * Nat.log p (d + 1) : ℕ))) : ℤ) := by
              positivity
            linarith)
        have heq : (-((((r + 1) * Nat.log p (d + 1) : ℕ))) : ℤ)
            = -(((Nat.log p (d + 1) : ℕ)) : ℤ)
              + -((((r * Nat.log p (d + 1) : ℕ))) : ℤ) := by
          push_cast
          ring
        rw [heq]
        exact hmul
  exact main r i hi

/-- Derivative loss at `r = 5` (five derivatives in `τ`). -/
theorem deriv_loss_five (d i : ℕ) (hi : i ≤ d) :
    -(5 * ((Nat.log p (d + 1) : ℕ) : ℤ))
      ≤ padicValRat p (derivCoeff 5 i) := by
  have h := deriv_loss (p := p) d 5 i hi
  have heq : ((((5 * Nat.log p (d + 1) : ℕ))) : ℤ)
      = 5 * (((Nat.log p (d + 1) : ℕ)) : ℤ) := by
    norm_cast
  rw [heq] at h
  exact h

end DerivLoss

-- NOTE (orchestrator): the full `τ`-bound with constant exactly 5
-- (`v_p(τ(P)) ≥ -A - 5*⌊log_p(d+1)⌋ - v_p(720)`) lived here as `tau_bound`
-- with an unproved placeholder. It is out of scope for this node (whose
-- contract is I1, I2,
-- and derivative loss) and needs a cancellation lemma for
-- `L(d^5 B_k)` plus the derivative-expansion identity `d^5 B_k = Σ_j D*B_j`,
-- neither provable from the per-term bounds in this file. Returned to
-- Roadmap: the small-prime-estimate node owns that bound. A numeric probe
-- (`p ∈ {2,3,5}`, `d ≤ 29`, basis elements, zero violations) suggests the
-- factor-5 form holds.

end ZetaSeven.IntegerValued
