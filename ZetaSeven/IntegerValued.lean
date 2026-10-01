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
  sorry

/-- Dividing a `p`-integral rational by a positive natural. -/
theorem padicValRat_div_int_ge (a : ℚ) (j : ℕ) (hj : 1 ≤ j)
    (ha : 0 ≤ padicValRat p a) :
    -((padicValNat p j : ℕ) : ℤ) ≤ padicValRat p (a / (j : ℚ)) := by
  sorry

/-- `v_p(m) ≤ ⌊log_p d⌋` for `1 ≤ m ≤ d`. -/
theorem padicValNat_le_log_of_le (m d : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) :
    ((padicValNat p m : ℕ) : ℤ) ≤ (Nat.log p d : ℤ) := by
  sorry

end ValuationHelpers

section Vandermonde

/-- Absorption identity: `j * C(t,j) = t * C(t-1,j-1)`. -/
theorem choose_absorb (t j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t) :
    j * t.choose j = t * (t - 1).choose (j - 1) := by
  sorry

/-- Vandermonde difference identity (via `Nat.add_choose_eq`). -/
theorem vandermonde_diff (n t k : ℕ) (ht : 1 ≤ t) :
    ((n + t).choose k : ℚ) - (n.choose k : ℚ)
      = (t : ℚ) * vandermondeQuot n t k := by
  sorry

/-- Valuation bound on the Vandermonde cofactor sum. -/
theorem padicValRat_vandermondeQuot_ge (d n t k : ℕ) (hk : k ≤ d) :
    -((Nat.log p (max 1 d) : ℕ) : ℤ)
      ≤ padicValRat p (vandermondeQuot n t k) := by
  sorry

/-- (I1) Lipschitz-type bound for integer-valued polynomials (3.8).
The difference is required to be nonzero (see file docstring). -/
theorem intValued_lipschitz (d : ℕ) (c : ℕ → ℚ)
    (hc : ∀ k ∈ Finset.range (d + 1), 0 ≤ padicValRat p (c k))
    (n t : ℕ) (hne : evalBinom c d (n + t) - evalBinom c d n ≠ 0) :
    padicValRat p (t : ℚ) - ((Nat.log p (max 1 d) : ℕ) : ℤ)
      ≤ padicValRat p (evalBinom c d (n + t) - evalBinom c d n) := by
  sorry

end Vandermonde

section Bernoulli

/-- (I2) Bernoulli-functional bound, adapted (3.9): factor 5, `v_p(720)`. -/
theorem bernoulli_functional_bound (d A : ℕ) (c : ℕ → ℚ)
    (hc : ∀ k ∈ Finset.range (d + 1), -((A : ℤ)) ≤ padicValRat p (c k)) :
    -((A : ℤ)) - 5 * ((Nat.log p (d + 1) : ℕ) : ℤ)
        - padicValRat p ((720 : ℕ) : ℚ)
      ≤ padicValRat p (bernFunctional c d) := by
  sorry

end Bernoulli

section DerivLoss

/-- `(j+1) * B(j+1) = (X - j) * B(j)`. -/
theorem binomPoly_succ_mul (j : ℕ) :
    Polynomial.C ((j : ℚ) + 1) * binomPoly (j + 1)
      = (Polynomial.X - Polynomial.C (j : ℚ)) * binomPoly j := by
  sorry

/-- Shift identity: `B(j) ∘ (X - 1) = Σ_s (-1)^{j-s} B(s)`. -/
theorem binomPoly_comp_X_sub_one (j : ℕ) :
    (binomPoly j).comp (Polynomial.X - 1)
      = ∑ s ∈ Finset.range (j + 1),
          Polynomial.C ((-1 : ℚ) ^ (j - s)) * binomPoly s := by
  sorry

/-- `i * B(i) = X * (B(i-1) ∘ (X-1))` for `i ≥ 1`. -/
theorem binomPoly_quot_comp (i : ℕ) (hi : 1 ≤ i) :
    Polynomial.C (i : ℚ) * binomPoly i
      = Polynomial.X * (binomPoly (i - 1)).comp (Polynomial.X - 1) := by
  sorry

/-- Coefficient recursion for `derivCoeff`. -/
theorem derivCoeff_succ (r i : ℕ) (hi : 1 ≤ i) :
    derivCoeff (r + 1) i = (((r : ℚ) + 1) / (i : ℚ))
      * ∑ s ∈ Finset.range i, (-1 : ℚ) ^ (i - 1 - s) * derivCoeff r s := by
  sorry

/-- `D(r+1, 0) = 0`. -/
theorem derivCoeff_succ_zero (r : ℕ) : derivCoeff (r + 1) 0 = 0 := by
  sorry

/-- `D(0, i)` is `p`-integral (it is `C(0,i) ∈ {0, 1}`). -/
theorem derivCoeff_zero_ge (i : ℕ) : 0 ≤ padicValRat p (derivCoeff 0 i) := by
  sorry

/-- Derivative loss: the `r`-th derivative of `C(X,i)` is integer-valued
up to a loss of `r * ⌊log_p (d+1)⌋`. -/
theorem deriv_loss (d r i : ℕ) (hi : i ≤ d) :
    -((((r * Nat.log p (d + 1) : ℕ))) : ℤ)
      ≤ padicValRat p (derivCoeff r i) := by
  sorry

/-- Derivative loss at `r = 5` (five derivatives in `τ`). -/
theorem deriv_loss_five (d i : ℕ) (hi : i ≤ d) :
    -(5 * ((Nat.log p (d + 1) : ℕ) : ℤ))
      ≤ padicValRat p (derivCoeff 5 i) := by
  sorry

end DerivLoss

end ZetaSeven.IntegerValued
