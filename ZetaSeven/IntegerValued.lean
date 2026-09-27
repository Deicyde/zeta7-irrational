import Mathlib

open scoped BigOperators

namespace ZetaSeven.IntegerValued

/-!
# Integer-valued polynomial estimates

Two integer-valued-polynomial facts imported from the predecessor paper
(Fauzan `zeta(5)`, Section 3.3), used by the Zeta 7 small-prime proof
(Lemma 3.8):

* **(F1)** Lipschitz-type bound: for integer-valued `A` of degree `d`,
  `v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1,d)⌋`
  (`lipschitz_poly`). Proof via binomial-basis expansion (forward
  differences) and Vandermonde's identity.
* **(F2)** Bound on `v_p` of the Bernoulli functional applied to such
  polynomials (`Lval_bound`, `bernoulli_L_bound_Z7`,
  `bernoulli_L_bound_Z5`). The functional is defined directly on
  binomial-coefficient sequences; `Lval_basis` shows it takes the value
  `(-1)^k / (k+1)` on basis elements, matching the predecessor's
  generating identity `L((1+z)^x) = log(1+z)/z`.

These are project-authored bridging lemmas adapted from the cited
predecessor argument. Inputs are natural numbers (the `ℤ_p` version is
left to the small-prime node, which needs `p`-adic continuity).
-/

section BinomialPoly

/-- Descending factorial polynomial `∏_{i<k} (X - i)`. -/
def descPoly (k : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (i : ℚ))

/-- Binomial polynomial `C(X, k)`. -/
def binomPoly (k : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial k : ℚ))⁻¹ * descPoly k

theorem descPoly_succ (k : ℕ) :
    descPoly (k + 1) = descPoly k * (Polynomial.X - Polynomial.C (k : ℚ)) := by
  sorry

theorem binomPoly_succ (k : ℕ) :
    Polynomial.C ((k : ℚ) + 1) * binomPoly (k + 1)
      = binomPoly k * (Polynomial.X - Polynomial.C (k : ℚ)) := by
  sorry

theorem binomPoly_mul_X_sub (m : ℕ) (t : ℚ) :
    binomPoly m * (Polynomial.X - Polynomial.C t)
      = Polynomial.C ((m : ℚ) + 1) * binomPoly (m + 1)
        + Polynomial.C ((m : ℚ) - t) * binomPoly m := by
  sorry

theorem eval_binomPoly (k n : ℕ) :
    (binomPoly k).eval (n : ℚ) = (Nat.choose n k : ℚ) := by
  sorry

theorem natDegree_binomPoly_le (k : ℕ) : (binomPoly k).natDegree ≤ k := by
  sorry

theorem derivative_C_mul_aux (c : ℚ) (P : Polynomial ℚ) :
    (Polynomial.C c * P).derivative = Polynomial.C c * P.derivative := by
  sorry

theorem coeff_split (k j : ℕ) :
    ((k : ℚ) + 1) * (((-1 : ℚ) ^ j) / ((j : ℚ) + 1))
      = ((k : ℚ) - (j : ℚ)) * (((-1 : ℚ) ^ j) / ((j : ℚ) + 1)) + (-1 : ℚ) ^ j := by
  sorry

theorem derivative_binomPoly (k : ℕ) :
    (binomPoly k).derivative
      = ∑ j ∈ Finset.range k,
        Polynomial.C (((-1 : ℚ) ^ j) / ((j : ℚ) + 1)) * binomPoly (k - 1 - j) := by
  sorry

end BinomialPoly

section FwdDiff

/-- Forward difference operator on rational sequences. -/
def fwdDiff (f : ℕ → ℚ) : ℕ → ℚ := fun n => f (n + 1) - f n

/-- Iterated forward difference. -/
def fwdDiffIter (f : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => f
  | k + 1 => fwdDiff (fwdDiffIter f k)

theorem fwdDiffIter_zero (f : ℕ → ℚ) : fwdDiffIter f 0 = f :=
  rfl

theorem fwdDiffIter_succ (f : ℕ → ℚ) (k : ℕ) :
    fwdDiffIter f (k + 1) = fwdDiff (fwdDiffIter f k) :=
  rfl

theorem fwdDiffIter_fwdDiff (f : ℕ → ℚ) (k n : ℕ) :
    fwdDiffIter (fwdDiff f) k n = fwdDiffIter f (k + 1) n := by
  sorry

/-- Peel the `0` term off a `range` sum. -/
theorem sum_range_succ_zero (M : Type*) [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i = f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  sorry

/-- Newton forward interpolation for sequences. -/
theorem newton_seq (f : ℕ → ℚ) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (n + 1), fwdDiffIter f k 0 * (Nat.choose n k : ℚ) := by
  sorry

theorem fwdDiffIter_int (f : ℕ → ℚ) (hf : ∀ n, ∃ m : ℤ, f n = (m : ℚ)) (k n : ℕ) :
    ∃ m : ℤ, fwdDiffIter f k n = (m : ℚ) := by
  sorry

/-- Extend a `range k` sum to a `range N` sum with an indicator. -/
theorem sum_range_le (M : Type*) [AddCommMonoid M] (f : ℕ → M) (k N : ℕ) (hk : k ≤ N) :
    ∑ i ∈ Finset.range k, f i
      = ∑ i ∈ Finset.range N, (if i < k then f i else 0) := by
  sorry

end FwdDiff

section Expansion

/-- A polynomial over ℚ is integer-valued (on ℕ) if all values at naturals are integers. -/
def IntValued (A : Polynomial ℚ) : Prop :=
  ∀ n : ℕ, ∃ m : ℤ, A.eval (n : ℚ) = (m : ℚ)

/-- Binomial-basis expansion of any polynomial of degree `≤ d`. -/
theorem binomial_expansion (A : Polynomial ℚ) (d : ℕ) (hdeg : A.natDegree ≤ d) :
    A = ∑ k ∈ Finset.range (d + 1),
      Polynomial.C (fwdDiffIter (fun m => A.eval (m : ℚ)) k 0) * binomPoly k := by
  sorry

theorem expansion_coeff_int (A : Polynomial ℚ) (hA : IntValued A) (k : ℕ) :
    ∃ m : ℤ, fwdDiffIter (fun m => A.eval (m : ℚ)) k 0 = (m : ℚ) := by
  sorry

end Expansion

section LcmBound

variable {p : ℕ} (hp : p.Prime)

/-- Uniform denominator: lcm of `{1, ..., N}`. -/
def lcmRange (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).lcm id

theorem mem_lcmRange_dvd (N m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ N) : m ∣ lcmRange N := by
  sorry

theorem lcmRange_dvd_pow_mul (N : ℕ) (hN : 1 ≤ N) :
    lcmRange N ∣ p ^ Nat.log p N * ∏ m ∈ Finset.Icc 1 N, (m / p ^ padicValNat p m) := by
  sorry

theorem lcmRange_ne_zero (N : ℕ) (hN : 1 ≤ N) : lcmRange N ≠ 0 := by
  sorry

theorem not_dvd_pfree (m : ℕ) (hm : m ≠ 0) : ¬ p ∣ m / p ^ padicValNat p m := by
  sorry

theorem not_dvd_prod_pfree (N : ℕ) :
    ¬ p ∣ ∏ m ∈ Finset.Icc 1 N, (m / p ^ padicValNat p m) := by
  sorry

theorem lcmRange_valuation (N : ℕ) (hN : 1 ≤ N) :
    padicValNat p (lcmRange N) ≤ Nat.log p N := by
  sorry

end LcmBound

section Lipschitz

variable {p : ℕ} (hp : p.Prime)

/-- Value of a binomial-coefficient sum at a point, as an integer. -/
def binomSum (a : ℕ → ℤ) (d x : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (d + 1), a k * (Nat.choose x k : ℤ)

theorem padicValInt_neg (a : ℤ) : padicValInt p (-a) = padicValInt p a := by
  sorry

/-- Vandermonde difference identity (integer form). -/
theorem vandermonde_diff (y n k : ℕ) :
    (Nat.choose (y + n) k : ℤ) - (Nat.choose y k : ℤ)
      = ∑ t ∈ Finset.range k,
        (Nat.choose y (k - (t + 1)) : ℤ) * (Nat.choose n (t + 1) : ℤ) := by
  sorry

theorem dvd_clear_denom_choose (d n : ℕ) (hn : 1 ≤ n) (y k : ℕ) (hk1 : 1 ≤ k)
    (hkd : k ≤ d) :
    (n : ℤ) ∣ (lcmRange d : ℤ)
      * ((Nat.choose (y + n) k : ℤ) - (Nat.choose y k : ℤ)) := by
  sorry

/-- (F1), sequence level, ordered inputs. -/
theorem lipschitz_seq_aux (a : ℕ → ℤ) (d x y : ℕ) (hlt : y < x) (hd : 1 ≤ d)
    (hne : binomSum a d x ≠ binomSum a d y) :
    padicValInt p ((x : ℤ) - (y : ℤ))
      ≤ padicValInt p (binomSum a d x - binomSum a d y) + Nat.log p d := by
  sorry

/-- (F1), sequence level. -/
theorem lipschitz_seq (a : ℕ → ℤ) (d x y : ℕ)
    (hne : binomSum a d x ≠ binomSum a d y) :
    padicValInt p ((x : ℤ) - (y : ℤ))
      ≤ padicValInt p (binomSum a d x - binomSum a d y) + Nat.log p (max 1 d) := by
  sorry

/-- (F1): Lipschitz-type bound for integer-valued polynomials. -/
theorem lipschitz_poly (A : Polynomial ℚ) (hA : IntValued A) (d x y : ℕ)
    (hdeg : A.natDegree ≤ d)
    (hne : A.eval (x : ℚ) ≠ A.eval (y : ℚ)) :
    ∃ m : ℤ, (m : ℚ) = A.eval (x : ℚ) - A.eval (y : ℚ)
      ∧ padicValInt p ((x : ℤ) - (y : ℤ)) ≤ padicValInt p m + Nat.log p (max 1 d) := by
  sorry

end Lipschitz

section Bernoulli

variable {p : ℕ} (hp : p.Prime)

/-- One step of binomial-coefficient differentiation. -/
def derivCoeffs (d : ℕ) (a : ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (d + 1),
    (if i < k then a k * (((-1 : ℚ) ^ (k - i - 1)) / ((k - i : ℕ) : ℚ)) else 0)

/-- Iterated coefficient differentiation. -/
def derivIter (d : ℕ) (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => a
  | r + 1 => derivCoeffs d (derivIter d a r)

theorem derivIter_zero (d : ℕ) (a : ℕ → ℚ) : derivIter d a 0 = a :=
  rfl

theorem derivIter_succ (d : ℕ) (a : ℕ → ℚ) (r : ℕ) :
    derivIter d a (r + 1) = derivCoeffs d (derivIter d a r) :=
  rfl

theorem derivative_expansion (d : ℕ) (a : ℕ → ℚ) :
    (∑ k ∈ Finset.range (d + 1), Polynomial.C (a k) * binomPoly k).derivative
      = ∑ i ∈ Finset.range (d + 1), Polynomial.C (derivCoeffs d a i) * binomPoly i := by
  sorry

/-- Iterated polynomial differentiation. -/
def polyDerivIter (P : Polynomial ℚ) : ℕ → Polynomial ℚ
  | 0 => P
  | r + 1 => (polyDerivIter P r).derivative

theorem polyDerivIter_zero (P : Polynomial ℚ) : polyDerivIter P 0 = P :=
  rfl

theorem polyDerivIter_succ (P : Polynomial ℚ) (r : ℕ) :
    polyDerivIter P (r + 1) = (polyDerivIter P r).derivative :=
  rfl

theorem derivIter_correct (d : ℕ) (a : ℕ → ℚ) (r : ℕ) :
    polyDerivIter (∑ k ∈ Finset.range (d + 1), Polynomial.C (a k) * binomPoly k) r
      = ∑ i ∈ Finset.range (d + 1), Polynomial.C (derivIter d a r i) * binomPoly i := by
  sorry

theorem derivCoeffs_scaled (d : ℕ) (S : ℚ) (b : ℕ → ℚ)
    (hb : ∀ k, ∃ m : ℤ, (m : ℚ) = S * b k) (i : ℕ) :
    ∃ m : ℤ, (m : ℚ) = S * (lcmRange (d + 1) : ℚ) * derivCoeffs d b i := by
  sorry

theorem derivIter_scaled (d : ℕ) (S : ℚ) (b : ℕ → ℚ)
    (hb : ∀ k, ∃ m : ℤ, (m : ℚ) = S * b k) (r i : ℕ) :
    ∃ m : ℤ, (m : ℚ) = S * ((lcmRange (d + 1) : ℚ) ^ r) * derivIter d b r i := by
  sorry

/-- The Bernoulli functional on binomial-coefficient sequences. -/
def Lval (d : ℕ) (b : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range (d + 1), b i * (((-1 : ℚ) ^ i) / ((i + 1 : ℕ) : ℚ))

theorem Lval_integral (d : ℕ) (S : ℚ) (b : ℕ → ℚ)
    (hb : ∀ i, ∃ m : ℤ, (m : ℚ) = S * b i) :
    ∃ m : ℤ, (m : ℚ) = S * (lcmRange (d + 1) : ℚ) * Lval d b := by
  sorry

theorem padicValRat_zero : padicValRat p (0 : ℚ) = 0 := by
  sorry

/-- (F2) master bound. -/
theorem Lval_bound (d : ℕ) (c : ℕ → ℤ) (B r : ℕ) :
    -(B : ℤ) - ((r + 1 : ℕ) : ℤ) * (Nat.log p (d + 1) : ℤ)
      ≤ padicValRat p (Lval d (derivIter d (fun k => (c k : ℚ) / (p : ℚ) ^ B) r)) := by
  sorry

/-- (F2) for Zeta 7 (`r = 5`, `/720`). CORRECTED constant `6⌊log⌋`; see report. -/
theorem bernoulli_L_bound_Z7 (d : ℕ) (c : ℕ → ℤ) (B : ℕ) :
    -(B : ℤ) - 6 * (Nat.log p (d + 1) : ℤ) - padicValRat p (720 : ℚ)
      ≤ padicValRat p (Lval d (derivIter d (fun k => (c k : ℚ) / (p : ℚ) ^ B) 5) / 720) := by
  sorry

/-- (F2) for the predecessor (`r = 4`, `/24`). CORRECTED constant `5⌊log⌋`; see report. -/
theorem bernoulli_L_bound_Z5 (d : ℕ) (c : ℕ → ℤ) (B : ℕ) :
    -(B : ℤ) - 5 * (Nat.log p (d + 1) : ℤ) - padicValRat p (24 : ℚ)
      ≤ padicValRat p (Lval d (derivIter d (fun k => (c k : ℚ) / (p : ℚ) ^ B) 4) / 24) := by
  sorry

theorem newton_coeff_binomPoly (k j : ℕ) :
    fwdDiffIter (fun n => (binomPoly k).eval (n : ℚ)) j 0
      = (if j = k then (1 : ℚ) else 0) := by
  sorry

/-- `Lval` takes the value `(-1)^k / (k+1)` on binomial basis elements. -/
theorem Lval_basis (d k : ℕ) (hk : k ≤ d) :
    Lval d (fun i => fwdDiffIter (fun n => (binomPoly k).eval (n : ℚ)) i 0)
      = ((-1 : ℚ) ^ k) / ((k + 1 : ℕ) : ℚ) := by
  sorry

end Bernoulli

end ZetaSeven.IntegerValued
