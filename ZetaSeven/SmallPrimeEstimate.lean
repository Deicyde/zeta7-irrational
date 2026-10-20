import ZetaSeven.TauPullback
import ZetaSeven.MatrixDet
import ZetaSeven.IntegerValued

/-!
# Small-prime estimate (paper Section 3.5, Lemma 3.8, equations (37)-(41))

Prince Anand, "Zeta 7 is Irrational", Section 3.5.

* Lemma 3.8 (37), `small_prime_tau_bound`: for `A ∈ ℚ[x]` integer-valued at `p`
  (`v_p(A(m)) ≥ 0` for every integer `m`) of degree `≤ d` and
  `g = (K!)² A / ∏_{-K ≤ r ≤ K} (x - r)`, every coefficient of `τ_X(g)` has
  `p`-adic valuation `≥ -8⌊log_p max(2K, d+1)⌋ - v_p(720)`. As in
  `ZetaSeven.tau_pullback`, `τ_X(g)` is `tauFunctional P c` for a partial-fraction
  representation `tauRatFunc P c = g` (which exists and is unique).
* (38): the bases `q_i` (`qPoly`) and `f_i` (`fPoly`), with the identities
  `q_i(-x²) = C(x+i, 2i) + C(x+i-1, 2i)` and `D_N(-x²)/(N!)² = C(N-x, N) C(N+x, N)`,
  so that `f_i(-x²)` is integer-valued.
* (39): the triangular transition matrix from `D_N⁴ t^j` to `f_i` and its determinant.
* (40): `F_K = (K!)^{2h} det[μ_X(f_i f_j / D_K)]`.
* (41), `FK_small_prime_bound`: `v^G_p(F_K) ≥ -8h⌊log_p(5K)⌋ - h v_p(720)` at every prime.

## Proof of (37)

The proof follows the paper's decomposition `g = P + ∑_r c_r/(x - r)`. The residue
`c_r = (K!)² A(r) / ((K+r)! (K-r)! (±1))` has valuation `≥ -v_p(C(2K, K)) ≥ -⌊log_p 2K⌋`,
and `v_p(H⁷_{d(r)}) ≥ -7⌊log_p K⌋`. For the polynomial part, the paper's ball argument is
replaced by an equivalent binomial-basis computation: expanding `A` in the basis
`C(x+K, k)` (integer-valued coefficients, by Newton's forward-difference formula), the
quotient by `∏_{|r| ≤ K} (x - r)` is `∑_{k > 2K} a_k (k-2K-1)!/k! · C(x-K-1, k-2K-1)`, and
Legendre's formula gives `v_p((K!)² (k-2K-1)!/k!) ≥ -⌊log_p 2K⌋ - ⌊log_p k⌋`, so
`P(ℤ) ⊂ p^{-L₀-M₀} ℤ_(p)` as in the paper. Finally `τ(C(x, k)) = [x⁶] C(x, k+1)`
(from `L(f(x+1) - f(x)) = f'(0)`), whose valuation is `≥ -6⌊log_p(k+2)⌋ - v_p(720)` by
the derivative loss of the integer-valued estimates; this is the per-term constant `6`,
which the constant `8` absorbs, as the article prescribes.
-/

set_option autoImplicit false

namespace ZetaSeven

open Polynomial

/-- `∏_{-K ≤ r ≤ K} (x - r)`, the denominator of `g` in Lemma 3.8. -/
noncomputable def Wpoly (K : ℕ) : ℚ[X] :=
  ∏ r ∈ Finset.Icc (-(K : ℤ)) K, (X - C (r : ℚ))

namespace SmallPrime

open IntegerValued

variable {p : ℕ} [Fact p.Prime]

/-! ## Valuation helpers -/

theorem le_padicValRat_add' {a b : ℚ} {B : ℤ} (hB : B ≤ 0) (ha : B ≤ padicValRat p a)
    (hb : B ≤ padicValRat p b) : B ≤ padicValRat p (a + b) := by
  by_cases hab : a + b = 0
  · rw [hab, padicValRat.zero]
    exact hB
  · exact le_trans (le_min ha hb) (padicValRat.min_le_padicValRat_add hab)

omit [Fact p.Prime] in
theorem padicValRat_intCast_nonneg (z : ℤ) : 0 ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Nat.cast_nonneg _

theorem padicValRat_div_natCast_ge (a : ℚ) (n : ℕ) {B : ℤ}
    (hB : B - (padicValNat p n : ℤ) ≤ 0) (ha : B ≤ padicValRat p a) :
    B - (padicValNat p n : ℤ) ≤ padicValRat p (a / (n : ℚ)) := by
  by_cases ha0 : a = 0
  · rw [ha0, zero_div, padicValRat.zero]
    exact hB
  by_cases hn : (n : ℚ) = 0
  · rw [hn, div_zero, padicValRat.zero]
    exact hB
  rw [padicValRat.div ha0 hn, padicValRat.of_nat]
  linarith

/-! ## Legendre-type factorial bounds -/

theorem succ_add_div_le (a b q : ℕ) (hq : 0 < q) : (a + b + 1) / q ≤ a / q + b / q + 1 := by
  have ha := Nat.lt_mul_div_succ a hq
  have hb := Nat.lt_mul_div_succ b hq
  have h : (a + b + 1) / q < a / q + b / q + 2 := by
    rw [Nat.div_lt_iff_lt_mul hq]
    nlinarith
  omega

/-- Legendre: `v_p((a+b+1)!) ≤ v_p(a!) + v_p(b!) + ⌊log_p(a+b+1)⌋`. -/
theorem padicValNat_factorial_add_succ_le (a b : ℕ) :
    padicValNat p (Nat.factorial (a + b + 1))
      ≤ padicValNat p (Nat.factorial a) + padicValNat p (Nat.factorial b)
        + Nat.log p (a + b + 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hlt : Nat.log p (a + b + 1) < Nat.log p (a + b + 1) + 1 := Nat.lt_succ_self _
  have ha : Nat.log p a < Nat.log p (a + b + 1) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  have hb : Nat.log p b < Nat.log p (a + b + 1) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial hlt, padicValNat_factorial ha, padicValNat_factorial hb]
  have hcard : (Finset.Ico 1 (Nat.log p (a + b + 1) + 1)).card = Nat.log p (a + b + 1) := by
    simp
  calc ∑ i ∈ Finset.Ico 1 (Nat.log p (a + b + 1) + 1), (a + b + 1) / p ^ i
      ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p (a + b + 1) + 1), (a / p ^ i + b / p ^ i + 1) :=
        Finset.sum_le_sum fun i _ => succ_add_div_le a b (p ^ i) (pow_pos hp i)
    _ = ∑ i ∈ Finset.Ico 1 (Nat.log p (a + b + 1) + 1), a / p ^ i
          + ∑ i ∈ Finset.Ico 1 (Nat.log p (a + b + 1) + 1), b / p ^ i
          + Nat.log p (a + b + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, smul_eq_mul,
          mul_one]

/-- `v_p((2K)!) ≤ 2 v_p(K!) + ⌊log_p 2K⌋`, from `v_p(C(2K, K)) ≤ ⌊log_p 2K⌋`. -/
theorem padicValNat_two_mul_factorial_le (K : ℕ) :
    padicValNat p (Nat.factorial (2 * K))
      ≤ 2 * padicValNat p (Nat.factorial K) + Nat.log p (2 * K) := by
  have h1 : (2 * K).choose K * Nat.factorial K * Nat.factorial K = Nat.factorial (2 * K) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show K ≤ 2 * K by omega)
    rwa [show 2 * K - K = K by omega] at h
  have h2 : padicValNat p ((2 * K).choose K) ≤ Nat.log p (2 * K) := by
    have h := Nat.factorization_choose_le_log (p := p) (n := 2 * K) (k := K)
    rwa [Nat.factorization_def _ (Fact.out : p.Prime)] at h
  have hc : (2 * K).choose K ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [← h1, padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero K)) (Nat.factorial_ne_zero K),
    padicValNat.mul hc (Nat.factorial_ne_zero K)]
  omega

/-- `v_p(a!) + v_p(b!) ≤ v_p((a+b)!)`, since `C(a+b, b)` is an integer. -/
theorem padicValNat_factorial_add_le (a b : ℕ) :
    padicValNat p (Nat.factorial a) + padicValNat p (Nat.factorial b)
      ≤ padicValNat p (Nat.factorial (a + b)) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  have hc : (a + b).choose b ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [← h, padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero b),
    padicValNat.mul hc (Nat.factorial_ne_zero a)]
  omega

/-- The quotient coefficient `(K!)² (k-2K-1)!/k!` has valuation
`≥ -⌊log_p 2K⌋ - ⌊log_p k⌋`. -/
theorem padicValRat_quotCoeff_ge (K k : ℕ) (hk : 2 * K + 1 ≤ k) :
    -((Nat.log p (2 * K) : ℤ) + Nat.log p k)
      ≤ padicValRat p ((Nat.factorial K : ℚ) ^ 2
          * ((Nat.factorial (k - (2 * K + 1)) : ℚ) / (Nat.factorial k : ℚ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * K + j + 1 := ⟨k - (2 * K + 1), by omega⟩
  rw [show 2 * K + j + 1 - (2 * K + 1) = j by omega]
  have hK : (Nat.factorial K : ℚ) ≠ 0 := by positivity
  have hj : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  have hk' : (Nat.factorial (2 * K + j + 1) : ℚ) ≠ 0 := by positivity
  rw [padicValRat.mul (pow_ne_zero 2 hK) (div_ne_zero hj hk'), padicValRat.pow,
    padicValRat.div hj hk', padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
  have h1 := padicValNat_factorial_add_succ_le (p := p) (2 * K) j
  have h2 := padicValNat_two_mul_factorial_le (p := p) K
  omega

/-! ## Integer values of binomial polynomials and Newton's formula -/

/-- `C(z, k)` is an integer at every integer `z`. -/
theorem binomPoly_eval_int (k : ℕ) (z : ℤ) :
    (binomPoly k).eval (z : ℚ) = ((Ring.choose z k : ℤ) : ℚ) := by
  unfold binomPoly
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have h1 : ∏ i ∈ Finset.range k, ((z : ℚ) - (i : ℚ))
      = (((descPochhammer ℤ k).eval z : ℤ) : ℚ) := by
    rw [descPochhammer_eval_eq_prod_range]
    push_cast
    try rfl
  rw [h1, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  field_simp

theorem binomPoly_eval_nat (k m : ℕ) : (binomPoly k).eval (m : ℚ) = (m.choose k : ℚ) := by
  simpa [Ring.choose_natCast] using binomPoly_eval_int k (m : ℤ)

omit [Fact p.Prime] in
theorem padicValRat_binomPoly_eval_int_nonneg (k : ℕ) (z : ℤ) :
    0 ≤ padicValRat p ((binomPoly k).eval (z : ℚ)) := by
  rw [binomPoly_eval_int]
  exact padicValRat_intCast_nonneg _

theorem natDegree_binomPoly_le (k : ℕ) : (binomPoly k).natDegree ≤ k := by
  unfold binomPoly
  refine (natDegree_mul_C_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  rw [Finset.sum_congr rfl (fun (i : ℕ) _ => natDegree_X_sub_C (i : ℚ))]
  simp

/-- Newton's forward-difference formula for polynomials: `f = ∑_{k ≤ e} Δᵏf(0) C(x, k)`. -/
theorem newton_expansion (f : ℚ[X]) {e : ℕ} (hf : f.natDegree ≤ e) :
    f = ∑ k ∈ Finset.range (e + 1), C ((fwdDiff (1 : ℚ))^[k] f.eval 0) * binomPoly k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_mul, eval_C, binomPoly_eval_nat]
  have h1 := shift_eq_sum_fwdDiff_iter (1 : ℚ) f.eval m 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h1
  rw [h1]
  have hA : ∑ k ∈ Finset.range (m + 1), (m.choose k : ℚ) * (fwdDiff (1 : ℚ))^[k] f.eval 0
      = ∑ k ∈ Finset.range (m + e + 1),
          (fwdDiff (1 : ℚ))^[k] f.eval 0 * (m.choose k : ℚ) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun k hk hk' => ?_)
      |>.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)
    have hmk : m < k := by
      simp only [Finset.mem_range] at hk hk'
      omega
    rw [Nat.choose_eq_zero_of_lt hmk, Nat.cast_zero, zero_mul]
  have hB : ∑ k ∈ Finset.range (e + 1), (fwdDiff (1 : ℚ))^[k] f.eval 0 * (m.choose k : ℚ)
      = ∑ k ∈ Finset.range (m + e + 1),
          (fwdDiff (1 : ℚ))^[k] f.eval 0 * (m.choose k : ℚ) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun k hk hk' => ?_)
    have hek : f.natDegree < k := by
      simp only [Finset.mem_range] at hk hk'
      omega
    rw [congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hek) 0, Pi.zero_apply, zero_mul]
  rw [hA, hB]

/-- Forward differences of a function with values in `p^{B} ℤ_(p)` on `ℕ` stay there. -/
theorem fwdDiff_iter_val (f : ℚ → ℚ) {B : ℤ} (hB : B ≤ 0)
    (hf : ∀ m : ℕ, B ≤ padicValRat p (f m)) (k : ℕ) :
    B ≤ padicValRat p ((fwdDiff (1 : ℚ))^[k] f 0) := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply padicValRat_le_sum _ _ _ hB
  intro j _
  rw [zsmul_eq_mul]
  simp only [zero_add, nsmul_eq_mul, mul_one]
  have h := padicValRat_mul_ge (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) : ℤ) : ℚ) (f j) 0 B
    (padicValRat_intCast_nonneg _) (hf j) (by linarith)
  simpa using h

/-! ## `τ` on binomial polynomials -/

theorem bernoulliL_C_mul (a : ℚ) (P : ℚ[X]) : bernoulliL (C a * P) = a * bernoulliL P := by
  unfold bernoulliL
  rw [C_mul', Polynomial.sum_smul_index P a (fun k x => x * _root_.bernoulli k)
      (fun i => zero_mul _), Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `L` as an additive map. -/
noncomputable def bernoulliLHom : ℚ[X] →+ ℚ where
  toFun := bernoulliL
  map_zero' := by simp [bernoulliL]
  map_add' := bernoulliL_add

theorem bernoulliL_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    bernoulliL (∑ i ∈ s, f i) = ∑ i ∈ s, bernoulliL (f i) :=
  map_sum bernoulliLHom f s

theorem bernoulliL_sub (P Q : ℚ[X]) : bernoulliL (P - Q) = bernoulliL P - bernoulliL Q :=
  map_sub bernoulliLHom P Q

/-- `L((x+1)ⁿ - xⁿ) = ∑_{k<n} C(n,k) B_k = [n = 1]`. -/
theorem bernoulliL_add_one_pow_sub (n : ℕ) :
    bernoulliL ((X + 1) ^ n - X ^ n) = if n = 1 then 1 else 0 := by
  have h : ((X + 1) ^ n - X ^ n : ℚ[X])
      = ∑ k ∈ Finset.range n, C ((n.choose k : ℕ) : ℚ) * X ^ k := by
    rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_pow, mul_one, mul_one,
      add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, ← C_eq_natCast, mul_comm]
  rw [h, bernoulliL_finsetSum]
  simp only [bernoulliL_C_mul_X_pow]
  exact _root_.sum_bernoulli n

/-- `L(f(x+1) - f(x)) = f'(0)`. -/
theorem bernoulliL_comp_add_one_sub (f : ℚ[X]) :
    bernoulliL (f.comp (X + 1) - f) = (derivative f).eval 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [add_comp, show f.comp (X + 1) + g.comp (X + 1) - (f + g)
        = (f.comp (X + 1) - f) + (g.comp (X + 1) - g) by ring, bernoulliL_add, hf, hg,
      derivative_add, eval_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← mul_sub, bernoulliL_C_mul,
      bernoulliL_add_one_pow_sub, derivative_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X]
    rcases n with _ | _ | n <;> simp

theorem iterate_derivative_comp_X_add_one (f : ℚ[X]) (n : ℕ) :
    derivative^[n] (f.comp (X + 1)) = (derivative^[n] f).comp (X + 1) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp,
      derivative_add, derivative_X, derivative_one, add_zero, one_mul, ih]

/-- `τ(f(x+1) - f(x)) = f⁽⁶⁾(0)/720 = [x⁶] f`. -/
theorem tauPoly_comp_add_one_sub (f : ℚ[X]) : tauPoly (f.comp (X + 1) - f) = f.coeff 6 := by
  unfold tauPoly
  rw [iterate_derivative_sub, iterate_derivative_comp_X_add_one, bernoulliL_comp_add_one_sub,
    ← Function.iterate_succ_apply' derivative, ← coeff_zero_eq_eval_zero,
    coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  norm_num [Nat.factorial]

/-- Pascal's rule `C(x+1, k+1) - C(x, k+1) = C(x, k)`. -/
theorem binomPoly_comp_add_one_sub (k : ℕ) :
    (binomPoly (k + 1)).comp (X + 1) - binomPoly (k + 1) = binomPoly k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_sub, eval_comp, eval_add, eval_X, eval_one]
  rw [show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) from (Nat.cast_succ m).symm, binomPoly_eval_nat,
    binomPoly_eval_nat, binomPoly_eval_nat, Nat.choose_succ_succ', Nat.cast_add]
  ring

/-- `τ(C(x, k)) = [x⁶] C(x, k+1)`. -/
theorem tauPoly_binomPoly (k : ℕ) : tauPoly (binomPoly k) = (binomPoly (k + 1)).coeff 6 := by
  rw [← binomPoly_comp_add_one_sub, tauPoly_comp_add_one_sub]

theorem tauPoly_C_mul (a : ℚ) (P : ℚ[X]) : tauPoly (C a * P) = a * tauPoly P := by
  unfold tauPoly
  rw [iterate_derivative_C_mul, bernoulliL_C_mul, mul_div_assoc]

theorem binomPoly_coeff_six (i : ℕ) :
    (binomPoly i).coeff 6 = derivCoeff 6 i / ((720 : ℕ) : ℚ) := by
  unfold derivCoeff
  rw [show ((Nat.factorial 6 : ℕ) : ℚ) = 720 by norm_num [Nat.factorial], Nat.cast_ofNat]
  ring

/-- The `τ`-bound with per-term constant `6`: if `deg P ≤ e` and `P(ℕ) ⊂ p^{-B} ℤ_(p)`, then
`v_p(τ(P)) ≥ -B - 6⌊log_p(e+2)⌋ - v_p(720)`. -/
theorem tauPoly_val_ge (P : ℚ[X]) (e B : ℕ) (hdeg : P.natDegree ≤ e)
    (hval : ∀ m : ℕ, -(B : ℤ) ≤ padicValRat p (P.eval (m : ℚ))) :
    -(B : ℤ) - 6 * (Nat.log p (e + 2) : ℤ) - (padicValNat p 720 : ℤ)
      ≤ padicValRat p (tauPoly P) := by
  have hL : (0 : ℤ) ≤ Nat.log p (e + 2) := Nat.cast_nonneg _
  have h720 : (0 : ℤ) ≤ padicValNat p 720 := Nat.cast_nonneg _
  have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg _
  have hL' : (0 : ℤ) ≤ Nat.log p (e + 1 + 1) := Nat.cast_nonneg _
  rw [newton_expansion P hdeg, tauPoly_sum]
  apply padicValRat_le_sum _ _ _ (by linarith)
  intro k hk
  have hk' : k + 1 ≤ e + 1 := by
    simp only [Finset.mem_range] at hk
    omega
  rw [tauPoly_C_mul, tauPoly_binomPoly, binomPoly_coeff_six]
  have h1 : -(B : ℤ) ≤ padicValRat p ((fwdDiff (1 : ℚ))^[k] P.eval 0) :=
    fwdDiff_iter_val _ (by linarith) hval k
  have h2 := deriv_loss (p := p) (e + 1) 6 (k + 1) hk'
  have h3 := padicValRat_div_natCast_ge (p := p) (derivCoeff 6 (k + 1)) 720
    (B := -(((6 * Nat.log p (e + 1 + 1) : ℕ)) : ℤ)) (by omega) h2
  rw [show e + 1 + 1 = e + 2 by ring] at h3
  have h4 := padicValRat_mul_ge _ _ _ _ h1 h3 (by omega)
  omega

/-! ## Partial fractions over distinct nodes -/

/-- Partial fractions for `U/T` with `T = ∏_{i ∈ s} (x - v_i)`, `v` injective on `s`:
`U = (U div T) T + ∑_i (U(v_i)/T'(v_i)) T/(x - v_i)`. -/
theorem pf_spec {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℚ) (hinj : Set.InjOn v s)
    (U : ℚ[X]) :
    U = (U /ₘ Lagrange.nodal s v) * Lagrange.nodal s v
      + ∑ i ∈ s, C (U.eval (v i) / (derivative (Lagrange.nodal s v)).eval (v i))
          * Lagrange.nodal (s.erase i) v := by
  have hmonic : (Lagrange.nodal s v).Monic := Lagrange.nodal_monic
  have hrem := Lagrange.eq_interpolate hinj
    ((degree_modByMonic_lt U hmonic).trans_eq Lagrange.degree_nodal)
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C] at hrem
  have hsum : ∀ i ∈ s, C (Lagrange.nodalWeight s v i)
        * (Lagrange.nodal s v / (X - C (v i))) * C (eval (v i) (U %ₘ Lagrange.nodal s v))
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

/-- The same partial fractions in `ℚ(x)`. -/
theorem pf_ratFunc {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℚ)
    (hinj : Set.InjOn v s) (U : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) U / algebraMap ℚ[X] (RatFunc ℚ) (Lagrange.nodal s v)
      = algebraMap ℚ[X] (RatFunc ℚ) (U /ₘ Lagrange.nodal s v)
        + ∑ i ∈ s, algebraMap ℚ[X] (RatFunc ℚ)
            (C (U.eval (v i) / (derivative (Lagrange.nodal s v)).eval (v i)))
            / algebraMap ℚ[X] (RatFunc ℚ) (X - C (v i)) := by
  have hT : algebraMap ℚ[X] (RatFunc ℚ) (Lagrange.nodal s v) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Lagrange.nodal_ne_zero
  have key : ∀ i ∈ s, ∀ c : ℚ,
      algebraMap ℚ[X] (RatFunc ℚ) (C c * Lagrange.nodal (s.erase i) v)
          / algebraMap ℚ[X] (RatFunc ℚ) (Lagrange.nodal s v)
        = algebraMap ℚ[X] (RatFunc ℚ) (C c) / algebraMap ℚ[X] (RatFunc ℚ) (X - C (v i)) := by
    intro i hi c
    rw [Lagrange.nodal_eq_mul_nodal_erase hi, map_mul, map_mul]
    exact mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero Lagrange.nodal_ne_zero)
  conv_lhs => rw [pf_spec s v hinj U]
  rw [map_add, map_mul, map_sum, add_div, mul_div_cancel_right₀ _ hT, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i hi => key i hi _

/-! ## The denominator `W = ∏_{|r| ≤ K} (x - r)` -/

theorem Wpoly_eq_nodal (K : ℕ) :
    Wpoly K = Lagrange.nodal (Finset.Icc (-(K : ℤ)) K) (fun r : ℤ => (r : ℚ)) := rfl

theorem Wpoly_monic (K : ℕ) : (Wpoly K).Monic := Lagrange.nodal_monic

theorem Wpoly_natDegree (K : ℕ) : (Wpoly K).natDegree = 2 * K + 1 := by
  rw [Wpoly_eq_nodal, Lagrange.natDegree_nodal, Int.card_Icc]
  omega

theorem Wpoly_eq_prod_range (K : ℕ) :
    Wpoly K = ∏ i ∈ Finset.range (2 * K + 1), (X - C ((i : ℚ) - K)) := by
  have hset : Finset.Icc (-(K : ℤ)) K
      = (Finset.range (2 * K + 1)).image (fun i : ℕ => (i : ℤ) - K) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(r + K).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [Wpoly, hset, Finset.prod_image (by
    intro i _ j _ h
    have h' : (i : ℤ) - K = (j : ℤ) - K := h
    omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  try ring

theorem prod_Ico_sub (r : ℤ) (n : ℕ) :
    ∏ j ∈ Finset.Ico (r - n) r, ((r : ℚ) - j) = (Nat.factorial n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hset : Finset.Ico (r - ((n + 1 : ℕ) : ℤ)) r
        = insert (r - ((n + 1 : ℕ) : ℤ)) (Finset.Ico (r - n) r) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : r - ((n + 1 : ℕ) : ℤ) ∉ Finset.Ico (r - n) r := by
      simp only [Finset.mem_Ico]
      omega
    rw [hset, Finset.prod_insert hnot, ih, Nat.factorial_succ]
    push_cast
    ring

theorem prod_Ioc_sub (r : ℤ) (n : ℕ) :
    ∏ j ∈ Finset.Ioc r (r + n), ((r : ℚ) - j) = (-1) ^ n * (Nat.factorial n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hset : Finset.Ioc r (r + ((n + 1 : ℕ) : ℤ))
        = insert (r + ((n + 1 : ℕ) : ℤ)) (Finset.Ioc r (r + n)) := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : r + ((n + 1 : ℕ) : ℤ) ∉ Finset.Ioc r (r + n) := by
      simp only [Finset.mem_Ioc]
      omega
    rw [hset, Finset.prod_insert hnot, ih, Nat.factorial_succ]
    push_cast
    ring

/-- `W'(r) = ∏_{s ≠ r} (r - s) = (K+r)! · (-1)^{K-r} (K-r)!`. -/
theorem derivative_Wpoly_eval (K : ℕ) {r : ℤ} (hr : r ∈ Finset.Icc (-(K : ℤ)) K) :
    (derivative (Wpoly K)).eval (r : ℚ)
      = (Nat.factorial ((K : ℤ) + r).toNat : ℚ)
        * ((-1) ^ ((K : ℤ) - r).toNat * (Nat.factorial ((K : ℤ) - r).toNat : ℚ)) := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (v := fun s : ℤ => (s : ℚ)) hr
  beta_reduce at h
  rw [Wpoly_eq_nodal, h, Lagrange.eval_nodal]
  simp only [Finset.mem_Icc] at hr
  have hset : (Finset.Icc (-(K : ℤ)) K).erase r
      = Finset.Ico (r - (((K : ℤ) + r).toNat : ℤ)) r
        ∪ Finset.Ioc r (r + (((K : ℤ) - r).toNat : ℤ)) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
      Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Ico (r - (((K : ℤ) + r).toNat : ℤ)) r)
      (Finset.Ioc r (r + (((K : ℤ) - r).toNat : ℤ))) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2
    omega
  rw [hset, Finset.prod_union hdisj, prod_Ico_sub, prod_Ioc_sub]

/-- Residue bound: `v_p(c_r) ≥ -⌊log_p 2K⌋` for `c_r = (K!)² A(r)/W'(r)`. -/
theorem residue_val (K : ℕ) (A : ℚ[X]) (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ)))
    {r : ℤ} (hr : r ∈ Finset.Icc (-(K : ℤ)) K) :
    -(Nat.log p (2 * K) : ℤ) ≤ padicValRat p
      ((C ((Nat.factorial K : ℚ) ^ 2) * A).eval (r : ℚ) / (derivative (Wpoly K)).eval (r : ℚ)) := by
  have hlog : (0 : ℤ) ≤ Nat.log p (2 * K) := Nat.cast_nonneg _
  have hm : ((K : ℤ) + r).toNat + ((K : ℤ) - r).toNat = 2 * K := by
    simp only [Finset.mem_Icc] at hr
    omega
  rw [derivative_Wpoly_eval K hr, eval_mul, eval_C]
  by_cases hA0 : A.eval (r : ℚ) = 0
  · rw [hA0, mul_zero, zero_div, padicValRat.zero]
    linarith
  have hK : (Nat.factorial K : ℚ) ≠ 0 := by positivity
  have h1 : (Nat.factorial ((K : ℤ) + r).toNat : ℚ) ≠ 0 := by positivity
  have h2 : (Nat.factorial ((K : ℤ) - r).toNat : ℚ) ≠ 0 := by positivity
  have hs : ((-1 : ℚ) ^ ((K : ℤ) - r).toNat) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero 2 hK) hA0) (mul_ne_zero h1 (mul_ne_zero hs h2)),
    padicValRat.mul (pow_ne_zero 2 hK) hA0, padicValRat.mul h1 (mul_ne_zero hs h2),
    padicValRat.mul hs h2, padicValRat.pow, padicValRat.pow, padicValRat.neg, padicValRat.one,
    padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
  have h3 := padicValNat_factorial_add_le (p := p) ((K : ℤ) + r).toNat ((K : ℤ) - r).toNat
  have h4 := padicValNat_two_mul_factorial_le (p := p) K
  rw [hm] at h3
  have h3' : (padicValNat p (Nat.factorial ((K : ℤ) + r).toNat) : ℤ)
      + padicValNat p (Nat.factorial ((K : ℤ) - r).toNat)
      ≤ padicValNat p (Nat.factorial (2 * K)) := by exact_mod_cast h3
  have h4' : (padicValNat p (Nat.factorial (2 * K)) : ℤ)
      ≤ 2 * padicValNat p (Nat.factorial K) + Nat.log p (2 * K) := by exact_mod_cast h4
  have h5 := hA r
  omega

/-- The partial-fraction data of `U/W` represents `U/W`. -/
theorem tauRatFunc_pfData (K : ℕ) (U : ℚ[X]) :
    tauRatFunc (U /ₘ Wpoly K) (∑ r ∈ Finset.Icc (-(K : ℤ)) K,
        Finsupp.single r (U.eval (r : ℚ) / (derivative (Wpoly K)).eval (r : ℚ)))
      = algebraMap ℚ[X] (RatFunc ℚ) U / algebraMap ℚ[X] (RatFunc ℚ) (Wpoly K) := by
  have hinj : Set.InjOn (fun r : ℤ => (r : ℚ)) (Finset.Icc (-(K : ℤ)) K) :=
    fun a _ b _ h => Int.cast_injective h
  unfold tauRatFunc
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_div]), Wpoly_eq_nodal,
    pf_ratFunc _ _ hinj U]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

theorem tauFunctional_pfData (K : ℕ) (U : ℚ[X]) (c : ℤ → ℚ) :
    tauFunctional (U /ₘ Wpoly K) (∑ r ∈ Finset.Icc (-(K : ℤ)) K, Finsupp.single r (c r))
      = C (tauPoly (U /ₘ Wpoly K)) + ∑ r ∈ Finset.Icc (-(K : ℤ)) K, C (c r) * tauPole r := by
  unfold tauFunctional
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_mul])]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

/-! ## Pole values -/

theorem H7_val (m : ℕ) : -(7 * (Nat.log p m : ℤ)) ≤ padicValRat p (H7 m) := by
  have hL : (0 : ℤ) ≤ Nat.log p m := Nat.cast_nonneg _
  unfold H7
  apply padicValRat_le_sum _ _ _ (by linarith)
  intro v hv
  have hvm : v + 1 ≤ m := by
    simp only [Finset.mem_range] at hv
    omega
  rw [one_div, padicValRat.inv, padicValRat.pow,
    show ((v : ℚ) + 1) = ((v + 1 : ℕ) : ℚ) from (Nat.cast_succ v).symm, padicValRat.of_nat]
  have h := padicValNat_le_log_of_le (p := p) (v + 1) m (by omega) hvm
  omega

theorem tauPole_coeff_val (K : ℕ) {r : ℤ} (hr : r ∈ Finset.Icc (-(K : ℤ)) K) (k : ℕ) :
    -(7 * (Nat.log p K : ℤ)) ≤ padicValRat p ((tauPole r).coeff k) := by
  have hd : dIndex r ≤ K := by
    simp only [Finset.mem_Icc] at hr
    unfold dIndex
    split_ifs <;> omega
  have hlog : (Nat.log p (dIndex r) : ℤ) ≤ Nat.log p K := by
    exact_mod_cast Nat.log_mono_right hd
  have h0 : (0 : ℤ) ≤ Nat.log p K := Nat.cast_nonneg _
  have hH := H7_val (p := p) (dIndex r)
  by_cases hk0 : k = 0
  · subst hk0
    simp only [tauPole, coeff_sub, coeff_C_zero, coeff_X_zero, sub_zero]
    linarith
  by_cases hk1 : k = 1
  · subst hk1
    rw [show (tauPole r).coeff 1 = -1 by simp [tauPole], padicValRat.neg, padicValRat.one]
    linarith
  rw [show (tauPole r).coeff k = 0 by simp [tauPole, coeff_C, coeff_X, hk0, Ne.symm hk1],
    padicValRat.zero]
  linarith

/-! ## The polynomial part via the binomial basis at `-K` -/

/-- Newton coefficients of `A` at `-K`: `A = ∑_k a_k C(x+K, k)`. -/
noncomputable def aK (A : ℚ[X]) (K k : ℕ) : ℚ :=
  (fwdDiff (1 : ℚ))^[k] (A.comp (X - C (K : ℚ))).eval 0

theorem aK_val (A : ℚ[X]) (K k : ℕ) (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ))) :
    0 ≤ padicValRat p (aK A K k) := by
  unfold aK
  refine fwdDiff_iter_val _ le_rfl (fun m => ?_) k
  rw [eval_comp, eval_sub, eval_X, eval_C,
    show (m : ℚ) - K = (((m : ℤ) - K : ℤ) : ℚ) by push_cast; try ring]
  exact hA _

theorem newton_shift (A : ℚ[X]) (K d : ℕ) (hdeg : A.natDegree ≤ d) :
    A = ∑ k ∈ Finset.range (d + 1), C (aK A K k) * (binomPoly k).comp (X + C (K : ℚ)) := by
  have hdeg' : (A.comp (X - C (K : ℚ))).natDegree ≤ d := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_sub_C, mul_one]
    exact hdeg
  have h := newton_expansion (A.comp (X - C (K : ℚ))) hdeg'
  have h2 := congrArg (fun q => q.comp (X + C (K : ℚ))) h
  simp only [comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X,
    Polynomial.sum_comp, mul_comp] at h2
  exact h2

/-- `C(x+K, 2K+1+j) = W(x) · j!/(2K+1+j)! · C(x-K-1, j)`. -/
theorem binomPoly_comp_shift (K j : ℕ) :
    (binomPoly (2 * K + 1 + j)).comp (X + C (K : ℚ))
      = Wpoly K * (C ((Nat.factorial j : ℚ) / (Nat.factorial (2 * K + 1 + j) : ℚ))
          * (binomPoly j).comp (X - C ((K : ℚ) + 1))) := by
  apply Polynomial.funext
  intro x
  simp only [binomPoly, Wpoly_eq_prod_range, eval_mul, eval_comp, eval_prod, eval_sub, eval_add,
    eval_X, eval_C]
  have hsplit : ∏ i ∈ Finset.range (2 * K + 1 + j), (x + (K : ℚ) - (i : ℚ))
      = (∏ i ∈ Finset.range (2 * K + 1), (x - ((i : ℚ) - K)))
        * ∏ l ∈ Finset.range j, (x - ((K : ℚ) + 1) - l) := by
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by ring
    · exact Finset.prod_congr rfl fun l _ => by push_cast; ring
  rw [hsplit]
  have hf1 : (Nat.factorial (2 * K + 1 + j) : ℚ) ≠ 0 := by positivity
  have hf2 : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  field_simp

/-- The part of the binomial expansion of `A` at `-K` of degree `≤ 2K`. -/
noncomputable def lowPart (A : ℚ[X]) (K d : ℕ) : ℚ[X] :=
  ∑ k ∈ (Finset.range (d + 1)).filter (fun k => ¬ 2 * K + 1 ≤ k),
    C (aK A K k) * (binomPoly k).comp (X + C (K : ℚ))

/-- The quotient of `A` by `W`: `∑_{k > 2K} a_k (k-2K-1)!/k! C(x-K-1, k-2K-1)`. -/
noncomputable def highQuot (A : ℚ[X]) (K d : ℕ) : ℚ[X] :=
  ∑ k ∈ (Finset.range (d + 1)).filter (fun k => 2 * K + 1 ≤ k),
    C (aK A K k * ((Nat.factorial (k - (2 * K + 1)) : ℚ) / (Nat.factorial k : ℚ)))
      * (binomPoly (k - (2 * K + 1))).comp (X - C ((K : ℚ) + 1))

theorem A_decomp (A : ℚ[X]) (K d : ℕ) (hdeg : A.natDegree ≤ d) :
    A = lowPart A K d + Wpoly K * highQuot A K d := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (d + 1))
    (fun k => 2 * K + 1 ≤ k) (fun k => C (aK A K k) * (binomPoly k).comp (X + C (K : ℚ)))
  have hhigh : ∑ k ∈ (Finset.range (d + 1)).filter (fun k => 2 * K + 1 ≤ k),
      C (aK A K k) * (binomPoly k).comp (X + C (K : ℚ)) = Wpoly K * highQuot A K d := by
    rw [highQuot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * K + 1 + j := ⟨k - (2 * K + 1), by
      simp only [Finset.mem_filter] at hk
      omega⟩
    rw [binomPoly_comp_shift K j, Nat.add_sub_cancel_left, C_mul]
    ring
  calc A = ∑ k ∈ Finset.range (d + 1), C (aK A K k) * (binomPoly k).comp (X + C (K : ℚ)) :=
        newton_shift A K d hdeg
    _ = _ := hsplit.symm
    _ = lowPart A K d + Wpoly K * highQuot A K d := by
        rw [hhigh]
        exact add_comm _ _

theorem natDegree_lowPart_le (A : ℚ[X]) (K d : ℕ) : (lowPart A K d).natDegree ≤ 2 * K := by
  unfold lowPart
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk2 : k ≤ 2 * K := by
    simp only [Finset.mem_filter] at hk
    omega
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  rw [natDegree_X_add_C, mul_one]
  exact (natDegree_binomPoly_le k).trans hk2

theorem natDegree_highQuot_le (A : ℚ[X]) (K d : ℕ) :
    (highQuot A K d).natDegree ≤ d - (2 * K + 1) := by
  unfold highQuot
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk2 : k ≤ d := by
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  rw [natDegree_X_sub_C, mul_one]
  exact (natDegree_binomPoly_le _).trans (by omega)

theorem highQuot_eq_zero (A : ℚ[X]) {K d : ℕ} (h : d < 2 * K + 1) : highQuot A K d = 0 := by
  unfold highQuot
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  exact absurd hk.2 (by omega)

/-- The polynomial part of `(K!)² A / W` is `(K!)² · highQuot`. -/
theorem divByMonic_Wpoly (A : ℚ[X]) (K d : ℕ) (hdeg : A.natDegree ≤ d) :
    (C ((Nat.factorial K : ℚ) ^ 2) * A) /ₘ Wpoly K
      = C ((Nat.factorial K : ℚ) ^ 2) * highQuot A K d := by
  refine (div_modByMonic_unique (C ((Nat.factorial K : ℚ) ^ 2) * highQuot A K d)
    (C ((Nat.factorial K : ℚ) ^ 2) * lowPart A K d) (Wpoly_monic K) ⟨?_, ?_⟩).1
  · conv_rhs => rw [A_decomp A K d hdeg]
    ring
  · apply degree_lt_degree
    rw [Wpoly_natDegree]
    exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (natDegree_lowPart_le A K d))
      (by omega)

/-- Values of the polynomial part: `v_p(P(z)) ≥ -⌊log_p 2K⌋ - ⌊log_p d⌋` at every integer. -/
theorem polyPart_val (A : ℚ[X]) (K d : ℕ) (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ)))
    (z : ℤ) :
    -((Nat.log p (2 * K) + Nat.log p d : ℕ) : ℤ)
      ≤ padicValRat p ((C ((Nat.factorial K : ℚ) ^ 2) * highQuot A K d).eval (z : ℚ)) := by
  have hL : (0 : ℤ) ≤ ((Nat.log p (2 * K) + Nat.log p d : ℕ) : ℤ) := Nat.cast_nonneg _
  rw [eval_mul, eval_C, highQuot, eval_finsetSum, Finset.mul_sum]
  apply padicValRat_le_sum _ _ _ (by linarith)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  rw [eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_C,
    show (z : ℚ) - ((K : ℚ) + 1) = ((z - K - 1 : ℤ) : ℚ) by push_cast; try ring,
    binomPoly_eval_int]
  have e : (Nat.factorial K : ℚ) ^ 2
        * (aK A K k * ((Nat.factorial (k - (2 * K + 1)) : ℚ) / (Nat.factorial k : ℚ))
          * ((Ring.choose (z - K - 1) (k - (2 * K + 1)) : ℤ) : ℚ))
      = ((Nat.factorial K : ℚ) ^ 2
          * ((Nat.factorial (k - (2 * K + 1)) : ℚ) / (Nat.factorial k : ℚ)))
        * (aK A K k * ((Ring.choose (z - K - 1) (k - (2 * K + 1)) : ℤ) : ℚ)) := by ring
  rw [e]
  have h1 := aK_val A K k hA
  have h2 := padicValRat_quotCoeff_ge (p := p) K k hk.2
  have h3 := padicValRat_intCast_nonneg (p := p) (Ring.choose (z - K - 1) (k - (2 * K + 1)))
  have h4 := padicValRat_mul_ge _ _ 0 0 h1 h3 le_rfl
  have hlog : (Nat.log p k : ℤ) ≤ Nat.log p d := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have hl0 : (0 : ℤ) ≤ Nat.log p (2 * K) := Nat.cast_nonneg _
  have hl1 : (0 : ℤ) ≤ Nat.log p k := Nat.cast_nonneg _
  have h4' : (0 : ℤ) ≤ padicValRat p
      (aK A K k * ((Ring.choose (z - K - 1) (k - (2 * K + 1)) : ℤ) : ℚ)) := by
    simpa using h4
  have h5 := padicValRat_mul_ge _ _ _ _ h2 h4' (by linarith)
  push_cast
  linarith

/-- The `τ`-value of the polynomial part. -/
theorem tauPoly_polyPart_val (A : ℚ[X]) {K d M : ℕ} (hdeg : A.natDegree ≤ d)
    (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ))) (h2K : 2 * K ≤ M) (hdM : d ≤ M)
    (hdM' : d + 1 ≤ M + 2 * K) :
    -(8 * (Nat.log p M : ℤ)) - (padicValNat p 720 : ℤ)
      ≤ padicValRat p (tauPoly ((C ((Nat.factorial K : ℚ) ^ 2) * A) /ₘ Wpoly K)) := by
  have hL : (0 : ℤ) ≤ Nat.log p M := Nat.cast_nonneg _
  have h720 : (0 : ℤ) ≤ padicValNat p 720 := Nat.cast_nonneg _
  rw [divByMonic_Wpoly A K d hdeg]
  by_cases hd : d < 2 * K + 1
  · rw [highQuot_eq_zero A hd, mul_zero]
    have h0 : tauPoly 0 = 0 := by simp [tauPoly, bernoulliL]
    rw [h0, padicValRat.zero]
    linarith
  have hdeg2 : (C ((Nat.factorial K : ℚ) ^ 2) * highQuot A K d).natDegree ≤ d - (2 * K + 1) :=
    (natDegree_C_mul_le _ _).trans (natDegree_highQuot_le A K d)
  have h := tauPoly_val_ge _ (d - (2 * K + 1)) (Nat.log p (2 * K) + Nat.log p d) hdeg2
    (fun m => by simpa using polyPart_val A K d hA (m : ℤ))
  have h1 : (Nat.log p (2 * K) : ℤ) ≤ Nat.log p M := by exact_mod_cast Nat.log_mono_right h2K
  have h2 : (Nat.log p d : ℤ) ≤ Nat.log p M := by exact_mod_cast Nat.log_mono_right hdM
  have h3 : (Nat.log p (d - (2 * K + 1) + 2) : ℤ) ≤ Nat.log p M := by
    exact_mod_cast Nat.log_mono_right (by omega)
  omega

/-! ## Lemma 3.8, core form -/

/-- Lemma 3.8 with the logarithm taken at any `M ≥ max(2K, d)` with `d + 1 ≤ M + 2K`. -/
theorem tau_bound_core {K d M : ℕ} (h2K : 2 * K ≤ M) (hdM : d ≤ M) (hdM' : d + 1 ≤ M + 2 * K)
    (A : ℚ[X]) (hdeg : A.natDegree ≤ d) (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ)))
    (P : ℚ[X]) (c : ℤ →₀ ℚ)
    (hg : tauRatFunc P c = algebraMap ℚ[X] (RatFunc ℚ) (C ((Nat.factorial K : ℚ) ^ 2) * A)
      / algebraMap ℚ[X] (RatFunc ℚ) (Wpoly K)) (k : ℕ) :
    -(8 * (Nat.log p M : ℤ)) - (padicValNat p 720 : ℤ)
      ≤ padicValRat p ((tauFunctional P c).coeff k) := by
  obtain ⟨rfl, rfl⟩ := tauRatFunc_inj
    (hg.trans (tauRatFunc_pfData K (C ((Nat.factorial K : ℚ) ^ 2) * A)).symm)
  rw [tauFunctional_pfData, coeff_add, finsetSum_coeff]
  have hL : (0 : ℤ) ≤ Nat.log p M := Nat.cast_nonneg _
  have h720 : (0 : ℤ) ≤ padicValNat p 720 := Nat.cast_nonneg _
  have h1 : (Nat.log p (2 * K) : ℤ) ≤ Nat.log p M := by exact_mod_cast Nat.log_mono_right h2K
  have h2 : (Nat.log p K : ℤ) ≤ Nat.log p M := by
    exact_mod_cast Nat.log_mono_right (by omega)
  apply le_padicValRat_add' (by linarith)
  · rw [coeff_C]
    split_ifs
    · exact tauPoly_polyPart_val A hdeg hA h2K hdM hdM'
    · rw [padicValRat.zero]
      linarith
  · apply padicValRat_le_sum _ _ _ (by linarith)
    intro r hr
    rw [coeff_C_mul]
    have hres := residue_val K A hA hr
    have hpole := tauPole_coeff_val (p := p) K hr k
    have hl0 : (0 : ℤ) ≤ Nat.log p (2 * K) := Nat.cast_nonneg _
    have hl1 : (0 : ℤ) ≤ Nat.log p K := Nat.cast_nonneg _
    have h3 := padicValRat_mul_ge _ _ _ _ hres hpole (by linarith)
    linarith

end SmallPrime

/-! ## Lemma 3.8 -/

/-- **Lemma 3.8** (small-prime estimate, (37)). Let `A ∈ ℚ[x]` with `v_p(A(m)) ≥ 0` for every
integer `m` (equivalently `A(ℤ_p) ⊂ ℤ_p`) and `deg A ≤ d`, and let
`g = (K!)² A(x) / ∏_{-K ≤ r ≤ K} (x - r)`. For the partial-fraction representation `(P, c)` of
`g` (`tauRatFunc P c = g`), every coefficient of `τ_X(g) = tauFunctional P c` has valuation
`≥ -8⌊log_p max(2K, d+1)⌋ - v_p(720)`, i.e. `v^G_p(τ_X(g)) ≥ -8⌊log_p max(2K, d+1)⌋ - v_p(720)`
(the Gauss valuation stated coefficientwise; zero coefficients impose nothing since
`padicValRat p 0 = 0` and the bound is `≤ 0`). -/
theorem small_prime_tau_bound (p : ℕ) [Fact p.Prime] (K d : ℕ) (A : ℚ[X])
    (hdeg : A.natDegree ≤ d) (hA : ∀ m : ℤ, 0 ≤ padicValRat p (A.eval (m : ℚ)))
    (P : ℚ[X]) (c : ℤ →₀ ℚ)
    (hg : tauRatFunc P c = algebraMap ℚ[X] (RatFunc ℚ) (C ((Nat.factorial K : ℚ) ^ 2) * A)
      / algebraMap ℚ[X] (RatFunc ℚ) (Wpoly K)) (k : ℕ) :
    -(8 * (Nat.log p (max (2 * K) (d + 1)) : ℤ)) - (padicValNat p 720 : ℤ)
      ≤ padicValRat p ((tauFunctional P c).coeff k) :=
  SmallPrime.tau_bound_core (le_max_left _ _) (le_trans (Nat.le_succ d) (le_max_right _ _))
    (by have := le_max_right (2 * K) (d + 1); omega) A hdeg hA P c hg k

/-- The partial-fraction representation in Lemma 3.8 exists. -/
theorem small_prime_tau_rep_exists (K : ℕ) (A : ℚ[X]) :
    ∃ (P : ℚ[X]) (c : ℤ →₀ ℚ), tauRatFunc P c
      = algebraMap ℚ[X] (RatFunc ℚ) (C ((Nat.factorial K : ℚ) ^ 2) * A)
        / algebraMap ℚ[X] (RatFunc ℚ) (Wpoly K) :=
  ⟨_, _, SmallPrime.tauRatFunc_pfData K _⟩

/-! ## The basis (38) -/

/-- Equation (38): `q_0 = 1` and `q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!` for `i ≥ 1`. -/
noncomputable def qPoly (i : ℕ) : ℚ[X] :=
  if i = 0 then 1 else C ((-1) ^ i * 2 / (Nat.factorial (2 * i) : ℚ)) * X * Dpoly (i - 1)

/-- Equation (38): `f_i(t) = (D_N(t)/(N!)²)⁴ q_i(t)`. -/
noncomputable def fPoly (n i : ℕ) : ℚ[X] :=
  (C ((Nat.factorial (N n) : ℚ) ^ 2)⁻¹ * Dpoly (N n)) ^ 4 * qPoly i

namespace SmallPrime

theorem qPoly_zero : qPoly 0 = 1 := by
  simp [qPoly]

theorem qPoly_succ (l : ℕ) :
    qPoly (l + 1) = C ((-1) ^ (l + 1) * 2 / (Nat.factorial (2 * (l + 1)) : ℚ)) * X * Dpoly l := by
  rw [qPoly, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel]

theorem Dpoly_monic (m : ℕ) : (Dpoly m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem Dpoly_natDegree (m : ℕ) : (Dpoly m).natDegree = m := by
  rw [Dpoly, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _,
    Finset.sum_congr rfl (fun j _ => natDegree_X_add_C _)]
  simp

theorem qPoly_natDegree_le (i : ℕ) : (qPoly i).natDegree ≤ i := by
  rcases i with _ | l
  · simp [qPoly_zero]
  · rw [qPoly_succ]
    refine (natDegree_mul_le).trans ?_
    rw [Dpoly_natDegree]
    have h : (C ((-1) ^ (l + 1) * 2 / (Nat.factorial (2 * (l + 1)) : ℚ)) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    omega

theorem qPoly_coeff_self (l : ℕ) :
    (qPoly (l + 1)).coeff (l + 1) = (-1) ^ (l + 1) * 2 / (Nat.factorial (2 * (l + 1)) : ℚ) := by
  have h1 : (Dpoly l).coeff l = 1 := by
    have h := (Dpoly_monic l).coeff_natDegree
    rwa [Dpoly_natDegree] at h
  rw [qPoly_succ, mul_assoc, coeff_C_mul, coeff_X_mul, h1, mul_one]

theorem qPoly_coeff_eq_zero {i j : ℕ} (h : i < j) : (qPoly i).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (qPoly_natDegree_le i) h)

/-- `(x+l)(x+l-1)⋯(x-l) = x ∏_{j<l} (x² - (j+1)²)`. -/
theorem prod_centered (x : ℚ) (l : ℕ) :
    ∏ a ∈ Finset.range (2 * l + 1), (x + (l : ℚ) - (a : ℚ))
      = x * ∏ j ∈ Finset.range l, (x ^ 2 - ((j : ℚ) + 1) ^ 2) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring, Finset.prod_range_succ' _ (2 * l + 1 + 1),
      Finset.prod_range_succ _ (2 * l + 1),
      Finset.prod_congr rfl (fun a _ => show x + ((l + 1 : ℕ) : ℚ) - ((a + 1 : ℕ) : ℚ)
        = x + (l : ℚ) - (a : ℚ) by push_cast; ring),
      ih, Finset.prod_range_succ _ l]
    push_cast
    ring

end SmallPrime

open SmallPrime in
/-- Equation (38): `q_i(-x²) = C(x+i, 2i) + C(x+i-1, 2i)` for `i ≥ 1`. -/
theorem qPoly_comp_neg_sq (i : ℕ) (hi : 1 ≤ i) :
    (qPoly i).comp (-X ^ 2)
      = (IntegerValued.binomPoly (2 * i)).comp (X + C (i : ℚ))
        + (IntegerValued.binomPoly (2 * i)).comp (X + C ((i : ℚ) - 1)) := by
  obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
  apply Polynomial.funext
  intro x
  rw [qPoly_succ]
  simp only [IntegerValued.binomPoly, Dpoly, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    eval_neg, eval_pow, eval_prod, eval_sub]
  have hA : ∏ a ∈ Finset.range (2 * (l + 1)), (x + ((l + 1 : ℕ) : ℚ) - (a : ℚ))
      = (∏ a ∈ Finset.range (2 * l + 1), (x + (l : ℚ) - (a : ℚ))) * (x + l + 1) := by
    rw [show 2 * (l + 1) = 2 * l + 1 + 1 by ring, Finset.prod_range_succ' _ (2 * l + 1),
      Finset.prod_congr rfl (fun a _ => show x + ((l + 1 : ℕ) : ℚ) - ((a + 1 : ℕ) : ℚ)
        = x + (l : ℚ) - (a : ℚ) by push_cast; ring)]
    push_cast
    ring
  have hB : ∏ a ∈ Finset.range (2 * (l + 1)), (x + (((l + 1 : ℕ) : ℚ) - 1) - (a : ℚ))
      = (∏ a ∈ Finset.range (2 * l + 1), (x + (l : ℚ) - (a : ℚ))) * (x - l - 1) := by
    rw [show 2 * (l + 1) = 2 * l + 1 + 1 by ring, Finset.prod_range_succ _ (2 * l + 1),
      Finset.prod_congr rfl (fun (a : ℕ) _ => show x + (((l + 1 : ℕ) : ℚ) - 1) - (a : ℚ)
        = x + (l : ℚ) - (a : ℚ) by push_cast; ring)]
    push_cast
    ring
  have hD : ∏ j ∈ Finset.range l, (-x ^ 2 + ((j : ℚ) + 1) ^ 2)
      = (-1) ^ l * ∏ j ∈ Finset.range l, (x ^ 2 - ((j : ℚ) + 1) ^ 2) := by
    rw [show (-1 : ℚ) ^ l = ∏ _j ∈ Finset.range l, (-1 : ℚ) by simp, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [hA, hB, prod_centered, hD]
  have hsq : (-1 : ℚ) ^ l * (-1) ^ l = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (2 * x ^ 2 * (∏ j ∈ Finset.range l, (x ^ 2 - ((j : ℚ) + 1) ^ 2))
    / (Nat.factorial (2 * (l + 1)) : ℚ)) * hsq

/-- Equation (38): `D_N(-x²)/(N!)² = C(N-x, N) C(N+x, N)`. -/
theorem Dpoly_comp_neg_sq (m : ℕ) :
    C ((Nat.factorial m : ℚ) ^ 2)⁻¹ * (Dpoly m).comp (-X ^ 2)
      = (IntegerValued.binomPoly m).comp (C (m : ℚ) - X)
        * (IntegerValued.binomPoly m).comp (C (m : ℚ) + X) := by
  apply Polynomial.funext
  intro x
  simp only [Dpoly, IntegerValued.binomPoly, eval_mul, eval_C, eval_comp, eval_prod, eval_add,
    eval_sub, eval_neg, eval_pow, eval_X]
  have hprod : (∏ i ∈ Finset.range m, ((m : ℚ) - x - i)) * ∏ i ∈ Finset.range m, ((m : ℚ) + x - i)
      = ∏ j ∈ Finset.range m, (-x ^ 2 + ((j : ℚ) + 1) ^ 2) := by
    rw [← Finset.prod_mul_distrib,
      ← Finset.prod_range_reflect (fun j : ℕ => -x ^ 2 + ((j : ℚ) + 1) ^ 2) m]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have hc : ((m - 1 - i : ℕ) : ℚ) = (m : ℚ) - 1 - i := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc]
    ring
  rw [← hprod]
  ring

open SmallPrime in
/-- Equation (38): `f_i(-x²)` is integer-valued on `ℤ`. -/
theorem fPoly_comp_neg_sq_intValued (n i : ℕ) (z : ℤ) :
    ∃ w : ℤ, ((fPoly n i).comp (-X ^ 2)).eval (z : ℚ) = w := by
  have hD : ((C ((Nat.factorial (N n) : ℚ) ^ 2)⁻¹ * Dpoly (N n)).comp (-X ^ 2)).eval (z : ℚ)
      = ((Ring.choose ((N n : ℤ) - z) (N n) : ℤ) : ℚ)
        * ((Ring.choose ((N n : ℤ) + z) (N n) : ℤ) : ℚ) := by
    rw [mul_comp, C_comp, Dpoly_comp_neg_sq, eval_mul, eval_comp, eval_comp, eval_sub, eval_add,
      eval_C, eval_X,
      show ((N n : ℚ) - z) = (((N n : ℤ) - z : ℤ) : ℚ) by push_cast; try ring,
      show ((N n : ℚ) + z) = (((N n : ℤ) + z : ℤ) : ℚ) by push_cast; try ring,
      binomPoly_eval_int, binomPoly_eval_int]
  have hq : ∃ w : ℤ, ((qPoly i).comp (-X ^ 2)).eval (z : ℚ) = w := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨1, by simp [qPoly_zero]⟩
    · refine ⟨Ring.choose (z + i) (2 * i) + Ring.choose (z + i - 1) (2 * i), ?_⟩
      rw [qPoly_comp_neg_sq i hi, eval_add, eval_comp, eval_comp, eval_add, eval_add, eval_X,
        eval_C, eval_C,
        show (z : ℚ) + i = ((z + i : ℤ) : ℚ) by push_cast; try ring,
        show (z : ℚ) + ((i : ℚ) - 1) = ((z + i - 1 : ℤ) : ℚ) by push_cast; try ring,
        binomPoly_eval_int, binomPoly_eval_int, Int.cast_add]
  obtain ⟨w, hw⟩ := hq
  refine ⟨(Ring.choose ((N n : ℤ) - z) (N n) * Ring.choose ((N n : ℤ) + z) (N n)) ^ 4 * w, ?_⟩
  rw [fPoly, mul_comp, pow_comp, eval_mul, eval_pow, hD, hw]
  push_cast
  try ring

/-! ## The transition determinant (39) -/

/-- Equation (39): the transition matrix from `D_N(t)⁴ t^j` to `f_i`, namely
`f_i = ∑_j T_{ij} D_N⁴ t^j` with `T_{ij} = [t^j] q_i / (N!)⁸`. -/
noncomputable def transMat (n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun i j => (qPoly i).coeff j / (Nat.factorial (N n) : ℚ) ^ 8

open SmallPrime in
theorem fPoly_eq_transMat_sum (n : ℕ) (i : Fin (hDim n)) :
    fPoly n i = ∑ j : Fin (hDim n), C (transMat n i j) * (Dpoly (N n) ^ 4 * X ^ (j : ℕ)) := by
  have hq : qPoly i = ∑ j ∈ Finset.range (hDim n), C ((qPoly i).coeff j) * X ^ j := by
    conv_lhs => rw [as_sum_range' (qPoly i) (hDim n)
      (lt_of_le_of_lt (qPoly_natDegree_le i) i.isLt)]
    exact Finset.sum_congr rfl fun j _ => C_mul_X_pow_eq_monomial.symm
  rw [fPoly, hq, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (qPoly i).coeff j / (Nat.factorial (N n) : ℚ) ^ 8
      = (qPoly i).coeff j * (((Nat.factorial (N n) : ℚ) ^ 2)⁻¹) ^ 4 := by
    rw [inv_pow, ← pow_mul]
    ring
  simp only [transMat, Matrix.of_apply]
  rw [hc, C_mul, C_pow]
  ring

theorem transMat_isLowerTriangular (n : ℕ) : (transMat n).IsLowerTriangular := by
  intro i j hij
  simp only [transMat, Matrix.of_apply]
  rw [SmallPrime.qPoly_coeff_eq_zero (OrderDual.toDual_lt_toDual.mp hij : (i : ℕ) < j), zero_div]

namespace SmallPrime

theorem prod_qPoly_lead (h : ℕ) :
    ∏ i ∈ Finset.range (h + 1), (qPoly i).coeff i
      = (-1) ^ (∑ i ∈ Finset.range (h + 1), i) * 2 ^ h
        / ∏ i ∈ Finset.Icc 1 h, (Nat.factorial (2 * i) : ℚ) := by
  induction h with
  | zero => simp [qPoly_zero]
  | succ h ih =>
    rw [Finset.prod_range_succ, ih, qPoly_coeff_self, Finset.sum_range_succ _ (h + 1),
      Finset.prod_Icc_succ_top (by omega)]
    have hP : ∏ i ∈ Finset.Icc 1 h, (Nat.factorial (2 * i) : ℚ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
    have hF : (Nat.factorial (2 * (h + 1)) : ℚ) ≠ 0 := by positivity
    ring

end SmallPrime

/-- Equation (39): `det T = ± 2^{h-1} / ∏_{i=1}^{h-1} (2i)! · (N!)^{-8h}`, with the sign
`(-1)^{0+1+⋯+(h-1)}`. -/
theorem det_transMat (n : ℕ) :
    (transMat n).det = (-1) ^ (∑ i ∈ Finset.range (hDim n), i) * 2 ^ (hDim n - 1)
      / ((∏ i ∈ Finset.Icc 1 (hDim n - 1), (Nat.factorial (2 * i) : ℚ))
        * (Nat.factorial (N n) : ℚ) ^ (8 * hDim n)) := by
  rw [Matrix.det_of_isLowerTriangular _ (transMat_isLowerTriangular n)]
  simp only [transMat, Matrix.of_apply]
  rw [Fin.prod_univ_eq_prod_range (fun i => (qPoly i).coeff i / (Nat.factorial (N n) : ℚ) ^ 8),
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  rcases Nat.eq_zero_or_pos (hDim n) with h0 | hpos
  · rw [h0]
    simp
  · obtain ⟨h, hh⟩ : ∃ h, hDim n = h + 1 := ⟨hDim n - 1, by omega⟩
    rw [hh, SmallPrime.prod_qPoly_lead, Nat.add_sub_cancel]
    ring

/-! ## The `μ`-data of `f_i f_j / D_K` and (40) -/

/-- The rational function `p(t) + ∑_j c_j/(t + j²)` with `μ`-data `(p, c)`. -/
noncomputable def muRatFunc (p : ℚ[X]) (c : ℕ →₀ ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) p
    + c.sum fun j a => algebraMap ℚ[X] (RatFunc ℚ) (C a)
        / algebraMap ℚ[X] (RatFunc ℚ) (X + C ((j : ℚ) ^ 2))

/-- `μ`-data representations are unique, so `μ_X` is well defined on rational functions. -/
theorem muRatFunc_inj {p₁ p₂ : ℚ[X]} {c₁ c₂ : ℕ →₀ ℚ}
    (h : muRatFunc p₁ c₁ = muRatFunc p₂ c₂) : p₁ = p₂ ∧ c₁ = c₂ := by
  have hg : ∀ j : ℕ, (X + C ((j : ℚ) ^ 2) : ℚ[X]) = X - C (-(j : ℚ) ^ 2) := fun j => by
    rw [C_neg, sub_neg_eq_add]
  have hsum : ∀ c : ℕ →₀ ℚ, c.support ⊆ c₁.support ∪ c₂.support →
      (c.sum fun j a => algebraMap ℚ[X] (RatFunc ℚ) (C a)
        / algebraMap ℚ[X] (RatFunc ℚ) (X + C ((j : ℚ) ^ 2)))
        = ∑ j ∈ c₁.support ∪ c₂.support, algebraMap ℚ[X] (RatFunc ℚ) (C (c j))
            / algebraMap ℚ[X] (RatFunc ℚ) (X - C (-(j : ℚ) ^ 2)) := fun c hc => by
    rw [Finsupp.sum_of_support_subset c hc _ (fun j _ => by simp)]
    exact Finset.sum_congr rfl fun j _ => by rw [hg]
  unfold muRatFunc at h
  rw [hsum c₁ Finset.subset_union_left, hsum c₂ Finset.subset_union_right] at h
  have hinj : Function.Injective (fun j : ℕ => -(j : ℚ) ^ 2) := by
    intro a b hab
    have hab' : -((a : ℚ) ^ 2) = -((b : ℚ) ^ 2) := hab
    have h1 : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := neg_injective hab'
    have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective (by norm_num) h2
  obtain ⟨hP, hd⟩ := Polynomial.quo_add_sum_rem_div_unique (RatFunc ℚ)
    (g := fun j : ℕ => X - C (-(j : ℚ) ^ 2)) (r₁ := fun j => C (c₁ j)) (r₂ := fun j => C (c₂ j))
    (fun j _ => monic_X_sub_C _)
    (by
      intro j _ j' _ hjj'
      exact pairwise_coprime_X_sub_C hinj hjj')
    (fun j _ => show (C (c₁ j)).degree < (X - C (-(j : ℚ) ^ 2)).degree by
      rw [degree_X_sub_C]
      exact degree_C_lt)
    (fun j _ => show (C (c₂ j)).degree < (X - C (-(j : ℚ) ^ 2)).degree by
      rw [degree_X_sub_C]
      exact degree_C_lt)
    h
  refine ⟨hP, Finsupp.ext fun j => ?_⟩
  by_cases hj : j ∈ c₁.support ∪ c₂.support
  · exact C_injective (hd j hj)
  · simp only [Finset.mem_union, not_or, Finsupp.notMem_support_iff] at hj
    rw [hj.1, hj.2]

namespace SmallPrime

theorem muRatFunc_add (p q : ℚ[X]) (c d : ℕ →₀ ℚ) :
    muRatFunc (p + q) (c + d) = muRatFunc p c + muRatFunc q d := by
  unfold muRatFunc
  rw [map_add, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_div])]
  ring

theorem muRatFunc_zero : muRatFunc 0 0 = 0 := by
  simp [muRatFunc]

theorem muRatFunc_sum {ι : Type*} (s : Finset ι) (p : ι → ℚ[X]) (c : ι → ℕ →₀ ℚ) :
    muRatFunc (∑ x ∈ s, p x) (∑ x ∈ s, c x) = ∑ x ∈ s, muRatFunc (p x) (c x) := by
  classical
  induction s using Finset.induction with
  | empty => simp [muRatFunc_zero]
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, Finset.sum_insert has, muRatFunc_add, ih]

theorem muRatFunc_smul (a : ℚ) (p : ℚ[X]) (c : ℕ →₀ ℚ) :
    muRatFunc (C a * p) (a • c) = algebraMap ℚ[X] (RatFunc ℚ) (C a) * muRatFunc p c := by
  unfold muRatFunc
  rw [Finsupp.sum_smul_index (fun i => by simp), map_mul, mul_add, Finsupp.sum, Finsupp.sum,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [C_mul, map_mul, mul_div_assoc]

theorem muFunctional_add (p q : ℚ[X]) (c d : ℕ →₀ ℚ) :
    muFunctional (p + q) (c + d) = muFunctional p c + muFunctional q d := by
  unfold muFunctional
  rw [Polynomial.sum_add_index p q _ (fun _ => by simp) (fun _ _ _ => by simp [add_mul]),
    Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  ring

theorem muFunctional_sum {ι : Type*} (s : Finset ι) (p : ι → ℚ[X]) (c : ι → ℕ →₀ ℚ) :
    muFunctional (∑ x ∈ s, p x) (∑ x ∈ s, c x) = ∑ x ∈ s, muFunctional (p x) (c x) := by
  classical
  induction s using Finset.induction with
  | empty => simp [muFunctional]
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, Finset.sum_insert has, muFunctional_add, ih]

theorem muFunctional_smul (a : ℚ) (p : ℚ[X]) (c : ℕ →₀ ℚ) :
    muFunctional (C a * p) (a • c) = C a * muFunctional p c := by
  unfold muFunctional
  rw [show C a * p = a • p from C_mul' a p,
    Polynomial.sum_smul_index p a (fun e x => C x * C (muMonomial e)) (fun i => by simp),
    Finsupp.sum_smul_index (fun i => by simp), mul_add, Polynomial.sum_def, Polynomial.sum_def,
    Finsupp.sum, Finsupp.sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun e _ => by rw [C_mul]; ring
  · exact Finset.sum_congr rfl fun j _ => by rw [C_mul]; ring

theorem Dpoly_eq_mul_Dtail (n : ℕ) : Dpoly (K n) = Dpoly (N n) * Dtail n := by
  have hNK : N n ≤ K n := by
    unfold N K
    omega
  rw [Dpoly, Dpoly, Dtail, ← Finset.prod_range_mul_prod_Ico _ hNK]
  congr 1
  rw [show Finset.Icc (N n + 1) (K n) = Finset.Ico (N n + 1) (K n + 1) by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega,
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
    show K n + 1 - (N n + 1) = K n - N n by omega]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

end SmallPrime

open SmallPrime in
/-- The partial-fraction data `(polyPart, poleCoeffs)` of `MatrixDet` represents
`D_N⁸ t^{i+j} / D_K` (proof of Lemma 2.3). -/
theorem muRatFunc_Gentry (n i j : ℕ) :
    muRatFunc (polyPart n i j) (poleCoeffs n i j)
      = algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (N n) ^ 8 * X ^ (i + j))
        / algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)) := by
  have hnod : Dtail n = Lagrange.nodal (Finset.Icc (N n + 1) (K n)) (fun a : ℕ => -(a : ℚ) ^ 2) := by
    rw [Dtail, Lagrange.nodal_eq]
    exact Finset.prod_congr rfl fun a _ => by rw [C_neg, sub_neg_eq_add]
  have hinj : Set.InjOn (fun a : ℕ => -(a : ℚ) ^ 2) (Finset.Icc (N n + 1) (K n)) := by
    intro a _ b _ hab
    have hab' : -((a : ℚ) ^ 2) = -((b : ℚ) ^ 2) := hab
    have h1 : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := neg_injective hab'
    have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective (by norm_num) h2
  have hmonic : (Dtail n).Monic := by
    rw [hnod]
    exact Lagrange.nodal_monic
  have hD : Dpoly (N n) ≠ 0 := (Dpoly_monic _).ne_zero
  have hR : algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (N n) ^ 8 * X ^ (i + j))
        / algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n))
      = algebraMap ℚ[X] (RatFunc ℚ) (Rnum n i j) / algebraMap ℚ[X] (RatFunc ℚ) (Dtail n) := by
    rw [Dpoly_eq_mul_Dtail, Rnum,
      show Dpoly (N n) ^ 8 * X ^ (i + j) = Dpoly (N n) * (Dpoly (N n) ^ 7 * X ^ (i + j)) by ring,
      map_mul (algebraMap ℚ[X] (RatFunc ℚ)) (Dpoly (N n)) (Dpoly (N n) ^ 7 * X ^ (i + j)),
      map_mul (algebraMap ℚ[X] (RatFunc ℚ)) (Dpoly (N n)) (Dtail n)]
    exact mul_div_mul_left _ _ (RatFunc.algebraMap_ne_zero hD)
  have hpp : (Rnum n i j).div (Dtail n) = Rnum n i j /ₘ Dtail n :=
    (divByMonic_eq_div _ hmonic).symm
  rw [hR, hnod, pf_ratFunc _ _ hinj]
  unfold muRatFunc
  congr 1
  · rw [polyPart, hpp, hnod]
  · rw [poleCoeffs, ← Finsupp.sum_finsetSum_index (by simp) (by simp [add_div])]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.sum_single_index (by simp), resCoeff, hnod, C_neg, sub_neg_eq_add]

/-- The `μ`-data of `f_i f_j / D_K`: the combination
`∑_{a,b} T_{ia} T_{jb} (polyPart, poleCoeffs)_{ab}` (with `T` from (39)). -/
noncomputable def muDataP (n : ℕ) (i j : Fin (hDim n)) : ℚ[X] :=
  ∑ a : Fin (hDim n), ∑ b : Fin (hDim n), C (transMat n i a * transMat n j b) * polyPart n a b

/-- The pole part of the `μ`-data of `f_i f_j / D_K`. -/
noncomputable def muDataC (n : ℕ) (i j : Fin (hDim n)) : ℕ →₀ ℚ :=
  ∑ a : Fin (hDim n), ∑ b : Fin (hDim n), (transMat n i a * transMat n j b) • poleCoeffs n a b

open SmallPrime in
theorem muRatFunc_muData (n : ℕ) (i j : Fin (hDim n)) :
    muRatFunc (muDataP n i j) (muDataC n i j)
      = algebraMap ℚ[X] (RatFunc ℚ) (fPoly n i * fPoly n j)
        / algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)) := by
  rw [muDataP, muDataC]
  simp_rw [muRatFunc_sum, muRatFunc_smul, muRatFunc_Gentry]
  rw [fPoly_eq_transMat_sum n i, fPoly_eq_transMat_sum n j, Finset.sum_mul_sum, map_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hpoly : C (transMat n i a * transMat n j b) * (Dpoly (N n) ^ 8 * X ^ ((a : ℕ) + b))
      = C (transMat n i a) * (Dpoly (N n) ^ 4 * X ^ (a : ℕ))
        * (C (transMat n j b) * (Dpoly (N n) ^ 4 * X ^ (b : ℕ))) := by
    rw [C_mul, pow_add]
    ring
  rw [← mul_div_assoc, ← map_mul, hpoly]

open SmallPrime in
theorem muFunctional_muData (n : ℕ) (i j : Fin (hDim n)) :
    muFunctional (muDataP n i j) (muDataC n i j)
      = ∑ a : Fin (hDim n), ∑ b : Fin (hDim n),
          C (transMat n i a * transMat n j b) * Gentry n a b := by
  rw [muDataP, muDataC]
  simp_rw [muFunctional_sum, muFunctional_smul]
  rfl

namespace SmallPrime

theorem neg_one_pow_sq (S : ℕ) : ((-1 : ℚ) ^ S) ^ 2 = 1 := by
  rw [← pow_mul, pow_mul']
  norm_num

/-- `S_K = (K!)^{2h} (det T)²`. -/
theorem SK_eq (n : ℕ) :
    SK n = (Nat.factorial (K n) : ℚ) ^ (2 * hDim n) * (transMat n).det ^ 2 := by
  have h4 : (4 : ℚ) ^ (hDim n - 1) = (2 ^ (hDim n - 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [SK, det_transMat, h4, Finset.prod_pow, div_pow, mul_pow, mul_pow, neg_one_pow_sq, one_mul,
    ← pow_mul (Nat.factorial (N n) : ℚ) (8 * hDim n) 2, show 8 * hDim n * 2 = 16 * hDim n by ring]
  ring

end SmallPrime

open SmallPrime in
/-- `F_K = (K!)^{2h} det[μ_X(f_i f_j / D_K)]` for the explicit `μ`-data. -/
theorem FK_eq_det_muData (n : ℕ) :
    FK n = C ((Nat.factorial (K n) : ℚ) ^ (2 * hDim n))
      * (Matrix.of fun i j => muFunctional (muDataP n i j) (muDataC n i j)).det := by
  have hmat : (Matrix.of fun i j => muFunctional (muDataP n i j) (muDataC n i j))
      = (transMat n).map C * Gmat n * ((transMat n).map C).transpose := by
    rw [Matrix.mul_assoc]
    ext i j
    rw [Matrix.of_apply, muFunctional_muData]
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Gmat, Matrix.of_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [C_mul]
    ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, FK, DeltaK, SK_eq]
  simp only [map_mul, map_pow]
  ring

/-- **Equation (40)**: `F_K = S_K Δ_K = (K!)^{2h} det[μ_X(f_i f_j / D_K)]_{0 ≤ i,j < h}`, where
`μ_X(f_i f_j / D_K)` is `μ_X` applied to the (unique, `muRatFunc_inj`) `μ`-data of
`f_i f_j / D_K`. Such data exists (`muRatFunc_muData`). -/
theorem FK_eq_det_fBasis (n : ℕ) (pd : Fin (hDim n) → Fin (hDim n) → ℚ[X])
    (cd : Fin (hDim n) → Fin (hDim n) → ℕ →₀ ℚ)
    (hrep : ∀ i j, muRatFunc (pd i j) (cd i j)
      = algebraMap ℚ[X] (RatFunc ℚ) (fPoly n i * fPoly n j)
        / algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n))) :
    FK n = C ((Nat.factorial (K n) : ℚ) ^ (2 * hDim n))
      * (Matrix.of fun i j => muFunctional (pd i j) (cd i j)).det := by
  have h : ∀ i j, pd i j = muDataP n i j ∧ cd i j = muDataC n i j := fun i j =>
    muRatFunc_inj ((hrep i j).trans (muRatFunc_muData n i j).symm)
  have hM : (Matrix.of fun i j => muFunctional (pd i j) (cd i j))
      = Matrix.of fun i j => muFunctional (muDataP n i j) (muDataC n i j) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, (h i j).1, (h i j).2]
  rw [hM]
  exact FK_eq_det_muData n

/-- The `μ`-data of `f_i f_j / D_K` in (40) exists. -/
theorem fBasis_muRep_exists (n : ℕ) (i j : Fin (hDim n)) :
    ∃ (p : ℚ[X]) (c : ℕ →₀ ℚ), muRatFunc p c
      = algebraMap ℚ[X] (RatFunc ℚ) (fPoly n i * fPoly n j)
        / algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)) :=
  ⟨_, _, muRatFunc_muData n i j⟩

/-! ## The crude global bound (41) -/

namespace SmallPrime

open IntegerValued

variable {p : ℕ} [Fact p.Prime]

/-- Gauss valuation of a product: `v^G(PQ) ≥ v^G(P) + v^G(Q)` (coefficientwise). -/
theorem coeff_mul_val (P Q : ℚ[X]) {B₁ B₂ : ℤ} (hB : B₁ + B₂ ≤ 0)
    (hP : ∀ k, B₁ ≤ padicValRat p (P.coeff k)) (hQ : ∀ k, B₂ ≤ padicValRat p (Q.coeff k))
    (k : ℕ) : B₁ + B₂ ≤ padicValRat p ((P * Q).coeff k) := by
  rw [coeff_mul]
  exact padicValRat_le_sum _ _ _ hB fun x _ => padicValRat_mul_ge _ _ _ _ (hP _) (hQ _) hB

theorem coeff_prod_val {ι : Type*} (s : Finset ι) (P : ι → ℚ[X]) {B : ℤ} (hB : B ≤ 0)
    (hP : ∀ i ∈ s, ∀ k, B ≤ padicValRat p ((P i).coeff k)) :
    ∀ k, (s.card : ℤ) * B ≤ padicValRat p ((∏ i ∈ s, P i).coeff k) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro k
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.prod_empty, coeff_one]
    split_ifs <;> simp
  | insert a s has ih =>
    intro k
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has, Nat.cast_succ, add_mul, one_mul,
      add_comm]
    have hc : (0 : ℤ) ≤ s.card := Nat.cast_nonneg _
    exact coeff_mul_val _ _ (by nlinarith) (hP a (Finset.mem_insert_self a s))
      (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))) k

/-- Gauss valuation of an `h × h` determinant: `v^G(det M) ≥ h · min v^G(M_{ij})`. -/
theorem det_coeff_val {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ[X]) {B : ℤ} (hB : B ≤ 0)
    (hM : ∀ i j k, B ≤ padicValRat p ((M i j).coeff k)) (k : ℕ) :
    (h : ℤ) * B ≤ padicValRat p (M.det.coeff k) := by
  have h0 : (0 : ℤ) ≤ h := Nat.cast_nonneg _
  rw [Matrix.det_apply, finsetSum_coeff]
  apply padicValRat_le_sum _ _ _ (by nlinarith)
  intro σ _
  rw [Units.smul_def, coeff_smul, zsmul_eq_mul]
  have hprod := coeff_prod_val (p := p) Finset.univ (fun i => M (σ i) i) hB
    (fun i _ k' => hM _ _ k') k
  rw [Finset.card_univ, Fintype.card_fin] at hprod
  have h1 := padicValRat_mul_ge _ _ 0 _
    (padicValRat_intCast_nonneg (p := p) ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) hprod (by nlinarith)
  linarith

theorem compRingHom_neg_sq_injective :
    Function.Injective (Polynomial.compRingHom (-X ^ 2 : ℚ[X])) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  rw [Polynomial.coe_compRingHom_apply] at hq
  rcases Polynomial.comp_eq_zero_iff.mp hq with h | ⟨-, h⟩
  · exact h
  · exfalso
    have h2 := congrArg (fun r : ℚ[X] => r.coeff 2) h
    simp at h2

/-- The substitution `t ↦ -x²` on `ℚ(t)`. -/
noncomputable def compNegSq : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.compRingHom (-X ^ 2)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((RatFunc.algebraMap_injective ℚ).comp compRingHom_neg_sq_injective))

theorem compNegSq_alg (q : ℚ[X]) :
    compNegSq (algebraMap ℚ[X] (RatFunc ℚ) q) = algebraMap ℚ[X] (RatFunc ℚ) (q.comp (-X ^ 2)) := by
  simp only [compNegSq, RatFunc.liftRingHom_algebraMap, RingHom.comp_apply,
    Polynomial.coe_compRingHom_apply]

/-- `x⁷ R(-x²)` is `x⁷` times the substitution `t ↦ -x²` applied to `R`. -/
theorem pullbackRatFunc_eq (p : ℚ[X]) (c : ℕ →₀ ℚ) :
    pullbackRatFunc p c = algebraMap ℚ[X] (RatFunc ℚ) X ^ 7 * compNegSq (muRatFunc p c) := by
  unfold pullbackRatFunc muRatFunc
  rw [map_add, map_finsuppSum, compNegSq_alg]
  congr 1
  congr 1
  refine Finsupp.sum_congr fun j _ => ?_
  rw [map_div₀, compNegSq_alg, compNegSq_alg, C_comp, add_comp, X_comp, C_comp]

theorem prod_neg_sq (x : ℚ) (l : ℕ) :
    ∏ j ∈ Finset.range l, (-x ^ 2 + ((j : ℚ) + 1) ^ 2)
      = (-1) ^ l * ∏ j ∈ Finset.range l, (x ^ 2 - ((j : ℚ) + 1) ^ 2) := by
  rw [show (-1 : ℚ) ^ l = ∏ _j ∈ Finset.range l, (-1 : ℚ) by simp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by ring

/-- `x D_K(-x²) = (-1)^K ∏_{|r| ≤ K} (x - r)`. -/
theorem X_mul_Dpoly_comp (K : ℕ) : X * (Dpoly K).comp (-X ^ 2) = C ((-1 : ℚ) ^ K) * Wpoly K := by
  apply Polynomial.funext
  intro x
  rw [Wpoly_eq_prod_range]
  simp only [Dpoly, eval_mul, eval_X, eval_comp, eval_neg, eval_pow, eval_prod, eval_add, eval_C,
    eval_sub]
  rw [Finset.prod_congr rfl (fun (i : ℕ) _ => show x - ((i : ℚ) - K) = x + K - i by ring),
    prod_centered, prod_neg_sq]
  ring

end SmallPrime

/-- The integer-valued numerator in the `τ`-form of `(K!)² μ_X(f_i f_j / D_K)`:
`x⁷ (K!)² f_i(-x²) f_j(-x²)/D_K(-x²) = (K!)² A_{ij}(x)/∏_{|r| ≤ K} (x - r)`. -/
noncomputable def Aij (n i j : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ K n) * X ^ 8 * (fPoly n i * fPoly n j).comp (-X ^ 2)

namespace SmallPrime

variable {p : ℕ} [Fact p.Prime]

theorem natDegree_fPoly_le (n i : ℕ) : (fPoly n i).natDegree ≤ 4 * N n + i := by
  unfold fPoly
  refine natDegree_mul_le.trans ?_
  have h1 : (C ((Nat.factorial (N n) : ℚ) ^ 2)⁻¹ * Dpoly (N n)).natDegree ≤ N n :=
    (natDegree_C_mul_le _ _).trans (Dpoly_natDegree _).le
  have h2 : ((C ((Nat.factorial (N n) : ℚ) ^ 2)⁻¹ * Dpoly (N n)) ^ 4).natDegree ≤ 4 * N n :=
    natDegree_pow_le.trans (by omega)
  have h3 := qPoly_natDegree_le i
  omega

theorem natDegree_Aij_le (n i j : ℕ) :
    (Aij n i j).natDegree ≤ 8 + 2 * (4 * N n + i + (4 * N n + j)) := by
  unfold Aij
  have h1 : (C ((-1 : ℚ) ^ K n) * X ^ 8).natDegree ≤ 8 :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 8)
  have h4 : (fPoly n i * fPoly n j).natDegree ≤ 4 * N n + i + (4 * N n + j) :=
    natDegree_mul_le.trans (add_le_add (natDegree_fPoly_le n i) (natDegree_fPoly_le n j))
  have h3 : (-X ^ 2 : ℚ[X]).natDegree = 2 := by
    rw [natDegree_neg, natDegree_X_pow]
  have h2 : ((fPoly n i * fPoly n j).comp (-X ^ 2)).natDegree
      ≤ 2 * (4 * N n + i + (4 * N n + j)) := by
    refine natDegree_comp_le.trans ?_
    rw [h3]
    omega
  exact natDegree_mul_le.trans (by omega)

theorem Aij_intValued (n i j : ℕ) (m : ℤ) : 0 ≤ padicValRat p ((Aij n i j).eval (m : ℚ)) := by
  obtain ⟨w1, hw1⟩ := fPoly_comp_neg_sq_intValued n i m
  obtain ⟨w2, hw2⟩ := fPoly_comp_neg_sq_intValued n j m
  have h : (Aij n i j).eval (m : ℚ) = (((-1) ^ K n * m ^ 8 * w1 * w2 : ℤ) : ℚ) := by
    rw [Aij, mul_comp, eval_mul, eval_mul, eval_mul, eval_C, eval_pow, eval_X, hw1, hw2]
    push_cast
    try ring
  rw [h]
  exact padicValRat_intCast_nonneg _

/-- `(K!)² μ_X(f_i f_j / D_K)` in `τ`-form: its pullback data represents `(K!)² A_{ij}/W`. -/
theorem pullback_muData (n : ℕ) (i j : Fin (hDim n)) :
    tauRatFunc (pullbackPoly (C ((Nat.factorial (K n) : ℚ) ^ 2) * muDataP n i j)
        (((Nat.factorial (K n) : ℚ) ^ 2) • muDataC n i j))
        (pullbackPoles (((Nat.factorial (K n) : ℚ) ^ 2) • muDataC n i j))
      = algebraMap ℚ[X] (RatFunc ℚ) (C ((Nat.factorial (K n) : ℚ) ^ 2) * Aij n i j)
        / algebraMap ℚ[X] (RatFunc ℚ) (Wpoly (K n)) := by
  have hW0 : Wpoly (K n) ≠ 0 := (Wpoly_monic _).ne_zero
  have hs : ((-1 : ℚ) ^ K n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD' : (Dpoly (K n)).comp (-X ^ 2) ≠ 0 := by
    intro h
    have h1 := X_mul_Dpoly_comp (K n)
    rw [h, mul_zero] at h1
    exact mul_ne_zero (C_ne_zero.mpr hs) hW0 h1.symm
  have hpoly : Wpoly (K n) = C ((-1 : ℚ) ^ K n) * (X * (Dpoly (K n)).comp (-X ^ 2)) := by
    rw [X_mul_Dpoly_comp, ← mul_assoc, ← C_mul, ← mul_pow,
      show ((-1 : ℚ) * -1) = 1 by norm_num, one_pow, C_1, one_mul]
  rw [tauRatFunc_pullbackData, pullbackRatFunc_eq, muRatFunc_smul, muRatFunc_muData, map_mul,
    map_div₀, compNegSq_alg, compNegSq_alg, compNegSq_alg, C_comp, hpoly, Aij]
  have hX : algebraMap ℚ[X] (RatFunc ℚ) X ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hsC : algebraMap ℚ[X] (RatFunc ℚ) (C ((-1 : ℚ) ^ K n)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (C_ne_zero.mpr hs)
  have hDa : algebraMap ℚ[X] (RatFunc ℚ) ((Dpoly (K n)).comp (-X ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hD'
  simp only [map_mul, map_pow]
  field_simp

/-- Entry bound: every coefficient of `(K!)² μ_X(f_i f_j / D_K)` has valuation
`≥ -8⌊log_p(5K)⌋ - v_p(720)`, by Lemma 3.8 with `max(2K, d) ≤ 5K`. -/
theorem muData_entry_val (n : ℕ) (i j : Fin (hDim n)) (k : ℕ) :
    -(8 * (Nat.log p (5 * K n) : ℤ)) - (padicValNat p 720 : ℤ)
      ≤ padicValRat p ((C ((Nat.factorial (K n) : ℚ) ^ 2)
          * muFunctional (muDataP n i j) (muDataC n i j)).coeff k) := by
  have hi := i.isLt
  have hj := j.isLt
  have hn : 1 ≤ n := by
    unfold hDim at hi
    omega
  have hK : 1 ≤ K n := by
    unfold K
    omega
  have hdeg : (Aij n i j).natDegree ≤ 5 * K n := by
    refine (natDegree_Aij_le n i j).trans ?_
    unfold N K
    unfold hDim at hi hj
    omega
  rw [← muFunctional_smul, ← tauFunctional_pullbackData]
  exact tau_bound_core (by omega) le_rfl (by omega) (Aij n i j) hdeg (Aij_intValued n i j) _ _
    (pullback_muData n i j) k

end SmallPrime

open SmallPrime in
/-- **Equation (41)** (crude global bound). For every prime `p`,
`v^G_p(F_K) ≥ -8h⌊log_p(5K)⌋ - h v_p(720)`; the Gauss valuation is stated coefficientwise
(zero coefficients impose nothing, since the bound is `≤ 0`). -/
theorem FK_small_prime_bound (n p : ℕ) [Fact p.Prime] (k : ℕ) :
    -(8 * (hDim n : ℤ) * (Nat.log p (5 * K n) : ℤ)) - (hDim n : ℤ) * (padicValNat p 720 : ℤ)
      ≤ padicValRat p ((FK n).coeff k) := by
  have hFK : FK n = (Matrix.of fun i j => C ((Nat.factorial (K n) : ℚ) ^ 2)
      * muFunctional (muDataP n i j) (muDataC n i j)).det := by
    rw [FK_eq_det_muData]
    have hsm : (Matrix.of fun i j => C ((Nat.factorial (K n) : ℚ) ^ 2)
          * muFunctional (muDataP n i j) (muDataC n i j))
        = C ((Nat.factorial (K n) : ℚ) ^ 2)
          • (Matrix.of fun i j => muFunctional (muDataP n i j) (muDataC n i j)) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hsm, Matrix.det_smul, Fintype.card_fin, ← C_pow, ← pow_mul]
  have hL : (0 : ℤ) ≤ Nat.log p (5 * K n) := Nat.cast_nonneg _
  have h720 : (0 : ℤ) ≤ padicValNat p 720 := Nat.cast_nonneg _
  have h := det_coeff_val (p := p) _
    (B := -(8 * (Nat.log p (5 * K n) : ℤ)) - (padicValNat p 720 : ℤ)) (by linarith)
    (fun i j k' => by simpa only [Matrix.of_apply] using muData_entry_val n i j k') k
  rw [hFK]
  calc _ = (hDim n : ℤ) * (-(8 * (Nat.log p (5 * K n) : ℤ)) - (padicValNat p 720 : ℤ)) := by
        ring
    _ ≤ _ := h

end ZetaSeven
