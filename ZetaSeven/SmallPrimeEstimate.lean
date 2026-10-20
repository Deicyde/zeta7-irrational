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

theorem padicValRat_binomPoly_eval_int_nonneg (k : ℕ) (z : ℤ) :
    0 ≤ padicValRat p ((binomPoly k).eval (z : ℚ)) := by
  rw [binomPoly_eval_int]
  exact padicValRat_intCast_nonneg _

theorem natDegree_binomPoly_le (k : ℕ) : (binomPoly k).natDegree ≤ k := by
  unfold binomPoly
  refine (natDegree_mul_C_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  rw [Finset.sum_congr rfl (fun i _ => natDegree_X_sub_C (i : ℚ))]
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

end ZetaSeven
