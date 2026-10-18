import ZetaSeven.Completion
import ZetaSeven.ReflectionDifference
import ZetaSeven.BernoulliMult

/-!
# The distribution formula (paper Section 3.4, Lemmas 3.6-3.7, equations (34)-(36))

Prince Anand, "Zeta 7 is Irrational", Section 3.4. Let `p ≥ 11` be prime.

* `poleSeries s` is the expansion `1/(x - s) = -∑_d x^d/s^{d+1}` at `x = 0`. For `v_p(s) < 0`
  it lies in the Tate algebra (`poleSeries_isRestricted`), and `tauAn p s = τ^an(1/(x - s))` is
  `τ` (32) applied to it; equation (35) is `tauAn_eq`.
* (34): `cP p = C_p = ∑_{a=1}^{p-1} τ^an(1/(x + a/p))` and `distY p = Y = p⁷ X + C_p`.
* Lemma 3.6 is `cP_mem`: `C_p ∈ p⁷ ℤ_p`.
* For `g = P + ∑_r d_r/(x - r)` (partial-fraction data, as in `ZetaSeven.TauPullback`) and
  `0 ≤ a < p`, `g(a + p z)` is the element of `B_T` with analytic part `substAnalytic p a P d`
  (the polynomial `P(a + p z)` plus the expansions of `d_r/(a - r + p z)` for `r ≢ a mod p`) and
  principal parts `substPrincipal p a d s/(z - s)` at the integers `s = (r - a)/p` for
  `r ≡ a mod p` (`substPoles p a d`). `substData_spec` checks that this data is the Laurent
  expansion at `z = 0` of the rational function `g(a + p z)` (`ratFuncAffine`), and the analytic
  part lies in the Tate algebra (`substAnalytic_isRestricted`).
* Lemma 3.7 (36) is `distribution_formula`:
  `τ_X(g) = p^{-6} ∑_{a=0}^{p-1} τ^ext_Y(g(a + p z))`.

The proof follows the paper. Polynomials reduce to the Bernoulli multiplication formula
(`sum_tauPoly_comp_affine`). For simple poles, `τ^an` satisfies the difference identity
`τ^an(1/(x - (s - 1))) - τ^an(1/(x - s)) = -s⁻⁷` (`tauAn_sub_one`, from the difference identity
(30) on polynomials and Fubini in `ℚ_p`), exactly as the pole values `H⁷_{d(r)}` do
(`H7_dIndex_sub_one_sub`). Starting from the pole `1/x`, induction on the pole `r ∈ ℤ` in both
directions then gives the formula at every simple integer pole (`sum_poleTerm`); this replaces the
paper's appeal to reflection for the negative poles.
-/

namespace ZetaSeven

open Polynomial Finset Filter Topology

/-! ## The substitution `g(x) ↦ g(a + b x)` and the expansion of `1/(x - s)` -/

theorem affine_comp_inv (a : ℚ) {b : ℚ} (hb : b ≠ 0) :
    (C a + C b * X : ℚ[X]).comp (C b⁻¹ * (X - C a)) = X := by
  rw [add_comp, mul_comp, C_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hb, C_1,
    one_mul]
  ring

/-- The substitution `g(x) ↦ g(a + b x)` on rational functions, for `b ≠ 0`. -/
noncomputable def ratFuncAffine (a : ℚ) {b : ℚ} (hb : b ≠ 0) : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom ((algebraMap ℚ[X] (RatFunc ℚ)).comp (compRingHom (C a + C b * X)))
    (nonZeroDivisors_le_comap_comp (affine_comp_inv a hb))

theorem ratFuncAffine_algebraMap (a : ℚ) {b : ℚ} (hb : b ≠ 0) (P : ℚ[X]) :
    ratFuncAffine a hb (algebraMap ℚ[X] (RatFunc ℚ) P)
      = algebraMap ℚ[X] (RatFunc ℚ) (P.comp (C a + C b * X)) := by
  unfold ratFuncAffine
  rw [RatFunc.liftRingHom_algebraMap, RingHom.comp_apply, coe_compRingHom_apply]

/-- The expansion `1/(x - s) = -∑_d x^d/s^{d+1}` at `x = 0` (proof of (35)). -/
noncomputable def poleSeries (s : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun d => -(s⁻¹ ^ (d + 1))

theorem poleSeries_eq_neg_invUnitsSub {s : ℚ} (hs : s ≠ 0) :
    poleSeries s = -PowerSeries.invUnitsSub (Units.mk0 s hs) := by
  ext n
  rw [poleSeries, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_invUnitsSub, divp_eq_div,
    Units.val_pow_eq_pow_val, Units.val_mk0, one_div, inv_pow]

/-- `poleSeries s` is the expansion of `1/(x - s)`: `poleSeries s · (x - s) = 1`. -/
theorem poleSeries_mul {s : ℚ} (hs : s ≠ 0) :
    poleSeries s * (PowerSeries.X - PowerSeries.C s) = 1 := by
  have h := PowerSeries.invUnitsSub_mul_sub (Units.mk0 s hs)
  rw [Units.val_mk0] at h
  rw [poleSeries_eq_neg_invUnitsSub hs, neg_mul, ← mul_neg, neg_sub, h]

/-! ## Polynomials: the Bernoulli multiplication formula -/

/-- `L((x + y)^m) = B_m(y)`. -/
theorem bernoulliL_X_add_C_pow (y : ℚ) (m : ℕ) :
    bernoulliL ((X + C y) ^ m) = (Polynomial.bernoulli m).eval y := by
  rw [add_pow, bernoulliL_sum, Polynomial.bernoulli, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_monomial, ← C_pow, ← C_eq_natCast, mul_assoc, ← C_mul, mul_comm (X ^ k),
    bernoulliL_C_mul_X_pow]
  ring

/-- `∑_{a=0}^{p-1} L((a + p z)^m) = p^m ∑_a B_m(a/p) = p B_m`, by the multiplication formula. -/
theorem sum_bernoulliL_affine_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    ∑ a ∈ range p, bernoulliL ((C (a : ℚ) + C (p : ℚ) * X) ^ m) = p * _root_.bernoulli m := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h1 : ∀ a : ℕ, (C (a : ℚ) + C (p : ℚ) * X) ^ m
      = C ((p : ℚ) ^ m) * (X + C ((a : ℚ) / p)) ^ m := by
    intro a
    have hc : (p : ℚ) * ((a : ℚ) / p) = a := mul_div_cancel₀ _ hpQ
    rw [C_pow, ← mul_pow, mul_add, ← C_mul, hc, add_comm]
  have h2 := congrArg (Polynomial.eval 0) (bernoulli_mul (n := m) hp)
  simp only [eval_finsetSum, eval_comp, eval_add, eval_X, eval_C, eval_mul, zero_add, mul_zero,
    Polynomial.bernoulli_eval_zero] at h2
  simp only [h1, bernoulliL_C_mul, bernoulliL_X_add_C_pow, ← Finset.mul_sum, h2]
  rw [← mul_assoc, mul_div_cancel₀ _ (pow_ne_zero m hpQ)]

theorem sum_bernoulliL_comp_affine {p : ℕ} (hp : p ≠ 0) (R : ℚ[X]) :
    ∑ a ∈ range p, bernoulliL (R.comp (C (a : ℚ) + C (p : ℚ) * X)) = p * bernoulliL R := by
  induction R using Polynomial.induction_on' with
  | add R₁ R₂ h₁ h₂ =>
    simp only [add_comp, bernoulliL_add, Finset.sum_add_distrib, h₁, h₂, mul_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, bernoulliL_C_mul_X_pow]
    simp only [mul_comp, C_comp, X_pow_comp, bernoulliL_C_mul]
    rw [← Finset.mul_sum, sum_bernoulliL_affine_pow hp]
    ring

theorem iterate_derivative_comp_affine (Q : ℚ[X]) (a b : ℚ) (k : ℕ) :
    derivative^[k] (Q.comp (C a + C b * X))
      = C (b ^ k) * (derivative^[k] Q).comp (C a + C b * X) := by
  induction k generalizing Q with
  | zero => simp
  | succ k ih =>
    have hL : derivative (C a + C b * X : ℚ[X]) = C b := by
      rw [derivative_add, derivative_C, derivative_C_mul_X, zero_add]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp, hL,
      iterate_derivative_C_mul, ih, pow_succ, C_mul]
    ring

/-- Lemma 3.7 for polynomials: `∑_{a=0}^{p-1} τ(g(a + p z)) = p⁶ τ(g)`. -/
theorem sum_tauPoly_comp_affine {p : ℕ} (hp : p ≠ 0) (Q : ℚ[X]) :
    ∑ a ∈ range p, tauPoly (Q.comp (C (a : ℚ) + C (p : ℚ) * X)) = (p : ℚ) ^ 6 * tauPoly Q := by
  unfold tauPoly
  simp only [iterate_derivative_comp_affine, bernoulliL_C_mul]
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_bernoulliL_comp_affine hp]
  ring

/-! ## The difference identity for `κ` -/

theorem tauPoly_X_add_one_pow (n : ℕ) :
    tauPoly ((X + 1) ^ n) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * kappa k := by
  rw [add_pow, tauPoly_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, ← C_eq_natCast, mul_comm (X ^ k), tauPoly_C_mul_X_pow, kappa_eq]
  ring

/-- `∑_k (n choose k) κ_k = τ((x + 1)^n) = κ_n + [n = 6]`: the difference identity (30) on
`x^n`. -/
theorem sum_choose_mul_kappa (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * kappa k = kappa n + if 6 = n then 1 else 0 := by
  have h := tauPoly_comp_X_add_one_sub (X ^ n)
  rw [X_pow_comp, coeff_X_pow] at h
  have h2 := tauPoly_add ((X + 1) ^ n - X ^ n) (X ^ n)
  rw [sub_add_cancel, h, tauPoly_X_add_one_pow] at h2
  rw [h2, kappa]
  ring

/-! ## `τ` on the Tate algebra: linearity and the analytic pole values `τ^an` -/

section Padic

variable {p : ℕ} [Fact p.Prime]

theorem tateTau_zero : tateTau (0 : PowerSeries ℚ_[p]) = 0 := by
  simp [tateTau]

theorem tateTau_C_mul (c : ℚ_[p]) (f : PowerSeries ℚ_[p]) :
    tateTau (PowerSeries.C c * f) = c * tateTau f := by
  unfold tateTau
  simp only [PowerSeries.coeff_C_mul, mul_assoc]
  exact tsum_mul_left

theorem tateTau_sum (hp7 : 7 ≤ p) {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ_[p])
    (hf : ∀ i ∈ s, (f i).IsRestricted 1) : tateTau (∑ i ∈ s, f i) = ∑ i ∈ s, tateTau (f i) := by
  unfold tateTau
  simp only [map_sum, Finset.sum_mul]
  exact Summable.tsum_finsetSum fun i hi => summable_tateTau hp7 (hf i hi)

theorem isRestricted_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ_[p])
    (hf : ∀ i ∈ s, (f i).IsRestricted 1) : (∑ i ∈ s, f i).IsRestricted 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact PowerSeries.isRestricted_zero 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact PowerSeries.isRestricted.add 1 (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem norm_coeff_map_poleSeries (s : ℚ) (d : ℕ) :
    ‖PowerSeries.coeff d (PowerSeries.map (Rat.castHom ℚ_[p]) (poleSeries s))‖
      = ‖((s⁻¹ : ℚ) : ℚ_[p])‖ ^ (d + 1) := by
  rw [PowerSeries.coeff_map, poleSeries, PowerSeries.coeff_mk, Rat.coe_castHom, Rat.cast_neg,
    norm_neg, Rat.cast_pow, norm_pow]

theorem norm_inv_lt_one {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) : ‖((s⁻¹ : ℚ) : ℚ_[p])‖ < 1 := by
  rw [Rat.cast_inv, norm_inv]
  exact inv_lt_one_of_one_lt₀ hs

/-- For `v_p(s) < 0` the expansion of `1/(x - s)` lies in the Tate algebra. -/
theorem poleSeries_isRestricted {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    (PowerSeries.map (Rat.castHom ℚ_[p]) (poleSeries s)).IsRestricted 1 := by
  rw [PowerSeries.isRestricted_iff']
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (norm_inv_lt_one hs)).mul_const ‖((s⁻¹ : ℚ) : ℚ_[p])‖
  rw [zero_mul] at h
  refine h.congr fun d => ?_
  rw [norm_coeff_map_poleSeries, one_pow, mul_one, pow_succ]

/-- `τ^an(1/(x - s))` (35): `τ` (32) of the expansion of `1/(x - s)` at `0`, which lies in the
Tate algebra when `v_p(s) < 0` (`poleSeries_isRestricted`). -/
noncomputable def tauAn (p : ℕ) [Fact p.Prime] (s : ℚ) : ℚ_[p] :=
  tateTau (PowerSeries.map (Rat.castHom ℚ_[p]) (poleSeries s))

theorem tauAn_eq_tsum (s : ℚ) :
    tauAn p s = ∑' d : ℕ, -(((s⁻¹ : ℚ) : ℚ_[p]) ^ (d + 1)) * ((kappa d : ℚ) : ℚ_[p]) := by
  unfold tauAn tateTau
  refine tsum_congr fun d => ?_
  rw [PowerSeries.coeff_map, poleSeries, PowerSeries.coeff_mk, Rat.coe_castHom, Rat.cast_neg,
    Rat.cast_pow]

theorem summable_tauAn (hp7 : 7 ≤ p) {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    Summable fun d : ℕ => -(((s⁻¹ : ℚ) : ℚ_[p]) ^ (d + 1)) * ((kappa d : ℚ) : ℚ_[p]) := by
  refine (summable_tateTau hp7 (poleSeries_isRestricted hs)).congr fun d => ?_
  rw [PowerSeries.coeff_map, poleSeries, PowerSeries.coeff_mk, Rat.coe_castHom, Rat.cast_neg,
    Rat.cast_pow]

/-- A double series on `ℕ × ℕ` supported on `k ≤ n`, with terms bounded by `M ρ^n` for some
`ρ < 1`, is summable in `ℚ_p`. -/
theorem summable_of_norm_le_geom {f : ℕ × ℕ → ℚ_[p]} {ρ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hM : 0 ≤ M) (hbound : ∀ n k, ‖f (n, k)‖ ≤ M * ρ ^ n)
    (hzero : ∀ n k, n < k → f (n, k) = 0) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < M + 1)) hρ
  rw [Filter.eventually_cofinite]
  refine (Finset.range N ×ˢ Finset.range N : Finset (ℕ × ℕ)).finite_toSet.subset ?_
  rintro ⟨n, k⟩ hx
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hx
  have hkn : k ≤ n := by
    by_contra h
    rw [hzero n k (by omega), norm_zero] at hx
    linarith
  have hnN : n < N := by
    by_contra h
    have h1 : ρ ^ n ≤ ρ ^ N := pow_le_pow_of_le_one hρ0 hρ.le (by omega)
    have h2 : (M + 1) * ρ ^ N < ε := by
      have := mul_lt_mul_of_pos_left hN (by linarith : (0 : ℝ) < M + 1)
      rwa [mul_div_cancel₀ _ (by linarith : (M + 1 : ℝ) ≠ 0)] at this
    have h3 : M * ρ ^ n ≤ (M + 1) * ρ ^ N :=
      mul_le_mul (by linarith) h1 (pow_nonneg hρ0 _) (by linarith)
    linarith [hbound n k]
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨hnN, lt_of_le_of_lt hkn hnN⟩

/-- The difference identity for `τ^an`: for `v_p(s) < 0`,
`τ^an(1/(x - (s - 1))) - τ^an(1/(x - s)) = -s⁻⁷`, the analogue of
`H⁷_{d(r-1)} - H⁷_{d(r)} = -r⁻⁷`. With `w = 1/s`, the expansion of `1/(x + 1 - s)` is
`-∑_n w^{n+1} (1 + x)^n`; Fubini in `ℚ_p` and `τ((1 + x)^n) = κ_n + [n = 6]` give the claim. -/
theorem tauAn_sub_one (hp7 : 7 ≤ p) {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    tauAn p (s - 1) - tauAn p s = -(((s⁻¹ : ℚ) : ℚ_[p]) ^ 7) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero, norm_zero] at hs
    linarith
  have hT := tauAn_eq_tsum (p := p) s
  have hA := summable_tauAn hp7 hs
  have key : (s⁻¹ / (1 - s⁻¹) : ℚ) = (s - 1)⁻¹ := by
    rw [show (1 : ℚ) - s⁻¹ = (s - 1) / s by
        rw [eq_div_iff hs0, sub_mul, one_mul, inv_mul_cancel₀ hs0],
      div_div_eq_mul_div, inv_mul_cancel₀ hs0, one_div]
  set w : ℚ_[p] := ((s⁻¹ : ℚ) : ℚ_[p]) with hw_def
  have hw : ‖w‖ < 1 := norm_inv_lt_one hs
  have hw' : w / (1 - w) = (((s - 1)⁻¹ : ℚ) : ℚ_[p]) := by
    rw [hw_def, ← key]
    norm_cast
  -- the coefficients of `1/(x - (s - 1))` as series in `w`
  have hcoeff : ∀ k : ℕ, HasSum (fun n : ℕ => -(w ^ (n + 1)) * (n.choose k : ℚ_[p]))
      (-((((s - 1)⁻¹ : ℚ) : ℚ_[p]) ^ (k + 1))) := by
    intro k
    have hz : ∑ i ∈ range k, -(w ^ (i + 1)) * (i.choose k : ℚ_[p]) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi), Nat.cast_zero, mul_zero]
    have hval : -(w ^ (k + 1)) * (1 / (1 - w) ^ (k + 1))
        = -((((s - 1)⁻¹ : ℚ) : ℚ_[p]) ^ (k + 1)) := by
      rw [neg_mul, one_div, ← div_eq_mul_inv, ← div_pow, hw']
    have h1 : HasSum (fun n : ℕ => -(w ^ (n + k + 1)) * ((n + k).choose k : ℚ_[p]))
        (-((((s - 1)⁻¹ : ℚ) : ℚ_[p]) ^ (k + 1))) := by
      rw [← hval]
      convert (hasSum_choose_mul_geometric_of_norm_lt_one k hw).mul_left (-(w ^ (k + 1)))
        using 1
      funext n
      ring
    exact (hasSum_nat_add_iff' k).mp (by rw [hz, sub_zero]; exact h1)
  -- Fubini
  have hFsum : Summable (Function.uncurry fun n k : ℕ =>
      -(w ^ (n + 1)) * (n.choose k : ℚ_[p]) * ((kappa k : ℚ) : ℚ_[p])) := by
    refine summable_of_norm_le_geom (norm_nonneg w) hw (Nat.cast_nonneg p) (fun n k => ?_)
      (fun n k hnk => ?_)
    · simp only [Function.uncurry_apply_pair, norm_mul, norm_neg, norm_pow]
      have h1 : ‖w‖ ^ (n + 1) ≤ ‖w‖ ^ n :=
        pow_le_pow_of_le_one (norm_nonneg w) hw.le (by omega)
      have h2 := padic_norm_natCast_le_one (p := p) (n.choose k)
      have h3 := norm_kappa_le hp7 k
      calc _ ≤ ‖w‖ ^ n * 1 * p :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) h3
              (norm_nonneg _) (by positivity)
        _ = p * ‖w‖ ^ n := by ring
    · simp only [Function.uncurry_apply_pair, Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero,
        mul_zero, zero_mul]
  have hrow : ∀ n : ℕ, ∑' k, -(w ^ (n + 1)) * (n.choose k : ℚ_[p]) * ((kappa k : ℚ) : ℚ_[p])
      = -(w ^ (n + 1)) * ((kappa n : ℚ) : ℚ_[p])
        + -(w ^ (n + 1)) * (((if 6 = n then 1 else 0 : ℚ)) : ℚ_[p]) := by
    intro n
    rw [tsum_eq_sum (s := range (n + 1))]
    · rw [← mul_add, ← Rat.cast_add, ← sum_choose_mul_kappa, Rat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Rat.cast_mul, Rat.cast_natCast]
      ring
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
  have hL : tauAn p (s - 1)
      = ∑' k, ∑' n, -(w ^ (n + 1)) * (n.choose k : ℚ_[p]) * ((kappa k : ℚ) : ℚ_[p]) := by
    rw [tauAn_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [tsum_mul_right, (hcoeff k).tsum_eq]
  have hB : Summable fun n : ℕ => -(w ^ (n + 1)) * (((if 6 = n then 1 else 0 : ℚ)) : ℚ_[p]) := by
    refine (hasSum_single 6 fun n hn => ?_).summable
    rw [ite_eq_right (Ne.symm hn), Rat.cast_zero, mul_zero]
  have hB' : ∑' n : ℕ, -(w ^ (n + 1)) * (((if 6 = n then 1 else 0 : ℚ)) : ℚ_[p])
      = -(w ^ (6 + 1)) := by
    rw [tsum_eq_single 6]
    · rw [ite_eq_left rfl, Rat.cast_one, mul_one]
    · intro n hn
      rw [ite_eq_right (Ne.symm hn), Rat.cast_zero, mul_zero]
  rw [hL, hFsum.tsum_comm, tsum_congr hrow, hA.tsum_add hB, hT, hB']
  ring

end Padic

end ZetaSeven
