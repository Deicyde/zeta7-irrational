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

theorem kappa_eq_zero_of_lt {d : ℕ} (hd : d < 5) : kappa d = 0 := by
  rw [kappa_eq, Nat.descFactorial_eq_zero_iff_lt.mpr hd, Nat.cast_zero, zero_mul, zero_div]

theorem kappa_five : kappa 5 = 1 / 6 := by
  rw [kappa_eq, show Nat.descFactorial 5 5 = 120 from rfl, Nat.sub_self, _root_.bernoulli_zero]
  norm_num

theorem kappa_six : kappa 6 = -1 / 2 := by
  rw [kappa_eq, show Nat.descFactorial 6 5 = 720 from rfl, show 6 - 5 = 1 from rfl,
    _root_.bernoulli_one]
  norm_num

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
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hx
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

/-! ## Equation (34), equation (35) and Lemma 3.6 -/

/-- (34): `C_p = ∑_{a=1}^{p-1} τ^an(1/(x + a/p))`. -/
noncomputable def cP (p : ℕ) [Fact p.Prime] : ℚ_[p] :=
  ∑ a ∈ Finset.Ico 1 p, tauAn p (-((a : ℚ) / p))

/-- (34): the parameter `Y = p⁷ X + C_p` (here `X` is the indeterminate of `ℚ_p[X]`). -/
noncomputable def distY (p : ℕ) [Fact p.Prime] : Polynomial ℚ_[p] :=
  C ((p : ℚ_[p]) ^ 7) * X + C (cP p)

/-- Equation (35): for `v_p(s) < 0`,
`τ^an(1/(x - s)) = -(1/720) ∑_{e ≥ 0} ((e + 5)!/e!) B_e / s^{e+6}`. -/
theorem tauAn_eq (hp7 : 7 ≤ p) {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    tauAn p s = -(1 / 720) * ∑' e : ℕ,
      (((((e + 5).factorial : ℚ) / e.factorial * _root_.bernoulli e / s ^ (e + 6) : ℚ)) :
        ℚ_[p]) := by
  have hz : ∑ d ∈ range 5, -(((s⁻¹ : ℚ) : ℚ_[p]) ^ (d + 1)) * ((kappa d : ℚ) : ℚ_[p]) = 0 :=
    Finset.sum_eq_zero fun d hd => by
      rw [kappa_eq_zero_of_lt (Finset.mem_range.mp hd), Rat.cast_zero, mul_zero]
  rw [tauAn_eq_tsum, ← (summable_tauAn hp7 hs).sum_add_tsum_nat_add 5, hz, zero_add,
    ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  have h := Nat.factorial_mul_descFactorial (show 5 ≤ e + 5 by omega)
  rw [Nat.add_sub_cancel] at h
  have hdesc : ((e + 5).factorial : ℚ) / e.factorial = ((e + 5).descFactorial 5 : ℚ) := by
    rw [← h, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero e))]
  rw [hdesc, kappa_eq, Nat.add_sub_cancel]
  push_cast
  rw [inv_pow]
  ring

/-- `τ^an(1/(x - s)) = -s⁻⁶/6 + s⁻⁷/2 + ∑_e (-s^{-(e+8)}) κ_{e+7}`, using `κ_d = 0` for `d < 5`,
`κ₅ = 1/6` and `κ₆ = -1/2`. -/
theorem tauAn_split (hp7 : 7 ≤ p) {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    tauAn p s = -(((s⁻¹ : ℚ) : ℚ_[p]) ^ 6) / 6 + ((s⁻¹ : ℚ) : ℚ_[p]) ^ 7 / 2
      + ∑' e : ℕ, -(((s⁻¹ : ℚ) : ℚ_[p]) ^ (e + 7 + 1)) * ((kappa (e + 7) : ℚ) : ℚ_[p]) := by
  rw [tauAn_eq_tsum, ← (summable_tauAn hp7 hs).sum_add_tsum_nat_add 7]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, kappa_five, kappa_six,
    kappa_eq_zero_of_lt (show 0 < 5 by norm_num), kappa_eq_zero_of_lt (show 1 < 5 by norm_num),
    kappa_eq_zero_of_lt (show 2 < 5 by norm_num), kappa_eq_zero_of_lt (show 3 < 5 by norm_num),
    kappa_eq_zero_of_lt (show 4 < 5 by norm_num)]
  push_cast
  ring

theorem norm_tail_le (hp7 : 7 ≤ p) {s : ℚ} (hs : 1 < ‖(s : ℚ_[p])‖) :
    ‖∑' e : ℕ, -(((s⁻¹ : ℚ) : ℚ_[p]) ^ (e + 7 + 1)) * ((kappa (e + 7) : ℚ) : ℚ_[p])‖
      ≤ p * ‖((s⁻¹ : ℚ) : ℚ_[p])‖ ^ 8 := by
  have hw := (norm_inv_lt_one hs).le
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun e => ?_
  rw [norm_mul, norm_neg, norm_pow, mul_comm (p : ℝ)]
  exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hw (by omega)) (norm_kappa_le hp7 _)
    (norm_nonneg _) (by positivity)

theorem norm_natCast_eq_one_of_lt {a : ℕ} (ha0 : 0 < a) (hap : a < p) : ‖(a : ℚ_[p])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (Nat.coprime_of_lt_prime ha0.ne' hap Fact.out)

theorem norm_neg_div_p {a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    ‖((-((a : ℚ) / p) : ℚ) : ℚ_[p])‖ = p := by
  rw [Rat.cast_neg, norm_neg, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, norm_div,
    norm_natCast_eq_one_of_lt ha0 hap, Padic.norm_p, one_div, inv_inv]

theorem norm_int_le_inv_of_dvd {k : ℤ} (hk : (p : ℤ) ∣ k) : ‖(k : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨m, rfl⟩ := hk
  rw [Int.cast_mul, Int.cast_natCast, norm_mul, Padic.norm_p]
  exact mul_le_of_le_one_right (inv_nonneg.mpr (Nat.cast_nonneg p)) (Padic.norm_int_le_one m)

theorem sum_range_zmod_pow (i : ℕ) :
    ∑ a ∈ range p, (a : ZMod p) ^ i = ∑ x : ZMod p, x ^ i :=
  Finset.sum_nbij' (fun a : ℕ => (a : ZMod p)) (fun x => x.val) (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun _ ha => ZMod.val_cast_of_lt (Finset.mem_range.mp ha))
    (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)

/-- `p ∣ ∑_{a=1}^{p-1} a^{p-7}` for `p ≥ 11`, since `0 < p - 7 < p - 1`. -/
theorem prime_dvd_sum_pow (hp11 : 11 ≤ p) :
    (p : ℤ) ∣ ∑ a ∈ Finset.Ico 1 p, (a : ℤ) ^ (p - 7) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have h0 : ∑ a ∈ range p, (a : ZMod p) ^ (p - 7)
      = ((0 : ℕ) : ZMod p) ^ (p - 7) + ∑ a ∈ Finset.Ico 1 p, (a : ZMod p) ^ (p - 7) :=
    Finset.sum_range_eq_add_Ico (fun a : ℕ => (a : ZMod p) ^ (p - 7)) (by omega)
  rw [Nat.cast_zero, zero_pow (by omega : p - 7 ≠ 0), zero_add, sum_range_zmod_pow] at h0
  rw [← h0]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 7) (by rw [ZMod.card]; omega)

/-- Proof of Lemma 3.6, the `e = 0` term: `∑_{a=1}^{p-1} a⁻⁶ ≡ ∑_a a^{p-7} ≡ 0 (mod p)` for
`p ≥ 11`. -/
theorem norm_sum_inv_pow_six_le (hp11 : 11 ≤ p) :
    ‖((∑ a ∈ Finset.Ico 1 p, (a : ℚ)⁻¹ ^ 6 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hpp : p.Prime := Fact.out
  have hid : ∀ a ∈ Finset.Ico 1 p, (a : ℚ)⁻¹ ^ 6
      = (((a : ℤ) ^ (p - 7) : ℤ) : ℚ) + (((1 - (a : ℤ) ^ (p - 1) : ℤ) : ℚ)) * (a : ℚ)⁻¹ ^ 6 := by
    intro a ha
    have ha1 := (Finset.mem_Ico.mp ha).1
    have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow : (a : ℚ) ^ (p - 1) = (a : ℚ) ^ (p - 7) * (a : ℚ) ^ 6 := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    rw [hpow, sub_mul, one_mul, mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, mul_one]
    ring
  rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib, Rat.cast_add, ← Int.cast_sum,
    Rat.cast_intCast]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact norm_int_le_inv_of_dvd (prime_dvd_sum_pow hp11)
  · rw [Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg p)) fun a ha => ?_
    obtain ⟨ha1, hap⟩ := Finset.mem_Ico.mp ha
    have hdvd : (p : ℤ) ∣ 1 - (a : ℤ) ^ (p - 1) :=
      (Int.ModEq.pow_card_sub_one_eq_one hpp
        (Nat.isCoprime_iff_coprime.mpr (Nat.coprime_of_lt_prime (by omega) hap hpp).symm)).dvd
    rw [Rat.cast_mul, Rat.cast_intCast, norm_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast,
      norm_pow, norm_inv, norm_natCast_eq_one_of_lt (by omega) hap, inv_one, one_pow, mul_one]
    exact norm_int_le_inv_of_dvd hdvd

theorem norm_split_le {u v T : ℚ_[p]} {B : ℝ} (hv : ‖v / 2‖ ≤ B) (hT : ‖T‖ ≤ B) :
    ‖-u / 6 + v / 2 + T + u / 6‖ ≤ B := by
  rw [show -u / 6 + v / 2 + T + u / 6 = v / 2 + T by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv hT)

/-- **Lemma 3.6** in norm form: `|C_p|_p ≤ p⁻⁷` for every prime `p ≥ 11`. The `e = 0` terms
`-p⁶/(6a⁶)` sum to `0` mod `p⁷` (`norm_sum_inv_pow_six_le`), the `e = 1` terms are `-p⁷/(2a⁷)`,
and the `e ≥ 2` terms have valuation `≥ e + 6 - 1 ≥ 7` by Lemma 3.4. -/
theorem norm_cP_le (hp11 : 11 ≤ p) : ‖cP p‖ ≤ (p : ℝ)⁻¹ ^ 7 := by
  have hp7 : 7 ≤ p := by omega
  have hpp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpinv : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hcop : ∀ n : ℕ, n ≤ 6 → 0 < n → ‖(n : ℚ_[p])‖ = 1 := fun n hn hn0 =>
    norm_natCast_eq_one_of_lt hn0 (by omega)
  have h2 : ‖(2 : ℚ_[p])‖ = 1 := by exact_mod_cast hcop 2 (by norm_num) (by norm_num)
  have h6 : ‖(6 : ℚ_[p])‖ = 1 := by exact_mod_cast hcop 6 (by norm_num) (by norm_num)
  have hterm : ∀ a ∈ Finset.Ico 1 p,
      ‖tauAn p (-((a : ℚ) / p)) + (p : ℚ_[p]) ^ 6 * (((a : ℚ)⁻¹ ^ 6 : ℚ) : ℚ_[p]) / 6‖
        ≤ (p : ℝ)⁻¹ ^ 7 := by
    intro a ha
    obtain ⟨ha1, hap⟩ := Finset.mem_Ico.mp ha
    have hs := norm_neg_div_p (p := p) (by omega : 0 < a) hap
    have hs1 : 1 < ‖((-((a : ℚ) / p) : ℚ) : ℚ_[p])‖ := by
      rw [hs]
      exact_mod_cast hpp.one_lt
    have hw : ‖(((-((a : ℚ) / p))⁻¹ : ℚ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
      rw [Rat.cast_inv, norm_inv, hs]
    have hq : ((-((a : ℚ) / p))⁻¹) ^ 6 = (p : ℚ) ^ 6 * (a : ℚ)⁻¹ ^ 6 := by
      rw [inv_neg, Even.neg_pow ⟨3, rfl⟩, inv_div, div_pow, div_eq_mul_inv, inv_pow]
    have hw6 : (((-((a : ℚ) / p))⁻¹ : ℚ) : ℚ_[p]) ^ 6
        = (p : ℚ_[p]) ^ 6 * (((a : ℚ)⁻¹ ^ 6 : ℚ) : ℚ_[p]) := by
      exact_mod_cast hq
    rw [tauAn_split hp7 hs1, ← hw6]
    refine norm_split_le ?_ ?_
    · rw [norm_div, norm_pow, hw, h2, div_one]
    · refine (norm_tail_le hp7 hs1).trans (le_of_eq ?_)
      rw [hw, show (p : ℝ) * (p : ℝ)⁻¹ ^ 8 = (p : ℝ)⁻¹ ^ 7 * ((p : ℝ) * (p : ℝ)⁻¹) by ring,
        mul_inv_cancel₀ hp0.ne', mul_one]
  have hcP : cP p = ∑ a ∈ Finset.Ico 1 p, (tauAn p (-((a : ℚ) / p))
        + (p : ℚ_[p]) ^ 6 * (((a : ℚ)⁻¹ ^ 6 : ℚ) : ℚ_[p]) / 6)
      + -((p : ℚ_[p]) ^ 6 * (((∑ a ∈ Finset.Ico 1 p, (a : ℚ)⁻¹ ^ 6 : ℚ)) : ℚ_[p]) / 6) := by
    rw [cP, Finset.sum_add_distrib, Rat.cast_sum, Finset.mul_sum, Finset.sum_div]
    ring
  rw [hcP]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hpinv 7) hterm
  · rw [norm_neg, norm_div, norm_mul, norm_pow, Padic.norm_p, h6, div_one]
    calc (p : ℝ)⁻¹ ^ 6 * ‖((∑ a ∈ Finset.Ico 1 p, (a : ℚ)⁻¹ ^ 6 : ℚ) : ℚ_[p])‖
        ≤ (p : ℝ)⁻¹ ^ 6 * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_sum_inv_pow_six_le hp11) (pow_nonneg hpinv 6)
      _ = (p : ℝ)⁻¹ ^ 7 := by ring

/-- **Lemma 3.6**: `C_p ∈ p⁷ ℤ_p` for every prime `p ≥ 11`. -/
theorem cP_mem (hp11 : 11 ≤ p) : ∃ c : ℤ_[p], cP p = (p : ℚ_[p]) ^ 7 * c := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0' : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnorm : ‖cP p / (p : ℚ_[p]) ^ 7‖ ≤ 1 := by
    rw [norm_div, norm_pow, Padic.norm_p, div_le_one (pow_pos (inv_pos.mpr hp0) 7)]
    exact norm_cP_le hp11
  refine ⟨⟨cP p / (p : ℚ_[p]) ^ 7, hnorm⟩, ?_⟩
  show cP p = (p : ℚ_[p]) ^ 7 * (cP p / (p : ℚ_[p]) ^ 7)
  rw [mul_div_cancel₀ _ (pow_ne_zero 7 hp0')]

end Padic

/-! ## The element `g(a + p z)` of `B_T` -/

/-- Analytic part of `g(a + p z)` for `g = P + ∑_r d_r/(x - r)`: the polynomial `P(a + p z)` plus,
for each pole `r ≢ a (mod p)`, the expansion at `z = 0` of
`d_r/(a - r + p z) = (d_r/p) · 1/(z - (r - a)/p)` (in the Tate algebra since `p ∤ r - a`). -/
noncomputable def substAnalytic (p a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) : PowerSeries ℚ :=
  ((P.comp (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X]) : PowerSeries ℚ)
    + ∑ r ∈ d.support, if (p : ℤ) ∣ r - a then 0
        else PowerSeries.C (d r / p) * poleSeries (((r - a : ℤ) : ℚ) / p)

/-- Integer poles of `g(a + p z)`: `s = (r - a)/p` for the poles `r ≡ a (mod p)` of `g`. -/
noncomputable def substPoles (p a : ℕ) (d : ℤ →₀ ℚ) : Finset ℤ :=
  (d.support.filter fun r => (p : ℤ) ∣ r - a).image fun r => (r - a) / (p : ℤ)

/-- Principal part of `g(a + p z)` at the integer `s`: `d_r/(a + p z - r) = (d_r/p)/(z - s)` for
`r = a + p s`. -/
noncomputable def substPrincipal (p a : ℕ) (d : ℤ →₀ ℚ) (s : ℤ) : ℚ :=
  d (a + p * s) / p

theorem comp_affine_X_sub_C {p : ℕ} (hp : (p : ℚ) ≠ 0) (a : ℕ) (r : ℤ) :
    (X - C (r : ℚ)).comp (C (a : ℚ) + C (p : ℚ) * X)
      = C (p : ℚ) * (X - C (((r - a : ℤ) : ℚ) / p)) := by
  have h : (((r - a : ℤ) : ℚ)) = (r : ℚ) - a := by rw [Int.cast_sub, Int.cast_natCast]
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ hp, h, C_sub]
  ring

section Laurent

open scoped RatFunc

/-- The expansion at `z = 0` of `c/(p (z - t))` for `t ≠ 0` is `(c/p) · poleSeries t`. -/
theorem laurent_pole_expansion {p : ℚ} (hp : p ≠ 0) (c : ℚ) {t : ℚ} (ht : t ≠ 0) :
    algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
        (algebraMap ℚ[X] (RatFunc ℚ) (C c) / algebraMap ℚ[X] (RatFunc ℚ) (C p * (X - C t)))
      = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.C (c / p) * poleSeries t) := by
  have hne : algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
      (algebraMap ℚ[X] (RatFunc ℚ) (C p * (X - C t))) ≠ 0 :=
    (_root_.map_ne_zero _).2 (RatFunc.algebraMap_ne_zero
      (mul_ne_zero (C_ne_zero.mpr hp) (X_sub_C_ne_zero t)))
  have h := poleSeries_mul ht
  have hC : PowerSeries.C (c / p) * PowerSeries.C p = PowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp]
  rw [map_div₀, div_eq_iff hne, laurent_algebraMap, laurent_algebraMap, ← map_mul]
  congr 1
  simp only [Polynomial.coe_C, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X]
  linear_combination (-(PowerSeries.C (c / p) * PowerSeries.C p)) * h - hC

theorem principal_eq (p c t : ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ) (C c) / algebraMap ℚ[X] (RatFunc ℚ) (C p * (X - C t))
      = algebraMap ℚ[X] (RatFunc ℚ) (C (c / p)) / algebraMap ℚ[X] (RatFunc ℚ) (X - C t) := by
  rw [map_mul, ← div_div, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    ← map_div₀]

/-- The data `(substAnalytic, substPoles, substPrincipal)` represents `g(a + p z)`: the Laurent
expansion at `z = 0` of the rational function `g(a + p z)` (`ratFuncAffine`) is the analytic part
plus the expansion of the principal parts `∑_s c_s/(z - s)`. -/
theorem substData_spec {p : ℕ} (hp : (p : ℚ) ≠ 0) (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (ratFuncAffine (a : ℚ) hp (tauRatFunc P d))
      = HahnSeries.ofPowerSeries ℤ ℚ (substAnalytic p a P d)
        + algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
            (∑ s ∈ substPoles p a d, algebraMap ℚ[X] (RatFunc ℚ) (C (substPrincipal p a d s))
              / algebraMap ℚ[X] (RatFunc ℚ) (X - C (s : ℚ))) := by
  have hpZ : ((p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hp
  have hL : algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (ratFuncAffine (a : ℚ) hp (tauRatFunc P d))
      = HahnSeries.ofPowerSeries ℤ ℚ ((P.comp (C (a : ℚ) + C (p : ℚ) * X) : ℚ[X]) : PowerSeries ℚ)
        + ∑ r ∈ d.support, algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
            (algebraMap ℚ[X] (RatFunc ℚ) (C (d r))
              / algebraMap ℚ[X] (RatFunc ℚ) (C (p : ℚ) * (X - C (((r - a : ℤ) : ℚ) / p)))) := by
    rw [tauRatFunc, Finsupp.sum, map_add, map_sum, ratFuncAffine_algebraMap, map_add, map_sum,
      laurent_algebraMap]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    rw [map_div₀, ratFuncAffine_algebraMap, ratFuncAffine_algebraMap, C_comp,
      comp_affine_X_sub_C hp]
  have hinj : Set.InjOn (fun r : ℤ => (r - a) / (p : ℤ))
      ↑(d.support.filter fun r => (p : ℤ) ∣ r - a) := by
    intro x hx y hy hxy
    have h1 := Int.mul_ediv_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have h2 := Int.mul_ediv_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hxy' : (x - a) / (p : ℤ) = (y - a) / p := hxy
    rw [hxy'] at h1
    linarith
  rw [hL]
  unfold substAnalytic
  simp only [map_add, map_sum]
  rw [add_assoc]
  congr 1
  rw [substPoles, Finset.sum_image hinj, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with h
  · have hs : ((((r - a) / p : ℤ)) : ℚ) = ((r - a : ℤ) : ℚ) / p := by
      rw [Int.cast_div h hpZ, Int.cast_natCast]
    rw [map_zero, zero_add, principal_eq, substPrincipal, Int.mul_ediv_cancel' h,
      add_sub_cancel, hs]
  · have ht : ((r - a : ℤ) : ℚ) / p ≠ 0 := by
      have hr : r - (a : ℤ) ≠ 0 := fun h0 => h (by rw [h0]; exact dvd_zero _)
      exact div_ne_zero (by exact_mod_cast hr) hp
    rw [add_zero, laurent_pole_expansion hp _ ht]

end Laurent

/-! ## Lemma 3.7 -/

section Padic

variable {p : ℕ} [Fact p.Prime]

theorem one_lt_norm_intCast_div {m : ℤ} (h : ¬ (p : ℤ) ∣ m) :
    1 < ‖((((m : ℚ) / p) : ℚ) : ℚ_[p])‖ := by
  have hm1 : ‖(m : ℚ_[p])‖ = 1 := le_antisymm (Padic.norm_int_le_one m)
    (not_lt.mp fun hlt => h (Padic.norm_intCast_lt_one_iff.mp hlt))
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, norm_div, hm1, Padic.norm_p, one_div,
    inv_inv]
  exact_mod_cast (Fact.out : p.Prime).one_lt

theorem isRestricted_substTerm (a : ℕ) (d : ℤ →₀ ℚ) (r : ℤ) :
    (PowerSeries.map (Rat.castHom ℚ_[p]) (if (p : ℤ) ∣ r - a then 0
      else PowerSeries.C (d r / p) * poleSeries (((r - a : ℤ) : ℚ) / p))).IsRestricted 1 := by
  split_ifs with h
  · rw [map_zero]
    exact PowerSeries.isRestricted_zero 1
  · rw [map_mul, PowerSeries.map_C]
    exact PowerSeries.isRestricted.mul 1 (PowerSeries.isRestricted_C 1 _)
      (poleSeries_isRestricted (one_lt_norm_intCast_div h))

/-- The analytic part of `g(a + p z)` lies in the Tate algebra `ℚ_p⟨z⟩`. -/
theorem substAnalytic_isRestricted (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d)).IsRestricted 1 := by
  unfold substAnalytic
  rw [map_add, ← Polynomial.polynomial_map_coe, map_sum]
  exact PowerSeries.isRestricted.add 1 (isRestricted_coe _)
    (isRestricted_sum _ _ fun r _ => isRestricted_substTerm a d r)

theorem tateTau_substAnalytic (hp7 : 7 ≤ p) (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    tateTau (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
      = ((tauPoly (P.comp (C (a : ℚ) + C (p : ℚ) * X)) : ℚ) : ℚ_[p])
        + ∑ r ∈ d.support, if (p : ℤ) ∣ r - a then 0
            else ((d r / p : ℚ) : ℚ_[p]) * tauAn p (((r - a : ℤ) : ℚ) / p) := by
  have hres : ∀ r ∈ d.support, (PowerSeries.map (Rat.castHom ℚ_[p])
      (if (p : ℤ) ∣ r - a then 0
        else PowerSeries.C (d r / p) * poleSeries (((r - a : ℤ) : ℚ) / p))).IsRestricted 1 :=
    fun r _ => isRestricted_substTerm a d r
  unfold substAnalytic
  rw [map_add, ← Polynomial.polynomial_map_coe, map_sum,
    tateTau_add hp7 (isRestricted_coe _) (isRestricted_sum _ _ hres), tateTau_map,
    tateTau_sum hp7 _ _ hres]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with h
  · rw [map_zero, tateTau_zero]
  · rw [map_mul, PowerSeries.map_C, tateTau_C_mul, Rat.coe_castHom]
    rfl

/-- The contribution of a simple pole `1/(x - r)` to `τ^ext_Y(g(a + p z))` (up to the factor
`p⁻¹`), as a function of `m = r - a`: for `p ∣ m` the term `1/(a + p z - r) = p⁻¹/(z - m/p)` is a
principal part with value `H⁷_{d(m/p)} - Y`; otherwise it is analytic, with value
`τ^an(1/(z - m/p))`. -/
noncomputable def poleTerm (p : ℕ) [Fact p.Prime] (m : ℤ) : Polynomial ℚ_[p] :=
  if (p : ℤ) ∣ m then C ((H7 (dIndex (m / p)) : ℚ) : ℚ_[p]) - distY p
  else C (tauAn p ((m : ℚ) / p))

/-- The difference identity for `poleTerm`, from `tauAn_sub_one` and `H7_dIndex_sub_one_sub`. -/
theorem poleTerm_sub (hp7 : 7 ≤ p) (m : ℤ) :
    poleTerm p m - poleTerm p (m - p)
      = C ((p : ℚ_[p]) ^ 7 * (((1 / (m : ℚ) ^ 7 : ℚ)) : ℚ_[p])) := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hdvd : (p : ℤ) ∣ m - p ↔ (p : ℤ) ∣ m := dvd_sub_self_right
  unfold poleTerm
  by_cases h : (p : ℤ) ∣ m
  · rw [ite_eq_left h, ite_eq_left (hdvd.mpr h)]
    obtain ⟨q, rfl⟩ := h
    have h1 : ((p : ℤ) * q - p) / p = q - 1 := by
      rw [show (p : ℤ) * q - p = p * (q - 1) by ring, Int.mul_ediv_cancel_left _ hpZ]
    have h2 := H7_dIndex_sub_one_sub q
    have hval : H7 (dIndex q) - H7 (dIndex (q - 1))
        = (p : ℚ) ^ 7 * (1 / ((((p : ℤ) * q : ℤ)) : ℚ) ^ 7) := by
      rw [Int.cast_mul, Int.cast_natCast, mul_pow, one_div, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 7 hp0), one_mul]
      linear_combination -h2
    rw [Int.mul_ediv_cancel_left _ hpZ, h1, sub_sub_sub_cancel_right, ← C_sub, ← Rat.cast_sub,
      hval, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  · rw [ite_eq_right h, ite_eq_right (mt hdvd.mp h), ← C_sub]
    congr 1
    have key := tauAn_sub_one hp7 (one_lt_norm_intCast_div h)
    have hcast : (((m - p : ℤ) : ℚ) / p) = (m : ℚ) / p - 1 := by
      rw [Int.cast_sub, Int.cast_natCast, sub_div, div_self hp0]
    have hq : (((m : ℚ) / p)⁻¹) ^ 7 = (p : ℚ) ^ 7 * (1 / (m : ℚ) ^ 7) := by
      rw [inv_div, div_pow, div_eq_mul_one_div]
    have hq' : ((((m : ℚ) / p)⁻¹ : ℚ) : ℚ_[p]) ^ 7
        = (p : ℚ_[p]) ^ 7 * (((1 / (m : ℚ) ^ 7 : ℚ)) : ℚ_[p]) := by
      exact_mod_cast hq
    rw [hcast, ← hq']
    linear_combination -key

/-- Lemma 3.7 for simple poles: `∑_{a=0}^{p-1} poleTerm p (r - a) = p⁷ (H⁷_{d(r)} - X)`, that is,
`∑_a τ^ext_Y(1/(a + p z - r)) = p⁶ τ_X(1/(x - r))`. At `r = 0` this is the paper's computation
for `g = 1/x` (with `Y = p⁷ X + C_p`); the difference identity `poleTerm_sub` and
`H⁷_{d(r)} - H⁷_{d(r-1)} = r⁻⁷` carry it to every `r ∈ ℤ`. -/
theorem sum_poleTerm (hp11 : 11 ≤ p) (r : ℤ) :
    ∑ a ∈ range p, poleTerm p (r - a)
      = C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex r) : ℚ) : ℚ_[p]) - X) := by
  have hp7 : 7 ≤ p := by omega
  -- the pole `1/x`
  have hz : ∀ a ∈ Finset.Ico 1 p, poleTerm p (0 - (a : ℤ)) = C (tauAn p (-((a : ℚ) / p))) := by
    intro a ha
    obtain ⟨ha1, hap⟩ := Finset.mem_Ico.mp ha
    have hnd : ¬ (p : ℤ) ∣ 0 - (a : ℤ) := by
      rw [zero_sub, Int.dvd_neg, Int.natCast_dvd_natCast]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    unfold poleTerm
    rw [ite_eq_right hnd, Int.cast_sub, Int.cast_zero, Int.cast_natCast, zero_sub, neg_div]
  have hfirst : poleTerm p (0 - ((0 : ℕ) : ℤ)) = -distY p := by
    unfold poleTerm
    rw [ite_eq_left (show (p : ℤ) ∣ 0 - ((0 : ℕ) : ℤ) by simp)]
    simp [dIndex, H7]
  have hsplit : ∑ a ∈ range p, poleTerm p (0 - (a : ℤ))
      = poleTerm p (0 - ((0 : ℕ) : ℤ)) + ∑ a ∈ Finset.Ico 1 p, poleTerm p (0 - (a : ℤ)) :=
    Finset.sum_range_eq_add_Ico (fun a : ℕ => poleTerm p (0 - (a : ℤ))) (by omega)
  have hd0 : H7 (dIndex 0) = 0 := by simp [dIndex, H7]
  have h0 : ∑ a ∈ range p, poleTerm p (0 - (a : ℤ))
      - C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex 0) : ℚ) : ℚ_[p]) - X) = 0 := by
    rw [hsplit, hfirst, Finset.sum_congr rfl hz, ← map_sum, hd0, Rat.cast_zero, map_zero, distY,
      cP]
    ring
  -- the difference identity in `r`
  have hshift : ∀ (r : ℤ) (i : ℕ), poleTerm p (r - (i : ℤ))
      = poleTerm p (r + 1 - ((i + 1 : ℕ) : ℤ)) := fun r i => by
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hstep : ∀ r : ℤ, ∑ a ∈ range p, poleTerm p (r + 1 - a)
        - C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex (r + 1)) : ℚ) : ℚ_[p]) - X)
      = ∑ a ∈ range p, poleTerm p (r - a)
        - C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex r) : ℚ) : ℚ_[p]) - X) := by
    intro r
    have htel : ∑ i ∈ range p, (poleTerm p (r + 1 - (i : ℤ))
          - poleTerm p (r + 1 - ((i + 1 : ℕ) : ℤ)))
        = poleTerm p (r + 1 - ((0 : ℕ) : ℤ)) - poleTerm p (r + 1 - (p : ℤ)) :=
      Finset.sum_range_sub' (fun i : ℕ => poleTerm p (r + 1 - (i : ℤ))) p
    have h1 : ∑ a ∈ range p, poleTerm p (r + 1 - a) - ∑ a ∈ range p, poleTerm p (r - a)
        = poleTerm p (r + 1) - poleTerm p (r + 1 - p) := by
      have hcongr : ∑ a ∈ range p, poleTerm p (r - (a : ℤ))
          = ∑ a ∈ range p, poleTerm p (r + 1 - ((a + 1 : ℕ) : ℤ)) :=
        Finset.sum_congr rfl fun i _ => hshift r i
      rw [hcongr, ← Finset.sum_sub_distrib, htel, Nat.cast_zero, sub_zero]
    have h2 := poleTerm_sub hp7 (r + 1)
    have h3 := H7_dIndex_sub_one_sub (r + 1)
    rw [add_sub_cancel_right] at h3
    have h5 : H7 (dIndex (r + 1)) - H7 (dIndex r) = 1 / ((r + 1 : ℤ) : ℚ) ^ 7 := by linarith
    have h4 : C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex (r + 1)) : ℚ) : ℚ_[p]) - X)
        - C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex r) : ℚ) : ℚ_[p]) - X)
        = C ((p : ℚ_[p]) ^ 7 * (((1 / ((r + 1 : ℤ) : ℚ) ^ 7 : ℚ)) : ℚ_[p])) := by
      rw [← mul_sub, sub_sub_sub_cancel_right, ← C_sub, ← Rat.cast_sub, h5, ← C_mul]
    linear_combination h1 + h2 - h4
  have key : ∀ r : ℤ, ∑ a ∈ range p, poleTerm p (r - a)
      - C ((p : ℚ_[p]) ^ 7) * (C ((H7 (dIndex r) : ℚ) : ℚ_[p]) - X) = 0 := by
    intro r
    induction r with
    | zero => exact h0
    | succ i ih => rw [hstep]; exact ih
    | pred i ih =>
      have h := hstep (-(i : ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [← h]
      exact ih
  exact sub_eq_zero.mp (key r)

theorem tauExt_subst (hp7 : 7 ≤ p) (a : ℕ) (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    tauExt (distY p) (substPoles p a d)
        (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
        (fun s => (substPrincipal p a d s : ℚ_[p]))
      = C ((tauPoly (P.comp (C (a : ℚ) + C (p : ℚ) * X)) : ℚ) : ℚ_[p])
        + ∑ r ∈ d.support, C (((d r / p : ℚ)) : ℚ_[p]) * poleTerm p (r - a) := by
  have hinj : Set.InjOn (fun r : ℤ => (r - a) / (p : ℤ))
      ↑(d.support.filter fun r => (p : ℤ) ∣ r - a) := by
    intro x hx y hy hxy
    have h1 := Int.mul_ediv_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have h2 := Int.mul_ediv_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hxy' : (x - a) / (p : ℤ) = (y - a) / p := hxy
    rw [hxy'] at h1
    linarith
  simp only [tauExt]
  rw [tateTau_substAnalytic hp7, substPoles, Finset.sum_image hinj, Finset.sum_filter, map_add,
    map_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold poleTerm
  split_ifs with h
  · rw [map_zero, zero_add, substPrincipal, Int.mul_ediv_cancel' h, add_sub_cancel]
  · rw [add_zero, C_mul]

/-- **Lemma 3.7** (distribution formula, (36)). Let `p ≥ 11` be prime and `Y = p⁷ X + C_p`
(`distY`, with `C_p` as in (34), `cP`). For every rational function `g = P + ∑_r d_r/(x - r)`
with polynomial part and simple integer poles,
`τ_X(g) = p^{-6} ∑_{a=0}^{p-1} τ^ext_Y(g(a + p z))`.
Here `g(a + p z)` is the element of `B_T` with analytic part `substAnalytic p a P d` (in the Tate
algebra, `substAnalytic_isRestricted`) and principal parts `substPrincipal p a d s/(z - s)` at
the integers `s ∈ substPoles p a d`; `substData_spec` checks that this is the expansion of the
rational function `g(a + p z)`. Both sides lie in `ℚ_p[X]`. -/
theorem distribution_formula (hp11 : 11 ≤ p) (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    (tauFunctional P d).map (Rat.castHom ℚ_[p])
      = C ((p : ℚ_[p]) ^ (-6 : ℤ)) * ∑ a ∈ range p, tauExt (distY p) (substPoles p a d)
          (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
          (fun s => (substPrincipal p a d s : ℚ_[p])) := by
  have hp7 : 7 ≤ p := by omega
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hscal : ∀ x : ℚ, ((x / p : ℚ) : ℚ_[p]) * (p : ℚ_[p]) ^ 7 = (p : ℚ_[p]) ^ 6 * (x : ℚ_[p]) :=
    fun x => by
      rw [Rat.cast_div, Rat.cast_natCast, div_mul_eq_mul_div, eq_comm, eq_div_iff hp0]
      ring
  have hsum : ∑ a ∈ range p, tauExt (distY p) (substPoles p a d)
          (PowerSeries.map (Rat.castHom ℚ_[p]) (substAnalytic p a P d))
          (fun s => (substPrincipal p a d s : ℚ_[p]))
      = C ((p : ℚ_[p]) ^ 6) * (tauFunctional P d).map (Rat.castHom ℚ_[p]) := by
    rw [Finset.sum_congr rfl fun a _ => tauExt_subst hp7 a P d, Finset.sum_add_distrib,
      ← map_sum, ← Rat.cast_sum, sum_tauPoly_comp_affine hpp.ne_zero, Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_poleTerm hp11]
    unfold tauFunctional
    rw [Polynomial.map_add, Polynomial.map_C, Finsupp.sum, Polynomial.map_sum, mul_add,
      Finset.mul_sum]
    congr 1
    · rw [Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, C_mul]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp only [tauPole, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
        Polynomial.map_X, Rat.coe_castHom]
      simp only [← mul_assoc, ← C_mul]
      rw [hscal]
  rw [hsum, ← mul_assoc, ← C_mul, zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 6 hp0), C_1,
    one_mul]

end Padic

end ZetaSeven
