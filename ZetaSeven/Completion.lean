import ZetaSeven.TauPullback

/-!
# P-adic completion (paper Section 3.3, Lemmas 3.4-3.5, equations (32)-(33))

Prince Anand, "Zeta 7 is Irrational", Section 3.3. Fix a prime `p ≥ 7`.

* `kappa d = κ_d = τ(x^d)` (24). Lemma 3.4: `v_p(κ_d) ≥ -1` for every `d`
  (`kappa_padicValRat_ge`, `norm_kappa_le`), and `κ_d ∈ ℤ_p` for `d ≤ p + 4`
  (`norm_kappa_le_one`), from von Staudt-Clausen (`Bernoulli.vonStaudt_clausen`).
* The Tate algebra `A = ℚ_p⟨z⟩` is Mathlib's ring of restricted power series
  `PowerSeries.IsRestricted 1` (coefficients tending to `0`), with the Gauss norm
  `PowerSeries.gaussNorm ‖·‖ 1`. Equation (32) extends `τ` to `A` by
  `tateTau f = ∑ f_d κ_d`; the series converges (`summable_tateTau`), extends `τ` on
  polynomials (`tateTau_map`), and `‖τ‖ ≤ p` (`norm_tateTau_le`).
* `B_T = A ⊕ ⊕_{r ∈ S} ℚ_p · 1/(z - r)` for `T = ∏_{r ∈ S} (z - r)`: an element is a
  pair `(f, c)` standing for `f + ∑_{r ∈ S} c_r/(z - r)`, and
  `tauExt Y S f c = τ(f) + ∑_r c_r (H⁷_{d(r)} - Y)` is `τ^ext_Y`. With `Y = X` it
  extends `τ_X` (`tauExt_map`).
* For `U ∈ ℚ_p[z]`, `polyPart S U = U /ₘ T` and `principalCoeff S U r = U(r)/T'(r)`
  are the partial fractions `U/T = P + ∑_r c_r/(z - r)` (`partialFraction_spec`).
  The normalized series `∑_j p^j U_j/T` is the element of `B_T` with analytic part
  `seriesAnalytic S U` (coefficients `∑_j p^j (P_j)_d`) and principal parts
  `seriesPrincipal S U r = ∑_j p^j c_{j,r}`; both series converge and the analytic part
  lies in `A` (`summable_seriesAnalytic`, `summable_seriesPrincipal`,
  `seriesAnalytic_isRestricted`).
* Lemma 3.5 (33) is `completion`: for `r_ν ∈ ℤ` pairwise incongruent mod `p` with
  `d(r_ν) < p`, `Y ∈ ℤ_p[X]`, `U_j ∈ ℤ_p[z]` and `deg U_0 ≤ p + 4`,
  `τ^ext_Y(∑_j p^j U_j/T) ∈ ℤ_p[X]`. Membership in `ℤ_p[z]`, `ℤ_p[X]` is
  `Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p])`.
-/

namespace ZetaSeven

open Polynomial Finset Filter Topology

/-! ## Lemma 3.4: the von Staudt-Clausen bound for `κ_d` -/

/-- Equation (24): `κ_d = τ(x^d)`. -/
noncomputable def kappa (d : ℕ) : ℚ := tauPoly (X ^ d)

theorem kappa_eq (d : ℕ) :
    kappa d = (d.descFactorial 5 : ℚ) * _root_.bernoulli (d - 5) / 720 := by
  have h := tauPoly_C_mul_X_pow 1 d
  rw [map_one, one_mul, one_mul] at h
  exact h

variable {p : ℕ} [Fact p.Prime]

theorem real_mul_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans ((one_mul b).trans_le hb)

theorem padic_norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have h := Padic.norm_int_le_one (p := p) (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem prime_not_dvd_720 (hp7 : 7 ≤ p) : ¬ p ∣ 720 := by
  have hpp : p.Prime := Fact.out
  intro hd
  rw [show (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h)
      omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem padic_norm_720 (hp7 : 7 ≤ p) : ‖(720 : ℚ_[p])‖ = 1 := by
  have h := (Padic.norm_natCast_eq_one_iff (p := p) (n := 720)).mpr
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (prime_not_dvd_720 hp7))
  exact_mod_cast h

theorem norm_inv_prime_eq_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    ‖(((1 : ℚ) / q : ℚ) : ℚ_[p])‖ = 1 := by
  have h1 : ‖(q : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes Fact.out hq).mpr (Ne.symm hqp))
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, norm_div, norm_one, h1, div_one]

theorem norm_inv_prime_self : ‖(((1 : ℚ) / p : ℚ) : ℚ_[p])‖ = p := by
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, norm_div, norm_one, Padic.norm_p, one_div,
    inv_inv]

/-- Von Staudt-Clausen: `B_{2k} = z - ∑_{(q-1) ∣ 2k} 1/q` with `z ∈ ℤ`, so
`‖B_{2k}‖_p ≤ p`, and `‖B_{2k}‖_p ≤ 1` unless `(p - 1) ∣ 2k`. -/
theorem norm_bernoulli_two_mul_le (k : ℕ) {B : ℝ} (hB1 : 1 ≤ B)
    (hB : (p - 1) ∣ 2 * k → (p : ℝ) ≤ B) :
    ‖((_root_.bernoulli (2 * k) : ℚ) : ℚ_[p])‖ ≤ B := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  rw [eq_sub_of_add_eq hz.symm, Rat.cast_sub, Rat.cast_intCast, Rat.cast_sum, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((Padic.norm_int_le_one z).trans hB1) ?_)
  rw [norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (zero_le_one.trans hB1)
    fun q hq => ?_
  obtain ⟨-, hqprime, hqdvd⟩ := Finset.mem_filter.mp hq
  by_cases hqp : q = p
  · subst hqp
    rw [norm_inv_prime_self]
    exact hB hqdvd
  · exact (norm_inv_prime_eq_one hqprime hqp).le.trans hB1

theorem norm_bernoulli_odd_le_one (hp2 : p ≠ 2) (k : ℕ) :
    ‖((_root_.bernoulli (2 * k + 1) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
    rw [Nat.cast_ofNat] at h2
    refine le_of_eq ?_
    rw [Nat.mul_zero, Nat.zero_add, _root_.bernoulli_one, Rat.cast_div, Rat.cast_neg, Rat.cast_one,
      Rat.cast_ofNat, norm_div, norm_neg, norm_one, h2, div_one]
  · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega), Rat.cast_zero, norm_zero]
    exact zero_le_one

theorem norm_bernoulli_le (hp2 : p ≠ 2) (n : ℕ) : ‖((_root_.bernoulli n : ℚ) : ℚ_[p])‖ ≤ p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact norm_bernoulli_two_mul_le k hp1 fun _ => le_rfl
  · exact (norm_bernoulli_odd_le_one hp2 k).trans hp1

theorem norm_bernoulli_le_one (hp2 : p ≠ 2) {n : ℕ} (hn : ¬ (p - 1) ∣ n) :
    ‖((_root_.bernoulli n : ℚ) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact norm_bernoulli_two_mul_le k le_rfl fun h => absurd h hn
  · exact norm_bernoulli_odd_le_one hp2 k

theorem norm_kappa_eq (hp7 : 7 ≤ p) (d : ℕ) :
    ‖((kappa d : ℚ) : ℚ_[p])‖
      = ‖((d.descFactorial 5 : ℕ) : ℚ_[p])‖ * ‖((_root_.bernoulli (d - 5) : ℚ) : ℚ_[p])‖ := by
  rw [kappa_eq, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, norm_div, norm_mul,
    padic_norm_720 hp7, div_one]

/-- **Lemma 3.4**, first part, in norm form: `|κ_d|_p ≤ p`. -/
theorem norm_kappa_le (hp7 : 7 ≤ p) (d : ℕ) : ‖((kappa d : ℚ) : ℚ_[p])‖ ≤ p := by
  rw [norm_kappa_eq hp7]
  calc _ ≤ 1 * (p : ℝ) :=
        mul_le_mul (padic_norm_natCast_le_one _) (norm_bernoulli_le (by omega) _) (norm_nonneg _)
          zero_le_one
    _ = p := one_mul _

/-- **Lemma 3.4**, second part: `κ_d ∈ ℤ_p` for `d ≤ p + 4`. For `d - 5 = p - 1` the factor
`d - 4 = p` of `d(d-1)(d-2)(d-3)(d-4)` cancels the `p⁻¹` of `B_{p-1}`. -/
theorem norm_kappa_le_one (hp7 : 7 ≤ p) {d : ℕ} (hd : d ≤ p + 4) :
    ‖((kappa d : ℚ) : ℚ_[p])‖ ≤ 1 := by
  rw [norm_kappa_eq hp7]
  by_cases hd5 : d < 5
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hd5, Nat.cast_zero, norm_zero, zero_mul]
    exact zero_le_one
  by_cases hn : (p - 1) ∣ (d - 5)
  · by_cases h0 : d - 5 = 0
    · rw [h0, _root_.bernoulli_zero, Rat.cast_one, norm_one, mul_one]
      exact padic_norm_natCast_le_one _
    · have hdp : d = p + 4 := by
        obtain ⟨m, hm⟩ := hn
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · interval_cases m <;> omega
        · have := Nat.mul_le_mul_left (p - 1) hm2
          omega
      subst hdp
      have hdvd : p ∣ (p + 4).descFactorial 5 := by
        have h := Nat.descFactorial_succ (p + 4) 4
        rw [Nat.add_sub_cancel] at h
        exact ⟨_, h⟩
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, Nat.cast_mul, norm_mul, Padic.norm_p]
      have h1 := padic_norm_natCast_le_one (p := p) c
      have h2 := norm_bernoulli_le (p := p) (by omega) (p + 4 - 5)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      calc _ ≤ (p : ℝ)⁻¹ * 1 * p := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hp0.le)) h2
              (norm_nonneg _)
            positivity
        _ = 1 := by rw [mul_one, inv_mul_cancel₀ hp0.ne']
  · exact real_mul_le_one (padic_norm_natCast_le_one _) (norm_nonneg _)
      (norm_bernoulli_le_one (by omega) hn)

theorem neg_le_padicValRat_of_norm_le {q : ℚ} {n : ℕ} (h : ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ n) :
    -(n : ℤ) ≤ padicValRat p q := by
  rcases eq_or_ne q 0 with rfl | hq
  · rw [padicValRat.zero]
    omega
  · rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast,
      ← zpow_natCast] at h
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have := (zpow_le_zpow_iff_right₀ hp1).mp h
    omega

/-- **Lemma 3.4** (von Staudt-Clausen bound for `κ_d`): `v_p(κ_d) ≥ -1` for every `d`
(with Mathlib's junk value `v_p(0) = 0` when `κ_d = 0`, where the paper's `v_p(0) = +∞`
also satisfies the bound). -/
theorem kappa_padicValRat_ge (hp7 : 7 ≤ p) (d : ℕ) : -1 ≤ padicValRat p (kappa d) := by
  have h := neg_le_padicValRat_of_norm_le (p := p) (n := 1)
    (by rw [pow_one]; exact norm_kappa_le hp7 d)
  simpa using h

/-- **Lemma 3.4**, second part, as a valuation: `v_p(κ_d) ≥ 0` for `d ≤ p + 4`. -/
theorem kappa_padicValRat_nonneg (hp7 : 7 ≤ p) {d : ℕ} (hd : d ≤ p + 4) :
    0 ≤ padicValRat p (kappa d) := by
  have h := neg_le_padicValRat_of_norm_le (p := p) (n := 0)
    (by rw [pow_zero]; exact norm_kappa_le_one hp7 hd)
  simpa using h

/-! ## Equation (32): `τ` on the Tate algebra -/

/-- Equation (32): `τ(∑_d f_d z^d) = ∑_d f_d κ_d` on the Tate algebra `ℚ_p⟨z⟩`
(`f` with `PowerSeries.IsRestricted 1 f`, i.e. `|f_d|_p → 0`). -/
noncomputable def tateTau (f : PowerSeries ℚ_[p]) : ℚ_[p] :=
  ∑' d, PowerSeries.coeff d f * ((kappa d : ℚ) : ℚ_[p])

/-- Equation (32) converges on the Tate algebra: `|f_d κ_d|_p ≤ p |f_d|_p → 0`. -/
theorem summable_tateTau (hp7 : 7 ≤ p) {f : PowerSeries ℚ_[p]} (hf : f.IsRestricted 1) :
    Summable fun d => PowerSeries.coeff d f * ((kappa d : ℚ) : ℚ_[p]) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [PowerSeries.isRestricted_iff] at hf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun d => ‖PowerSeries.coeff d f‖ * (p : ℝ)) cofinite (𝓝 0) := by
    have := hf.mul_const (p : ℝ)
    simpa using this
  refine squeeze_zero (fun d => norm_nonneg _) (fun d => ?_) hg
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_kappa_le hp7 d) (norm_nonneg _)

theorem norm_tateTau_le_of_le (hp7 : 7 ≤ p) {f : PowerSeries ℚ_[p]} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ d, ‖PowerSeries.coeff d f‖ ≤ M) : ‖tateTau f‖ ≤ p * M := by
  unfold tateTau
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (Nat.cast_nonneg p) hM) fun d => ?_
  rw [norm_mul, mul_comm (p : ℝ)]
  exact mul_le_mul (h d) (norm_kappa_le hp7 d) (norm_nonneg _) hM

/-- `‖τ‖ ≤ p` on the Tate algebra: `|τ(f)|_p ≤ p ‖f‖` for the Gauss norm
`‖f‖ = sup_d |f_d|_p`. -/
theorem norm_tateTau_le (hp7 : 7 ≤ p) {f : PowerSeries ℚ_[p]} (hf : f.IsRestricted 1) :
    ‖tateTau f‖ ≤ p * PowerSeries.gaussNorm (fun x : ℚ_[p] => ‖x‖) 1 f := by
  have hbd : PowerSeries.HasGaussNorm (fun x : ℚ_[p] => ‖x‖) 1 f := by
    rw [PowerSeries.isRestricted_iff] at hf
    exact hf.bddAbove_range_of_cofinite
  refine norm_tateTau_le_of_le hp7
    (PowerSeries.gaussNorm_nonneg _ _ _ fun a => norm_nonneg a) fun d => ?_
  have := PowerSeries.le_gaussNorm (fun x : ℚ_[p] => ‖x‖) 1 f hbd d
  simpa only [one_pow, mul_one] using this

theorem tateTau_add (hp7 : 7 ≤ p) {f g : PowerSeries ℚ_[p]} (hf : f.IsRestricted 1)
    (hg : g.IsRestricted 1) : tateTau (f + g) = tateTau f + tateTau g := by
  unfold tateTau
  rw [← (summable_tateTau hp7 hf).tsum_add (summable_tateTau hp7 hg)]
  refine tsum_congr fun d => ?_
  rw [map_add, add_mul]

/-- A polynomial is a restricted power series. -/
theorem isRestricted_coe (P : Polynomial ℚ_[p]) : (P : PowerSeries ℚ_[p]).IsRestricted 1 := by
  rw [PowerSeries.isRestricted_iff']
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop P.natDegree] with d hd
  rw [Polynomial.coeff_coe, coeff_eq_zero_of_natDegree_lt hd, norm_zero, zero_mul]

theorem tateTau_coe (P : Polynomial ℚ_[p]) :
    tateTau (P : PowerSeries ℚ_[p])
      = ∑ d ∈ range (P.natDegree + 1), P.coeff d * ((kappa d : ℚ) : ℚ_[p]) := by
  unfold tateTau
  simp only [Polynomial.coeff_coe]
  rw [tsum_eq_sum (s := range (P.natDegree + 1))]
  intro d hd
  simp only [Finset.mem_range, not_lt] at hd
  rw [coeff_eq_zero_of_natDegree_lt (show P.natDegree < d by omega), zero_mul]

/-- `τ` on the Tate algebra extends `τ` on `ℚ[x]` (23)-(24). -/
theorem tateTau_map (P : Polynomial ℚ) :
    tateTau ((P.map (Rat.castHom ℚ_[p]) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])
      = (tauPoly P : ℚ_[p]) := by
  have hP : tauPoly P = ∑ d ∈ range (P.natDegree + 1), P.coeff d * kappa d := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
    rw [tauPoly_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [tauPoly_C_mul_X_pow, kappa_eq]
    ring
  unfold tateTau
  rw [hP, Rat.cast_sum, tsum_eq_sum (s := range (P.natDegree + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Polynomial.coeff_coe, coeff_map, Rat.cast_mul, Rat.coe_castHom]
  · intro d hd
    simp only [Finset.mem_range, not_lt] at hd
    rw [Polynomial.coeff_coe, coeff_map,
      coeff_eq_zero_of_natDegree_lt (show P.natDegree < d by omega), map_zero, zero_mul]


/-! ## `τ^ext_Y` on `B_T` -/

/-- `τ^ext_Y` on `B_T = A ⊕ ⊕_{r ∈ S} ℚ_p · 1/(z - r)` (Lemma 3.5): the element
`f + ∑_{r ∈ S} c_r/(z - r)`, with `f` in the Tate algebra, is sent to
`τ(f) + ∑_{r ∈ S} c_r (H⁷_{d(r)} - Y)`. Here `Y ∈ ℚ_p[X]` for the indeterminate `X`. -/
noncomputable def tauExt (Y : Polynomial ℚ_[p]) (S : Finset ℤ) (f : PowerSeries ℚ_[p])
    (c : ℤ → ℚ_[p]) : Polynomial ℚ_[p] :=
  C (tateTau f) + ∑ r ∈ S, C (c r) * (C ((H7 (dIndex r) : ℚ) : ℚ_[p]) - Y)

/-- `τ^ext_X` extends `τ_X` (26): on a rational function `P + ∑_r d_r/(x - r)` with
`P ∈ ℚ[x]` and simple poles in `S`, it is `τ_X(P, d)` (`tauFunctional`). -/
theorem tauExt_map (S : Finset ℤ) (P : Polynomial ℚ) (d : ℤ →₀ ℚ) (hd : d.support ⊆ S) :
    tauExt (X : Polynomial ℚ_[p]) S
        ((P.map (Rat.castHom ℚ_[p]) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])
        (fun r => (d r : ℚ_[p]))
      = (tauFunctional P d).map (Rat.castHom ℚ_[p]) := by
  unfold tauExt tauFunctional
  rw [tateTau_map, Finsupp.sum_of_support_subset d hd, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_sum, Rat.coe_castHom]
  · congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [tauPole, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_X, Rat.coe_castHom]
  · intro r _
    simp

/-! ## Partial fractions over `T = ∏_{r ∈ S} (z - r)` -/

/-- Polynomial part `P = U div T` of `U/T`, for `T = ∏_{r ∈ S} (z - r)` (Mathlib's
`Lagrange.nodal`). -/
noncomputable def polyPart (S : Finset ℤ) (U : Polynomial ℚ_[p]) : Polynomial ℚ_[p] :=
  U /ₘ Lagrange.nodal S fun r : ℤ => (r : ℚ_[p])

/-- Residue `c_r = U(r)/T'(r)` of `U/T` at the simple pole `r`. -/
noncomputable def principalCoeff (S : Finset ℤ) (U : Polynomial ℚ_[p]) (r : ℤ) : ℚ_[p] :=
  U.eval (r : ℚ_[p]) / (derivative (Lagrange.nodal S fun s : ℤ => (s : ℚ_[p]))).eval (r : ℚ_[p])

/-- Partial fractions (proof of Lemma 3.5): `U/T = P + ∑_{r ∈ S} c_r/(z - r)`, that is,
`U = P T + ∑_r c_r T/(z - r)` with `T/(z - r) = ∏_{s ∈ S, s ≠ r} (z - s)`. -/
theorem partialFraction_spec (S : Finset ℤ) (U : Polynomial ℚ_[p]) :
    U = polyPart S U * Lagrange.nodal S (fun r : ℤ => (r : ℚ_[p]))
      + ∑ r ∈ S, C (principalCoeff S U r)
          * Lagrange.nodal (S.erase r) (fun s : ℤ => (s : ℚ_[p])) := by
  have hinj : Set.InjOn (fun r : ℤ => (r : ℚ_[p])) S := fun a _ b _ h => Int.cast_injective h
  have hmonic : (Lagrange.nodal S fun r : ℤ => (r : ℚ_[p])).Monic := Lagrange.nodal_monic
  have hrem := Lagrange.eq_interpolate hinj
    ((degree_modByMonic_lt U hmonic).trans_eq Lagrange.degree_nodal)
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C] at hrem
  have hsum : ∀ i ∈ S, C (Lagrange.nodalWeight S (fun r : ℤ => (r : ℚ_[p])) i)
        * (Lagrange.nodal S (fun r : ℤ => (r : ℚ_[p])) / (X - C (i : ℚ_[p])))
        * C (eval (i : ℚ_[p]) (U %ₘ Lagrange.nodal S fun r : ℤ => (r : ℚ_[p])))
      = C (principalCoeff S U i) * Lagrange.nodal (S.erase i) (fun s : ℤ => (s : ℚ_[p])) := by
    intro i hi
    rw [← Lagrange.nodal_erase_eq_nodal_div hi, Lagrange.nodalWeight_eq_eval_derivative_nodal hi,
      modByMonic_eq_sub_mul_div, eval_sub, eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul,
      sub_zero, principalCoeff, div_eq_mul_inv, C_mul]
    ring
  conv_lhs => rw [← modByMonic_add_div U (Lagrange.nodal S fun r : ℤ => (r : ℚ_[p]))]
  rw [hrem, Finset.sum_congr rfl hsum, polyPart]
  ring

/-! ## Integrality in `ℤ_p` -/

theorem norm_coeff_le_one_of_mem_lifts {P : Polynomial ℚ_[p]}
    (hP : P ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) (d : ℕ) : ‖P.coeff d‖ ≤ 1 := by
  obtain ⟨x, hx⟩ := (lifts_iff_coeff_lifts P).mp hP d
  rw [← hx, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one x

theorem C_mem_lifts_of_norm_le_one {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    C a ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
  have h : algebraMap ℤ_[p] ℚ_[p] ⟨a, ha⟩ = a := PadicInt.algebraMap_apply _
  rw [← h]
  exact C_mem_lifts _ _

theorem nodal_map_padicInt (S : Finset ℤ) :
    (Lagrange.nodal S fun r : ℤ => (r : ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p])
      = Lagrange.nodal S fun r : ℤ => (r : ℚ_[p]) := by
  simp only [Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    map_intCast, Polynomial.map_intCast]

/-- The polynomial quotient of `U ∈ ℤ_p[z]` by the monic `T ∈ ℤ[z]` lies in `ℤ_p[z]`. -/
theorem polyPart_mem_lifts (S : Finset ℤ) {U : Polynomial ℚ_[p]}
    (hU : U ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) :
    polyPart S U ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
  obtain ⟨V, rfl⟩ := (mem_lifts U).mp hU
  have hmonic : (Lagrange.nodal S fun r : ℤ => (r : ℤ_[p])).Monic := Lagrange.nodal_monic
  rw [polyPart, ← nodal_map_padicInt, ← map_divByMonic (algebraMap ℤ_[p] ℚ_[p]) hmonic]
  exact (mem_lifts _).mpr ⟨_, rfl⟩

/-- `v_p(c_r) ≥ 0`: `T'(r) = ∏_{s ≠ r} (r - s)` is a `p`-unit by pairwise incongruence. -/
theorem norm_principalCoeff_le_one {S : Finset ℤ}
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → ¬ (p : ℤ) ∣ r - s) {U : Polynomial ℚ_[p]}
    (hU : U ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) {r : ℤ} (hr : r ∈ S) :
    ‖principalCoeff S U r‖ ≤ 1 := by
  obtain ⟨V, rfl⟩ := (mem_lifts U).mp hU
  have hden : ‖∏ s ∈ S.erase r, ((r : ℚ_[p]) - (s : ℚ_[p]))‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun s hs => ?_
    obtain ⟨hsr, hs⟩ := Finset.mem_erase.mp hs
    rw [← Int.cast_sub]
    exact le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hS r hr s hs (Ne.symm hsr) (Padic.norm_intCast_lt_one_iff.mp hlt))
  rw [principalCoeff, Lagrange.eval_nodal_derivative_eval_node_eq hr, Lagrange.eval_nodal,
    norm_div, hden, div_one, eval_intCast_map, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one _

/-- `H⁷_n ∈ ℤ_p` for `n < p`: no multiple of `p` occurs among `1, …, n`. -/
theorem norm_H7_le_one {n : ℕ} (hn : n < p) : ‖((H7 n : ℚ) : ℚ_[p])‖ ≤ 1 := by
  unfold H7
  rw [Rat.cast_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun v hv => ?_
  rw [Finset.mem_range] at hv
  have h1 : ‖((v + 1 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (Nat.coprime_of_lt_prime (by omega) (by omega) Fact.out)
  rw [Nat.cast_add, Nat.cast_one] at h1
  refine le_of_eq ?_
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
    norm_div, norm_one, norm_pow, h1, one_pow, div_one]

/-- `τ^ext_Y(f + ∑_r c_r/(z - r)) ∈ ℤ_p[X]` once `τ(f) ∈ ℤ_p`, `c_r ∈ ℤ_p`, `d(r) < p` and
`Y ∈ ℤ_p[X]`. -/
theorem tauExt_mem_lifts {Y : Polynomial ℚ_[p]} (hY : Y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]))
    {S : Finset ℤ} (hd : ∀ r ∈ S, dIndex r < p) {f : PowerSeries ℚ_[p]} {c : ℤ → ℚ_[p]}
    (hf : ‖tateTau f‖ ≤ 1) (hc : ∀ r ∈ S, ‖c r‖ ≤ 1) :
    tauExt Y S f c ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [lifts_iff_liftsRing] at hY ⊢
  unfold tauExt
  refine add_mem ((lifts_iff_liftsRing _ _).mp (C_mem_lifts_of_norm_le_one hf))
    (_root_.sum_mem fun r hr => mul_mem
      ((lifts_iff_liftsRing _ _).mp (C_mem_lifts_of_norm_le_one (hc r hr)))
      (sub_mem
        ((lifts_iff_liftsRing _ _).mp (C_mem_lifts_of_norm_le_one (norm_H7_le_one (hd r hr))))
        hY))

/-! ## The normalized series `∑_j p^j U_j/T` in `B_T` -/

/-- Analytic part of `∑_j p^j U_j/T ∈ B_T`: the power series with coefficients
`∑_j p^j (P_j)_d`, where `P_j = polyPart S (U j)` is the polynomial part of `U_j/T`. -/
noncomputable def seriesAnalytic (S : Finset ℤ) (U : ℕ → Polynomial ℚ_[p]) :
    PowerSeries ℚ_[p] :=
  PowerSeries.mk fun d => ∑' j, (p : ℚ_[p]) ^ j * (polyPart S (U j)).coeff d

/-- Principal part of `∑_j p^j U_j/T ∈ B_T` at the pole `r`: `∑_j p^j c_{j,r}`, where
`c_{j,r} = principalCoeff S (U j) r` is the residue of `U_j/T` at `r`. -/
noncomputable def seriesPrincipal (S : Finset ℤ) (U : ℕ → Polynomial ℚ_[p]) (r : ℤ) : ℚ_[p] :=
  ∑' j, (p : ℚ_[p]) ^ j * principalCoeff S (U j) r

theorem inv_prime_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem norm_p_pow_mul_le {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) (j : ℕ) :
    ‖(p : ℚ_[p]) ^ j * a‖ ≤ (p : ℝ)⁻¹ ^ j := by
  rw [norm_mul, norm_pow, Padic.norm_p]
  exact mul_le_of_le_one_right (by positivity) ha

theorem summable_p_pow_mul {a : ℕ → ℚ_[p]} (ha : ∀ j, ‖a j‖ ≤ 1) :
    Summable fun j => (p : ℚ_[p]) ^ j * a j := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => norm_p_pow_mul_le (ha j) j)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) inv_prime_lt_one)

theorem norm_tsum_p_pow_mul_le {a : ℕ → ℚ_[p]} (ha : ∀ j, ‖a j‖ ≤ 1) :
    ‖∑' j, (p : ℚ_[p]) ^ j * a j‖ ≤ 1 :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j =>
    (norm_p_pow_mul_le (ha j) j).trans (pow_le_one₀ (by positivity) inv_prime_lt_one.le)

/-- The coefficient series of `seriesAnalytic` converge. -/
theorem summable_seriesAnalytic (S : Finset ℤ) {U : ℕ → Polynomial ℚ_[p]}
    (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) (d : ℕ) :
    Summable fun j => (p : ℚ_[p]) ^ j * (polyPart S (U j)).coeff d :=
  summable_p_pow_mul fun j => norm_coeff_le_one_of_mem_lifts (polyPart_mem_lifts S (hU j)) d

/-- The series `seriesPrincipal` converge at every pole. -/
theorem summable_seriesPrincipal {S : Finset ℤ}
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → ¬ (p : ℤ) ∣ r - s) {U : ℕ → Polynomial ℚ_[p]}
    (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) {r : ℤ} (hr : r ∈ S) :
    Summable fun j => (p : ℚ_[p]) ^ j * principalCoeff S (U j) r :=
  summable_p_pow_mul fun j => norm_principalCoeff_le_one hS (hU j) hr

theorem norm_seriesPrincipal_le_one {S : Finset ℤ}
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → ¬ (p : ℤ) ∣ r - s) {U : ℕ → Polynomial ℚ_[p]}
    (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) {r : ℤ} (hr : r ∈ S) :
    ‖seriesPrincipal S U r‖ ≤ 1 :=
  norm_tsum_p_pow_mul_le fun j => norm_principalCoeff_le_one hS (hU j) hr

/-- The analytic part of `∑_j p^j U_j/T` lies in the Tate algebra: the `P_j` with `j < N`
vanish in high degree and the terms with `j ≥ N` have norm `≤ p^{-N}`. -/
theorem seriesAnalytic_isRestricted (S : Finset ℤ) {U : ℕ → Polynomial ℚ_[p]}
    (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p])) : (seriesAnalytic S U).IsRestricted 1 := by
  rw [PowerSeries.isRestricted_iff', Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_prime_lt_one (p := p))
  refine ⟨(∑ j ∈ range N, (polyPart S (U j)).natDegree) + 1, fun d hd => ?_⟩
  rw [Real.dist_eq, sub_zero, one_pow, mul_one, abs_norm, seriesAnalytic, PowerSeries.coeff_mk]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    fun j => ?_) hN
  by_cases hj : j < N
  · have hle : (polyPart S (U j)).natDegree ≤ ∑ i ∈ range N, (polyPart S (U i)).natDegree :=
      Finset.single_le_sum (f := fun i => (polyPart S (U i)).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    rw [coeff_eq_zero_of_natDegree_lt (show (polyPart S (U j)).natDegree < d by omega), mul_zero,
      norm_zero]
    positivity
  · exact (norm_p_pow_mul_le
      (norm_coeff_le_one_of_mem_lifts (polyPart_mem_lifts S (hU j)) d) j).trans
      (pow_le_pow_of_le_one (by positivity) inv_prime_lt_one.le (by omega))

/-- Proof of Lemma 3.5, analytic part: `|τ(∑_j p^j P_j)|_p ≤ 1`. The `j = 0` term has
degree `≤ deg U_0 ≤ p + 4`, so `τ(P_0) ∈ ℤ_p` by Lemma 3.4; the `j ≥ 1` terms have Gauss
norm `≤ p⁻¹`, and `‖τ‖ ≤ p`. -/
theorem norm_tateTau_seriesAnalytic_le_one (hp7 : 7 ≤ p) (S : Finset ℤ)
    {U : ℕ → Polynomial ℚ_[p]} (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p]))
    (hU0 : (U 0).natDegree ≤ p + 4) : ‖tateTau (seriesAnalytic S U)‖ ≤ 1 := by
  have hcoeff : ∀ j d, ‖(polyPart S (U j)).coeff d‖ ≤ 1 := fun j d =>
    norm_coeff_le_one_of_mem_lifts (polyPart_mem_lifts S (hU j)) d
  set G : PowerSeries ℚ_[p] := PowerSeries.mk fun d =>
    ∑' j, (p : ℚ_[p]) ^ (j + 1) * (polyPart S (U (j + 1))).coeff d with hG
  have hsplit : seriesAnalytic S U
      = ((polyPart S (U 0) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) + G := by
    ext d
    rw [map_add, Polynomial.coeff_coe, hG, PowerSeries.coeff_mk, seriesAnalytic,
      PowerSeries.coeff_mk, (summable_seriesAnalytic S hU d).tsum_eq_zero_add, pow_zero, one_mul]
  have hGr : G.IsRestricted 1 := by
    have h : G = seriesAnalytic S U
        + -((polyPart S (U 0) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) := by
      rw [hsplit]
      ring
    rw [h]
    exact PowerSeries.isRestricted.add 1 (seriesAnalytic_isRestricted S hU)
      (PowerSeries.isRestricted.neg 1 (isRestricted_coe _))
  rw [hsplit, tateTau_add hp7 (isRestricted_coe _) hGr]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [tateTau_coe]
    have hdeg : (polyPart S (U 0)).natDegree ≤ p + 4 := by
      have hmonic : (Lagrange.nodal S fun r : ℤ => (r : ℚ_[p])).Monic := Lagrange.nodal_monic
      rw [polyPart, natDegree_divByMonic _ hmonic]
      omega
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d hd => ?_
    rw [Finset.mem_range] at hd
    rw [norm_mul]
    exact real_mul_le_one (hcoeff 0 d) (norm_nonneg _) (norm_kappa_le_one hp7 (by omega))
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    refine (norm_tateTau_le_of_le hp7 (M := (p : ℝ)⁻¹) (inv_nonneg.mpr hp0.le)
      fun d => ?_).trans (mul_inv_cancel₀ hp0.ne').le
    rw [hG, PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (inv_nonneg.mpr hp0.le)
      fun j => ?_
    exact (norm_p_pow_mul_le (hcoeff (j + 1) d) (j + 1)).trans
      (pow_le_of_le_one (inv_nonneg.mpr hp0.le) inv_prime_lt_one.le (by omega))

/-! ## Lemma 3.5 -/

/-- **Lemma 3.5** (Completion, (33)). Let `p ≥ 7` be prime and `T = ∏_{r ∈ S} (z - r)` with
the `r ∈ S ⊆ ℤ` pairwise incongruent modulo `p` and `d(r) < p`, and let `Y ∈ ℤ_p[X]`. For
every sequence `U_j ∈ ℤ_p[z]` with `deg U_0 ≤ p + 4`, `τ^ext_Y(∑_j p^j U_j/T) ∈ ℤ_p[X]`.
The element `∑_j p^j U_j/T` of `B_T` has analytic part `seriesAnalytic S U` and principal
parts `seriesPrincipal S U` (the termwise sums of the partial fractions of
`partialFraction_spec`). -/
theorem completion (hp7 : 7 ≤ p) {S : Finset ℤ}
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hd : ∀ r ∈ S, dIndex r < p)
    {Y : Polynomial ℚ_[p]} (hY : Y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]))
    {U : ℕ → Polynomial ℚ_[p]} (hU : ∀ j, U j ∈ lifts (algebraMap ℤ_[p] ℚ_[p]))
    (hU0 : (U 0).natDegree ≤ p + 4) :
    tauExt Y S (seriesAnalytic S U) (seriesPrincipal S U) ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) :=
  tauExt_mem_lifts hY hd (norm_tateTau_seriesAnalytic_le_one hp7 S hU hU0)
    fun _ hr => norm_seriesPrincipal_le_one hS hU hr

end ZetaSeven
