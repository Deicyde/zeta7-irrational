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
  · exact mul_le_one₀ (padic_norm_natCast_le_one _) (norm_nonneg _)
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
  refine tsum_eq_sum fun d hd => ?_
  simp only [Finset.mem_range, not_lt] at hd
  rw [Polynomial.coeff_coe, coeff_eq_zero_of_natDegree_lt (show P.natDegree < d by omega),
    zero_mul]

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

end ZetaSeven
