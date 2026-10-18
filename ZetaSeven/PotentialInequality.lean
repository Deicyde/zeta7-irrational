import ZetaSeven.ComparisonMeasure
import ZetaSeven.Enclosures

/-!
# Potential inequality (paper Lemma 6.1, (94); Appendix A.3, equations (113)-(116))

The bound `2 U_ρ(t) - V(t) ≤ M_0 = -109/20 = -5.45` for all `t ≥ 0`
(`two_mul_Ulog_compMeasure_sub_Vfield_le`), where `ρ = compMeasure` is the comparison measure of
Table 1 and `V = Vfield` is the external field (91).

The proof follows Appendix A.3.

* **Closed form of `V`.** For every real `a` and `t ≥ 0`,
  `J_a(t) = a log (t + a²) - 2a + 2 √t arctan (a / √t)` (`Jfield_eq`, equation (92)); the
  antiderivative `u log (t + u²) - 2u + 2 √t arctan (u / √t)` of `log (t + u²)` gives it for
  `t > 0`, and `∫_0^a log u² du = a log a² - 2a` gives it at `t = 0`, where Lean's `a / 0 = 0`
  makes the arctangent term vanish. Summing gives (113) (`Vfield_eq`) and the value at zero
  (`Vfield_zero`), `V(0) = -16 α log α - 2 + 16 α`.
* **The minimum of `V`.** With `y = √t`, `Φ(y) = V(y²)` has
  `Φ'(y) = 2 (π + arctan (1/y) - 8 arctan (α/y))`. We write `Φ` with `arctan (1/y) =
  π/2 - arctan y` so that it is smooth on `ℝ` (`vfieldSq`, `hasDerivAt_vfieldSq`). Half its
  derivative `H(y) = 8 arctan (y/α) - arctan y - 5π/2` increases on `[0, 1]` (its derivative is
  `8α/(α² + y²) - 1/(1 + y²) > 0` there) and is positive for `y ≥ 1/5` (since
  `arctan (α/y) ≤ α/y ≤ 3/8` and `π > 3`). The rational enclosures (112) give
  `Φ'(√q_-) < 0 < Φ'(√q_+)` (`pi_add_arctan_sub_qMinus_neg`, `pi_add_arctan_sub_qPlus_pos`):
  after `arctan (α/y) = π/4 - arctan ((y - α)/(y + α))` both arctangent arguments are below
  `1/2`, and six Taylor terms with `π` to twenty digits decide the signs, whose sizes are about
  `2 · 10⁻⁷` and `5 · 10⁻⁸`. So `V` has a unique minimum `q_*` with `q_- < q_* < q_+`
  (`exists_Vfield_min_between`).
* **The interval bound (114)-(115).** `V_*` bounds `V` below on `[q_-, q_+]`
  (`Vstar_le_Vfield`), hence everywhere, since the minimum lies there. `U_ρ` is nondecreasing on
  `[0, ∞)` (each term of (109) is), so `2 U_ρ(t) - V(t) ≤ B(l, r)` on `[l, r]`
  (`two_mul_Ulog_sub_Vfield_le_potBound`).
* **The certificate (116).** `B(l, r) < -5.45` on each of the 26 intervals of the paper's
  partition `0 < q_- < q_+ < L_16 < ⋯ < L_1 < 2` with `[L_1, 2]` cut into eight equal pieces
  (`potBound_potBreak_lt`). Each interval past `q_+` lies in one of seven blocks `[l₀, r₀]`,
  and monotonicity gives `B(l, r) ≤ 2 U_ρ(r₀) - V(l₀)`. For the latter, each term of (109) is at
  most `log (r₀ - L_j/2)` (as `√(r₀ (r₀ - L_j)) ≤ r₀ - L_j/2`) or `log (L_j/4)`, and
  `V(l₀) ≥ 3π √l₀ + log (1 + l₀) - (3/5) log (l₀ + α²) - 2 - 2 l₀` (from (113) with
  `arctan x ≤ x`). Since every `c_j` is a multiple of `1/200`, the logarithms combine into the
  logarithm of one rational number, which `norm_num` compares with a power of `2`; then
  `log 2 = 0.6931471803…` and `π > 3.141592` finish. The worst block keeps a margin above `0.12`.
* **Past 2.** For `t ≥ 2`, `U_ρ(t) ≤ λ log t`, `J_1(t) ≥ log t` and
  `J_α(t) ≤ α log (t + α²) ≤ α log t + α³/t`, so
  `2 U_ρ(t) - V(t) ≤ (29/20) log t + 8 α³ / t - 2π √t`
  (`two_mul_Ulog_sub_Vfield_le_of_two_le`), which stays below `-5.45` by `log t ≤ 2 (√t - 1)`,
  `√t ≥ 7/5` and `π > 3` (`tail_bound_lt`). The paper's (99) prints the coefficient `13/10`;
  the bounds above give `2λ - 1 + 8α = 29/20`, and with `13/10` the inequality fails for large
  `t` (already at `t = 5`).
-/

namespace ZetaSeven

open MeasureTheory

/-! ### Constants -/

/-- `α = 3/40 > 0`. -/
theorem eAlpha_pos : 0 < eAlpha := by
  norm_num [eAlpha]

/-- `α = 3/40`. -/
theorem eAlpha_eq : eAlpha = 3 / 40 := rfl

/-- Appendix A.3: the rational `q_- = 13415500 / 10⁹` just below the minimum of `V`. -/
noncomputable def qMinus : ℝ := 13415500 / 10 ^ 9

/-- Appendix A.3: the rational `q_+ = 13415502 / 10⁹` just above the minimum of `V`. -/
noncomputable def qPlus : ℝ := 13415502 / 10 ^ 9

theorem qMinus_pos : 0 < qMinus := by
  norm_num [qMinus]

theorem qPlus_pos : 0 < qPlus := by
  norm_num [qPlus]

/-! ### Arctangent facts -/

/-- `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := Real.le_tan (Real.arctan_nonneg.2 hx) (Real.arctan_lt_pi_div_two x)
  rwa [Real.tan_arctan] at h

/-- `y arctan (c/y) = y (π/2 - arctan (y/c))` for `c > 0`, `y ≥ 0` (both sides vanish at
`y = 0`). -/
theorem mul_arctan_div_eq {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    y * Real.arctan (c / y) = y * (Real.pi / 2 - Real.arctan (y / c)) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  · rw [← Real.arctan_inv_of_pos (div_pos hy hc), inv_div]

/-- `√t arctan (c / √t) ≤ c` for `c ≥ 0`. -/
theorem sqrt_mul_arctan_div_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    Real.sqrt t * Real.arctan (c / Real.sqrt t) ≤ c := by
  rcases (Real.sqrt_nonneg t).eq_or_lt with h | h
  · rw [← h, zero_mul]
    exact hc
  · calc Real.sqrt t * Real.arctan (c / Real.sqrt t)
        ≤ Real.sqrt t * (c / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left (arctan_le_self (div_nonneg hc h.le)) h.le
      _ = c := mul_div_cancel₀ c h.ne'

/-- `√t (π/2 - √t) ≤ √t arctan (1 / √t)`. -/
theorem sqrt_mul_arctan_one_div_ge (t : ℝ) :
    Real.sqrt t * (Real.pi / 2 - Real.sqrt t) ≤ Real.sqrt t * Real.arctan (1 / Real.sqrt t) := by
  rw [mul_arctan_div_eq zero_lt_one (Real.sqrt_nonneg t), div_one]
  exact mul_le_mul_of_nonneg_left (by linarith [arctan_le_self (Real.sqrt_nonneg t)])
    (Real.sqrt_nonneg t)

/-- `arctan (a/y) + arctan ((y - a)/(y + a)) = π/4` for `a, y > 0`. -/
theorem arctan_div_add_arctan {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    Real.arctan (a / y) + Real.arctan ((y - a) / (y + a)) = Real.pi / 4 := by
  have hya : 0 < y + a := by linarith
  have hlt : a / y * ((y - a) / (y + a)) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity)]
    nlinarith [mul_pos ha ha, mul_pos hy hy]
  rw [Real.arctan_add hlt, ← Real.arctan_one]
  congr 1
  rw [div_eq_one_iff_eq (sub_pos.2 hlt).ne']
  field

/-! ### The closed form of `V`, equations (92) and (113) -/

/-- For `s > 0`, `u log (s² + u²) - 2u + 2s arctan (u/s)` is an antiderivative of
`log (s² + u²)`. -/
theorem hasDerivAt_Jfield_primitive {s : ℝ} (hs : 0 < s) (u : ℝ) :
    HasDerivAt (fun u => u * Real.log (s ^ 2 + u ^ 2) - 2 * u + 2 * s * Real.arctan (u / s))
      (Real.log (s ^ 2 + u ^ 2)) u := by
  have hpos : 0 < s ^ 2 + u ^ 2 := by positivity
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hlog := (hsq.const_add (s ^ 2)).log hpos.ne'
  have harc := ((hasDerivAt_id' u).div_const s).arctan
  have h := (((hasDerivAt_id' u).fun_mul hlog).fun_sub ((hasDerivAt_id' u).const_mul 2)).fun_add
    (harc.const_mul (2 * s))
  exact h.congr_deriv (by field)

/-- Equation (92) with `t = s²`, `s > 0`. -/
theorem Jfield_sq_eq {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Jfield a (s ^ 2) = a * Real.log (s ^ 2 + a ^ 2) - 2 * a + 2 * s * Real.arctan (a / s) := by
  have hcont : Continuous fun u : ℝ => Real.log (s ^ 2 + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => (by positivity : (0 : ℝ) < s ^ 2 + u ^ 2).ne'
  rw [Jfield, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_Jfield_primitive hs u) (hcont.intervalIntegrable 0 a)]
  simp

/-- Equation (92) at `t = 0`: `J_a(0) = ∫_0^a log u² du = a log a² - 2a`. -/
theorem Jfield_zero_eq (a : ℝ) : Jfield a 0 = a * Real.log (a ^ 2) - 2 * a := by
  have h : (fun u : ℝ => Real.log (0 + u ^ 2)) = fun u => 2 * Real.log u := by
    funext u
    rw [zero_add, Real.log_pow]
    norm_num
  rw [Jfield, h, intervalIntegral.integral_const_mul, integral_log, Real.log_pow]
  push_cast
  ring

/-- Equation (92): `J_a(t) = a log (t + a²) - 2a + 2 √t arctan (a / √t)`. The paper states it
for `a > 0`, `t > 0`; it holds for every real `a` and `t ≥ 0` (at `t = 0` the arctangent term
is `0` by Lean's convention `a / 0 = 0`). -/
theorem Jfield_eq (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Jfield a t = a * Real.log (t + a ^ 2) - 2 * a +
      2 * Real.sqrt t * Real.arctan (a / Real.sqrt t) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [Jfield_zero_eq]
    simp
  · have h := Jfield_sq_eq (Real.sqrt_pos.2 ht) a
    rwa [Real.sq_sqrt ht.le] at h

/-- Equation (113): for `t ≥ 0`,
`V(t) = log (1 + t) - 8α log (t + α²) - 2 + 16α + 2 √t (π + arctan (1/√t) - 8 arctan (α/√t))`.
At `t = 0` the last term is `0`. -/
theorem Vfield_eq {t : ℝ} (ht : 0 ≤ t) :
    Vfield t = Real.log (1 + t) - 8 * eAlpha * Real.log (t + eAlpha ^ 2) - 2 + 16 * eAlpha +
      2 * Real.sqrt t * (Real.pi + Real.arctan (1 / Real.sqrt t) -
        8 * Real.arctan (eAlpha / Real.sqrt t)) := by
  rw [Vfield, Jfield_eq 1 ht, Jfield_eq eAlpha ht, one_pow, add_comm t 1]
  ring

/-- Appendix A.3: the value `V(0) = -16 α log α - 2 + 16 α`, the `t → 0` limit of (113). (The
paper prints `-8 α log α`, dropping the factor `2` of `log α² = 2 log α`.) -/
theorem Vfield_zero : Vfield 0 = -16 * eAlpha * Real.log eAlpha - 2 + 16 * eAlpha := by
  rw [Vfield_eq le_rfl, zero_add, add_zero, Real.log_one, Real.sqrt_zero, Real.log_pow]
  push_cast
  ring

/-! ### The field in the variable `y = √t` and the minimum of `V` -/

/-- `Φ(y) = V(y²)` for `y ≥ 0` (`Vfield_sq_eq`), written with `π/2 - arctan` in place of
`arctan (1/y)` and `arctan (α/y)` so that it is smooth on `ℝ`. -/
noncomputable def vfieldSq (y : ℝ) : ℝ :=
  2 * Real.pi * y + Real.log (1 + y ^ 2) - 2 + 2 * y * (Real.pi / 2 - Real.arctan y) -
    8 * eAlpha * Real.log (y ^ 2 + eAlpha ^ 2) + 16 * eAlpha -
    16 * y * (Real.pi / 2 - Real.arctan (y / eAlpha))

/-- Half the derivative of `vfieldSq`: `H(y) = 8 arctan (y/α) - arctan y - 5π/2`, which equals
`π + arctan (1/y) - 8 arctan (α/y)` for `y > 0`. -/
noncomputable def vfieldSqHalfDeriv (y : ℝ) : ℝ :=
  8 * Real.arctan (y / eAlpha) - Real.arctan y - 5 * Real.pi / 2

theorem Vfield_sq_eq {y : ℝ} (hy : 0 ≤ y) : Vfield (y ^ 2) = vfieldSq y := by
  have h1 := mul_arctan_div_eq zero_lt_one hy
  have h2 := mul_arctan_div_eq eAlpha_pos hy
  rw [div_one] at h1
  rw [Vfield_eq (sq_nonneg y), Real.sqrt_sq hy, vfieldSq]
  linear_combination 2 * h1 - 16 * h2

theorem Vfield_eq_vfieldSq {t : ℝ} (ht : 0 ≤ t) : Vfield t = vfieldSq (Real.sqrt t) := by
  rw [← Vfield_sq_eq (Real.sqrt_nonneg t), Real.sq_sqrt ht]

theorem hasDerivAt_vfieldSq (y : ℝ) : HasDerivAt vfieldSq (2 * vfieldSqHalfDeriv y) y := by
  have hα := eAlpha_pos
  have h1 : 0 < 1 + y ^ 2 := by positivity
  have h2 : 0 < y ^ 2 + eAlpha ^ 2 := by positivity
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have d1 := (hasDerivAt_id' y).const_mul (2 * Real.pi)
  have d2 := (hsq.const_add 1).log h1.ne'
  have d3 := ((hasDerivAt_id' y).const_mul 2).fun_mul
    ((hasDerivAt_id' y).arctan.const_sub (Real.pi / 2))
  have d4 := ((hsq.add_const (eAlpha ^ 2)).log h2.ne').const_mul (8 * eAlpha)
  have d5 := ((hasDerivAt_id' y).const_mul 16).fun_mul
    (((hasDerivAt_id' y).div_const eAlpha).arctan.const_sub (Real.pi / 2))
  have h := (((((d1.fun_add d2).sub_const 2).fun_add d3).fun_sub d4).add_const
    (16 * eAlpha)).fun_sub d5
  exact h.congr_deriv (by rw [vfieldSqHalfDeriv]; field)

theorem hasDerivAt_vfieldSqHalfDeriv (y : ℝ) :
    HasDerivAt vfieldSqHalfDeriv (8 * eAlpha / (eAlpha ^ 2 + y ^ 2) - 1 / (1 + y ^ 2)) y := by
  have hα := eAlpha_pos
  have h := ((((hasDerivAt_id' y).div_const eAlpha).arctan.const_mul 8).fun_sub
    (hasDerivAt_id' y).arctan).sub_const (5 * Real.pi / 2)
  exact h.congr_deriv (by field)

theorem continuous_vfieldSq : Continuous vfieldSq :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_vfieldSq y).continuousAt

theorem continuous_vfieldSqHalfDeriv : Continuous vfieldSqHalfDeriv :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_vfieldSqHalfDeriv y).continuousAt

/-- For `y > 0`, `π + arctan (1/y) - 8 arctan (α/y) = H(y)`, i.e. `Φ'(y) = 2 H(y)`. -/
theorem pi_add_arctan_eq_vfieldSqHalfDeriv {y : ℝ} (hy : 0 < y) :
    Real.pi + Real.arctan (1 / y) - 8 * Real.arctan (eAlpha / y) = vfieldSqHalfDeriv y := by
  rw [vfieldSqHalfDeriv, one_div, Real.arctan_inv_of_pos hy, ← inv_div y eAlpha,
    Real.arctan_inv_of_pos (div_pos hy eAlpha_pos)]
  ring

/-- `H` is strictly increasing on `[0, 1]`: `H'(y) = 8α/(α² + y²) - 1/(1 + y²) > 0` there. -/
theorem vfieldSqHalfDeriv_strictMonoOn : StrictMonoOn vfieldSqHalfDeriv (Set.Icc 0 1) := by
  have hα := eAlpha_pos
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) continuous_vfieldSqHalfDeriv.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
  rw [(hasDerivAt_vfieldSqHalfDeriv x).deriv, sub_pos,
    div_lt_div_iff₀ (by positivity) (by positivity), eAlpha_eq]
  nlinarith

/-- `H(y) > 0` for `y ≥ 1/5`: `H(y) = π + arctan (1/y) - 8 arctan (α/y) ≥ π - 8α/y ≥ π - 3`. -/
theorem vfieldSqHalfDeriv_pos_of_ge {y : ℝ} (hy : 1 / 5 ≤ y) : 0 < vfieldSqHalfDeriv y := by
  have hy0 : 0 < y := by linarith
  have hα := eAlpha_pos
  rw [← pi_add_arctan_eq_vfieldSqHalfDeriv hy0]
  have h1 : 0 ≤ Real.arctan (1 / y) := Real.arctan_nonneg.2 (by positivity)
  have h2 : Real.arctan (eAlpha / y) ≤ eAlpha / y := arctan_le_self (by positivity)
  have h3 : eAlpha / y ≤ 3 / 8 := by
    rw [div_le_iff₀ hy0, eAlpha_eq]
    linarith
  linarith [Real.pi_gt_three]

/-- Appendix A.3: `Φ'(√q_-) < 0`, i.e. `π + arctan (1/√q_-) - 8 arctan (α/√q_-) < 0`, from the
enclosures (112). -/
theorem pi_add_arctan_sub_qMinus_neg :
    Real.pi + Real.arctan (1 / Real.sqrt qMinus) -
      8 * Real.arctan (eAlpha / Real.sqrt qMinus) < 0 := by
  have hy : 0 < Real.sqrt qMinus := Real.sqrt_pos.2 qMinus_pos
  have h1 : Real.arctan (1 / Real.sqrt qMinus) =
      Real.pi / 2 - Real.arctan (Real.sqrt qMinus) := by
    rw [one_div, Real.arctan_inv_of_pos hy]
  have h2 := arctan_div_add_arctan eAlpha_pos hy
  have hlo : (579126497 / 5000000000 : ℝ) ≤ Real.sqrt qMinus :=
    Real.le_sqrt_of_sq_le (by norm_num [qMinus])
  have hhi : Real.sqrt qMinus ≤ 231650599 / 2000000000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num [qMinus])
  have hw : (Real.sqrt qMinus - eAlpha) / (Real.sqrt qMinus + eAlpha) ≤
      81650599 / 381650599 := by
    rw [div_le_iff₀ (by linarith [eAlpha_pos]), eAlpha_eq]
    linarith
  have ha1 := Real.arctan_strictMono.monotone hlo
  have ha2 := Real.arctan_strictMono.monotone hw
  obtain ⟨t1, -⟩ := abs_le.1 (arctan_taylor_enclosure
    (z := 579126497 / 5000000000) (by norm_num) (by norm_num) 6)
  obtain ⟨-, t2⟩ := abs_le.1 (arctan_taylor_enclosure
    (z := 81650599 / 381650599) (by norm_num) (by norm_num) 6)
  norm_num [Finset.sum_range_succ] at t1 t2
  linarith [Real.pi_gt_d20]

/-- Appendix A.3: `Φ'(√q_+) > 0`, i.e. `π + arctan (1/√q_+) - 8 arctan (α/√q_+) > 0`, from the
enclosures (112). -/
theorem pi_add_arctan_sub_qPlus_pos :
    0 < Real.pi + Real.arctan (1 / Real.sqrt qPlus) -
      8 * Real.arctan (eAlpha / Real.sqrt qPlus) := by
  have hy : 0 < Real.sqrt qPlus := Real.sqrt_pos.2 qPlus_pos
  have h1 : Real.arctan (1 / Real.sqrt qPlus) =
      Real.pi / 2 - Real.arctan (Real.sqrt qPlus) := by
    rw [one_div, Real.arctan_inv_of_pos hy]
  have h2 := arctan_div_add_arctan eAlpha_pos hy
  have hlo : (1158253081 / 10000000000 : ℝ) ≤ Real.sqrt qPlus :=
    Real.le_sqrt_of_sq_le (by norm_num [qPlus])
  have hhi : Real.sqrt qPlus ≤ 579126541 / 5000000000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num [qPlus])
  have hw : (408253081 / 1908253081 : ℝ) ≤
      (Real.sqrt qPlus - eAlpha) / (Real.sqrt qPlus + eAlpha) := by
    rw [le_div_iff₀ (by linarith [eAlpha_pos]), eAlpha_eq]
    linarith
  have ha1 := Real.arctan_strictMono.monotone hhi
  have ha2 := Real.arctan_strictMono.monotone hw
  obtain ⟨-, t1⟩ := abs_le.1 (arctan_taylor_enclosure
    (z := 579126541 / 5000000000) (by norm_num) (by norm_num) 6)
  obtain ⟨t2, -⟩ := abs_le.1 (arctan_taylor_enclosure
    (z := 408253081 / 1908253081) (by norm_num) (by norm_num) 6)
  norm_num [Finset.sum_range_succ] at t1 t2
  linarith [Real.pi_lt_d20]

/-- The zero of `H` between `√q_-` and `√q_+`. -/
theorem exists_vfieldSqHalfDeriv_eq_zero :
    ∃ y, Real.sqrt qMinus < y ∧ y < Real.sqrt qPlus ∧ vfieldSqHalfDeriv y = 0 := by
  have hle : Real.sqrt qMinus ≤ Real.sqrt qPlus :=
    Real.sqrt_le_sqrt (by norm_num [qMinus, qPlus])
  have h1 : vfieldSqHalfDeriv (Real.sqrt qMinus) < 0 := by
    rw [← pi_add_arctan_eq_vfieldSqHalfDeriv (Real.sqrt_pos.2 qMinus_pos)]
    exact pi_add_arctan_sub_qMinus_neg
  have h2 : 0 < vfieldSqHalfDeriv (Real.sqrt qPlus) := by
    rw [← pi_add_arctan_eq_vfieldSqHalfDeriv (Real.sqrt_pos.2 qPlus_pos)]
    exact pi_add_arctan_sub_qPlus_pos
  obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ :=
    intermediate_value_Ioo hle continuous_vfieldSqHalfDeriv.continuousOn ⟨h1, h2⟩
  exact ⟨y, hy1, hy2, hy⟩

/-- Appendix A.3: `V` has exactly one minimum on `[0, ∞)`, at a point `q_*` strictly between
the rationals `q_-` and `q_+`: `V` is strictly decreasing on `[0, q_*]` and strictly increasing
on `[q_*, ∞)`. -/
theorem exists_Vfield_min_between :
    ∃ q, qMinus < q ∧ q < qPlus ∧
      StrictAntiOn Vfield (Set.Icc 0 q) ∧ StrictMonoOn Vfield (Set.Ici q) := by
  obtain ⟨y, hy1, hy2, hy⟩ := exists_vfieldSqHalfDeriv_eq_zero
  have hy0 : 0 < y := (Real.sqrt_nonneg _).trans_lt hy1
  have hy1' : y < 1 := hy2.trans ((Real.sqrt_lt' zero_lt_one).2 (by norm_num [qPlus]))
  have hneg : ∀ x, 0 ≤ x → x < y → vfieldSqHalfDeriv x < 0 := fun x hx hxy =>
    (vfieldSqHalfDeriv_strictMonoOn ⟨hx, (hxy.trans hy1').le⟩ ⟨hy0.le, hy1'.le⟩
      hxy).trans_eq hy
  have hpos : ∀ x, y < x → 0 < vfieldSqHalfDeriv x := fun x hxy => by
    rcases le_or_gt x 1 with hx1 | hx1
    · exact hy.symm.trans_lt
        (vfieldSqHalfDeriv_strictMonoOn ⟨hy0.le, hy1'.le⟩ ⟨(hy0.trans hxy).le, hx1⟩ hxy)
    · exact vfieldSqHalfDeriv_pos_of_ge (by linarith)
  have hanti : StrictAntiOn vfieldSq (Set.Icc 0 y) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 y) continuous_vfieldSq.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_vfieldSq x).deriv]
    linarith [hneg x hx.1.le hx.2]
  have hmono : StrictMonoOn vfieldSq (Set.Ici y) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici y) continuous_vfieldSq.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_vfieldSq x).deriv]
    linarith [hpos x hx]
  refine ⟨y ^ 2, (Real.sqrt_lt' hy0).1 hy1, (Real.lt_sqrt hy0.le).1 hy2, ?_, ?_⟩
  · intro a ha b hb hab
    rw [Vfield_eq_vfieldSq ha.1, Vfield_eq_vfieldSq hb.1]
    exact hanti ⟨Real.sqrt_nonneg a, (Real.sqrt_le_left hy0.le).2 ha.2⟩
      ⟨Real.sqrt_nonneg b, (Real.sqrt_le_left hy0.le).2 hb.2⟩ (Real.sqrt_lt_sqrt ha.1 hab)
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := (sq_nonneg y).trans (Set.mem_Ici.1 ha)
    rw [Vfield_eq_vfieldSq ha0, Vfield_eq_vfieldSq (ha0.trans hab.le)]
    exact hmono (Real.le_sqrt_of_sq_le (Set.mem_Ici.1 ha))
      (Real.le_sqrt_of_sq_le (Set.mem_Ici.1 hb)) (Real.sqrt_lt_sqrt ha0 hab)

/-! ### The lower bound `V_*` and the interval bound `B(l, r)`, equations (114)-(115) -/

/-- Equation (114): the lower bound `V_*` of `V` on `[q_-, q_+]`. -/
noncomputable def Vstar : ℝ :=
  Real.log (1 + qMinus) - 8 * eAlpha * Real.log (qPlus + eAlpha ^ 2) - 2 + 16 * eAlpha +
    2 * Real.sqrt qPlus * (Real.pi + Real.arctan (1 / Real.sqrt qPlus) -
      8 * Real.arctan (eAlpha / Real.sqrt qMinus))

/-- Equation (114): `V(t) ≥ V_*` for `q_- ≤ t ≤ q_+`. Each term of (113) is bounded at an
endpoint; the bracket `π + arctan (1/√t) - 8 arctan (α/√t)` is at least
`π + arctan (1/√q_+) - 8 arctan (α/√q_-)`, which is negative because it is below `Φ'(√q_-)/2`,
so its product with `2√t` is at least its product with `2√q_+`. -/
theorem Vstar_le_Vfield {t : ℝ} (h1 : qMinus ≤ t) (h2 : t ≤ qPlus) : Vstar ≤ Vfield t := by
  have hqm := qMinus_pos
  have hα := eAlpha_pos
  have ht : 0 < t := hqm.trans_le h1
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsm : 0 < Real.sqrt qMinus := Real.sqrt_pos.2 hqm
  have hsmt : Real.sqrt qMinus ≤ Real.sqrt t := Real.sqrt_le_sqrt h1
  have hstp : Real.sqrt t ≤ Real.sqrt qPlus := Real.sqrt_le_sqrt h2
  have hl1 : Real.log (1 + qMinus) ≤ Real.log (1 + t) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl2 : 8 * eAlpha * Real.log (t + eAlpha ^ 2) ≤
      8 * eAlpha * Real.log (qPlus + eAlpha ^ 2) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by positivity)
  have ha1 : Real.arctan (1 / Real.sqrt qPlus) ≤ Real.arctan (1 / Real.sqrt t) :=
    Real.arctan_strictMono.monotone (one_div_le_one_div_of_le hst hstp)
  have ha2 : Real.arctan (eAlpha / Real.sqrt t) ≤ Real.arctan (eAlpha / Real.sqrt qMinus) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left hα.le hsm hsmt)
  have ha3 : Real.arctan (1 / Real.sqrt qPlus) ≤ Real.arctan (1 / Real.sqrt qMinus) :=
    Real.arctan_strictMono.monotone (one_div_le_one_div_of_le hsm (hsmt.trans hstp))
  have hb : Real.pi + Real.arctan (1 / Real.sqrt qPlus) -
      8 * Real.arctan (eAlpha / Real.sqrt qMinus) < 0 := by
    linarith [pi_add_arctan_sub_qMinus_neg]
  have hm1 := mul_le_mul_of_nonneg_left (show Real.pi + Real.arctan (1 / Real.sqrt qPlus) -
      8 * Real.arctan (eAlpha / Real.sqrt qMinus) ≤ Real.pi + Real.arctan (1 / Real.sqrt t) -
      8 * Real.arctan (eAlpha / Real.sqrt t) by linarith)
    (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)
  have hm2 := mul_le_mul_of_nonpos_right (show 2 * Real.sqrt t ≤ 2 * Real.sqrt qPlus by linarith)
    hb.le
  rw [Vfield_eq ht.le, Vstar]
  linarith

theorem Vfield_antitoneOn_qMinus : AntitoneOn Vfield (Set.Icc 0 qMinus) := by
  obtain ⟨q, hq1, -, hanti, -⟩ := exists_Vfield_min_between
  exact hanti.antitoneOn.mono (Set.Icc_subset_Icc le_rfl hq1.le)

theorem Vfield_monotoneOn_qPlus : MonotoneOn Vfield (Set.Ici qPlus) := by
  obtain ⟨q, -, hq2, -, hmono⟩ := exists_Vfield_min_between
  exact hmono.monotoneOn.mono (Set.Ici_subset_Ici.2 hq2.le)

/-- `V_* ≤ V(t)` for every `t ≥ 0`: the minimum of `V` lies in `[q_-, q_+]`. -/
theorem Vstar_le_Vfield_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Vstar ≤ Vfield t := by
  obtain ⟨q, hq1, hq2, hanti, hmono⟩ := exists_Vfield_min_between
  have hq0 : 0 ≤ q := qMinus_pos.le.trans hq1.le
  have hVq : Vfield q ≤ Vfield t := by
    rcases le_total t q with h | h
    · exact hanti.antitoneOn ⟨ht, h⟩ ⟨hq0, le_rfl⟩ h
    · exact hmono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
  exact (Vstar_le_Vfield hq1.le hq2.le).trans hVq

/-- Each term `U_{ω_{[0,L]}}` of (109) is nondecreasing: constant `log (L/4)` up to `L`, then
increasing. -/
theorem arcsinePotential_monotone {L : ℝ} (hL : 0 < L) : Monotone (arcsinePotential L) := by
  intro t₁ t₂ h
  unfold arcsinePotential
  by_cases h₂ : t₂ ≤ L
  · simp only [ite_eq_left (h.trans h₂), ite_eq_left h₂, le_refl]
  · by_cases h₁ : t₁ ≤ L
    · rw [ite_eq_left h₁, ite_eq_right h₂]
      apply Real.log_le_log (by positivity)
      linarith [Real.sqrt_nonneg (t₂ * (t₂ - L)), not_le.1 h₂]
    · rw [ite_eq_right h₁, ite_eq_right h₂]
      have h₁' := not_le.1 h₁
      apply Real.log_le_log (by linarith [Real.sqrt_nonneg (t₁ * (t₁ - L))])
      have hmul : 0 ≤ (t₂ - t₁) * (t₂ + t₁ - L) :=
        mul_nonneg (sub_nonneg.2 h) (by linarith)
      have : Real.sqrt (t₁ * (t₁ - L)) ≤ Real.sqrt (t₂ * (t₂ - L)) :=
        Real.sqrt_le_sqrt (by nlinarith [hmul])
      linarith

theorem compPotential_monotone : Monotone compPotential := fun _ _ h =>
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (arcsinePotential_monotone (compEndpoint_pos j) h) (compWeight_pos j).le

/-- Appendix A.3: the potential `U_ρ` of the comparison measure is nondecreasing on `[0, ∞)`. -/
theorem Ulog_compMeasure_monotoneOn : MonotoneOn (Ulog compMeasure) (Set.Ici 0) :=
  fun a ha b hb hab => by
    rw [Ulog_compMeasure (Set.mem_Ici.1 ha), Ulog_compMeasure (Set.mem_Ici.1 hb)]
    exact compPotential_monotone hab

/-- Equation (115): the interval bound
`B(l, r) = 2 max (U_ρ(l), U_ρ(r)) - (V(r) if r ≤ q_-, V(l) if l ≥ q_+, V_* otherwise)`. -/
noncomputable def potBound (l r : ℝ) : ℝ :=
  2 * max (Ulog compMeasure l) (Ulog compMeasure r) -
    (if r ≤ qMinus then Vfield r else if qPlus ≤ l then Vfield l else Vstar)

/-- Appendix A.3: `2 U_ρ(t) - V(t) ≤ B(l, r)` for `0 ≤ l ≤ t ≤ r`. -/
theorem two_mul_Ulog_sub_Vfield_le_potBound {l r t : ℝ} (hl0 : 0 ≤ l) (hlt : l ≤ t)
    (htr : t ≤ r) : 2 * Ulog compMeasure t - Vfield t ≤ potBound l r := by
  have ht0 : 0 ≤ t := hl0.trans hlt
  have hr0 : 0 ≤ r := ht0.trans htr
  have hU : Ulog compMeasure t ≤ max (Ulog compMeasure l) (Ulog compMeasure r) :=
    (Ulog_compMeasure_monotoneOn ht0 hr0 htr).trans (le_max_right _ _)
  have hV : (if r ≤ qMinus then Vfield r else if qPlus ≤ l then Vfield l else Vstar) ≤
      Vfield t := by
    split_ifs with h1 h2
    · exact Vfield_antitoneOn_qMinus ⟨ht0, htr.trans h1⟩ ⟨hr0, h1⟩ htr
    · exact Vfield_monotoneOn_qPlus h2 (h2.trans hlt) hlt
    · exact Vstar_le_Vfield_of_nonneg ht0
  rw [potBound]
  linarith

/-! ### Rational bounds for the certificate -/

/-- The argument bounding the `j`-th logarithm of (109) at `R`: `L/4` if `R ≤ L`, else
`R - L/2` (as `√(R (R - L)) ≤ R - L/2`). -/
noncomputable def uArg (L R : ℝ) : ℝ := if R ≤ L then L / 4 else R - L / 2

theorem uArg_pos {L : ℝ} (hL : 0 < L) (R : ℝ) : 0 < uArg L R := by
  unfold uArg
  split_ifs with h
  · positivity
  · linarith [not_le.1 h]

theorem arcsinePotential_le_log_uArg {L : ℝ} (hL : 0 < L) (R : ℝ) :
    arcsinePotential L R ≤ Real.log (uArg L R) := by
  unfold arcsinePotential uArg
  split_ifs with h
  · exact le_rfl
  · have h' := not_le.1 h
    apply Real.log_le_log (by linarith [Real.sqrt_nonneg (R * (R - L))])
    have : Real.sqrt (R * (R - L)) ≤ R - L / 2 :=
      (Real.sqrt_le_left (by linarith)).2 (by nlinarith [sq_nonneg L])
    linarith

theorem compPotential_le_sum_log (R : ℝ) :
    compPotential R ≤ ∑ j, compWeight j * Real.log (uArg (compEndpoint j) R) :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (arcsinePotential_le_log_uArg (compEndpoint_pos j) R) (compWeight_pos j).le

/-- Table 1: `c_j = cExp j / 200`. -/
def cExp : Fin 16 → ℕ := ![20, 16, 12, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 3, 24]

theorem compWeight_eq_cExp (j : Fin 16) : compWeight j = (cExp j : ℝ) / 200 := by
  fin_cases j <;> norm_num [compWeight, tableCNum, cExp]

theorem sum_compWeight_mul_log {x : Fin 16 → ℝ} (hx : ∀ j, 0 < x j) :
    ∑ j, compWeight j * Real.log (x j) = Real.log (∏ j, x j ^ cExp j) / 200 := by
  rw [Real.log_prod (fun j _ => pow_ne_zero _ (hx j).ne'), Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.log_pow, compWeight_eq_cExp]
  ring

/-- Taking logarithms in `A B⁶⁰ 2ᵇ ≤ C¹⁰⁰ 2ᵃ`. -/
theorem log_bound_of_prod {A B C : ℝ} (a b : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A * B ^ 60 * 2 ^ b ≤ C ^ 100 * 2 ^ a) :
    Real.log A ≤ 100 * Real.log C - 60 * Real.log B + (a * Real.log 2 - b * Real.log 2) := by
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h2
  push_cast at h2
  linarith

/-- From (113) with `arctan (1/√t) ≥ π/2 - √t` and `√t arctan (α/√t) ≤ α`:
`V(t) ≥ 3π √t + log (1 + t) - (3/5) log (t + α²) - 2 - 2t`. -/
theorem Vfield_ge_crude {t : ℝ} (ht : 0 ≤ t) :
    3 * Real.pi * Real.sqrt t + Real.log (1 + t) - 3 / 5 * Real.log (t + eAlpha ^ 2) - 2 - 2 * t ≤
      Vfield t := by
  have h8 : 8 * eAlpha * Real.log (t + eAlpha ^ 2) = 3 / 5 * Real.log (t + eAlpha ^ 2) := by
    rw [eAlpha_eq]
    ring
  rw [Vfield_eq ht]
  linarith [sqrt_mul_arctan_one_div_ge t, sqrt_mul_arctan_div_le eAlpha_pos.le t,
    Real.sq_sqrt ht, eAlpha_eq]

/-- The block estimate behind (116): if `s² ≤ l₀` and the rational inequality `hP` holds, then
`2 U_ρ(r₀) - V(l₀) < -109/20` (here `r₀ = R`, `l₀ = Lo`). -/
theorem two_compPotential_sub_Vfield_lt {Lo R : ℝ} (s : ℝ) (a b : ℕ) (hLo : 0 ≤ Lo)
    (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ Lo)
    (hP : (∏ j, uArg (compEndpoint j) R ^ cExp j) * (Lo + eAlpha ^ 2) ^ 60 * 2 ^ b ≤
      (1 + Lo) ^ 100 * 2 ^ a)
    (hnum : ((a : ℝ) * 0.6931471808 - b * 0.6931471803) / 100 - 3 * 3.141592 * s + 2 + 2 * Lo <
      -109 / 20) :
    2 * compPotential R - Vfield Lo < -109 / 20 := by
  have hx : ∀ j, 0 < uArg (compEndpoint j) R := fun j => uArg_pos (compEndpoint_pos j) R
  have hprod : 0 < ∏ j, uArg (compEndpoint j) R ^ cExp j :=
    Finset.prod_pos fun j _ => pow_pos (hx j) _
  have hU := compPotential_le_sum_log R
  rw [sum_compWeight_mul_log hx] at hU
  have hα := eAlpha_pos
  have hlog := log_bound_of_prod a b hprod (by positivity : 0 < Lo + eAlpha ^ 2)
    (by linarith : 0 < 1 + Lo) hP
  linarith [Vfield_ge_crude hLo,
    mul_le_mul Real.pi_gt_d6.le (Real.le_sqrt_of_sq_le hs2) hs Real.pi_pos.le,
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg (α := ℝ) a),
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg (α := ℝ) b)]

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[0, q_-]`: `2 U_ρ(q_-) - V(q_-) < -109/20`. -/
theorem cover_qMinus : 2 * compPotential qMinus - Vfield qMinus < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (4633 / 40000) 0 1138 qMinus_pos.le (by norm_num)
    (by norm_num [qMinus])
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, qMinus, eAlpha])
    (by norm_num [qMinus])

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[q_+, L_11] = [q_+, 3/25]`. -/
theorem cover_qPlus : 2 * compPotential (3 / 25) - Vfield qPlus < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (4633 / 40000) 0 961 qPlus_pos.le (by norm_num)
    (by norm_num [qPlus])
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, qPlus, eAlpha])
    (by norm_num [qPlus])

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[L_11, L_8] = [3/25, 1/4]`. -/
theorem cover_3_25 : 2 * compPotential (1 / 4) - Vfield (3 / 25) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (34641 / 100000) 0 675 (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[L_8, L_6] = [1/4, 2/5]`. -/
theorem cover_1_4 : 2 * compPotential (2 / 5) - Vfield (1 / 4) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (1 / 2) 0 520 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[L_6, L_4] = [2/5, 3/5]`. -/
theorem cover_2_5 : 2 * compPotential (3 / 5) - Vfield (2 / 5) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (126491 / 200000) 0 389 (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[L_4, L_1] = [3/5, 87/100]`. -/
theorem cover_3_5 : 2 * compPotential (87 / 100) - Vfield (3 / 5) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (193649 / 250000) 0 237 (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[L_1, L_1 + 3(2 - L_1)/8] = [87/100, 207/160]`. -/
theorem cover_87_100 : 2 * compPotential (207 / 160) - Vfield (87 / 100) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (932737 / 1000000) 0 75 (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The block `[207/160, 2]`. -/
theorem cover_207_160 : 2 * compPotential 2 - Vfield (207 / 160) < -109 / 20 :=
  two_compPotential_sub_Vfield_lt (1137431 / 1000000) 62 0 (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, eAlpha])
    (by norm_num)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 2000 in
/-- The interval `[q_-, q_+]`: `2 U_ρ(q_+) - V_* < -109/20`. -/
theorem two_compPotential_qPlus_sub_Vstar_lt : 2 * compPotential qPlus - Vstar < -109 / 20 := by
  have hx : ∀ j, 0 < uArg (compEndpoint j) qPlus := fun j => uArg_pos (compEndpoint_pos j) qPlus
  have hprod : 0 < ∏ j, uArg (compEndpoint j) qPlus ^ cExp j :=
    Finset.prod_pos fun j _ => pow_pos (hx j) _
  have hU := compPotential_le_sum_log qPlus
  rw [sum_compWeight_mul_log hx] at hU
  have hα := eAlpha_pos
  have hqm := qMinus_pos
  have hqp := qPlus_pos
  have hlog := log_bound_of_prod 0 1138 hprod
    (by positivity : 0 < qPlus + eAlpha ^ 2) (by linarith : 0 < 1 + qMinus)
    (by norm_num [uArg, cExp, compEndpoint, tableLNum, Fin.prod_univ_succ, qPlus, qMinus, eAlpha])
  push_cast at hlog
  have hylo : (579126497 / 5000000000 : ℝ) ≤ Real.sqrt qMinus :=
    Real.le_sqrt_of_sq_le (by norm_num [qMinus])
  have hyhi : Real.sqrt qPlus ≤ 579126541 / 5000000000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num [qPlus])
  have hcp : (1158253081 / 10000000000 : ℝ) ≤ Real.sqrt qPlus :=
    Real.le_sqrt_of_sq_le (by norm_num [qPlus])
  have hat : Real.arctan (eAlpha / Real.sqrt qMinus) ≤ 3 / 40 / (579126497 / 5000000000) := by
    refine (arctan_le_self (by positivity)).trans ?_
    rw [eAlpha_eq]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hylo
  have hA2 : Real.sqrt qPlus * Real.arctan (eAlpha / Real.sqrt qMinus) ≤
      579126541 / 5000000000 * (3 / 40 / (579126497 / 5000000000)) :=
    mul_le_mul hyhi hat (Real.arctan_nonneg.2 (by positivity)) (by norm_num)
  have h8 : 8 * eAlpha * Real.log (qPlus + eAlpha ^ 2) =
      3 / 5 * Real.log (qPlus + eAlpha ^ 2) := by
    rw [eAlpha_eq]
    ring
  rw [Vstar]
  linarith [sqrt_mul_arctan_one_div_ge qPlus, Real.sq_sqrt hqp.le, Real.log_two_gt_d9,
    mul_le_mul Real.pi_gt_d6.le hcp (by norm_num) Real.pi_pos.le, eAlpha_eq,
    (show qPlus = 13415502 / 10 ^ 9 from rfl)]

/-! ### The certificate (116) on the partition of `[0, 2]` -/

/-- An interval `[l, r]` with `q_+ ≤ l₀ ≤ l ≤ r ≤ r₀` has `B(l, r) ≤ 2 U_ρ(r₀) - V(l₀)`. -/
theorem potBound_lt_of_cover {l r Lo R : ℝ} (hLo : qPlus ≤ Lo) (hl : Lo ≤ l) (hlr : l ≤ r)
    (hR : r ≤ R) (hc : 2 * compPotential R - Vfield Lo < -109 / 20) :
    potBound l r < -109 / 20 := by
  have hl0 : 0 ≤ l := qPlus_pos.le.trans (hLo.trans hl)
  have hr : ¬ r ≤ qMinus := not_le.2 (by
    have : qMinus < qPlus := by norm_num [qMinus, qPlus]
    linarith)
  rw [potBound, ite_eq_right hr, ite_eq_left (hLo.trans hl), Ulog_compMeasure hl0,
    Ulog_compMeasure (hl0.trans hlr), max_eq_right (compPotential_monotone hlr)]
  linarith [compPotential_monotone hR, Vfield_monotoneOn_qPlus hLo (hLo.trans hl) hl]

/-- Intervals `[l, r] ⊆ [0, q_-]` have `B(l, r) ≤ 2 U_ρ(q_-) - V(q_-) < -109/20`. -/
theorem potBound_lt_of_le_qMinus {l r : ℝ} (hl0 : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ qMinus) :
    potBound l r < -109 / 20 := by
  have hr0 : 0 ≤ r := hl0.trans hlr
  rw [potBound, ite_eq_left hr, Ulog_compMeasure hl0, Ulog_compMeasure hr0,
    max_eq_right (compPotential_monotone hlr)]
  linarith [compPotential_monotone hr, cover_qMinus,
    Vfield_antitoneOn_qMinus ⟨hr0, hr⟩ ⟨hr0.trans hr, le_rfl⟩ hr]

/-- The interval `[q_-, q_+]`: `B(q_-, q_+) = 2 U_ρ(q_+) - V_* < -109/20`. -/
theorem potBound_qMinus_qPlus_lt : potBound qMinus qPlus < -109 / 20 := by
  have h : ¬ qPlus ≤ qMinus := by norm_num [qMinus, qPlus]
  rw [potBound, ite_eq_right h, ite_eq_right h, Ulog_compMeasure qMinus_pos.le,
    Ulog_compMeasure qPlus_pos.le,
    max_eq_right (compPotential_monotone (by norm_num [qMinus, qPlus] : qMinus ≤ qPlus))]
  exact two_compPotential_qPlus_sub_Vstar_lt

theorem potBound_lt_of_eq_qMinus_qPlus {l r : ℝ} (hl : l = qMinus) (hr : r = qPlus) :
    potBound l r < -109 / 20 := by
  subst hl hr
  exact potBound_qMinus_qPlus_lt

/-- Appendix A.3: the eight equal pieces of `[L_1, 2]` have breakpoints
`L_1 + k (2 - L_1) / 8`, `0 ≤ k ≤ 8`. -/
noncomputable def tailPoint (k : ℕ) : ℝ := compEndpoint 0 + k * (2 - compEndpoint 0) / 8

/-- Appendix A.3: the breakpoints `A_0 < A_1 < ⋯ < A_26` of the partition of `[0, 2]`:
`0, q_-, q_+, L_16, L_15, …, L_1`, then `[L_1, 2]` cut into eight equal pieces. -/
noncomputable def potBreak : Fin 27 → ℝ :=
  ![0, qMinus, qPlus, compEndpoint 15, compEndpoint 14, compEndpoint 13, compEndpoint 12,
    compEndpoint 11, compEndpoint 10, compEndpoint 9, compEndpoint 8, compEndpoint 7,
    compEndpoint 6, compEndpoint 5, compEndpoint 4, compEndpoint 3, compEndpoint 2,
    compEndpoint 1, compEndpoint 0, tailPoint 1, tailPoint 2, tailPoint 3, tailPoint 4,
    tailPoint 5, tailPoint 6, tailPoint 7, tailPoint 8]

/-- Evaluates partition breakpoints. -/
local macro "bp" : tactic =>
  `(tactic| norm_num [potBreak, tailPoint, compEndpoint, tableLNum, qMinus, qPlus])

/-- Appendix A.3: the breakpoints increase, `0 < q_- < q_+ < L_16 < ⋯ < L_1 < ⋯ < 2`. -/
theorem potBreak_strictMono : StrictMono potBreak := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> bp

/-- Appendix A.3: the partition runs from `A_0 = 0` to `A_26 = 2`. -/
theorem potBreak_zero_last : potBreak 0 = 0 ∧ potBreak 26 = 2 := by
  constructor <;> bp

/-- Equation (116): `B(l, r) < -5.45` on every interval `[A_i, A_{i+1}]` of the partition. -/
theorem potBound_potBreak_lt (i : Fin 26) :
    potBound (potBreak i.castSucc) (potBreak i.succ) < -109 / 20 := by
  fin_cases i
  · exact potBound_lt_of_le_qMinus (by bp) (by bp) (by bp)
  · exact potBound_lt_of_eq_qMinus_qPlus (by bp) (by bp)
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_qPlus
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_25
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_25
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_25
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_1_4
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_1_4
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_2_5
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_2_5
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_5
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_5
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_3_5
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_87_100
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_87_100
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_87_100
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_207_160
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_207_160
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_207_160
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_207_160
  · exact potBound_lt_of_cover (by bp) (by bp) (by bp) (by bp) cover_207_160

/-! ### Past `2`: the asymptotic bound -/

theorem arcsinePotential_le_log {L t : ℝ} (hL : 0 < L) (hLt : L < t) :
    arcsinePotential L t ≤ Real.log t := by
  rw [arcsinePotential, ite_eq_right (not_le.2 hLt)]
  apply Real.log_le_log (by linarith [Real.sqrt_nonneg (t * (t - L))])
  have : Real.sqrt (t * (t - L)) ≤ t :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith [mul_pos (hL.trans hLt) hL])
  linarith

/-- For `t ≥ 2`, `U_ρ(t) ≤ λ log t`: `ρ` lives on `(0, 2)` and has mass `λ = 37/40`. -/
theorem compPotential_le_log {t : ℝ} (ht : 2 ≤ t) : compPotential t ≤ 37 / 40 * Real.log t :=
  calc compPotential t ≤ ∑ j, compWeight j * Real.log t :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (arcsinePotential_le_log (compEndpoint_pos j) ((compEndpoint_lt_two j).trans_le ht))
          (compWeight_pos j).le
    _ = 37 / 40 * Real.log t := by rw [← Finset.sum_mul, sum_compWeight]

/-- `J_1(t) ≥ log t` for `t > 0`. -/
theorem log_le_Jfield_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ Jfield 1 t := by
  have hcont : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => (by positivity : (0 : ℝ) < t + u ^ 2).ne'
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (intervalIntegrable_const (c := Real.log t)) (hcont.intervalIntegrable 0 1)
    (fun u _ => Real.log_le_log ht (le_add_of_nonneg_right (sq_nonneg u)))
  simpa [Jfield] using h

/-- `J_α(t) ≤ α log (t + α²)` for `t ≥ 0`, from (92) and `arctan x ≤ x`. -/
theorem Jfield_eAlpha_le {t : ℝ} (ht : 0 ≤ t) :
    Jfield eAlpha t ≤ eAlpha * Real.log (t + eAlpha ^ 2) := by
  rw [Jfield_eq eAlpha ht]
  linarith [sqrt_mul_arctan_div_le eAlpha_pos.le t]

/-- Past `2` (cf. (99)): `2 U_ρ(t) - V(t) ≤ (29/20) log t + 8 α³ / t - 2π √t` for `t ≥ 2`. -/
theorem two_mul_Ulog_sub_Vfield_le_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    2 * Ulog compMeasure t - Vfield t ≤
      29 / 20 * Real.log t + 8 * eAlpha ^ 3 / t - 2 * Real.pi * Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have hα := eAlpha_pos
  have hlog : Real.log (t + eAlpha ^ 2) ≤ Real.log t + eAlpha ^ 2 / t := by
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < (t + eAlpha ^ 2) / t)
    rw [Real.log_div (by positivity) ht0.ne'] at h1
    have h2 : (t + eAlpha ^ 2) / t - 1 = eAlpha ^ 2 / t := by field
    linarith
  have h8 : 8 * (eAlpha * Real.log (t + eAlpha ^ 2)) ≤
      3 / 5 * Real.log t + 8 * eAlpha ^ 3 / t := by
    calc 8 * (eAlpha * Real.log (t + eAlpha ^ 2))
        ≤ 8 * (eAlpha * (Real.log t + eAlpha ^ 2 / t)) := by gcongr
      _ = 3 / 5 * Real.log t + 8 * eAlpha ^ 3 / t := by rw [eAlpha_eq]; ring
  rw [Ulog_compMeasure ht0.le, Vfield]
  linarith [compPotential_le_log ht, log_le_Jfield_one ht0, Jfield_eAlpha_le ht0.le]

/-- Past `2`: `(29/20) log t + 8 α³ / t - 2π √t < -109/20` for `t ≥ 2`, from
`log t ≤ 2 (√t - 1)`, `√t ≥ 7/5` and `π > 3`. -/
theorem tail_bound_lt {t : ℝ} (ht : 2 ≤ t) :
    29 / 20 * Real.log t + 8 * eAlpha ^ 3 / t - 2 * Real.pi * Real.sqrt t < -109 / 20 := by
  have ht0 : 0 < t := by linarith
  have hs : 7 / 5 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht0)
    rw [Real.log_sqrt ht0.le] at h
    linarith
  have hfrac : 8 * eAlpha ^ 3 / t ≤ 27 / 16000 := by
    rw [div_le_iff₀ ht0, eAlpha_eq]
    norm_num
    linarith
  linarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg t)]

/-! ### Lemma 6.1, equation (94) -/

/-- Lemma 6.1, equation (94): the comparison measure `ρ` of Table 1 satisfies
`2 U_ρ(t) - V(t) ≤ M_0 = -109/20 = -5.45` for every `t ≥ 0`. -/
theorem two_mul_Ulog_compMeasure_sub_Vfield_le {t : ℝ} (ht : 0 ≤ t) :
    2 * Ulog compMeasure t - Vfield t ≤ -109 / 20 := by
  have key : ∀ l r, 0 ≤ l → l ≤ t → t ≤ r → potBound l r < -109 / 20 →
      2 * Ulog compMeasure t - Vfield t ≤ -109 / 20 := fun l r h0 hl hr hB =>
    ((two_mul_Ulog_sub_Vfield_le_potBound h0 hl hr).trans_lt hB).le
  have hqm := qMinus_pos.le
  have hqp := qPlus_pos.le
  have hq : qPlus ≤ 3 / 25 := by norm_num [qPlus]
  rcases le_or_gt t qMinus with h1 | h1
  · exact key 0 qMinus le_rfl ht h1 (potBound_lt_of_le_qMinus le_rfl hqm le_rfl)
  rcases le_or_gt t qPlus with h2 | h2
  · exact key qMinus qPlus hqm h1.le h2 potBound_qMinus_qPlus_lt
  rcases le_or_gt t (3 / 25) with h3 | h3
  · exact key qPlus (3 / 25) hqp h2.le h3
      (potBound_lt_of_cover le_rfl le_rfl hq le_rfl cover_qPlus)
  rcases le_or_gt t (1 / 4) with h4 | h4
  · exact key (3 / 25) (1 / 4) (by norm_num) h3.le h4
      (potBound_lt_of_cover hq le_rfl (by norm_num) le_rfl cover_3_25)
  rcases le_or_gt t (2 / 5) with h5 | h5
  · exact key (1 / 4) (2 / 5) (by norm_num) h4.le h5
      (potBound_lt_of_cover (hq.trans (by norm_num)) le_rfl (by norm_num) le_rfl cover_1_4)
  rcases le_or_gt t (3 / 5) with h6 | h6
  · exact key (2 / 5) (3 / 5) (by norm_num) h5.le h6
      (potBound_lt_of_cover (hq.trans (by norm_num)) le_rfl (by norm_num) le_rfl cover_2_5)
  rcases le_or_gt t (87 / 100) with h7 | h7
  · exact key (3 / 5) (87 / 100) (by norm_num) h6.le h7
      (potBound_lt_of_cover (hq.trans (by norm_num)) le_rfl (by norm_num) le_rfl cover_3_5)
  rcases le_or_gt t (207 / 160) with h8 | h8
  · exact key (87 / 100) (207 / 160) (by norm_num) h7.le h8
      (potBound_lt_of_cover (hq.trans (by norm_num)) le_rfl (by norm_num) le_rfl cover_87_100)
  rcases le_or_gt t 2 with h9 | h9
  · exact key (207 / 160) 2 (by norm_num) h8.le h9
      (potBound_lt_of_cover (hq.trans (by norm_num)) le_rfl (by norm_num) le_rfl cover_207_160)
  · exact (two_mul_Ulog_sub_Vfield_le_of_two_le h9.le).trans (tail_bound_lt h9.le).le

end ZetaSeven
