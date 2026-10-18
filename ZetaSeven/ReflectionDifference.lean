import ZetaSeven.TauPullback

/-!
# Reflection and difference identities (paper Section 3.2, Lemmas 3.2-3.3, equations (29)-(31))

Two identities for the functional `τ_X` of `ZetaSeven.TauPullback`, used later in the
distribution formula.

* **Lemma 3.2** (reflection identity (29)): `τ_X(g(-1-x)) = -τ_X(g(x))`. For polynomials this is
  `tauPoly_reflection`; for rational functions with polynomial part and simple integer poles it
  is `tau_reflection`. Under `x ↦ -1-x` a pole at `r` moves to `-1-r`, and `d(-1-r) = d(r)`.
* **Lemma 3.3** (difference identity (30)): `τ_X(g(x+1) - g(x)) = g⁽⁶⁾(0)/720`. For polynomials
  this is `tauPoly_difference`; for rational functions with polynomial part and simple integer
  poles it is `tau_difference`, where `g⁽⁶⁾(0)` is read off the Laurent expansion of `g` at `0`
  (Mathlib's `LaurentSeries.derivative`). A pole `1/x` contributes zero to both sides, so the
  rational statement needs no regularity hypothesis at `0`.
* Equation (31): `L((x+1)^j - x^j) = [j = 1]` (`bernoulliL_X_add_one_pow_sub`), from the
  Bernoulli-polynomial endpoint values `B_n(1) = B_n` for `n ≠ 1` and `B_1(1) = 1/2`
  (`bernoulli_eval_one_eq`, `bernoulliL_X_add_one_pow_eq_eval_one`), and its consequence
  `L(h(x+1) - h(x)) = h'(0)` (`bernoulliL_comp_X_add_one_sub`).

As in `ZetaSeven.TauPullback`, `τ_X` is evaluated on partial-fraction data `(P, d)` standing for
`P(x) + ∑_r d_r/(x - r)` (`tauRatFunc`). The substitutions `g(x) ↦ g(-1-x)` and `g(x) ↦ g(x+1)`
act on `RatFunc ℚ` as ring homomorphisms (`ratFuncReflect`, `ratFuncShift`), and on the data as
`(P(-1-x), reflectPoles d)` and `(P(x+1), shiftPoles d)`.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## Linearity of `L` -/

/-- The Bernoulli functional `L` (22) as a `ℚ`-linear map. -/
noncomputable def bernoulliLin : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun k => LinearMap.mulRight ℚ (_root_.bernoulli k)

theorem bernoulliLin_apply (P : ℚ[X]) : bernoulliLin P = bernoulliL P := rfl

theorem bernoulliL_neg (P : ℚ[X]) : bernoulliL (-P) = -bernoulliL P := by
  simp only [← bernoulliLin_apply, map_neg]

theorem bernoulliL_sub (P Q : ℚ[X]) : bernoulliL (P - Q) = bernoulliL P - bernoulliL Q := by
  simp only [← bernoulliLin_apply, map_sub]

theorem bernoulliL_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    bernoulliL (∑ i ∈ s, f i) = ∑ i ∈ s, bernoulliL (f i) := by
  simp only [← bernoulliLin_apply, map_sum]

theorem bernoulliL_C_mul (a : ℚ) (P : ℚ[X]) : bernoulliL (C a * P) = a * bernoulliL P := by
  simp only [← bernoulliLin_apply, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

theorem bernoulliL_X_pow (n : ℕ) : bernoulliL (X ^ n) = _root_.bernoulli n := by
  simpa using bernoulliL_C_mul_X_pow 1 n

theorem bernoulliL_X_pow_mul_natCast (m c : ℕ) :
    bernoulliL (X ^ m * (c : ℚ[X])) = (c : ℚ) * _root_.bernoulli m := by
  rw [← C_eq_natCast, mul_comm, bernoulliL_C_mul_X_pow]

/-! ## Bernoulli-polynomial endpoint values and equation (31) -/

/-- `L((x+1)^n) = ∑_i (n choose i) B_i = B_n + [n = 1]`. -/
theorem bernoulliL_X_add_one_pow (n : ℕ) :
    bernoulliL ((X + 1) ^ n) = _root_.bernoulli n + if n = 1 then 1 else 0 := by
  rw [add_pow, bernoulliL_sum]
  simp only [one_pow, mul_one, bernoulliL_X_pow_mul_natCast]
  rw [Finset.sum_range_succ, _root_.sum_bernoulli, Nat.choose_self, Nat.cast_one, one_mul,
    add_comm]

/-- Bernoulli-polynomial endpoint values over `ℚ`: `B_n(1) = B_n` for `n ≠ 1`, and
`B_1(1) = B_1 + 1 = 1/2`. -/
theorem bernoulli_eval_one_eq (n : ℕ) :
    (Polynomial.bernoulli n).eval 1 = _root_.bernoulli n + if n = 1 then 1 else 0 := by
  rw [Polynomial.bernoulli_eval_one]
  rcases eq_or_ne n 1 with rfl | hn
  · rw [bernoulli'_one, _root_.bernoulli_one, ite_eq_left rfl]
    norm_num
  · rw [ite_eq_right hn, add_zero, _root_.bernoulli_eq_bernoulli'_of_ne_one hn]

/-- The identity `L((1+x)^n) = B_n(1)` of the proof of Lemma 3.2. -/
theorem bernoulliL_X_add_one_pow_eq_eval_one (n : ℕ) :
    bernoulliL ((X + 1) ^ n) = (Polynomial.bernoulli n).eval 1 := by
  rw [bernoulliL_X_add_one_pow, bernoulli_eval_one_eq]

/-- Equation (31): `L((x+1)^j - x^j) = 1` for `j = 1` and `0` otherwise. -/
theorem bernoulliL_X_add_one_pow_sub (j : ℕ) :
    bernoulliL ((X + 1) ^ j - X ^ j) = if j = 1 then 1 else 0 := by
  rw [bernoulliL_sub, bernoulliL_X_add_one_pow, bernoulliL_X_pow]
  ring

/-- Proof of Lemma 3.3: `L(h(x+1) - h(x)) = h₁ = h'(0)`, the coefficient of `x` in `h`. -/
theorem bernoulliL_comp_X_add_one_sub (h : ℚ[X]) :
    bernoulliL (h.comp (X + 1) - h) = h.coeff 1 := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, show p.comp (X + 1) + q.comp (X + 1) - (p + q)
        = (p.comp (X + 1) - p) + (q.comp (X + 1) - q) by ring, bernoulliL_add, hp, hq, coeff_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← mul_sub, bernoulliL_C_mul,
      bernoulliL_X_add_one_pow_sub, coeff_C_mul_X_pow]
    split_ifs <;> first | omega | simp

/-- `L((-1-x)^n) = (-1)^n B_n(1) = B_n` (for odd `n ≥ 3` both sides vanish). -/
theorem bernoulliL_neg_one_sub_X_pow (n : ℕ) :
    bernoulliL ((-1 - X) ^ n) = _root_.bernoulli n := by
  have h1 : (-1 - X : ℚ[X]) = C (-1) * (X + 1) := by
    rw [C_neg, C_1]
    ring
  rw [h1, mul_pow, ← C_pow, bernoulliL_C_mul, bernoulliL_X_add_one_pow]
  rcases Nat.even_or_odd n with hn | hn
  · have hn1 : n ≠ 1 := by
      rintro rfl
      exact Nat.not_even_one hn
    rw [hn.neg_one_pow, ite_eq_right hn1]
    ring
  · rw [hn.neg_one_pow]
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ite_eq_left rfl, _root_.bernoulli_one]
      norm_num
    · have hlt : 1 < n := by
        have := hn.pos
        omega
      rw [ite_eq_right hn1, _root_.bernoulli_eq_zero_of_odd hn hlt]
      ring

/-- `L` is invariant under `x ↦ -1-x`. -/
theorem bernoulliL_comp_neg_one_sub_X (Q : ℚ[X]) :
    bernoulliL (Q.comp (-1 - X)) = bernoulliL Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, bernoulliL_add, bernoulliL_add, hp, hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, bernoulliL_C_mul_X_pow, mul_comp, C_comp, X_pow_comp,
      bernoulliL_C_mul, bernoulliL_neg_one_sub_X_pow]

/-! ## The identities on polynomials -/

theorem iterate_derivative_comp_neg_one_sub_X (p : ℚ[X]) (k : ℕ) :
    derivative^[k] (p.comp (-1 - X)) = (-1) ^ k * (derivative^[k] p).comp (-1 - X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

theorem iterate_derivative_comp_X_add_one (p : ℚ[X]) (k : ℕ) :
    derivative^[k] (p.comp (X + 1)) = (derivative^[k] p).comp (X + 1) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp]

/-- **Lemma 3.2** for polynomials (29): `τ(g(-1-x)) = -τ(g(x))`. -/
theorem tauPoly_reflection (g : ℚ[X]) : tauPoly (g.comp (-1 - X)) = -tauPoly g := by
  unfold tauPoly
  rw [iterate_derivative_comp_neg_one_sub_X, show ((-1 : ℚ[X]) ^ 5) = -1 by norm_num, neg_one_mul,
    bernoulliL_neg, bernoulliL_comp_neg_one_sub_X, neg_div]

/-- `τ(g(x+1) - g(x))` is the coefficient of `x⁶` in `g`. -/
theorem tauPoly_comp_X_add_one_sub (g : ℚ[X]) : tauPoly (g.comp (X + 1) - g) = g.coeff 6 := by
  unfold tauPoly
  rw [iterate_derivative_sub, iterate_derivative_comp_X_add_one, bernoulliL_comp_X_add_one_sub,
    coeff_iterate_derivative, show Nat.descFactorial (1 + 5) 5 = 720 from rfl, nsmul_eq_mul,
    show (1 + 5 : ℕ) = 6 from rfl]
  push_cast
  ring

/-- **Lemma 3.3** for polynomials (30): `τ(g(x+1) - g(x)) = g⁽⁶⁾(0)/720`. -/
theorem tauPoly_difference (g : ℚ[X]) :
    tauPoly (g.comp (X + 1) - g) = (derivative^[6] g).eval 0 / 720 := by
  rw [tauPoly_comp_X_add_one_sub, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative,
    show Nat.descFactorial (0 + 6) 6 = 720 from rfl, nsmul_eq_mul, show (0 + 6 : ℕ) = 6 from rfl]
  push_cast
  ring

/-! ## The pole values -/

theorem dIndex_neg_one_sub (r : ℤ) : dIndex (-1 - r) = dIndex r := by
  unfold dIndex
  split_ifs <;> omega

theorem tauPole_neg_one_sub (r : ℤ) : tauPole (-1 - r) = tauPole r := by
  unfold tauPole
  rw [dIndex_neg_one_sub]

/-- Proof of Lemma 3.3 for a pole: `H⁷_{d(r-1)} - H⁷_{d(r)} = -r⁻⁷` (both sides are `0` for
`r = 0`, with Lean's `1/0 = 0`). -/
theorem H7_dIndex_sub_one_sub (r : ℤ) :
    H7 (dIndex (r - 1)) - H7 (dIndex r) = -(1 / (r : ℚ) ^ 7) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have h1 : dIndex (r - 1) = (-r - 1).toNat + 1 := by
      unfold dIndex
      split_ifs <;> omega
    have h2 : dIndex r = (-r - 1).toNat := by
      unfold dIndex
      split_ifs <;> omega
    have h3 : (((-r - 1).toNat : ℕ) : ℚ) + 1 = -(r : ℚ) := by
      have h4 : (((-r - 1).toNat : ℕ) : ℤ) + 1 = -r := by omega
      exact_mod_cast h4
    rw [h1, h2, H7_succ, h3]
    ring
  · have h1 : dIndex (0 - 1) = 0 := by
      unfold dIndex
      split_ifs <;> omega
    have h2 : dIndex 0 = 0 := by
      unfold dIndex
      split_ifs <;> omega
    rw [h1, h2, sub_self]
    simp
  · have h1 : dIndex (r - 1) = (r - 1).toNat := by
      unfold dIndex
      split_ifs <;> omega
    have h2 : dIndex r = (r - 1).toNat + 1 := by
      unfold dIndex
      split_ifs <;> omega
    have h3 : (((r - 1).toNat : ℕ) : ℚ) + 1 = (r : ℚ) := by
      have h4 : (((r - 1).toNat : ℕ) : ℤ) + 1 = r := by omega
      exact_mod_cast h4
    rw [h1, h2, H7_succ, h3]
    ring

theorem tauPole_sub_one_sub (r : ℤ) : tauPole (r - 1) - tauPole r = C (-(1 / (r : ℚ) ^ 7)) := by
  rw [← H7_dIndex_sub_one_sub r, C_sub]
  unfold tauPole
  ring

/-! ## The identities on partial-fraction data -/

/-- Pole data of `g(-1-x)`: the term `d_r/(x - r)` of `g` becomes `-d_r/(x - (-1-r))`. -/
noncomputable def reflectPoles (d : ℤ →₀ ℚ) : ℤ →₀ ℚ :=
  d.sum fun r a => Finsupp.single (-1 - r) (-a)

/-- Pole data of `g(x+1)`: the term `d_r/(x - r)` of `g` becomes `d_r/(x - (r-1))`. -/
noncomputable def shiftPoles (d : ℤ →₀ ℚ) : ℤ →₀ ℚ :=
  d.sum fun r a => Finsupp.single (r - 1) a

/-- **Lemma 3.2** on partial-fraction data: `τ_X(P(-1-x), reflectPoles d) = -τ_X(P, d)`. -/
theorem tauFunctional_reflect (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    tauFunctional (P.comp (-1 - X)) (reflectPoles d) = -tauFunctional P d := by
  have hterm : ∀ r a, (Finsupp.single (-1 - r) (-a)).sum (fun s b => C b * tauPole s)
      = -(C a * tauPole r) := by
    intro r a
    rw [Finsupp.sum_single_index (by simp), tauPole_neg_one_sub, C_neg, neg_mul]
  unfold tauFunctional reflectPoles
  rw [tauPoly_reflection, Finsupp.sum_sum_index (by simp) (by simp [add_mul])]
  simp only [hterm]
  simp only [Finsupp.sum, Finset.sum_neg_distrib, C_neg, neg_add]

/-- **Lemma 3.3** on partial-fraction data:
`τ_X(P(x+1) - P(x), shiftPoles d - d) = P₆ + ∑_r d_r · (-r⁻⁷)`. -/
theorem tauFunctional_difference (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    tauFunctional (P.comp (X + 1) - P) (shiftPoles d - d)
      = C (P.coeff 6 + d.sum fun r a => -(a / (r : ℚ) ^ 7)) := by
  unfold tauFunctional shiftPoles
  rw [tauPoly_comp_X_add_one_sub, Finsupp.sum_sub_index (by intros; simp [sub_mul]),
    Finsupp.sum_sum_index (by simp) (by simp [add_mul]), map_add, map_finsuppSum,
    ← Finsupp.sum_sub]
  congr 1
  refine Finsupp.sum_congr fun r _ => ?_
  rw [Finsupp.sum_single_index (by simp), ← mul_sub, tauPole_sub_one_sub, ← C_mul]
  congr 1
  ring

theorem tauRatFunc_sub (P₁ P₂ : ℚ[X]) (d₁ d₂ : ℤ →₀ ℚ) :
    tauRatFunc (P₁ - P₂) (d₁ - d₂) = tauRatFunc P₁ d₁ - tauRatFunc P₂ d₂ := by
  unfold tauRatFunc
  rw [map_sub, Finsupp.sum_sub_index (by intros; simp [sub_div])]
  ring

/-! ## Substitution in rational functions -/

theorem neg_one_sub_X_comp_self : (-1 - X : ℚ[X]).comp (-1 - X) = X := by
  rw [sub_comp, neg_comp, one_comp, X_comp]
  ring

theorem X_add_one_comp_X_sub_one : (X + 1 : ℚ[X]).comp (X - 1) = X := by
  rw [add_comp, X_comp, one_comp]
  ring

/-- Composition with a polynomial `q` that has a right compositional inverse sends nonzero
polynomials to nonzero rational functions, so `q` can be substituted into rational functions. -/
theorem nonZeroDivisors_le_comap_comp {q q' : ℚ[X]} (h : q.comp q' = X) :
    nonZeroDivisors ℚ[X] ≤
      (nonZeroDivisors (RatFunc ℚ)).comap ((algebraMap ℚ[X] (RatFunc ℚ)).comp (compRingHom q)) := by
  intro p hp
  rw [Submonoid.mem_comap, RingHom.comp_apply, coe_compRingHom_apply,
    mem_nonZeroDivisors_iff_ne_zero]
  refine RatFunc.algebraMap_ne_zero fun hpq => nonZeroDivisors.ne_zero hp ?_
  calc p = p.comp (q.comp q') := by rw [h, comp_X]
    _ = (p.comp q).comp q' := (comp_assoc p q q').symm
    _ = 0 := by rw [hpq, zero_comp]

/-- The substitution `g(x) ↦ g(-1-x)` on rational functions. -/
noncomputable def ratFuncReflect : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom ((algebraMap ℚ[X] (RatFunc ℚ)).comp (compRingHom (-1 - X)))
    (nonZeroDivisors_le_comap_comp neg_one_sub_X_comp_self)

/-- The substitution `g(x) ↦ g(x+1)` on rational functions. -/
noncomputable def ratFuncShift : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom ((algebraMap ℚ[X] (RatFunc ℚ)).comp (compRingHom (X + 1)))
    (nonZeroDivisors_le_comap_comp X_add_one_comp_X_sub_one)

theorem ratFuncReflect_algebraMap (p : ℚ[X]) :
    ratFuncReflect (algebraMap ℚ[X] (RatFunc ℚ) p)
      = algebraMap ℚ[X] (RatFunc ℚ) (p.comp (-1 - X)) := by
  unfold ratFuncReflect
  rw [RatFunc.liftRingHom_algebraMap, RingHom.comp_apply, coe_compRingHom_apply]

theorem ratFuncShift_algebraMap (p : ℚ[X]) :
    ratFuncShift (algebraMap ℚ[X] (RatFunc ℚ) p) = algebraMap ℚ[X] (RatFunc ℚ) (p.comp (X + 1)) := by
  unfold ratFuncShift
  rw [RatFunc.liftRingHom_algebraMap, RingHom.comp_apply, coe_compRingHom_apply]

/-- `(P(-1-x), reflectPoles d)` is a partial-fraction representation of `g(-1-x)`. -/
theorem ratFuncReflect_tauRatFunc (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    ratFuncReflect (tauRatFunc P d) = tauRatFunc (P.comp (-1 - X)) (reflectPoles d) := by
  unfold tauRatFunc reflectPoles
  rw [map_add, ratFuncReflect_algebraMap, map_finsuppSum,
    Finsupp.sum_sum_index (by simp) (by simp [add_div])]
  congr 1
  refine Finsupp.sum_congr fun r _ => ?_
  have hcomp : (X - C (r : ℚ)).comp (-1 - X) = -(X - C ((-1 - r : ℤ) : ℚ)) := by
    simp only [sub_comp, X_comp, C_comp, Int.cast_sub, Int.cast_neg, Int.cast_one, map_sub,
      map_neg, map_one]
    ring
  rw [Finsupp.sum_single_index (by simp), map_div₀, ratFuncReflect_algebraMap,
    ratFuncReflect_algebraMap, C_comp, hcomp]
  simp only [map_neg, div_neg, neg_div]

/-- `(P(x+1), shiftPoles d)` is a partial-fraction representation of `g(x+1)`. -/
theorem ratFuncShift_tauRatFunc (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    ratFuncShift (tauRatFunc P d) = tauRatFunc (P.comp (X + 1)) (shiftPoles d) := by
  unfold tauRatFunc shiftPoles
  rw [map_add, ratFuncShift_algebraMap, map_finsuppSum,
    Finsupp.sum_sum_index (by simp) (by simp [add_div])]
  congr 1
  refine Finsupp.sum_congr fun r _ => ?_
  have hcomp : (X - C (r : ℚ)).comp (X + 1) = X - C ((r - 1 : ℤ) : ℚ) := by
    simp only [sub_comp, X_comp, C_comp, Int.cast_sub, Int.cast_one, map_sub, map_one]
    ring
  rw [Finsupp.sum_single_index (by simp), map_div₀, ratFuncShift_algebraMap,
    ratFuncShift_algebraMap, C_comp, hcomp]

/-! ## Laurent expansion at `0`

The embedding `RatFunc ℚ → LaurentSeries ℚ` (expansion at `0`) is Mathlib's scoped instance
`RatFunc.liftAlgebra`, the one behind the coercion `RatFunc.coeToLaurentSeries`. -/

section Laurent

open scoped RatFunc

theorem laurent_algebraMap (p : ℚ[X]) :
    algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (algebraMap ℚ[X] (RatFunc ℚ) p)
      = HahnSeries.ofPowerSeries ℤ ℚ (p : PowerSeries ℚ) :=
  (RatFunc.coe_coe p).symm

theorem laurent_algebraMap_coeff_six (p : ℚ[X]) :
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (algebraMap ℚ[X] (RatFunc ℚ) p)).coeff 6
      = p.coeff 6 := by
  rw [laurent_algebraMap, show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num,
    HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]

/-- The coefficient of `x⁶` in the Laurent expansion at `0` of `a/(x - r)` is `-a/r⁷` (and `0`
for `r = 0`, matching Lean's `a/0 = 0`). -/
theorem laurent_pole_coeff_six (a : ℚ) (r : ℤ) :
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
        (algebraMap ℚ[X] (RatFunc ℚ) (C a) / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))).coeff 6
      = -(a / (r : ℚ) ^ 7) := by
  have hne : algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
      (algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ))) ≠ 0 :=
    (_root_.map_ne_zero _).2 (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _))
  rcases eq_or_ne (r : ℚ) 0 with hr | hr
  · have hS : algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
        (algebraMap ℚ[X] (RatFunc ℚ) (C a) / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))
        = HahnSeries.single (-1 : ℤ) a := by
      rw [map_div₀, div_eq_iff hne, laurent_algebraMap, laurent_algebraMap, hr, map_zero, sub_zero,
        Polynomial.coe_C, Polynomial.coe_X, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X,
        HahnSeries.single_mul_single, mul_one]
      simp
    rw [hS, HahnSeries.coeff_single_of_ne (show (6 : ℤ) ≠ -1 by norm_num), hr]
    simp
  · have hS : algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
        (algebraMap ℚ[X] (RatFunc ℚ) (C a) / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))
        = HahnSeries.ofPowerSeries ℤ ℚ
            (-(PowerSeries.C a) * PowerSeries.invUnitsSub (Units.mk0 (r : ℚ) hr)) := by
      rw [map_div₀, div_eq_iff hne, laurent_algebraMap, laurent_algebraMap, ← map_mul]
      congr 1
      have h1 := PowerSeries.invUnitsSub_mul_sub (Units.mk0 (r : ℚ) hr)
      rw [Units.val_mk0] at h1
      simp only [Polynomial.coe_C, Polynomial.coe_sub, Polynomial.coe_X]
      linear_combination (-(PowerSeries.C a)) * h1
    rw [hS, show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, HahnSeries.ofPowerSeries_apply_coeff, neg_mul,
      map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_invUnitsSub, divp_eq_div,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    ring

/-- The coefficient of `x⁶` in the Laurent expansion at `0` of `P(x) + ∑_r d_r/(x - r)`. -/
theorem laurent_tauRatFunc_coeff_six (P : ℚ[X]) (d : ℤ →₀ ℚ) :
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (tauRatFunc P d)).coeff 6
      = P.coeff 6 + d.sum fun r a => -(a / (r : ℚ) ^ 7) := by
  unfold tauRatFunc
  rw [map_add, HahnSeries.coeff_add, laurent_algebraMap_coeff_six, map_finsuppSum]
  simp only [Finsupp.sum, HahnSeries.coeff_sum]
  congr 1
  exact Finset.sum_congr rfl fun r _ => laurent_pole_coeff_six (d r) r

/-- For a Laurent series `f`, the constant coefficient of `f⁽⁶⁾` divided by `720 = 6!` is the
coefficient of `x⁶`; for `f` regular at `0` this is `f⁽⁶⁾(0)/720`. -/
theorem laurent_iterate_derivative_six_coeff_zero (f : LaurentSeries ℚ) :
    ((LaurentSeries.derivative ℚ)^[6] f).coeff 0 / 720 = f.coeff 6 := by
  rw [LaurentSeries.derivative_iterate_coeff, zero_add,
    Polynomial.descPochhammer_smeval_eq_descFactorial, show Nat.descFactorial 6 6 = 720 from rfl,
    zsmul_eq_mul]
  push_cast
  ring

end Laurent

/-! ## Lemmas 3.2 and 3.3 for rational functions -/

/-- **Lemma 3.2** (reflection identity (29)) for rational functions with polynomial part and simple
integer poles: if `(P, d)` represents `g` and `(P', d')` represents `g(-1-x)`, then
`τ_X(g(-1-x)) = -τ_X(g(x))`. -/
theorem tau_reflection (g : RatFunc ℚ) (P : ℚ[X]) (d : ℤ →₀ ℚ) (P' : ℚ[X]) (d' : ℤ →₀ ℚ)
    (hg : tauRatFunc P d = g) (h : tauRatFunc P' d' = ratFuncReflect g) :
    tauFunctional P' d' = -tauFunctional P d := by
  subst hg
  rw [ratFuncReflect_tauRatFunc] at h
  obtain ⟨rfl, rfl⟩ := tauRatFunc_inj h
  exact tauFunctional_reflect P d

open scoped RatFunc in
/-- **Lemma 3.3** (difference identity (30)) for rational functions with polynomial part and
simple integer poles: if `(P, d)` represents `g` and `(P', d')` represents `g(x+1) - g(x)`, then
`τ_X(g(x+1) - g(x)) = g⁽⁶⁾(0)/720`, with `g⁽⁶⁾(0)` the constant coefficient of the sixth
derivative of the Laurent expansion of `g` at `0`. -/
theorem tau_difference (g : RatFunc ℚ) (P : ℚ[X]) (d : ℤ →₀ ℚ) (P' : ℚ[X]) (d' : ℤ →₀ ℚ)
    (hg : tauRatFunc P d = g) (h : tauRatFunc P' d' = ratFuncShift g - g) :
    tauFunctional P' d'
      = C (((LaurentSeries.derivative ℚ)^[6]
          (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) g)).coeff 0 / 720) := by
  subst hg
  rw [ratFuncShift_tauRatFunc, ← tauRatFunc_sub] at h
  obtain ⟨rfl, rfl⟩ := tauRatFunc_inj h
  rw [tauFunctional_difference, laurent_iterate_derivative_six_coeff_zero,
    laurent_tauRatFunc_coeff_six]

end ZetaSeven
