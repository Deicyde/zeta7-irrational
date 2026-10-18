import ZetaSeven.FunctionalMu

/-!
# Tau pullback identity (paper Section 3.1, Lemma 3.1, equations (22)-(28))

The Bernoulli functional `L(∑ a_k x^k) = ∑ a_k B_k` (22), the operator
`τ(P) = L(P⁽⁵⁾)/720` (23), the index `d(r)` (25), and the `ℚ`-linear
functional `τ_X` on rational functions with polynomial part and simple
integer poles, given on `1/(x - r)` by `H⁷_{d(r)} - X` (26).

As for `μ_X` (`ZetaSeven.muFunctional`), `τ_X` is evaluated on
partial-fraction data: `(P, d)` stands for the rational function
`P(x) + ∑_r d_r/(x - r)` (`tauRatFunc`). The `μ`-data `(p, c)` stands for
`R(t) = p(t) + ∑_j c_j/(t + j²)`, and `pullbackRatFunc p c` is `x⁷ R(-x²)`
in `RatFunc ℚ`. Lemma 3.1 (27) is `tau_pullback`: for every partial-fraction
representation `(P, d)` of `x⁷ R(-x²)`, `μ_X(R) = τ_X(P, d)`. Such a
representation exists (`tauRatFunc_pullbackData`) and is unique
(`tauRatFunc_inj`, from Mathlib's uniqueness of partial fractions), so this is
`μ_X(R) = τ_X(x⁷ R(-x²))`.

The proof follows the paper: monomials via (24), simple poles via the
division identity (28) and `κ₅ = 1/6`, `κ₃ = κ₁ = 0`, then linearity.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The functionals `L`, `τ` and `τ_X` -/

/-- Equation (22): the Bernoulli functional `L(∑ a_k x^k) = ∑ a_k B_k`. -/
noncomputable def bernoulliL (P : ℚ[X]) : ℚ :=
  P.sum fun k a => a * _root_.bernoulli k

/-- Equation (23): `τ(P) = L(P⁽⁵⁾)/720`. -/
noncomputable def tauPoly (P : ℚ[X]) : ℚ :=
  bernoulliL (derivative^[5] P) / 720

/-- Equation (25): `d(r) = r` for `r ≥ 0` and `d(r) = -r - 1` for `r < 0`. -/
def dIndex (r : ℤ) : ℕ :=
  if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- Equation (26): `τ_X(1/(x - r)) = H⁷_{d(r)} - X`, affine in `X`
(here `X` is the polynomial variable). -/
noncomputable def tauPole (r : ℤ) : ℚ[X] :=
  C (H7 (dIndex r)) - X

/-- The `ℚ`-linear functional `τ_X` on the partial-fraction data `(P, d)` of the
rational function `P(x) + ∑_r d_r/(x - r)`: `τ` on the polynomial part and (26)
on the simple integer poles, extended by linearity. -/
noncomputable def tauFunctional (P : ℚ[X]) (d : ℤ →₀ ℚ) : ℚ[X] :=
  C (tauPoly P) + d.sum fun r a => C a * tauPole r

/-- The rational function `P(x) + ∑_r d_r/(x - r)` with polynomial part `P` and
simple integer poles with coefficients `d`. -/
noncomputable def tauRatFunc (P : ℚ[X]) (d : ℤ →₀ ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) P
    + d.sum fun r a =>
        algebraMap ℚ[X] (RatFunc ℚ) (C a) / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ))

/-- `x⁷ R(-x²)` for the rational function `R(t) = p(t) + ∑_j c_j/(t + j²)` with
`μ`-data `(p, c)`: substitute `t = -x²` in each term and multiply by `x⁷`. -/
noncomputable def pullbackRatFunc (p : ℚ[X]) (c : ℕ →₀ ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) X ^ 7
    * (algebraMap ℚ[X] (RatFunc ℚ) (p.comp (-X ^ 2))
      + c.sum fun j a =>
          algebraMap ℚ[X] (RatFunc ℚ) (C a)
            / algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((j : ℚ) ^ 2)))

/-- Polynomial part of `x⁷ R(-x²)`, from the division identity (28):
`x⁷ p(-x²) + ∑_j c_j (-x⁵ - j² x³ - j⁴ x)`. -/
noncomputable def pullbackPoly (p : ℚ[X]) (c : ℕ →₀ ℚ) : ℚ[X] :=
  X ^ 7 * p.comp (-X ^ 2)
    + c.sum fun j a =>
        C (-a) * X ^ 5 + C (-(a * (j : ℚ) ^ 2)) * X ^ 3 + C (-(a * (j : ℚ) ^ 4)) * X ^ 1

/-- Pole part of `x⁷ R(-x²)`, from (28): coefficient `-c_j j⁶/2` at `x = j` and
at `x = -j`. -/
noncomputable def pullbackPoles (c : ℕ →₀ ℚ) : ℤ →₀ ℚ :=
  c.sum fun j a =>
    Finsupp.single (j : ℤ) (-(a * (j : ℚ) ^ 6 / 2))
      + Finsupp.single (-(j : ℤ)) (-(a * (j : ℚ) ^ 6 / 2))

/-! ## Linearity of `τ` and its values on monomials (24) -/

theorem bernoulliL_add (P Q : ℚ[X]) : bernoulliL (P + Q) = bernoulliL P + bernoulliL Q := by
  unfold bernoulliL
  exact Polynomial.sum_add_index P Q _ (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem bernoulliL_C_mul_X_pow (a : ℚ) (n : ℕ) :
    bernoulliL (C a * X ^ n) = a * _root_.bernoulli n := by
  unfold bernoulliL
  rw [C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index _ _ (by simp)]

theorem tauPoly_add (P Q : ℚ[X]) : tauPoly (P + Q) = tauPoly P + tauPoly Q := by
  unfold tauPoly
  rw [iterate_map_add, bernoulliL_add, add_div]

/-- `τ` as an additive map, for linearity arguments. -/
noncomputable def tauPolyHom : ℚ[X] →+ ℚ where
  toFun := tauPoly
  map_zero' := by simp [tauPoly, bernoulliL]
  map_add' := tauPoly_add

theorem tauPoly_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tauPoly (∑ i ∈ s, f i) = ∑ i ∈ s, tauPoly (f i) :=
  map_sum tauPolyHom f s

theorem tauPoly_finsuppSum (c : ℕ →₀ ℚ) (g : ℕ → ℚ → ℚ[X]) :
    tauPoly (c.sum g) = c.sum fun j a => tauPoly (g j a) :=
  map_finsuppSum tauPolyHom c g

/-- Equation (24) with a scalar: `τ(a x^n) = a n(n-1)(n-2)(n-3)(n-4) B_{n-5}/720`
(zero for `n < 5`, where the descending factorial vanishes). -/
theorem tauPoly_C_mul_X_pow (a : ℚ) (n : ℕ) :
    tauPoly (C a * X ^ n) = a * (n.descFactorial 5 : ℚ) * _root_.bernoulli (n - 5) / 720 := by
  unfold tauPoly
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul,
    bernoulliL_C_mul_X_pow]

theorem descFactorial_add_five (n : ℕ) :
    ((n + 5).descFactorial 5 : ℚ) = ((n : ℚ) + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) := by
  rw [Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ,
    Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.descFactorial_zero]
  push_cast
  ring

/-- Monomials (Lemma 3.1 proof): `τ(x⁷ (b (-x²)^e)) = b μ_X(t^e)`. -/
theorem tauPoly_monomial_pullback (b : ℚ) (e : ℕ) :
    tauPoly (X ^ 7 * (C b * (-X ^ 2) ^ e)) = b * muMonomial e := by
  have hpoly : (X ^ 7 * (C b * (-X ^ 2) ^ e) : ℚ[X])
      = C (b * (-1) ^ e) * X ^ (2 * e + 2 + 5) := by
    rw [neg_pow, C_mul, C_pow, C_neg, C_1]
    ring
  rw [hpoly, tauPoly_C_mul_X_pow, Nat.add_sub_cancel, descFactorial_add_five]
  unfold muMonomial
  push_cast
  ring

theorem tauPoly_pullback_poly (p : ℚ[X]) :
    tauPoly (X ^ 7 * p.comp (-X ^ 2)) = p.sum fun e a => a * muMonomial e := by
  rw [comp_eq_sum_left, Polynomial.sum_def, Finset.mul_sum, tauPoly_sum, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun e _ => tauPoly_monomial_pullback (p.coeff e) e

/-- The polynomial part of (28) for one pole: `τ(-x⁵ - j²x³ - j⁴x) = -κ₅ = -1/6`,
using `κ₅ = 1/6` and `κ₃ = κ₁ = 0`. -/
theorem tauPoly_pullback_pole_poly (j : ℕ) (a : ℚ) :
    tauPoly (C (-a) * X ^ 5 + C (-(a * (j : ℚ) ^ 2)) * X ^ 3 + C (-(a * (j : ℚ) ^ 4)) * X ^ 1)
      = -a / 6 := by
  have h5 : Nat.descFactorial 5 5 = 120 := rfl
  have h3 : Nat.descFactorial 3 5 = 0 := rfl
  have h1 : Nat.descFactorial 1 5 = 0 := rfl
  rw [tauPoly_add, tauPoly_add, tauPoly_C_mul_X_pow, tauPoly_C_mul_X_pow, tauPoly_C_mul_X_pow,
    h5, h3, h1, Nat.sub_self, _root_.bernoulli_zero]
  push_cast
  ring

/-! ## The pole values (25)-(26) -/

theorem dIndex_natCast (j : ℕ) : dIndex (j : ℤ) = j := by
  unfold dIndex
  split_ifs <;> omega

theorem dIndex_neg_succ (k : ℕ) : dIndex (-((k + 1 : ℕ) : ℤ)) = k := by
  unfold dIndex
  split_ifs <;> omega

theorem H7_succ (k : ℕ) : H7 (k + 1) = H7 k + 1 / ((k : ℚ) + 1) ^ 7 := by
  unfold H7
  rw [Finset.sum_range_succ]

/-- Simple poles (Lemma 3.1 proof): applying `τ_X` to the decomposition (28) of
`c_j x⁷/(j² - x²)` gives `c_j μ_X(1/(t + j²))`, using `H⁷_{j-1} = H⁷_j - j⁻⁷`. -/
theorem pullback_term_tau (j : ℕ) (a : ℚ) :
    C (tauPoly (C (-a) * X ^ 5 + C (-(a * (j : ℚ) ^ 2)) * X ^ 3 + C (-(a * (j : ℚ) ^ 4)) * X ^ 1))
      + (Finsupp.single (j : ℤ) (-(a * (j : ℚ) ^ 6 / 2))
          + Finsupp.single (-(j : ℤ)) (-(a * (j : ℚ) ^ 6 / 2))).sum
          (fun r b => C b * tauPole r)
      = C a * muPole j := by
  rw [Finsupp.sum_add_index' (by simp) (by simp [add_mul]), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp), tauPoly_pullback_pole_poly]
  apply Polynomial.funext
  intro x
  cases j with
  | zero =>
    simp only [tauPole, muPole, eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_pow,
      Nat.cast_zero, mul_zero, div_zero]
    ring
  | succ k =>
    simp only [tauPole, muPole, eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_pow]
    rw [dIndex_natCast, dIndex_neg_succ, H7_succ]
    push_cast
    field

/-! ## The pullback data represents `x⁷ R(-x²)` -/

/-- The division identity (28), times `c_j`, in `RatFunc ℚ`. -/
theorem pullback_term_ratFunc (j : ℕ) (a : ℚ) :
    algebraMap ℚ[X] (RatFunc ℚ)
        (C (-a) * X ^ 5 + C (-(a * (j : ℚ) ^ 2)) * X ^ 3 + C (-(a * (j : ℚ) ^ 4)) * X ^ 1)
      + (Finsupp.single (j : ℤ) (-(a * (j : ℚ) ^ 6 / 2))
          + Finsupp.single (-(j : ℤ)) (-(a * (j : ℚ) ^ 6 / 2))).sum
          (fun r b => algebraMap ℚ[X] (RatFunc ℚ) (C b)
            / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))
      = algebraMap ℚ[X] (RatFunc ℚ) X ^ 7
          * (algebraMap ℚ[X] (RatFunc ℚ) (C a)
            / algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + C ((j : ℚ) ^ 2))) := by
  have hq3 : (-X ^ 2 + C ((j : ℚ) ^ 2) : ℚ[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun q : ℚ[X] => q.coeff 2) h
    simp only [coeff_add, coeff_neg, coeff_X_pow, coeff_C, coeff_zero] at h2
    norm_num at h2
  have h1 := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero (((j : ℤ) : ℚ)))
  have h2 := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero (((-(j : ℤ) : ℤ) : ℚ)))
  have h3 := RatFunc.algebraMap_ne_zero hq3
  rw [Finsupp.sum_add_index' (by simp) (by simp [add_div]), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp)]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_div₀, map_natCast, map_ofNat,
    Int.cast_natCast, Int.cast_neg, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    sub_neg_eq_add] at h1 h2 h3 ⊢
  field

/-- The pullback data is a partial-fraction representation of `x⁷ R(-x²)`. -/
theorem tauRatFunc_pullbackData (p : ℚ[X]) (c : ℕ →₀ ℚ) :
    tauRatFunc (pullbackPoly p c) (pullbackPoles c) = pullbackRatFunc p c := by
  unfold tauRatFunc pullbackRatFunc pullbackPoly pullbackPoles
  rw [Finsupp.sum_sum_index (by simp) (by simp [add_div]), map_add, map_mul, map_pow,
    map_finsuppSum, mul_add, Finsupp.mul_sum, add_assoc, ← Finsupp.sum_add]
  congr 1
  exact Finsupp.sum_congr fun j _ => pullback_term_ratFunc j (c j)

/-- Partial-fraction representations with simple integer poles are unique, so
`τ_X` is well defined on rational functions. -/
theorem tauRatFunc_inj {P₁ P₂ : ℚ[X]} {d₁ d₂ : ℤ →₀ ℚ}
    (h : tauRatFunc P₁ d₁ = tauRatFunc P₂ d₂) : P₁ = P₂ ∧ d₁ = d₂ := by
  have hsum : ∀ d : ℤ →₀ ℚ, d.support ⊆ d₁.support ∪ d₂.support →
      (d.sum fun r a => algebraMap ℚ[X] (RatFunc ℚ) (C a)
        / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)))
        = ∑ r ∈ d₁.support ∪ d₂.support, algebraMap ℚ[X] (RatFunc ℚ) (C (d r))
            / algebraMap ℚ[X] (RatFunc ℚ) (X - C (r : ℚ)) := fun d hd =>
    Finsupp.sum_of_support_subset d hd _ (fun r _ => by simp)
  unfold tauRatFunc at h
  rw [hsum d₁ Finset.subset_union_left, hsum d₂ Finset.subset_union_right] at h
  obtain ⟨hP, hd⟩ := Polynomial.quo_add_sum_rem_div_unique (RatFunc ℚ)
    (g := fun r : ℤ => X - C (r : ℚ)) (r₁ := fun r => C (d₁ r)) (r₂ := fun r => C (d₂ r))
    (fun r _ => monic_X_sub_C _)
    (by
      intro r _ r' _ hrr'
      exact pairwise_coprime_X_sub_C (Int.cast_injective (α := ℚ)) hrr')
    (fun r _ => show (C (d₁ r)).degree < (X - C (r : ℚ)).degree by
      rw [degree_X_sub_C]
      exact degree_C_lt)
    (fun r _ => show (C (d₂ r)).degree < (X - C (r : ℚ)).degree by
      rw [degree_X_sub_C]
      exact degree_C_lt)
    h
  refine ⟨hP, Finsupp.ext fun r => ?_⟩
  by_cases hr : r ∈ d₁.support ∪ d₂.support
  · exact C_injective (hd r hr)
  · simp only [Finset.mem_union, not_or, Finsupp.notMem_support_iff] at hr
    rw [hr.1, hr.2]

theorem tauFunctional_pullbackData (p : ℚ[X]) (c : ℕ →₀ ℚ) :
    tauFunctional (pullbackPoly p c) (pullbackPoles c) = muFunctional p c := by
  unfold tauFunctional pullbackPoly pullbackPoles muFunctional
  rw [Finsupp.sum_sum_index (by simp) (by simp [add_mul]), tauPoly_add, tauPoly_pullback_poly,
    tauPoly_finsuppSum, map_add, add_assoc]
  congr 1
  · simp only [Polynomial.sum_def, map_sum, C_mul]
  · rw [map_finsuppSum, ← Finsupp.sum_add]
    exact Finsupp.sum_congr fun j _ => pullback_term_tau j (c j)

/-! ## Lemma 3.1 -/

/-- **Lemma 3.1** (pullback identity, (27)). Let `(p, c)` be the `μ`-data of the
rational function `R(t) = p(t) + ∑_j c_j/(t + j²)`. For every partial-fraction
representation `(P, d)` of `x⁷ R(-x²)` (polynomial part plus simple integer
poles), `μ_X(R) = τ_X(x⁷ R(-x²))`. -/
theorem tau_pullback (p : ℚ[X]) (c : ℕ →₀ ℚ) (P : ℚ[X]) (d : ℤ →₀ ℚ)
    (h : tauRatFunc P d = pullbackRatFunc p c) :
    muFunctional p c = tauFunctional P d := by
  obtain ⟨rfl, rfl⟩ := tauRatFunc_inj (h.trans (tauRatFunc_pullbackData p c).symm)
  exact (tauFunctional_pullbackData p c).symm

end ZetaSeven
