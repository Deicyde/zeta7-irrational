import ZetaSeven.OuterClassRows
import ZetaSeven.OuterModifiedFunctional
import ZetaSeven.OuterMomentIntegrality
import ZetaSeven.PairedPoleCongruence

/-!
# Outer entry valuations (paper Section 4.2, equation (56), proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2, proof of Proposition 4.6: "Cross-class
entries of `A` are integral; within a class, if either row index is at least `ℓ - 2`, the poles
with `j > p` cancel, and the two remaining pole values at `a` and `p - a` are integral and
congruent modulo `p`. For `i, j < ℓ - 2`, the residue part has valuation at least
`i + j + 8δ - ℓ - 6`." The paper defers the weighted entry bound to its `ζ(5)` predecessor; the
statement below is reconstructed by this project.

Let `p` be a prime satisfying the outer-range hypothesis (52) (`ZetaSeven.OuterRange`). For two
outer class rows `r`, `s` (`ZetaSeven.outerRow`, indexed by the outer weight family
`ZetaSeven.outerIdx`) put `A'_{rs} = μ_0(r(t) s(t) D_N(t)⁷ / D_tail(t))` (`outerAprime`), where
`μ_0` is the modified functional (`ZetaSeven.muZeroFunctional`) applied to the partial-fraction
data of the rational function over `D_tail` (`muZeroTail`), a polynomial of degree at most one
in `X` (`outerAprime_natDegree_le`). Then every entry satisfies
`v^G_p(A'_{rs}) ≥ w_r + w_s` for the weights `w` of the outer weight family
(`outer_entry_valuations`); `outer_entry_valuations_dbl` is the same bound with the doubled
integer weights `ZetaSeven.outerFamWeightDbl`, the form `ZetaSeven.gauss_rank_lemma` takes.

As in `ZetaSeven.gauss_rank_lemma`, the Gauss valuation is stated coefficientwise with
`padicValRat`: `v^G_p(P) ≥ b` is `∀ k, b ≤ padicValRat p (P.coeff k)`. Every weight is at most
`0` (`ZetaSeven.outerFamWeight_nonpos`), so the zero coefficients, where `padicValRat` is `0`
and the paper's valuation is `+∞`, impose nothing, and the statement is exactly the paper's.

The proof follows the cases of the article. The rows of different classes have a product
divisible by `D_tail`; within a class `c ≥ 1` the product has the form `R Q` with
`D_tail = R T_S`, `T_S = ∏_{b ∈ S} (t + b²)`, and then `muZeroTail_eq` writes the entry as
`μ_0` of a `p`-integral polynomial plus `∑_{b ∈ S} ρ_b π_b`, with the residues
`ρ_b = Q(-b²)/T_S'(-b²)` (`ZetaSeven.poleResidue`) and the pole values
`π_b = μ_X(1/(t + b²))` (`ZetaSeven.muPole`). Valuations of possibly zero rationals are handled
with `OuterEntry.vGe p k x`, which says `p^{-k} x` is `p`-integral.

The four cases: cross-class entries are `p`-integral (`OuterEntry.muZeroTail_mem_cross`); within
a class `c ≥ 1`, an index at least `ℓ - 2` gives a `p`-integral entry
(`OuterEntry.muZeroTail_mem_high`, through `ZetaSeven.paired_residues`); two indices below `ℓ - 2`
give valuation at least `min(0, i + j + 8δ - ℓ - 6)` (`OuterEntry.muZeroTail_coeff_ge_low`); two
zero-class rows give valuation at least `min(0, 2(i + j) - 2⌊K/p⌋ + 1)`
(`OuterEntry.muZeroTail_coeff_ge_zero`). Under (52) the class `S_c` has `ℓ_K(c) - δ_c` elements
(`OuterEntry.card_outerClassSet_add`), and `μ_0` is `p`-integral on `p`-integral polynomials
(`OuterEntry.muZeroMonomial_mem_pInt`, `OuterEntry.muZeroFunctional_mem_pIntPoly`).
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The modified Gram matrix in the outer class basis -/

/-- The residue `F(-a²)/D_tail'(-a²)` of `F/D_tail` at `t = -a²`. For `F = D_N⁷ t^{i+j}` it is
`ZetaSeven.resCoeff`. -/
noncomputable def outerTailRes (n : ℕ) (F : ℚ[X]) (a : ℕ) : ℚ :=
  F.eval (-(a : ℚ) ^ 2) / (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)

/-- The pole coefficients of `F/D_tail`, supported on `N < a ≤ K`. For `F = D_N⁷ t^{i+j}` they
are `ZetaSeven.poleCoeffs`. -/
noncomputable def outerTailPoles (n : ℕ) (F : ℚ[X]) : ℕ →₀ ℚ :=
  ∑ a ∈ Icc (N n + 1) (K n), Finsupp.single a (outerTailRes n F a)

/-- `μ_0(F/D_tail)`: the modified functional `μ_0` (`ZetaSeven.muZeroFunctional`) applied to the
partial-fraction data of `F/D_tail`, its polynomial part (the quotient of `F` by the monic
`D_tail`) and its residues at the simple poles `-a²`, `N < a ≤ K`. For `F = D_N⁷ t^{i+j}` it is
the entry `A_{ij}` of (53) (`outerAentry_eq_muZeroTail`). -/
noncomputable def muZeroTail (p n : ℕ) (F : ℚ[X]) : ℚ[X] :=
  muZeroFunctional p (F.div (Dtail n)) (outerTailPoles n F)

/-- The entry `A_{ij} = μ_0(D_N⁸ t^{i+j}/D_K)` of (53) is `μ_0(D_N⁷ t^{i+j}/D_tail)`. -/
theorem outerAentry_eq_muZeroTail (p n i j : ℕ) :
    outerAentry p n i j = muZeroTail p n (Rnum n i j) := rfl

/-- The modified Gram matrix in the outer class basis: for two outer class rows `r`, `s`
(`ZetaSeven.outerRow`, integer polynomials indexed by the outer weight family),
`A'_{rs} = μ_0(r(t) s(t) D_N(t)⁷ / D_tail(t))`, a polynomial of degree at most one in `X`. -/
noncomputable def outerAprime (p n : ℕ) : Matrix (outerIdx n p) (outerIdx n p) ℚ[X] :=
  Matrix.of fun ρ σ =>
    muZeroTail p n ((outerRow n p ρ * outerRow n p σ).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7)

theorem outerAprime_apply (p n : ℕ) (ρ σ : outerIdx n p) :
    outerAprime p n ρ σ = muZeroTail p n ((outerRowPoly n p ρ.1 ρ.2 *
      outerRowPoly n p σ.1 σ.2).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7) := rfl

/-- `μ_0` takes values of degree at most one in `X`: the monomial values are constants and the
pole values (6) are affine in `X`. -/
theorem natDegree_muZeroFunctional_le (p : ℕ) (P : ℚ[X]) (c : ℕ →₀ ℚ) :
    (muZeroFunctional p P c).natDegree ≤ 1 := by
  unfold muZeroFunctional
  rw [Polynomial.sum_def, Finsupp.sum]
  refine natDegree_add_le_of_degree_le (natDegree_sum_le_of_forall_le _ fun e _ => ?_)
    (natDegree_sum_le_of_forall_le _ fun j _ => ?_)
  · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_C]; exact zero_le_one)
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [muPole_eq]
    exact natDegree_linear_le

/-- Every entry `A'_{rs}` is a polynomial of degree at most one in `X`. -/
theorem outerAprime_natDegree_le (p n : ℕ) (ρ σ : outerIdx n p) :
    (outerAprime p n ρ σ).natDegree ≤ 1 := by
  rw [outerAprime_apply]
  exact natDegree_muZeroFunctional_le _ _ _

namespace OuterEntry

variable {n p : ℕ}

/-! ## Partial fractions over `D_tail` -/

theorem monic_Dtail (n : ℕ) : (Dtail n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem eval_prod_sq_self {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) :
    (∏ b ∈ S, (X + C ((b : ℚ) ^ 2))).eval (-(a : ℚ) ^ 2) = 0 := by
  rw [eval_prod]
  exact prod_eq_zero ha (by simp)

theorem eval_prod_sq_ne_zero {S : Finset ℕ} {a : ℕ} (ha : a ∉ S) :
    (∏ b ∈ S, (X + C ((b : ℚ) ^ 2))).eval (-(a : ℚ) ^ 2) ≠ 0 := by
  rw [eval_prod, prod_ne_zero_iff]
  intro b hb h
  rw [eval_add, eval_X, eval_C] at h
  have h2 : b ^ 2 = a ^ 2 := by
    have h3 : (b : ℚ) ^ 2 = (a : ℚ) ^ 2 := by linarith
    exact_mod_cast h3
  exact ha (Nat.pow_left_injective two_ne_zero h2 ▸ hb)

/-- Outside `S`, the residue of `R Q / D_tail` vanishes when `D_tail = R T_S`. -/
theorem outerTailRes_eq_zero {S : Finset ℕ} {F R Q : ℚ[X]} (hF : F = R * Q)
    (hD : Dtail n = R * ∏ b ∈ S, (X + C ((b : ℚ) ^ 2))) {a : ℕ}
    (ha : a ∈ Icc (N n + 1) (K n)) (haS : a ∉ S) : outerTailRes n F a = 0 := by
  subst hF
  have h0 : (Dtail n).eval (-(a : ℚ) ^ 2) = 0 := eval_prod_sq_self ha
  rw [hD, eval_mul] at h0
  have hR0 : R.eval (-(a : ℚ) ^ 2) = 0 :=
    (mul_eq_zero.mp h0).resolve_right (eval_prod_sq_ne_zero haS)
  rw [outerTailRes, eval_mul, hR0, zero_mul, zero_div]

/-- On `S`, the residue of `R Q / D_tail` is the residue `Q(-b²)/T_S'(-b²)` of `Q / T_S` when
`D_tail = R T_S`. -/
theorem outerTailRes_eq {S : Finset ℕ} (hS : S ⊆ Icc (N n + 1) (K n)) {F R Q : ℚ[X]}
    (hF : F = R * Q) (hD : Dtail n = R * ∏ b ∈ S, (X + C ((b : ℚ) ^ 2))) {b : ℕ}
    (hb : b ∈ S) : outerTailRes n F b = poleResidue S Q b := by
  subst hF
  have hT0 : (∏ c ∈ S, (X + C ((c : ℚ) ^ 2))).eval (-(b : ℚ) ^ 2) = 0 := eval_prod_sq_self hb
  have hder : (derivative (Dtail n)).eval (-(b : ℚ) ^ 2) = R.eval (-(b : ℚ) ^ 2) *
      (derivative (∏ c ∈ S, (X + C ((c : ℚ) ^ 2)))).eval (-(b : ℚ) ^ 2) := by
    rw [hD, derivative_mul, eval_add, eval_mul, eval_mul, hT0, mul_zero, zero_add]
  have hne : (derivative (Dtail n)).eval (-(b : ℚ) ^ 2) ≠ 0 := by
    have h := derivative_prod_eval (Icc (N n + 1) (K n)) (hS hb)
    rw [show Dtail n = ∏ c ∈ Icc (N n + 1) (K n), (X + C ((c : ℚ) ^ 2)) from rfl, h,
      prod_ne_zero_iff]
    intro c hc h0
    have hcb : c ≠ b := (mem_erase.mp hc).1
    have h2 : c ^ 2 = b ^ 2 := by
      have h3 : (c : ℚ) ^ 2 = (b : ℚ) ^ 2 := by linarith
      exact_mod_cast h3
    exact hcb (Nat.pow_left_injective two_ne_zero h2)
  have hR0 : R.eval (-(b : ℚ) ^ 2) ≠ 0 := fun h0 => hne (by rw [hder, h0, zero_mul])
  rw [outerTailRes, poleResidue, eval_mul, hder, mul_div_mul_left _ _ hR0]

/-- `μ_0` on a polynomial part and the pole coefficients `∑_{b ∈ S} ρ_b [b]`. -/
theorem muZeroFunctional_sum_single (P : ℚ[X]) (S : Finset ℕ) (ρ : ℕ → ℚ) :
    muZeroFunctional p P (∑ b ∈ S, Finsupp.single b (ρ b)) =
      muZeroFunctional p P 0 + ∑ b ∈ S, C (ρ b) * muPole b := by
  unfold muZeroFunctional
  rw [Finsupp.sum_zero_index, add_zero, ← Finsupp.sum_finsetSum_index]
  · refine congrArg _ (sum_congr rfl fun b _ => ?_)
    rw [Finsupp.sum_single_index]
    rw [C_0, zero_mul]
  · intro j
    rw [C_0, zero_mul]
  · intro j a₁ a₂
    rw [C_add, add_mul]

/-- **Partial fractions of `R Q / D_tail`.** If `D_tail = R T_S` with `T_S = ∏_{b ∈ S} (t + b²)`
and `S ⊆ (N, K]`, then `μ_0(R Q / D_tail)` is `μ_0` of the polynomial part plus
`∑_{b ∈ S} ρ_b π_b`, with the residues `ρ_b = Q(-b²)/T_S'(-b²)` and the pole values
`π_b = μ_X(1/(t + b²))`. -/
theorem muZeroTail_eq {S : Finset ℕ} (hS : S ⊆ Icc (N n + 1) (K n)) {F R Q : ℚ[X]}
    (hF : F = R * Q) (hD : Dtail n = R * ∏ b ∈ S, (X + C ((b : ℚ) ^ 2))) :
    muZeroTail p n F = muZeroFunctional p (F /ₘ Dtail n) 0 +
      ∑ b ∈ S, C (poleResidue S Q b) * muPole b := by
  have hdiv : F.div (Dtail n) = F /ₘ Dtail n := (divByMonic_eq_div _ (monic_Dtail n)).symm
  have hpoles : outerTailPoles n F = ∑ b ∈ S, Finsupp.single b (poleResidue S Q b) := by
    unfold outerTailPoles
    rw [← sum_subset hS]
    · exact sum_congr rfl fun b hb => by rw [outerTailRes_eq hS hF hD hb]
    · intro a ha haS
      rw [outerTailRes_eq_zero hF hD ha haS, Finsupp.single_zero]
  unfold muZeroTail
  rw [hdiv, hpoles, muZeroFunctional_sum_single]

/-! ## Valuations of possibly zero rationals -/

/-- `vGe p k x`: `x ∈ p^k ℤ_(p)`, that is `x = 0` or `v_p(x) ≥ k` (`vGe_iff`). -/
def vGe (p : ℕ) [Fact p.Prime] (k : ℤ) (x : ℚ) : Prop := (p : ℚ) ^ (-k) * x ∈ pInt p

section Val

variable [hp : Fact p.Prime]

theorem natCast_p_ne_zero : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

theorem vGe_iff {k : ℤ} {x : ℚ} : vGe p k x ↔ x = 0 ∨ k ≤ padicValRat p x := by
  unfold vGe
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨fun _ => Or.inl rfl, fun _ => by rw [mul_zero]; exact zero_mem _⟩
  · have hpk : (p : ℚ) ^ (-k) ≠ 0 := zpow_ne_zero _ natCast_p_ne_zero
    rw [mem_pInt_iff_padicValRat, padicValRat.mul hpk hx, padicValRat.zpow,
      padicValRat.self hp.out.one_lt]
    constructor
    · intro h
      exact Or.inr (by omega)
    · rintro (h | h)
      · exact absurd h hx
      · omega

theorem vGe.le_padicValRat {k : ℤ} {x : ℚ} (hk : k ≤ 0) (h : vGe p k x) :
    k ≤ padicValRat p x := by
  rcases vGe_iff.mp h with h0 | h
  · rw [h0, padicValRat.zero]
    exact hk
  · exact h

theorem vGe_of_le {k : ℤ} {x : ℚ} (h : k ≤ padicValRat p x) : vGe p k x :=
  vGe_iff.mpr (Or.inr h)

theorem vGe_zero_iff {x : ℚ} : vGe p 0 x ↔ x ∈ pInt p := by
  unfold vGe
  rw [neg_zero, zpow_zero, one_mul]

theorem vGe_neg_natCast_iff (m : ℕ) {x : ℚ} : vGe p (-(m : ℤ)) x ↔ (p : ℚ) ^ m * x ∈ pInt p := by
  unfold vGe
  rw [neg_neg, zpow_natCast]

theorem vGe_of_mem {x : ℚ} (h : x ∈ pInt p) : vGe p 0 x := vGe_zero_iff.mpr h

theorem vGe_zero (k : ℤ) : vGe p k 0 := by
  unfold vGe
  rw [mul_zero]
  exact zero_mem _

theorem vGe_one : vGe p 0 (1 : ℚ) := vGe_of_mem (one_mem _)

theorem vGe.add {k : ℤ} {x y : ℚ} (hx : vGe p k x) (hy : vGe p k y) : vGe p k (x + y) := by
  unfold vGe at hx hy ⊢
  rw [mul_add]
  exact add_mem hx hy

theorem vGe.neg {k : ℤ} {x : ℚ} (hx : vGe p k x) : vGe p k (-x) := by
  unfold vGe at hx ⊢
  rw [mul_neg]
  exact neg_mem hx

theorem vGe.sub {k : ℤ} {x y : ℚ} (hx : vGe p k x) (hy : vGe p k y) : vGe p k (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem vGe.mono {k l : ℤ} {x : ℚ} (h : vGe p k x) (hlk : l ≤ k) : vGe p l x := by
  unfold vGe at h ⊢
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k - l = m := ⟨(k - l).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have e : (p : ℚ) ^ (-l) = (p : ℚ) ^ (m : ℤ) * (p : ℚ) ^ (-k) := by
    rw [← zpow_add₀ natCast_p_ne_zero, ← hm, show k - l + -k = -l by ring]
  rw [e, zpow_natCast, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ p) m) h

theorem vGe.mul {k l : ℤ} {x y : ℚ} (hx : vGe p k x) (hy : vGe p l y) :
    vGe p (k + l) (x * y) := by
  unfold vGe at hx hy ⊢
  have e : (p : ℚ) ^ (-(k + l)) * (x * y) = ((p : ℚ) ^ (-k) * x) * ((p : ℚ) ^ (-l) * y) := by
    rw [neg_add, zpow_add₀ natCast_p_ne_zero]
    ring
  rw [e]
  exact mul_mem hx hy

theorem vGe.mul_le {k l m : ℤ} {x y : ℚ} (hx : vGe p k x) (hy : vGe p l y) (h : m ≤ k + l) :
    vGe p m (x * y) :=
  (hx.mul hy).mono h

theorem vGe.pow {k : ℤ} {x : ℚ} (h : vGe p k x) : ∀ m : ℕ, vGe p (m * k) (x ^ m)
  | 0 => by
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact vGe_one
  | m + 1 => by
    rw [pow_succ]
    exact (h.pow m).mul_le h (le_of_eq (by push_cast; ring))

theorem vGe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {k : ℤ} (h : ∀ i ∈ s, vGe p k (f i)) :
    vGe p k (∑ i ∈ s, f i) := by
  unfold vGe
  rw [mul_sum]
  exact sum_mem fun i hi => h i hi

theorem vGe_prod_const {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) {k : ℤ}
    (h : ∀ i ∈ s, vGe p k (f i)) : vGe p (s.card * k) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, card_empty, Nat.cast_zero, zero_mul]
    exact vGe_one
  | insert j s hj ih =>
    rw [prod_insert hj, card_insert_of_notMem hj]
    exact (h j (mem_insert_self j s)).mul_le (ih fun i hi => h i (mem_insert_of_mem hi))
      (le_of_eq (by push_cast; ring))

theorem vGe_natCast_self : vGe p 1 (p : ℚ) := by
  unfold vGe
  rw [zpow_neg, zpow_one, inv_mul_cancel₀ natCast_p_ne_zero]
  exact one_mem _

theorem vGe_inv_natCast_self : vGe p (-1) ((p : ℚ)⁻¹) := by
  unfold vGe
  rw [neg_neg, zpow_one, mul_inv_cancel₀ natCast_p_ne_zero]
  exact one_mem _

theorem vGe_natCast (m : ℕ) : vGe p 0 (m : ℚ) := vGe_of_mem (natCast_mem _ m)

theorem vGe_one_of_dvd {z : ℤ} (h : (p : ℤ) ∣ z) : vGe p 1 (z : ℚ) := by
  obtain ⟨w, rfl⟩ := h
  rw [Int.cast_mul, Int.cast_natCast]
  exact vGe_natCast_self.mul_le (vGe_of_mem (intCast_mem _ w)) (by omega)

/-! ## `μ_0` is `p`-integral on `p`-integral polynomials -/

/-- The remark of the outer modified functional: for `p ≥ 7`, every `μ_0(t^e)` is `p`-integral.
For `e < 3p - 4` this is the outer moment integrality; for larger `e`, `p μ(t^e)` is `p`-integral
and congruent to `c_e` modulo `p`. -/
theorem muZeroMonomial_mem_pInt (hp7 : 7 ≤ p) (e : ℕ) : muZeroMonomial p e ∈ pInt p := by
  unfold muZeroMonomial
  by_cases he : e < 3 * p - 4
  · rw [outerCe_of_lt he, Nat.cast_zero, zero_div, sub_zero]
    exact mem_pInt_iff_padicValRat.mpr (muMonomial_padicValRat_nonneg hp7 he)
  · rw [not_lt] at he
    have hp0 : (p : ℚ) ≠ 0 := natCast_p_ne_zero
    have hxmem : (p : ℚ) * muMonomial e ∈ pInt p := by
      rw [mem_pInt_iff_padicValRat]
      rcases eq_or_ne (muMonomial e) 0 with h0 | h0
      · rw [h0, mul_zero, padicValRat.zero]
      · rw [padicValRat.mul hp0 h0, padicValRat.self hp.out.one_lt]
        have := muMonomial_padicValRat_ge hp7 e
        omega
    have hden : ¬ p ∣ ((p : ℚ) * muMonomial e).den := mem_pInt_iff_den.mp hxmem
    have hspec := outerCe_spec hp.out he hden
    generalize hx : (p : ℚ) * muMonomial e = x at hspec hden
    have hdvd : (p : ℤ) ∣ x.num - (outerCe p e : ℤ) * (x.den : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hspec, sub_self]
    obtain ⟨w, hw⟩ := hdvd
    have hden0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
    have h1 : x * x.den = x.num := Rat.mul_den_eq_num x
    have hw' : (x.num : ℚ) - (outerCe p e : ℚ) * (x.den : ℚ) = (p : ℚ) * w := by
      exact_mod_cast hw
    have hxc : x - (outerCe p e : ℚ) = (p : ℚ) * w * (x.den : ℚ)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hden0]
      linear_combination h1 + hw'
    have hmu : muMonomial e = x / p := by
      rw [← hx, mul_div_cancel_left₀ _ hp0]
    rw [hmu, div_sub_div_same, hxc, mul_assoc, mul_div_cancel_left₀ _ hp0]
    exact mul_mem (intCast_mem _ w) (inv_natCast_mem_pInt hden)

/-- `μ_0` of a polynomial with `p`-integral coefficients is a `p`-integral constant. -/
theorem muZeroFunctional_mem_pIntPoly (hp7 : 7 ≤ p) {Q : ℚ[X]} (hQ : Q ∈ pIntPoly p) :
    muZeroFunctional p Q 0 ∈ pIntPoly p := by
  unfold muZeroFunctional
  rw [Finsupp.sum_zero_index, add_zero, Polynomial.sum_def]
  refine sum_mem fun e _ => ?_
  rw [← C_mul]
  exact C_mem_pIntPoly (mul_mem (mem_pIntPoly.mp hQ e) (muZeroMonomial_mem_pInt hp7 e))

/-- Division by a monic polynomial with `p`-integral coefficients preserves `p`-integrality. -/
theorem divByMonic_mem_pIntPoly {F T : ℚ[X]} (hF : F ∈ pIntPoly p) (hT : T ∈ pIntPoly p)
    (hTm : T.Monic) : F /ₘ T ∈ pIntPoly p := by
  rw [pIntPoly, ← lifts_iff_liftsRing] at hF hT ⊢
  obtain ⟨F', hF'⟩ := (mem_lifts F).mp hF
  obtain ⟨T', hT', -, hT'm⟩ := lifts_and_natDegree_eq_and_monic hT hTm
  exact (mem_lifts _).mpr ⟨F' /ₘ T', by rw [map_divByMonic _ hT'm, hF', hT']⟩

theorem map_intCast_mem_pIntPoly (P : ℤ[X]) : P.map (Int.castRingHom ℚ) ∈ pIntPoly p := by
  rw [mem_pIntPoly]
  intro i
  rw [coeff_map, eq_intCast]
  exact intCast_mem _ _

theorem Dpoly_mem_pIntPoly (m : ℕ) : Dpoly m ∈ pIntPoly p := by
  unfold Dpoly
  exact prod_mem fun j _ => add_mem X_mem_pIntPoly
    (C_mem_pIntPoly (pow_mem (add_mem (natCast_mem _ j) (one_mem _)) 2))

theorem Dtail_mem_pIntPoly (n : ℕ) : Dtail n ∈ pIntPoly p := by
  unfold Dtail
  exact prod_mem fun j _ => add_mem X_mem_pIntPoly (C_mem_pIntPoly (pow_mem (natCast_mem _ j) 2))

/-- The numerator `r s D_N⁷` of an entry has `p`-integral coefficients. -/
theorem entryNum_mem_pIntPoly (r s : ℤ[X]) :
    (r * s).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7 ∈ pIntPoly p :=
  mul_mem (map_intCast_mem_pIntPoly _) (pow_mem (Dpoly_mem_pIntPoly _) 7)

theorem polyPart_mem (hp7 : 7 ≤ p) {F : ℚ[X]} (hF : F ∈ pIntPoly p) :
    muZeroFunctional p (F /ₘ Dtail n) 0 ∈ pIntPoly p :=
  muZeroFunctional_mem_pIntPoly hp7 (divByMonic_mem_pIntPoly hF (Dtail_mem_pIntPoly n)
    (monic_Dtail n))

/-- An entry is `p`-integral when its pole part is. -/
theorem muZeroTail_mem (hp7 : 7 ≤ p) {S : Finset ℕ} (hS : S ⊆ Icc (N n + 1) (K n))
    {F R Q : ℚ[X]} (hF : F = R * Q) (hD : Dtail n = R * ∏ b ∈ S, (X + C ((b : ℚ) ^ 2)))
    (hFm : F ∈ pIntPoly p) (hpole : ∑ b ∈ S, C (poleResidue S Q b) * muPole b ∈ pIntPoly p) :
    muZeroTail p n F ∈ pIntPoly p := by
  rw [muZeroTail_eq hS hF hD]
  exact add_mem (polyPart_mem hp7 hFm) hpole

/-- An entry has coefficients of valuation at least `B ≤ 0` when every pole term has. -/
theorem muZeroTail_coeff_ge (hp7 : 7 ≤ p) {S : Finset ℕ} (hS : S ⊆ Icc (N n + 1) (K n))
    {F R Q : ℚ[X]} (hF : F = R * Q) (hD : Dtail n = R * ∏ b ∈ S, (X + C ((b : ℚ) ^ 2)))
    (hFm : F ∈ pIntPoly p) {B : ℤ} (hB : B ≤ 0)
    (hpole : ∀ b ∈ S, ∀ k, vGe p B (poleResidue S Q b * (muPole b).coeff k)) (k : ℕ) :
    B ≤ padicValRat p ((muZeroTail p n F).coeff k) := by
  rw [muZeroTail_eq hS hF hD, Polynomial.coeff_add, finsetSum_coeff]
  refine vGe.le_padicValRat hB (vGe.add ?_ (vGe_sum _ _ fun b hb => ?_))
  · exact (vGe_of_mem (mem_pIntPoly.mp (polyPart_mem hp7 hFm) k)).mono hB
  · simp only [coeff_C_mul]
    exact hpole b hb k

end Val

/-! ## The classes `S_d` and the factorizations of `D_tail` -/

section Classes

theorem int_eq_zero_of_dvd {x : ℤ} (h : (p : ℤ) ∣ x) (h1 : -(p : ℤ) < x) (h2 : x < p) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨h1, h2⟩)

theorem outerClassSet_subset (c : ℕ) : outerClassSet n p c ⊆ Icc (N n + 1) (K n) :=
  filter_subset _ _

/-- For odd `p`, the classes `S_c`, `S_d` with `c ≠ d` in `{0, …, m}` are disjoint. -/
theorem disjoint_outerClassSet (hm : 2 * mHalf p + 1 = p) {c d : ℕ} (hc : c ≤ mHalf p)
    (hd : d ≤ mHalf p) (hcd : c ≠ d) : Disjoint (outerClassSet n p c) (outerClassSet n p d) := by
  rw [Finset.disjoint_left]
  intro j hjc hjd
  obtain ⟨-, h1⟩ := mem_outerClassSet.mp hjc
  obtain ⟨-, h2⟩ := mem_outerClassSet.mp hjd
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have h := int_eq_zero_of_dvd (dvd_sub h1 h2) (by omega) (by omega)
    omega
  · have h := int_eq_zero_of_dvd (dvd_sub h2 h1) (by omega) (by omega)
    omega
  · have h := int_eq_zero_of_dvd (dvd_sub h1 h2) (by omega) (by omega)
    omega
  · have h := int_eq_zero_of_dvd (dvd_sub h1 h2) (by omega) (by omega)
    omega

/-- Every `N < j ≤ K` lies in some class `S_d`, `0 ≤ d ≤ m`. -/
theorem exists_mem_outerClassSet (hm : 2 * mHalf p + 1 = p) {j : ℕ}
    (hj : j ∈ Icc (N n + 1) (K n)) : ∃ d ∈ range (mHalf p + 1), j ∈ outerClassSet n p d := by
  have hp0 : 0 < p := by omega
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < p ∧ j = p * q + r :=
    ⟨j / p, j % p, Nat.mod_lt j hp0, (Nat.div_add_mod j p).symm⟩
  rw [mem_Icc] at hj
  by_cases hrm : r ≤ mHalf p
  · refine ⟨r, mem_range.mpr (by omega), mem_outerClassSet.mpr ⟨⟨by omega, hj.2⟩, Or.inl ?_⟩⟩
    exact ⟨(q : ℤ), by push_cast; ring⟩
  · refine ⟨p - r, mem_range.mpr (by omega), mem_outerClassSet.mpr ⟨⟨by omega, hj.2⟩, Or.inr ?_⟩⟩
    exact ⟨(q : ℤ) + 1, by rw [Nat.cast_sub hr.le]; push_cast; ring⟩

theorem biUnion_outerClassSet (hm : 2 * mHalf p + 1 = p) :
    (range (mHalf p + 1)).biUnion (outerClassSet n p) = Icc (N n + 1) (K n) := by
  ext j
  rw [mem_biUnion]
  constructor
  · rintro ⟨d, -, hj⟩
    exact outerClassSet_subset d hj
  · exact exists_mem_outerClassSet hm

/-- `D_tail = ∏_{0 ≤ d ≤ m} ∏_{b ∈ S_d} (t + b²)`. -/
theorem Dtail_eq_prod_outerClassSet (hm : 2 * mHalf p + 1 = p) :
    Dtail n = ∏ d ∈ range (mHalf p + 1), ∏ b ∈ outerClassSet n p d, (X + C ((b : ℚ) ^ 2)) := by
  have hdisj : Set.PairwiseDisjoint (↑(range (mHalf p + 1)) : Set ℕ) (outerClassSet n p) := by
    intro c hc d hd hcd
    have hc' := mem_range.mp (Finset.mem_coe.mp hc)
    have hd' := mem_range.mp (Finset.mem_coe.mp hd)
    exact disjoint_outerClassSet hm (by omega) (by omega) hcd
  unfold Dtail
  rw [← biUnion_outerClassSet hm]
  exact prod_biUnion hdisj

theorem map_X_add_C_sq (b : ℕ) :
    (X + C ((b : ℤ) ^ 2)).map (Int.castRingHom ℚ) = X + C ((b : ℚ) ^ 2) := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  simp

theorem map_prod_X_add_C (s : Finset ℕ) :
    (∏ b ∈ s, (X + C ((b : ℤ) ^ 2))).map (Int.castRingHom ℚ) = ∏ b ∈ s, (X + C ((b : ℚ) ^ 2)) := by
  rw [Polynomial.map_prod]
  exact prod_congr rfl fun b _ => map_X_add_C_sq b

/-- `∏_{0 ≤ d ≤ m} F_d = D_tail`. -/
theorem map_prod_outerClassPoly (hm : 2 * mHalf p + 1 = p) :
    (∏ d ∈ range (mHalf p + 1), outerClassPoly n p d).map (Int.castRingHom ℚ) = Dtail n := by
  rw [Polynomial.map_prod, Dtail_eq_prod_outerClassSet hm]
  exact prod_congr rfl fun d _ => map_prod_X_add_C _

/-- `P_c F_c = ∏_{0 ≤ d ≤ m} F_d`. -/
theorem outerCofactor_mul_outerClassPoly {c : ℕ} (hc : c ≤ mHalf p) :
    outerCofactor n p c * outerClassPoly n p c = ∏ d ∈ range (mHalf p + 1), outerClassPoly n p d := by
  unfold outerCofactor
  exact prod_erase_mul _ _ (mem_range.mpr (by omega))

/-- For two classes `c ≠ d`, `P_c P_d = G ∏_{0 ≤ e ≤ m} F_e`. -/
theorem outerCofactor_mul_outerCofactor {c d : ℕ} (hd : d ≤ mHalf p) (hcd : c ≠ d) :
    outerCofactor n p c * outerCofactor n p d =
      (∏ e ∈ ((range (mHalf p + 1)).erase c).erase d, outerClassPoly n p e) *
        ∏ e ∈ range (mHalf p + 1), outerClassPoly n p e := by
  have h1 : outerCofactor n p c =
      (∏ e ∈ ((range (mHalf p + 1)).erase c).erase d, outerClassPoly n p e) *
        outerClassPoly n p d := by
    unfold outerCofactor
    exact (prod_erase_mul _ _ (mem_erase.mpr ⟨Ne.symm hcd, mem_range.mpr (by omega)⟩)).symm
  rw [h1, ← outerCofactor_mul_outerClassPoly hd]
  ring

/-- `F_c = E_c ∏_{b ∈ S_c, b ≤ p} (t + b²)`. -/
theorem outerClassPoly_eq_high_mul (c : ℕ) :
    outerClassPoly n p c = outerHighPoly n p c *
      ∏ b ∈ (outerClassSet n p c).filter (fun j => ¬ p < j), (X + C ((b : ℤ) ^ 2)) :=
  (prod_filter_mul_prod_filter_not _ _ _).symm

/-- Every row is `P_c` times an integer polynomial. -/
theorem outerRowPoly_eq_cofactor_mul (c i : ℕ) :
    ∃ x : ℤ[X], outerRowPoly n p c i = outerCofactor n p c * x := by
  unfold outerRowPoly
  split_ifs with h
  · exact ⟨X ^ i, by rw [h]⟩
  · exact ⟨_, rfl⟩

/-- A pole `b ∈ S_c` of a class `1 ≤ c ≤ m` is prime to `p`. -/
theorem not_dvd_of_mem_class (hm : 2 * mHalf p + 1 = p) {c b : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) (hb : b ∈ outerClassSet n p c) : ¬ p ∣ b := by
  intro h
  have hpb : (p : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr h
  obtain ⟨-, hbc⟩ := mem_outerClassSet.mp hb
  have hpc : (p : ℤ) ∣ (c : ℤ) := by
    rcases hbc with h' | h'
    · have := dvd_sub hpb h'
      rwa [show (b : ℤ) - (b - c) = c by ring] at this
    · have := dvd_sub h' hpb
      rwa [show (b : ℤ) + c - b = c by ring] at this
  have := int_eq_zero_of_dvd hpc (by omega) (by omega)
  omega

/-- A pole `b ∈ S_c` satisfies `b² ≡ c² (mod p)`. -/
theorem dvd_sq_sub_of_mem {c b : ℕ} (hb : b ∈ outerClassSet n p c) :
    (p : ℤ) ∣ (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
  obtain ⟨-, hbc⟩ := mem_outerClassSet.mp hb
  rcases hbc with h | h
  · rw [show (c : ℤ) ^ 2 - (b : ℤ) ^ 2 = ((b : ℤ) - c) * (-((b : ℤ) + c)) by ring]
    exact h.mul_right _
  · rw [show (c : ℤ) ^ 2 - (b : ℤ) ^ 2 = ((b : ℤ) + c) * ((c : ℤ) - b) by ring]
    exact h.mul_right _

/-- The doubled weight of a class row with index `i < ℓ - 2`. -/
theorem outerFamWeightDbl_low {c i : ℕ} (hc0 : c ≠ 0) (hi : i < ell p (K n) c - 2) :
    outerFamWeightDbl n p c i =
      min 0 (2 * (i : ℤ) + 8 * classDelta n c - ell p (K n) c - 6) := by
  unfold outerFamWeightDbl outerWeightDbl
  rw [ite_eq_right hc0, ite_eq_left hi]

theorem outerFamWeightDbl_zero_class (i : ℕ) :
    outerFamWeightDbl n p 0 i = outerZeroWeightDbl n p i := by
  unfold outerFamWeightDbl
  rw [ite_eq_left rfl]

/-! ### Class facts under the outer-range hypothesis (52) -/

/-- Under (52), `N + m < p`. -/
theorem N_add_mHalf_lt (hR : OuterRange n p) (hm : 2 * mHalf p + 1 = p) : N n + mHalf p < p := by
  have h7 := hR.seven_mul_N_le
  omega

/-- Under (52), for a class `1 ≤ c ≤ m` the only `1 ≤ j ≤ N` with `j ≡ ±c` is `j = c`. -/
theorem eq_of_le_N (hR : OuterRange n p) (hm : 2 * mHalf p + 1 = p) {c j : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) (hj1 : 1 ≤ j) (hjN : j ≤ N n)
    (h : (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c) : j = c := by
  have hNm := N_add_mHalf_lt hR hm
  rcases h with h | h
  · have := int_eq_zero_of_dvd h (by omega) (by omega)
    omega
  · have := int_eq_zero_of_dvd h (by omega) (by omega)
    omega

/-- Under (52), a class `1 ≤ c ≤ m` has `|S_c| = ℓ_K(c) - δ_c` elements. -/
theorem card_outerClassSet_add (hR : OuterRange n p) (hm : 2 * mHalf p + 1 = p) {c : ℕ}
    (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    (outerClassSet n p c).card + classDelta n c = ell p (K n) c := by
  have hNm := N_add_mHalf_lt hR hm
  have hK := hR.le_K
  have hP : ∀ j, j ∈ (Icc 1 (K n)).filter
      (fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c) ↔
      ((1 ≤ j ∧ j ≤ K n) ∧ ((p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c)) := fun j => by
    rw [mem_filter, mem_Icc]
  unfold ell classDelta
  by_cases hcN : c ≤ N n
  · have hX : (Icc 1 (K n)).filter
        (fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c) =
        insert c (outerClassSet n p c) := by
      ext j
      rw [hP, mem_insert, mem_outerClassSet]
      constructor
      · rintro ⟨⟨hj1, hjK⟩, h⟩
        by_cases hjN : j ≤ N n
        · exact Or.inl (eq_of_le_N hR hm hc1 hcm hj1 hjN h)
        · exact Or.inr ⟨⟨by omega, hjK⟩, h⟩
      · rintro (h | ⟨⟨hj1, hjK⟩, h⟩)
        · rw [h]
          exact ⟨⟨hc1, by omega⟩, Or.inl (by simp)⟩
        · exact ⟨⟨by omega, hjK⟩, h⟩
    have hc : c ∉ outerClassSet n p c := fun h => by
      have := (mem_outerClassSet.mp h).1.1
      omega
    rw [hX, card_insert_of_notMem hc, ite_eq_left hcN]
  · have hX : (Icc 1 (K n)).filter
        (fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c) = outerClassSet n p c := by
      ext j
      rw [hP, mem_outerClassSet]
      constructor
      · rintro ⟨⟨hj1, hjK⟩, h⟩
        by_cases hjN : j ≤ N n
        · exact absurd (eq_of_le_N hR hm hc1 hcm hj1 hjN h) (by omega)
        · exact ⟨⟨by omega, hjK⟩, h⟩
      · rintro ⟨⟨hj1, hjK⟩, h⟩
        exact ⟨⟨by omega, hjK⟩, h⟩
    rw [hX, ite_eq_right hcN, add_zero]

/-- Under (52), the poles of a class `1 ≤ c ≤ m` not cancelled by `E_c` are among `c`, `p - c`. -/
theorem filter_not_lt_subset (hR : OuterRange n p) (hm : 2 * mHalf p + 1 = p) {c : ℕ}
    (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    (outerClassSet n p c).filter (fun j => ¬ p < j) ⊆ {c, p - c} := by
  have hNm := N_add_mHalf_lt hR hm
  intro j hj
  rw [mem_filter, mem_outerClassSet] at hj
  obtain ⟨⟨⟨hNj, hjK⟩, h⟩, hjp⟩ := hj
  rw [mem_insert, mem_singleton]
  rcases h with h | h
  · left
    have := int_eq_zero_of_dvd h (by omega) (by omega)
    omega
  · right
    have := int_eq_zero_of_dvd (dvd_sub h (dvd_refl (p : ℤ))) (by omega) (by omega)
    omega

/-- Under (52), the pole `p - c` of a class `1 ≤ c ≤ m` is not cancelled by `E_c`. -/
theorem sub_mem_filter_not_lt (hR : OuterRange n p) (hm : 2 * mHalf p + 1 = p) {c : ℕ}
    (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    p - c ∈ (outerClassSet n p c).filter (fun j => ¬ p < j) := by
  have hNm := N_add_mHalf_lt hR hm
  have hK := hR.le_K
  rw [mem_filter, mem_outerClassSet]
  refine ⟨⟨⟨by omega, by omega⟩, Or.inr ⟨1, ?_⟩⟩, by omega⟩
  rw [Nat.cast_sub (by omega : c ≤ p)]
  ring

/-- Under (52), the zero class consists of multiples `p`, `2p`. -/
theorem mem_outerClassSet_zero (hR : OuterRange n p) {b : ℕ} (hb : b ∈ outerClassSet n p 0) :
    b = p ∨ b = 2 * p := by
  rw [outerClassSet_zero, mem_filter, mem_Icc] at hb
  obtain ⟨⟨hb1, hbK⟩, k, rfl⟩ := hb
  have hK := hR.K_lt
  have hk1 : k ≠ 0 := by
    rintro rfl
    omega
  have hk3 : k < 3 := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · left
    ring
  · right
    ring

/-- Under (52), the zero class has at most `⌊K/p⌋` elements. -/
theorem card_outerClassSet_zero_le (hR : OuterRange n p) :
    (outerClassSet n p 0).card ≤ mK n p := by
  by_cases h2 : K n < 2 * p
  · rw [hR.mK_eq_one h2]
    have hsub : outerClassSet n p 0 ⊆ {p} := by
      intro b hb
      rw [mem_singleton]
      rcases mem_outerClassSet_zero hR hb with h | h
      · exact h
      · have := (mem_outerClassSet.mp hb).1.2
        omega
    simpa using card_le_card hsub
  · rw [hR.mK_eq_two (by omega)]
    have hsub : outerClassSet n p 0 ⊆ {p, 2 * p} := by
      intro b hb
      rcases mem_outerClassSet_zero hR hb with h | h
      · rw [h]
        exact mem_insert_self _ _
      · rw [h]
        exact mem_insert_of_mem (mem_singleton_self _)
    exact (card_le_card hsub).trans card_le_two

end Classes

/-! ## Valuations of the residues and of the pole values -/

section Bounds

variable [hp : Fact p.Prime]

/-- A prime `p ≥ 11` is odd: `2m + 1 = p`. -/
theorem two_mul_mHalf_add_one (hR : OuterRange n p) : 2 * mHalf p + 1 = p := by
  obtain ⟨t, ht⟩ := hp.out.odd_of_ne_two (by have := hR.eleven_le; omega)
  unfold mHalf
  omega

theorem padicValNat_le_one {a : ℕ} (ha : 0 < a) (hap : a < p ^ 2) : padicValNat p a ≤ 1 := by
  by_contra h
  have h2 : p ^ 2 ∣ a := (padicValNat_dvd_iff_le ha.ne').mpr (by omega)
  exact absurd (Nat.le_of_dvd ha h2) (by omega)

theorem vGe_inv_of_padicValRat_le {x : ℚ} {m : ℤ} (h : padicValRat p x ≤ m) :
    vGe p (-m) x⁻¹ := by
  rw [vGe_iff, padicValRat.inv]
  rcases eq_or_ne x 0 with hx | _
  · left
    rw [hx, inv_zero]
  · right
    omega

/-- `v_p(a⁻¹) ≥ -1` for `0 < a < p²`. -/
theorem vGe_inv_natCast_of_lt_sq {a : ℕ} (ha : 0 < a) (hap : a < p ^ 2) :
    vGe p (-1) ((a : ℚ)⁻¹) :=
  vGe_inv_of_padicValRat_le (by rw [padicValRat.of_nat]; exact_mod_cast padicValNat_le_one ha hap)

theorem vGe_inv_natCast_of_not_dvd {a : ℕ} (h : ¬ p ∣ a) : vGe p 0 ((a : ℚ)⁻¹) :=
  vGe_of_mem (inv_natCast_mem_pInt h)

/-- `v_p(H⁷_j) ≥ -7` for `j < 3p`: every `v ≤ j` has `v_p(v) ≤ 1`. -/
theorem vGe_H7 (hp3 : 3 ≤ p) {j : ℕ} (hj : j < 3 * p) : vGe p (-7) (H7 j) := by
  unfold H7
  refine vGe_sum _ _ fun v hv => ?_
  have hv' := mem_range.mp hv
  have hsq : 3 * p ≤ p ^ 2 := by nlinarith
  have h := vGe_inv_natCast_of_lt_sq (p := p) (a := v + 1) (by omega) (by omega)
  have h' : vGe p (-1) (((v : ℚ) + 1)⁻¹) := by exact_mod_cast h
  rw [one_div, ← inv_pow]
  exact (h'.pow 7).mono (by norm_num)

/-- A bound on all coefficients of the pole value `π_j = μ_X(1/(t + j²))` from bounds on its two
coefficients `j⁶` and `1/(2j) - 1/6 - j⁶ H⁷_j`. -/
theorem muPole_coeff_vGe {B : ℤ} {j : ℕ} (h1 : vGe p B ((j : ℚ) ^ 6))
    (h0 : vGe p B (1 / (2 * (j : ℚ)) - 1 / 6 - (j : ℚ) ^ 6 * H7 j)) (k : ℕ) :
    vGe p B ((muPole j).coeff k) := by
  rw [muPole_eq, coeff_add, coeff_C_mul]
  match k with
  | 0 =>
    rw [coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
    exact h0
  | 1 =>
    rw [coeff_X_one, mul_one, coeff_C_of_ne_zero one_ne_zero, add_zero]
    exact h1
  | k + 2 =>
    rw [coeff_X_of_ne_one (by omega : k + 2 ≠ 1), mul_zero, zero_add,
      coeff_C_of_ne_zero (by omega : k + 2 ≠ 0)]
    exact vGe_zero B

theorem vGe_one_div_six (hp7 : 7 ≤ p) : vGe p 0 (1 / 6 : ℚ) := by
  have h6 : ¬ p ∣ 6 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  rw [one_div]
  exact_mod_cast vGe_inv_natCast_of_not_dvd h6

/-- The pole value at `b` with `p ∤ b` and `b < 3p` has coefficients of valuation at least
`-7`. -/
theorem vGe_muPole_of_not_dvd (hp7 : 7 ≤ p) {b : ℕ} (hb : ¬ p ∣ b) (hb3 : b < 3 * p) (k : ℕ) :
    vGe p (-7) ((muPole b).coeff k) := by
  have hb6 : vGe p 0 ((b : ℚ) ^ 6) := ((vGe_natCast b).pow 6).mono (by norm_num)
  refine muPole_coeff_vGe (hb6.mono (by norm_num)) ?_ k
  have h2b : ¬ p ∣ 2 * b := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hb h
  have h1 : vGe p 0 (1 / (2 * (b : ℚ))) := by
    rw [one_div]
    exact_mod_cast vGe_inv_natCast_of_not_dvd h2b
  have hH := vGe_H7 (by omega) hb3
  exact ((h1.mono (by norm_num)).sub ((vGe_one_div_six hp7).mono (by norm_num))).sub
    ((hb6.mul hH).mono (by norm_num))

/-- The pole value at a multiple `0 < b < 3p` of `p` has coefficients of valuation at least
`-1`. -/
theorem vGe_muPole_of_dvd (hp7 : 7 ≤ p) {b : ℕ} (hb : p ∣ b) (hb0 : 0 < b) (hb3 : b < 3 * p)
    (k : ℕ) : vGe p (-1) ((muPole b).coeff k) := by
  have hbv : vGe p 1 (b : ℚ) := by
    obtain ⟨w, hw⟩ := hb
    rw [hw, Nat.cast_mul]
    exact vGe_natCast_self.mul_le (vGe_natCast w) (by norm_num)
  have hb6 : vGe p 6 ((b : ℚ) ^ 6) := (hbv.pow 6).mono (by norm_num)
  refine muPole_coeff_vGe (hb6.mono (by norm_num)) ?_ k
  have hsq : 7 * p ≤ p ^ 2 := by nlinarith
  have h1 : vGe p (-1) (1 / (2 * (b : ℚ))) := by
    rw [one_div]
    exact_mod_cast vGe_inv_natCast_of_lt_sq (p := p) (a := 2 * b) (by omega) (by omega)
  have hH := vGe_H7 (by omega) hb3
  exact (h1.sub ((vGe_one_div_six hp7).mono (by norm_num))).sub ((hb6.mul hH).mono (by norm_num))

/-- For `b ≠ b'` with `p ∤ b` and `b, b' ≤ K`, (52) gives `v_p(b'² - b²) ≤ 1`: only one of
`b' - b`, `b' + b` is divisible by `p`, and both are below `p²` in absolute value. -/
theorem vGe_inv_sq_sub_sq_of_not_dvd (hR : OuterRange n p) {b b' : ℕ} (hb : ¬ p ∣ b)
    (hb1 : 1 ≤ b) (hb'1 : 1 ≤ b') (hbK : b ≤ K n) (hb'K : b' ≤ K n) (hne : b' ≠ b) :
    vGe p (-1) (((b' : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹) := by
  have hK2 := hR.two_mul_K_lt
  have h11 := hR.eleven_le
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hx : (b' : ℚ) ^ 2 - (b : ℚ) ^ 2 =
      (((b' : ℤ) - b : ℤ) : ℚ) * (((b' : ℤ) + b : ℤ) : ℚ) := by
    push_cast
    ring
  have h1 : (b' : ℤ) - b ≠ 0 := by omega
  have h2 : (b' : ℤ) + b ≠ 0 := by omega
  have hboth : ¬ ((p : ℤ) ∣ (b' : ℤ) - b ∧ (p : ℤ) ∣ (b' : ℤ) + b) := by
    rintro ⟨d1, d2⟩
    have h2b : (p : ℤ) ∣ 2 * (b : ℤ) := by
      have := dvd_sub d2 d1
      rwa [show (b' : ℤ) + b - (b' - b) = 2 * b by ring] at this
    rcases hpZ.dvd_or_dvd h2b with h | h
    · have h2 : p ∣ 2 := by exact_mod_cast h
      exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hb (by exact_mod_cast h)
  have hle : ∀ z : ℤ, z ≠ 0 → z.natAbs < p ^ 2 → padicValInt p z ≤ 1 := fun z hz hzp =>
    padicValNat_le_one (Int.natAbs_pos.mpr hz) hzp
  have hz1 := hle _ h1 (by omega)
  have hz2 := hle _ h2 (by omega)
  refine vGe_inv_of_padicValRat_le ?_
  rw [hx, padicValRat.mul (Int.cast_ne_zero.mpr h1) (Int.cast_ne_zero.mpr h2),
    padicValRat.of_int, padicValRat.of_int]
  by_cases hd : (p : ℤ) ∣ (b' : ℤ) - b
  · rw [padicValInt.eq_zero_of_not_dvd fun h => hboth ⟨hd, h⟩]
    omega
  · rw [padicValInt.eq_zero_of_not_dvd hd]
    omega

/-- For distinct `b, b' ∈ {p, 2p}`, `v_p(b'² - b²) = 2`. -/
theorem vGe_inv_sq_sub_sq_of_mem (hp7 : 7 ≤ p) {b b' : ℕ} (hb : b = p ∨ b = 2 * p)
    (hb' : b' = p ∨ b' = 2 * p) (hne : b' ≠ b) :
    vGe p (-2) (((b' : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹) := by
  have h3 : ¬ p ∣ 3 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hv3 : padicValRat p (3 : ℚ) = 0 := by
    have := padicValRat.of_nat (p := p) (n := 3)
    rw [padicValNat.eq_zero_of_not_dvd h3] at this
    exact_mod_cast this
  have hval : padicValRat p (3 * (p : ℚ) ^ 2) = 2 := by
    rw [padicValRat.mul (by norm_num : (3 : ℚ) ≠ 0) (pow_ne_zero 2 natCast_p_ne_zero), hv3,
      padicValRat.pow,
      padicValRat.self hp.out.one_lt]
    norm_num
  refine vGe_inv_of_padicValRat_le (le_of_eq ?_)
  rcases hb with hb | hb <;> rcases hb' with hb' | hb'
  · exact absurd (hb'.trans hb.symm) hne
  · rw [hb, hb', show ((2 * p : ℕ) : ℚ) ^ 2 - (p : ℚ) ^ 2 = 3 * (p : ℚ) ^ 2 by push_cast; ring,
      hval]
  · rw [hb, hb', show (p : ℚ) ^ 2 - ((2 * p : ℕ) : ℚ) ^ 2 = -(3 * (p : ℚ) ^ 2) by push_cast; ring,
      padicValRat.neg, hval]
  · exact absurd (hb'.trans hb.symm) hne

/-- `D_N(-b²)` has valuation at least `δ_c` when `b ≡ ±c (mod p)`: for `c ≤ N` it contains the
factor `c² - b²`. -/
theorem vGe_Dpoly_eval {c b : ℕ} (hc1 : 1 ≤ c) (hcb : (p : ℤ) ∣ (c : ℤ) ^ 2 - (b : ℤ) ^ 2) :
    vGe p (classDelta n c) ((Dpoly (N n)).eval (-((b : ℚ) ^ 2))) := by
  have hmem : ∀ j : ℕ, -((b : ℚ) ^ 2) + ((j : ℚ) + 1) ^ 2 ∈ pInt p := fun j =>
    add_mem (neg_mem (pow_mem (natCast_mem _ b) 2))
      (pow_mem (add_mem (natCast_mem _ j) (one_mem _)) 2)
  unfold Dpoly classDelta
  rw [eval_prod]
  simp only [eval_add, eval_X, eval_C]
  split_ifs with hcN
  · have hc : c - 1 ∈ range (N n) := mem_range.mpr (by omega)
    rw [← mul_prod_erase _ _ hc]
    have h1 : vGe p 1 (-((b : ℚ) ^ 2) + (((c - 1 : ℕ) : ℚ) + 1) ^ 2) := by
      have e : -((b : ℚ) ^ 2) + (((c - 1 : ℕ) : ℚ) + 1) ^ 2 =
          (((c : ℤ) ^ 2 - (b : ℤ) ^ 2 : ℤ) : ℚ) := by
        rw [Nat.cast_sub hc1]
        push_cast
        ring
      rw [e]
      exact vGe_one_of_dvd hcb
    exact h1.mul_le (vGe_of_mem (prod_mem fun j _ => hmem j)) (by norm_num)
  · exact (vGe_of_mem (prod_mem fun j _ => hmem j)).mono (by norm_num)

/-- The residue `ρ_b = Q(-b²) ∏_{c ∈ S, c ≠ b} (c² - b²)⁻¹`. -/
theorem poleResidue_eq_mul {S : Finset ℕ} {b : ℕ} (hb : b ∈ S) (Q : ℚ[X]) :
    poleResidue S Q b =
      Q.eval (-((b : ℚ) ^ 2)) * ∏ c ∈ S.erase b, ((c : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹ := by
  rw [poleResidue, derivative_prod_eval S hb, prod_inv_distrib, div_eq_mul_inv]

/-- A lower bound for a residue from bounds on `Q(-b²)` and on the inverted factors. -/
theorem vGe_poleResidue {S : Finset ℕ} {b : ℕ} (hb : b ∈ S) {Q : ℚ[X]} {a d : ℤ}
    (hQ : vGe p a (Q.eval (-((b : ℚ) ^ 2))))
    (hd : ∀ c ∈ S.erase b, vGe p d (((c : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹)) :
    vGe p (a + (S.erase b).card * d) (poleResidue S Q b) := by
  rw [poleResidue_eq_mul hb]
  exact hQ.mul (vGe_prod_const _ _ hd)

/-- Under the hypotheses of the paired-pole congruence, the pole part over a set of poles
`S ⊆ {c, p - c}` containing `p - c` is `p`-integral: a lone pole `p - c` has a `p`-integral
residue and pole value, and the pair `c`, `p - c` is `ZetaSeven.paired_residues`. -/
theorem pole_sum_mem (hp7 : 7 ≤ p) (hm : 2 * mHalf p + 1 = p) {c : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) {S : Finset ℕ} (hsub : S ⊆ {c, p - c}) (hpc : p - c ∈ S) {Q : ℚ[X]}
    (hQ : Q ∈ pIntPoly p) : ∑ b ∈ S, C (poleResidue S Q b) * muPole b ∈ pIntPoly p := by
  by_cases hcS : c ∈ S
  · have hS : S = {c, p - c} :=
      Finset.Subset.antisymm hsub (insert_subset hcS (singleton_subset_iff.mpr hpc))
    subst hS
    have hpair : ∀ b ∈ ({c, p - c} : Finset ℕ),
        ((b : ZMod p) = c ∨ (b : ZMod p) = -(c : ZMod p)) → b = c ∨ b = p - c := by
      intro b hb _
      rcases mem_insert.mp hb with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.mp h)
    have h := (paired_residues hp7 hc1 hcm (mem_insert_self c {p - c})
      (mem_insert_of_mem (mem_singleton_self (p - c))) hpair
      (fun i => mem_pInt_iff_padicValRat.mp (mem_pIntPoly.mp hQ i))).2.2.2.2
    rw [sum_pair (by omega : c ≠ p - c)]
    exact mem_pIntPoly.mpr fun i => mem_pInt_iff_padicValRat.mpr (h i)
  · have hS : S = {p - c} := by
      ext b
      rw [mem_singleton]
      constructor
      · intro hb
        rcases mem_insert.mp (hsub hb) with h | h
        · rw [h] at hb
          exact absurd hb hcS
        · exact mem_singleton.mp h
      · intro h
        rw [h]
        exact hpc
    subst hS
    rw [sum_singleton]
    refine mul_mem (C_mem_pIntPoly ?_) (muPole_mem_pIntPoly hp7 (by omega) (by omega))
    rw [poleResidue, derivative_prod_eval _ (mem_singleton_self _), erase_singleton, prod_empty,
      div_one]
    exact eval_mem_pInt (mem_pIntPoly.mp hQ) (neg_mem (pow_mem (natCast_mem _ _) 2))

end Bounds

/-! ## The four cases of the entry bound -/

section Entries

variable [hp : Fact p.Prime]

/-- **Cross-class entries.** For two classes `c ≠ d`, the product `r s` of a row of class `c`
and a row of class `d` is divisible by `D_tail`, so the entry `μ_0(r s D_N⁷/D_tail)` is `μ_0` of
an integer polynomial and is `p`-integral. -/
theorem muZeroTail_mem_cross (hR : OuterRange n p) {c d : ℕ} (hd : d ≤ mHalf p) (hcd : c ≠ d)
    (x y : ℤ[X]) :
    muZeroTail p n ((outerCofactor n p c * x * (outerCofactor n p d * y)).map
      (Int.castRingHom ℚ) * Dpoly (N n) ^ 7) ∈ pIntPoly p := by
  have hm := two_mul_mHalf_add_one hR
  have hp7 : 7 ≤ p := by have := hR.eleven_le; omega
  have hF : (outerCofactor n p c * x * (outerCofactor n p d * y)).map (Int.castRingHom ℚ) *
      Dpoly (N n) ^ 7 = Dtail n * (((∏ e ∈ ((range (mHalf p + 1)).erase c).erase d,
        outerClassPoly n p e) * x * y).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7) := by
    rw [← map_prod_outerClassPoly hm (n := n),
      show outerCofactor n p c * x * (outerCofactor n p d * y) =
        (outerCofactor n p c * outerCofactor n p d) * (x * y) by ring,
      outerCofactor_mul_outerCofactor hd hcd]
    simp only [Polynomial.map_mul]
    ring
  refine muZeroTail_mem hp7 (S := ∅) (empty_subset _) hF (by rw [prod_empty, mul_one])
    (entryNum_mem_pIntPoly _ _) ?_
  rw [sum_empty]
  exact zero_mem _

/-- **A row index at least `ℓ - 2`.** For a class `1 ≤ c ≤ m`, a row `P_c E_c x` and a row
`P_c y`: the factor `E_c` cancels the poles with `b > p`, the remaining poles are `p - c` and,
when `δ_c = 0`, `c` (`filter_not_lt_subset`), and the entry is `p`-integral. -/
theorem muZeroTail_mem_high (hR : OuterRange n p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p)
    (x y : ℤ[X]) :
    muZeroTail p n ((outerCofactor n p c * (outerHighPoly n p c * x) *
      (outerCofactor n p c * y)).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7) ∈ pIntPoly p := by
  have hm := two_mul_mHalf_add_one hR
  have hp7 : 7 ≤ p := by have := hR.eleven_le; omega
  have hD : Dtail n = (outerCofactor n p c * outerHighPoly n p c).map (Int.castRingHom ℚ) *
      ∏ b ∈ (outerClassSet n p c).filter (fun j => ¬ p < j), (X + C ((b : ℚ) ^ 2)) := by
    rw [← map_prod_outerClassPoly hm (n := n), ← outerCofactor_mul_outerClassPoly hcm,
      outerClassPoly_eq_high_mul, ← map_prod_X_add_C, ← Polynomial.map_mul]
    congr 1
    ring
  refine muZeroTail_mem hp7 (S := (outerClassSet n p c).filter (fun j => ¬ p < j))
    ((filter_subset _ _).trans (outerClassSet_subset c))
    (Q := (outerCofactor n p c * x * y).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7) ?_ hD
    (entryNum_mem_pIntPoly _ _)
    (pole_sum_mem hp7 hm hc1 hcm (filter_not_lt_subset hR hm hc1 hcm)
      (sub_mem_filter_not_lt hR hm hc1 hcm)
      (mul_mem (map_intCast_mem_pIntPoly _) (pow_mem (Dpoly_mem_pIntPoly _) 7)))
  simp only [Polynomial.map_mul]
  ring

/-- **Both row indices below `ℓ - 2`.** For a class `1 ≤ c ≤ m` and the rows `P_c (t + c²)^i`,
`P_c (t + c²)^j`, the residue at `b ∈ S_c` has valuation at least `(i + j) + 7δ - (ℓ - δ - 1)`
(from `(t + c²)^{i+j}`, from the factor `t + c²` of `D_N` when `δ = 1`, and from the derivative
of `F_c`), and the pole value has valuation at least `-7`, so the entry has valuation at least
`min(0, i + j + 8δ - ℓ - 6)`. -/
theorem muZeroTail_coeff_ge_low (hR : OuterRange n p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p)
    (i j k : ℕ) :
    min 0 ((i : ℤ) + j + 8 * classDelta n c - ell p (K n) c - 6) ≤
      padicValRat p ((muZeroTail p n ((outerCofactor n p c * (X + C ((c : ℤ) ^ 2)) ^ i *
        (outerCofactor n p c * (X + C ((c : ℤ) ^ 2)) ^ j)).map (Int.castRingHom ℚ) *
          Dpoly (N n) ^ 7)).coeff k) := by
  have hm := two_mul_mHalf_add_one hR
  have hp7 : 7 ≤ p := by have := hR.eleven_le; omega
  have hK3 := hR.K_lt
  have hD : Dtail n = (outerCofactor n p c).map (Int.castRingHom ℚ) *
      ∏ b ∈ outerClassSet n p c, (X + C ((b : ℚ) ^ 2)) := by
    rw [← map_prod_outerClassPoly hm (n := n), ← outerCofactor_mul_outerClassPoly hcm,
      Polynomial.map_mul, outerClassPoly, map_prod_X_add_C]
  have hF : (outerCofactor n p c * (X + C ((c : ℤ) ^ 2)) ^ i *
      (outerCofactor n p c * (X + C ((c : ℤ) ^ 2)) ^ j)).map (Int.castRingHom ℚ) *
        Dpoly (N n) ^ 7 = (outerCofactor n p c).map (Int.castRingHom ℚ) *
      ((outerCofactor n p c).map (Int.castRingHom ℚ) * (X + C ((c : ℚ) ^ 2)) ^ (i + j) *
        Dpoly (N n) ^ 7) := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, map_X_add_C_sq]
    ring
  have hcard := card_outerClassSet_add hR hm hc1 hcm
  refine muZeroTail_coeff_ge hp7 (outerClassSet_subset c) hF hD (entryNum_mem_pIntPoly _ _)
    (min_le_left _ _) ?_ k
  intro b hb k'
  obtain ⟨⟨hNb, hbK⟩, -⟩ := mem_outerClassSet.mp hb
  have hnd : ¬ p ∣ b := not_dvd_of_mem_class hm hc1 hcm hb
  have hdvd : (p : ℤ) ∣ (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := dvd_sq_sub_of_mem hb
  have hP : vGe p 0 (((outerCofactor n p c).map (Int.castRingHom ℚ)).eval (-((b : ℚ) ^ 2))) :=
    vGe_of_mem (eval_mem_pInt (mem_pIntPoly.mp (map_intCast_mem_pIntPoly _))
      (neg_mem (pow_mem (natCast_mem _ _) 2)))
  have hZ : vGe p 1 (-((b : ℚ) ^ 2) + (c : ℚ) ^ 2) := by
    have e : -((b : ℚ) ^ 2) + (c : ℚ) ^ 2 = (((c : ℤ) ^ 2 - (b : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast
      ring
    rw [e]
    exact vGe_one_of_dvd hdvd
  have hQ : vGe p (0 + ((i + j : ℕ) : ℤ) * 1 + ((7 : ℕ) : ℤ) * classDelta n c)
      (((outerCofactor n p c).map (Int.castRingHom ℚ) * (X + C ((c : ℚ) ^ 2)) ^ (i + j) *
        Dpoly (N n) ^ 7).eval (-((b : ℚ) ^ 2))) := by
    simp only [eval_mul, eval_pow, eval_add, eval_X, eval_C]
    exact (hP.mul (hZ.pow (i + j))).mul ((vGe_Dpoly_eval hc1 hdvd).pow 7)
  have hden : ∀ b' ∈ (outerClassSet n p c).erase b,
      vGe p (-1) (((b' : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹) := by
    intro b' hb'
    obtain ⟨hne, hb'S⟩ := mem_erase.mp hb'
    obtain ⟨⟨hNb', hb'K⟩, -⟩ := mem_outerClassSet.mp hb'S
    exact vGe_inv_sq_sub_sq_of_not_dvd hR hnd (by omega) (by omega) hbK hb'K hne
  have hres := vGe_poleResidue hb hQ hden
  have hpole := vGe_muPole_of_not_dvd hp7 hnd (by omega) k'
  have herase := card_erase_of_mem hb
  have hpos : 0 < (outerClassSet n p c).card := card_pos.mpr ⟨b, hb⟩
  exact (hres.mul hpole).mono (by omega)

/-- **Two zero-class rows.** The poles are `-(kp)²` with `1 ≤ k ≤ ⌊K/p⌋`; the residues of
`P_0 t^{i+j} D_N⁷/F_0` have valuation at least `2(i + j) - 2(⌊K/p⌋ - 1)` and the pole values at
least `-1`, so the entry has valuation at least `min(0, 2(i + j) - 2⌊K/p⌋ + 1)`. -/
theorem muZeroTail_coeff_ge_zero (hR : OuterRange n p) (i j k : ℕ) :
    min 0 (2 * ((i : ℤ) + j) - 2 * mK n p + 1) ≤
      padicValRat p ((muZeroTail p n ((outerCofactor n p 0 * X ^ i *
        (outerCofactor n p 0 * X ^ j)).map (Int.castRingHom ℚ) * Dpoly (N n) ^ 7)).coeff k) := by
  have hm := two_mul_mHalf_add_one hR
  have hp7 : 7 ≤ p := by have := hR.eleven_le; omega
  have hD : Dtail n = (outerCofactor n p 0).map (Int.castRingHom ℚ) *
      ∏ b ∈ outerClassSet n p 0, (X + C ((b : ℚ) ^ 2)) := by
    rw [← map_prod_outerClassPoly hm (n := n),
      ← outerCofactor_mul_outerClassPoly (Nat.zero_le (mHalf p)), Polynomial.map_mul,
      outerClassPoly, map_prod_X_add_C]
  have hF : (outerCofactor n p 0 * X ^ i * (outerCofactor n p 0 * X ^ j)).map
      (Int.castRingHom ℚ) * Dpoly (N n) ^ 7 = (outerCofactor n p 0).map (Int.castRingHom ℚ) *
      ((outerCofactor n p 0).map (Int.castRingHom ℚ) * X ^ (i + j) * Dpoly (N n) ^ 7) := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    ring
  have hcard := card_outerClassSet_zero_le hR
  refine muZeroTail_coeff_ge hp7 (outerClassSet_subset 0) hF hD (entryNum_mem_pIntPoly _ _)
    (min_le_left _ _) ?_ k
  intro b hb k'
  have hb' := mem_outerClassSet_zero hR hb
  have hpb : p ∣ b := by
    rcases hb' with h | h
    · exact ⟨1, by rw [h, mul_one]⟩
    · exact ⟨2, by rw [h, mul_comm]⟩
  have hb0 : 0 < b := by omega
  have hb3 : b < 3 * p := by omega
  have hP : vGe p 0 (((outerCofactor n p 0).map (Int.castRingHom ℚ)).eval (-((b : ℚ) ^ 2))) :=
    vGe_of_mem (eval_mem_pInt (mem_pIntPoly.mp (map_intCast_mem_pIntPoly _))
      (neg_mem (pow_mem (natCast_mem _ _) 2)))
  have hDN : vGe p 0 ((Dpoly (N n)).eval (-((b : ℚ) ^ 2))) :=
    vGe_of_mem (eval_mem_pInt (mem_pIntPoly.mp (Dpoly_mem_pIntPoly _))
      (neg_mem (pow_mem (natCast_mem _ _) 2)))
  have hbv : vGe p 1 (b : ℚ) := by
    obtain ⟨w, hw⟩ := hpb
    rw [hw, Nat.cast_mul]
    exact vGe_natCast_self.mul_le (vGe_natCast w) (by norm_num)
  have hB2 : vGe p 2 (-((b : ℚ) ^ 2)) := ((hbv.pow 2).mono (by norm_num)).neg
  have hQ : vGe p (0 + ((i + j : ℕ) : ℤ) * 2 + ((7 : ℕ) : ℤ) * 0)
      (((outerCofactor n p 0).map (Int.castRingHom ℚ) * X ^ (i + j) *
        Dpoly (N n) ^ 7).eval (-((b : ℚ) ^ 2))) := by
    simp only [eval_mul, eval_pow, eval_X]
    exact (hP.mul (hB2.pow (i + j))).mul (hDN.pow 7)
  have hden : ∀ b' ∈ (outerClassSet n p 0).erase b,
      vGe p (-2) (((b' : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹) := by
    intro b' hb''
    obtain ⟨hne, hb'S⟩ := mem_erase.mp hb''
    exact vGe_inv_sq_sub_sq_of_mem hp7 hb' (mem_outerClassSet_zero hR hb'S) hne
  have hres := vGe_poleResidue hb hQ hden
  have hpole := vGe_muPole_of_dvd hp7 hpb hb0 hb3 k'
  have herase := card_erase_of_mem hb
  have hpos : 0 < (outerClassSet n p 0).card := card_pos.mpr ⟨b, hb⟩
  exact (hres.mul hpole).mono (by omega)

/-- The entry bound on the rows of two pairs `(c, i)`, `(d, j)` with `c, d ≤ m`, by the four
cases of the article. -/
theorem entry_bound (hR : OuterRange n p) {c d : ℕ} (hc : c ≤ mHalf p) (hd : d ≤ mHalf p)
    (i j k : ℕ) :
    outerFamWeightDbl n p c i + outerFamWeightDbl n p d j ≤
      2 * padicValRat p ((muZeroTail p n ((outerRowPoly n p c i * outerRowPoly n p d j).map
        (Int.castRingHom ℚ) * Dpoly (N n) ^ 7)).coeff k) := by
  have hint : ∀ A : ℚ[X], A ∈ pIntPoly p →
      outerFamWeightDbl n p c i + outerFamWeightDbl n p d j ≤ 2 * padicValRat p (A.coeff k) := by
    intro A hA
    have h0 := mem_pInt_iff_padicValRat.mp (mem_pIntPoly.mp hA k)
    have h1 := outerFamWeightDbl_nonpos n p c i
    have h2 := outerFamWeightDbl_nonpos n p d j
    omega
  rcases eq_or_ne c d with rfl | hcd
  · rcases Nat.eq_zero_or_pos c with rfl | hc1
    · rw [outerRowPoly_zero, outerRowPoly_zero, outerFamWeightDbl_zero_class,
        outerFamWeightDbl_zero_class]
      have hB := muZeroTail_coeff_ge_zero hR i j k
      unfold outerZeroWeightDbl
      by_cases h2 : K n < 2 * p
      · rw [hR.mK_eq_one h2] at hB
        split_ifs <;> omega
      · rw [hR.mK_eq_two (by omega)] at hB
        split_ifs <;> omega
    · have hc0 : c ≠ 0 := by omega
      by_cases hi : ell p (K n) c - 2 ≤ i
      · obtain ⟨y, hy⟩ := outerRowPoly_eq_cofactor_mul (n := n) (p := p) c j
        rw [outerRowPoly_of_ne_zero n p hc0 i, outerQ_of_le hi, hy]
        exact hint _ (muZeroTail_mem_high hR (by omega) hc _ _)
      · by_cases hj : ell p (K n) c - 2 ≤ j
        · obtain ⟨y, hy⟩ := outerRowPoly_eq_cofactor_mul (n := n) (p := p) c i
          rw [mul_comm (outerRowPoly n p c i), outerRowPoly_of_ne_zero n p hc0 j, outerQ_of_le hj,
            hy]
          exact hint _ (muZeroTail_mem_high hR (by omega) hc _ _)
        · rw [not_le] at hi hj
          rw [outerRowPoly_of_ne_zero n p hc0 i, outerQ_of_lt hi, outerRowPoly_of_ne_zero n p hc0 j,
            outerQ_of_lt hj, outerFamWeightDbl_low hc0 hi, outerFamWeightDbl_low hc0 hj]
          have hB := muZeroTail_coeff_ge_low hR (by omega) hc i j k
          omega
  · obtain ⟨x, hx⟩ := outerRowPoly_eq_cofactor_mul (n := n) (p := p) c i
    obtain ⟨y, hy⟩ := outerRowPoly_eq_cofactor_mul (n := n) (p := p) d j
    rw [hx, hy]
    exact hint _ (muZeroTail_mem_cross hR hd hcd x y)

end Entries

end OuterEntry

/-! ## The entry valuations -/

/-- **Outer entry valuations**, with the doubled weights of `ZetaSeven.gauss_rank_lemma`. Let `p`
be a prime satisfying the outer-range hypothesis (52). For two outer class rows `r`, `s`, with
the doubled weights `2 w_r`, `2 w_s` of the outer weight family (`ZetaSeven.outerFamWeightDbl`),
every coefficient of `A'_{rs} = μ_0(r s D_N⁷/D_tail)` satisfies
`2 w_r + 2 w_s ≤ 2 v_p`, that is `v^G_p(A'_{rs}) ≥ w_r + w_s` in the coefficientwise convention of
`ZetaSeven.gauss_rank_lemma`. -/
theorem outer_entry_valuations_dbl {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (ρ σ : outerIdx n p) (k : ℕ) :
    outerFamWeightDbl n p ρ.1 ρ.2 + outerFamWeightDbl n p σ.1 σ.2 ≤
      2 * padicValRat p ((outerAprime p n ρ σ).coeff k) := by
  have hc := ρ.1.isLt
  have hd := σ.1.isLt
  rw [outerAprime_apply]
  exact OuterEntry.entry_bound hR (by omega) (by omega) ρ.2 σ.2 k

/-- **Outer entry valuations.** Let `p` be a prime satisfying the outer-range hypothesis (52).
For two outer class rows `r`, `s` with weights `w_r`, `w_s` of the outer weight family
(`ZetaSeven.outerFamWeight`), the entry `A'_{rs} = μ_0(r s D_N⁷/D_tail)` (`ZetaSeven.outerAprime`)
satisfies `v^G_p(A'_{rs}) ≥ w_r + w_s`, stated coefficientwise: every coefficient has
`padicValRat ≥ w_r + w_s`. The weights are at most `0`, so the zero coefficients impose nothing. -/
theorem outer_entry_valuations {n p : ℕ} [Fact p.Prime] (hR : OuterRange n p)
    (ρ σ : outerIdx n p) (k : ℕ) :
    outerFamWeight n p ρ.1 ρ.2 + outerFamWeight n p σ.1 σ.2 ≤
      (padicValRat p ((outerAprime p n ρ σ).coeff k) : ℚ) := by
  have h := outer_entry_valuations_dbl hR ρ σ k
  have h' : ((outerFamWeightDbl n p ρ.1 ρ.2 + outerFamWeightDbl n p σ.1 σ.2 : ℤ) : ℚ) ≤
      ((2 * padicValRat p ((outerAprime p n ρ σ).coeff k) : ℤ) : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  rw [outerFamWeightDbl_eq_two_mul, outerFamWeightDbl_eq_two_mul] at h'
  linarith

end ZetaSeven
