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
data of the rational function over `D_tail` (`muZeroTail`). Then every entry satisfies
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
  · push_neg at he
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

end OuterEntry

end ZetaSeven
