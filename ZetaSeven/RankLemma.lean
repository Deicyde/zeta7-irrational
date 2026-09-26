import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic

open Finset

namespace ZetaSeven

variable {h : ℕ}

/-! ## Subtype normalization helpers -/

theorem subtype_mk_coe {α : Type*} {p : α → Prop} (y : { x // p x }) (h : p ↑y) :
    (⟨↑y, h⟩ : { x // p x }) = y := rfl

theorem subtype_coe_mk {α : Type*} {p : α → Prop} (a : α) (h : p a) :
    (↑(⟨a, h⟩ : { x // p x }) : α) = a := rfl

/-!
# Rank lemma (Lemma 4.5, equation (55))

For `h × h` matrices with `v_p (A i j) ≥ w i + w j` for nonpositive
half-integer weights `w`, and an integral matrix `L` of `ℚ`-rank at most `r`,
where exactly `z` of the weights are zero:
`v_p (det (A + p⁻¹ L)) ≥ 2 ∑ w i - min r z`.

The formalization uses doubled integer weights `w : Fin h → ℤ` (so `w i`
is twice the paper's weight), giving the equivalent statement
`∑ w i - min r z ≤ v_p (det (A + p⁻¹ L))`.

Proof strategy (following the paper): expand `det (A + B)` by complementary
minors, bound each term's valuation, and maximize over `k ≤ min r h` using
the zero-weight structure.
-/

/-! ## Order embeddings for minor indexing -/

/-- Cardinality of a complement in `Fin h`. -/
theorem compl_card_fin (S : Finset (Fin h)) : Sᶜ.card = h - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- Order embedding of a finset of `Fin h`, indexed by its cardinality. -/
noncomputable def finEmb (S : Finset (Fin h)) : Fin S.card ↪o Fin h :=
  Finset.orderEmbOfFin S rfl

/-- Order embedding of `R`, indexed by `S.card`, given `R.card = S.card`. -/
noncomputable def finEmbOf (R S : Finset (Fin h)) (hR : R.card = S.card) :
    Fin S.card ↪o Fin h :=
  Finset.orderEmbOfFin R hR

/-- Order embedding of the complement, indexed by `h - S.card`. -/
noncomputable def finEmbCompl (S : Finset (Fin h)) : Fin (h - S.card) ↪o Fin h :=
  Finset.orderEmbOfFin Sᶜ (compl_card_fin S)

/-- Order embedding of `Rᶜ`, indexed by `h - S.card`. -/
noncomputable def finEmbComplOf (R S : Finset (Fin h)) (hR : R.card = S.card) :
    Fin (h - S.card) ↪o Fin h :=
  Finset.orderEmbOfFin Rᶜ (by rw [compl_card_fin R, hR])

/-- Order isomorphism onto the subtype, for equiv reasoning. -/
noncomputable def finIso (S : Finset (Fin h)) : Fin S.card ≃o ↥S :=
  Finset.orderIsoOfFin S rfl

noncomputable def finIsoOf (R S : Finset (Fin h)) (hR : R.card = S.card) :
    Fin S.card ≃o ↥R :=
  Finset.orderIsoOfFin R hR

noncomputable def finIsoCompl (S : Finset (Fin h)) : Fin (h - S.card) ≃o ↥Sᶜ :=
  Finset.orderIsoOfFin Sᶜ (compl_card_fin S)

noncomputable def finIsoComplOf (R S : Finset (Fin h)) (hR : R.card = S.card) :
    Fin (h - S.card) ≃o ↥Rᶜ :=
  Finset.orderIsoOfFin Rᶜ (by rw [compl_card_fin R, hR])

@[simp]
theorem coe_finIso (S : Finset (Fin h)) (a : Fin S.card) :
    ↑(finIso S a) = finEmb S a :=
  Finset.coe_orderIsoOfFin_apply S rfl a

@[simp]
theorem coe_finIsoOf (R S : Finset (Fin h)) (hR : R.card = S.card) (a : Fin S.card) :
    ↑(finIsoOf R S hR a) = finEmbOf R S hR a :=
  Finset.coe_orderIsoOfFin_apply R hR a

@[simp]
theorem coe_finIsoCompl (S : Finset (Fin h)) (a : Fin (h - S.card)) :
    ↑(finIsoCompl S a) = finEmbCompl S a :=
  Finset.coe_orderIsoOfFin_apply Sᶜ (compl_card_fin S) a

@[simp]
theorem coe_finIsoComplOf (R S : Finset (Fin h)) (hR : R.card = S.card)
    (a : Fin (h - S.card)) :
    ↑(finIsoComplOf R S hR a) = finEmbComplOf R S hR a :=
  Finset.coe_orderIsoOfFin_apply Rᶜ (by rw [compl_card_fin R, hR]) a

theorem mem_finEmb (S : Finset (Fin h)) (a : Fin S.card) : finEmb S a ∈ S := by
  rw [← coe_finIso]; exact (finIso S a).2

theorem mem_finEmbOf (R S : Finset (Fin h)) (hR : R.card = S.card) (a : Fin S.card) :
    finEmbOf R S hR a ∈ R := by
  rw [← coe_finIsoOf]; exact (finIsoOf R S hR a).2

theorem mem_finEmbCompl (S : Finset (Fin h)) (a : Fin (h - S.card)) :
    finEmbCompl S a ∈ Sᶜ := by
  rw [← coe_finIsoCompl]; exact (finIsoCompl S a).2

theorem mem_finEmbComplOf (R S : Finset (Fin h)) (hR : R.card = S.card)
    (a : Fin (h - S.card)) : finEmbComplOf R S hR a ∈ Rᶜ := by
  rw [← coe_finIsoComplOf]; exact (finIsoComplOf R S hR a).2

/-! ## Reindexing sums and products along order embeddings -/

theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] {s : Finset (Fin h)} {k : ℕ}
    (hk : s.card = k) (g : Fin h → M) :
    ∏ a : Fin k, g (Finset.orderEmbOfFin s hk a) = ∏ i ∈ s, g i := by
  refine Finset.prod_bij (fun a _ => Finset.orderEmbOfFin s hk a) ?hi ?inj ?surj ?h
  · intro a _
    rw [← Finset.coe_orderIsoOfFin_apply s hk a]
    exact (Finset.orderIsoOfFin s hk a).2
  · intro a₁ _ a₂ _ heq
    exact (Finset.orderEmbOfFin s hk).injective heq
  · intro b hb
    exact ⟨(Finset.orderIsoOfFin s hk).symm ⟨b, hb⟩, mem_univ _,
      by
        have hcan : ∀ (y : ↥s), Finset.orderIsoOfFin s hk
            (((Finset.orderIsoOfFin s hk).symm) y) = y := by
          intro y
          show ((Finset.orderIsoOfFin s hk).toEquiv)
            (((Finset.orderIsoOfFin s hk).toEquiv).symm y) = y
          exact Equiv.apply_symm_apply _ _
        simp only [← Finset.coe_orderIsoOfFin_apply, hcan, subtype_coe_mk]⟩
  · intro a _; rfl

theorem sum_orderEmbOfFin {M : Type*} [AddCommMonoid M] {s : Finset (Fin h)} {k : ℕ}
    (hk : s.card = k) (g : Fin h → M) :
    ∑ a : Fin k, g (Finset.orderEmbOfFin s hk a) = ∑ i ∈ s, g i := by
  refine Finset.sum_bij (fun a _ => Finset.orderEmbOfFin s hk a) ?hi ?inj ?surj ?h
  · intro a _
    rw [← Finset.coe_orderIsoOfFin_apply s hk a]
    exact (Finset.orderIsoOfFin s hk a).2
  · intro a₁ _ a₂ _ heq
    exact (Finset.orderEmbOfFin s hk).injective heq
  · intro b hb
    exact ⟨(Finset.orderIsoOfFin s hk).symm ⟨b, hb⟩, mem_univ _,
      by
        have hcan : ∀ (y : ↥s), Finset.orderIsoOfFin s hk
            (((Finset.orderIsoOfFin s hk).symm) y) = y := by
          intro y
          show ((Finset.orderIsoOfFin s hk).toEquiv)
            (((Finset.orderIsoOfFin s hk).toEquiv).symm y) = y
          exact Equiv.apply_symm_apply _ _
        simp only [← Finset.coe_orderIsoOfFin_apply, hcan, subtype_coe_mk]⟩
  · intro a _; rfl

/-! ## Apply lemmas for `Equiv.subtypeCongr` -/

theorem subtypeCongr_apply_of_pos {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : p a) : Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

theorem subtypeCongr_apply_of_neg {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : ¬p a) : Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

/-! ## Fiber decomposition: permutations by image of a finset -/

/-- The fiber condition: `σ` maps `S` onto `R` (as a pointwise iff). -/
def FiberProp (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h)) : Prop :=
  ∀ i, σ i ∈ R ↔ i ∈ S

/-- Bridge between `↥Sᶜ` and the negated-membership subtype (not defeq). -/
noncomputable def complEquiv (S : Finset (Fin h)) : ↥Sᶜ ≃ { x : Fin h // x ∉ S } where
  toFun x := ⟨↑x, Finset.mem_compl.mp x.2⟩
  invFun y := ⟨↑y, Finset.mem_compl.mpr y.2⟩
  left_inv x := rfl
  right_inv y := rfl

theorem coe_complEquiv (S : Finset (Fin h)) (x : ↥Sᶜ) :
    (↑((complEquiv S) x) : Fin h) = ↑x := rfl

theorem complEquiv_symm_apply (S : Finset (Fin h)) (y : { x : Fin h // x ∉ S }) :
    (complEquiv S).symm y = ⟨↑y, Finset.mem_compl.mpr y.2⟩ := rfl

theorem coe_complEquiv_symm (S : Finset (Fin h)) (y : { x : Fin h // x ∉ S }) :
    (↑((complEquiv S).symm y) : Fin h) = ↑y := rfl

/-- Canonical permutation mapping `S` onto `R`, order-preserving on each side. -/
noncomputable def minorBase (S R : Finset (Fin h)) (hR : R.card = S.card) :
    Equiv.Perm (Fin h) :=
  Equiv.subtypeCongr
    ((finIso S).toEquiv.symm.trans (finIsoOf R S hR).toEquiv)
    (((complEquiv S).symm.trans ((finIsoCompl S).toEquiv.symm.trans
      (finIsoComplOf R S hR).toEquiv)).trans (complEquiv R))

theorem minorBase_fiber (S R : Finset (Fin h)) (hR : R.card = S.card) :
    FiberProp S R (minorBase S R hR) := by
  intro i
  by_cases hi : i ∈ S
  · simp only [hi, iff_true]
    show Equiv.subtypeCongr _ _ i ∈ R
    rw [subtypeCongr_apply_of_pos _ _ hi]
    exact ((finIso S).toEquiv.symm.trans (finIsoOf R S hR).toEquiv ⟨i, hi⟩).2
  · simp only [hi, iff_false]
    show Equiv.subtypeCongr _ _ i ∉ R
    rw [subtypeCongr_apply_of_neg _ _ hi]
    exact ((((complEquiv S).symm.trans ((finIsoCompl S).toEquiv.symm.trans
      (finIsoComplOf R S hR).toEquiv)).trans (complEquiv R)) ⟨i, hi⟩).2

/-- A permutation in the fiber restricts to an equiv `S ≃ R`. -/
noncomputable def fiberSubEquiv (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) : ↥S ≃ ↥R where
  toFun i := ⟨σ i, (hf i).mpr i.2⟩
  invFun j := ⟨σ.symm j, (hf (σ.symm j)).mp (by simpa using j.2)⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

/-- A permutation in the fiber restricts to an equiv `Sᶜ ≃ Rᶜ`. -/
noncomputable def fiberSubEquivCompl (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) : ↥Sᶜ ≃ ↥Rᶜ where
  toFun i := ⟨σ i, Finset.mem_compl.mpr fun hcon =>
    Finset.mem_compl.mp i.2 ((hf i).mp hcon)⟩
  invFun j := ⟨σ.symm j, Finset.mem_compl.mpr fun hcon =>
    Finset.mem_compl.mp j.2 (by simpa using (hf (σ.symm j)).mpr hcon)⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

/-- A permutation preserving `s` restricts to a permutation of `s`. -/
noncomputable def restrictPerm (s : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hs : ∀ i, σ i ∈ s ↔ i ∈ s) : Equiv.Perm ↥s where
  toFun i := ⟨σ i, (hs i).mpr i.2⟩
  invFun j := ⟨σ.symm j, (hs (σ.symm j)).mp (by simpa using j.2)⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

/-- A permutation preserving `s` restricts to a permutation of `sᶜ`. -/
noncomputable def restrictPermCompl (s : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hs : ∀ i, σ i ∈ s ↔ i ∈ s) : Equiv.Perm ↥sᶜ where
  toFun i := ⟨σ i, Finset.mem_compl.mpr fun hcon =>
    Finset.mem_compl.mp i.2 ((hs i).mp hcon)⟩
  invFun j := ⟨σ.symm j, Finset.mem_compl.mpr fun hcon =>
    Finset.mem_compl.mp j.2 (by simpa using (hs (σ.symm j)).mpr hcon)⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

/-! ## Computation rules for restricted equivs (definitional) -/

theorem fiberSubEquiv_apply (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) (x : ↥S) :
    fiberSubEquiv S R σ hf x = ⟨σ ↑x, (hf ↑x).mpr x.2⟩ := rfl

theorem coe_fiberSubEquiv (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) (x : ↥S) : ↑(fiberSubEquiv S R σ hf x) = σ ↑x := rfl

theorem fiberSubEquivCompl_apply (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) (x : ↥Sᶜ) :
    fiberSubEquivCompl S R σ hf x =
      ⟨σ ↑x, Finset.mem_compl.mpr fun hcon =>
        Finset.mem_compl.mp x.2 ((hf ↑x).mp hcon)⟩ := rfl

theorem coe_fiberSubEquivCompl (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) (x : ↥Sᶜ) : ↑(fiberSubEquivCompl S R σ hf x) = σ ↑x := rfl

theorem coe_restrictPerm (s : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hs : ∀ i, σ i ∈ s ↔ i ∈ s) (x : ↥s) : ↑(restrictPerm s σ hs x) = σ ↑x := rfl

theorem coe_restrictPermCompl (s : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hs : ∀ i, σ i ∈ s ↔ i ∈ s) (x : ↥sᶜ) :
    ↑(restrictPermCompl s σ hs x) = σ ↑x := rfl

/-- Forward map of the fiber equivalence: restrict and conjugate to `Fin`. -/
noncomputable def fiberToFun (S R : Finset (Fin h)) (hR : R.card = S.card)
    (x : { σ : Equiv.Perm (Fin h) // FiberProp S R σ }) :
    Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)) :=
  (((finIso S).toEquiv.trans (fiberSubEquiv S R x.1 x.2)).trans
    (finIsoOf R S hR).toEquiv.symm,
  ((finIsoCompl S).toEquiv.trans (fiberSubEquivCompl S R x.1 x.2)).trans
    (finIsoComplOf R S hR).toEquiv.symm)

/-- Backward map of the fiber equivalence: glue minor perms along the base. -/
noncomputable def fiberInvFun (S R : Finset (Fin h)) (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    { σ : Equiv.Perm (Fin h) // FiberProp S R σ } :=
  ⟨Equiv.subtypeCongr
    ((finIso S).toEquiv.symm.trans (ρ.1.trans (finIsoOf R S hR).toEquiv))
    (((complEquiv S).symm.trans ((finIsoCompl S).toEquiv.symm.trans
      (ρ.2.trans (finIsoComplOf R S hR).toEquiv))).trans (complEquiv R)),
  by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, iff_true]
      show Equiv.subtypeCongr _ _ i ∈ R
      rw [subtypeCongr_apply_of_pos _ _ hi]
      exact (((finIso S).toEquiv.symm.trans
        (ρ.1.trans (finIsoOf R S hR).toEquiv)) ⟨i, hi⟩).2
    · simp only [hi, iff_false]
      show Equiv.subtypeCongr _ _ i ∉ R
      rw [subtypeCongr_apply_of_neg _ _ hi]
      exact ((((complEquiv S).symm.trans ((finIsoCompl S).toEquiv.symm.trans
        (ρ.2.trans (finIsoComplOf R S hR).toEquiv))).trans (complEquiv R)) ⟨i, hi⟩).2⟩

theorem fiber_left_inv (S R : Finset (Fin h)) (hR : R.card = S.card)
    (x : { σ : Equiv.Perm (Fin h) // FiberProp S R σ }) :
    fiberInvFun S R hR (fiberToFun S R hR x) = x := by
  obtain ⟨σ, hf⟩ := x
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ S
  · show Equiv.subtypeCongr _ _ i = σ i
    rw [subtypeCongr_apply_of_pos _ _ hi]
    have hρ1 : ((fiberToFun S R hR ⟨σ, hf⟩).1)
        = (((finIso S).toEquiv.trans (fiberSubEquiv S R σ hf)).trans
          (finIsoOf R S hR).toEquiv.symm) := rfl
    rw [hρ1]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
      coe_fiberSubEquiv, subtype_coe_mk]
  · show Equiv.subtypeCongr _ _ i = σ i
    rw [subtypeCongr_apply_of_neg _ _ hi]
    have hρ2 : ((fiberToFun S R hR ⟨σ, hf⟩).2)
        = (((finIsoCompl S).toEquiv.trans (fiberSubEquivCompl S R σ hf)).trans
          (finIsoComplOf R S hR).toEquiv.symm) := rfl
    rw [hρ2]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
      coe_fiberSubEquivCompl, coe_complEquiv, coe_complEquiv_symm, subtype_coe_mk]

theorem fiber_right_inv (S R : Finset (Fin h)) (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    fiberToFun S R hR (fiberInvFun S R hR ρ) = ρ := by
  obtain ⟨ρ₁, ρ₂⟩ := ρ
  rw [Prod.ext_iff]
  constructor
  · apply Equiv.ext
    intro a
    show ((fiberToFun S R hR (fiberInvFun S R hR (ρ₁, ρ₂))).1) a = ρ₁ a
    dsimp only [fiberToFun, fiberInvFun]
    simp only [Equiv.trans_apply, fiberSubEquiv_apply,
      subtypeCongr_apply_of_pos _ _ ((finIso S).toEquiv a).2,
      Equiv.trans_apply, subtype_mk_coe, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply, subtype_coe_mk]
  · apply Equiv.ext
    intro b
    show ((fiberToFun S R hR (fiberInvFun S R hR (ρ₁, ρ₂))).2) b = ρ₂ b
    dsimp only [fiberToFun, fiberInvFun]
    simp only [Equiv.trans_apply, fiberSubEquivCompl_apply,
      subtypeCongr_apply_of_neg _ _
        (Finset.mem_compl.mp ((finIsoCompl S).toEquiv b).2),
      Equiv.trans_apply, complEquiv_symm_apply, subtype_coe_mk,
      subtype_mk_coe, Equiv.symm_apply_apply, Equiv.apply_symm_apply, coe_complEquiv]

/-- The fiber over `(S, R)` is equivalent to a pair of permutations. -/
noncomputable def fiberEquiv (S R : Finset (Fin h)) (hR : R.card = S.card) :
    { σ : Equiv.Perm (Fin h) // FiberProp S R σ } ≃
      Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)) :=
  ⟨fiberToFun S R hR, fiberInvFun S R hR,
    fiber_left_inv S R hR, fiber_right_inv S R hR⟩

/-! ## Doubled `padicValRat` infrastructure

Since the paper's weights are half-integers, all valuation bounds are tracked in
doubled form (`C ≤ 2 * padicValRat p x`), keeping every computation in `ℤ`.
-/

variable {p : ℕ} [Fact p.Prime]

/-- Two-factor bound: constants add across multiplication (doubled form). -/
theorem val_two_mul {x y : ℚ} {C₁ C₂ : ℤ}
    (h1 : C₁ ≤ 2 * padicValRat p x) (h2 : C₂ ≤ 2 * padicValRat p y)
    (hc1 : C₁ ≤ 0) (hc2 : C₂ ≤ 0) :
    C₁ + C₂ ≤ 2 * padicValRat p (x * y) := by
  by_cases h : x * y = 0
  · rw [h, padicValRat.zero]
    linarith
  · have hx : x ≠ 0 := left_ne_zero_of_mul h
    have hy : y ≠ 0 := right_ne_zero_of_mul h
    rw [padicValRat.mul hx hy]
    linarith

/-- Sum bound (doubled form): if every term clears `C` and the sum is nonzero,
the sum clears `C`. -/
theorem val_two_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) (C : ℤ)
    (hall : ∀ i ∈ s, C ≤ 2 * padicValRat p (f i))
    (hne : ∑ i ∈ s, f i ≠ 0) :
    C ≤ 2 * padicValRat p (∑ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty => simp at hne
  | @insert a s has ih =>
    rw [Finset.sum_insert has]
    have hqr : f a + ∑ i ∈ s, f i ≠ 0 := by rwa [Finset.sum_insert has] at hne
    by_cases hr : ∑ i ∈ s, f i = 0
    · rw [hr, add_zero]
      exact hall a (Finset.mem_insert_self a s)
    · have h1 : C ≤ 2 * padicValRat p (f a) := hall a (Finset.mem_insert_self a s)
      have h2 : C ≤ 2 * padicValRat p (∑ i ∈ s, f i) :=
        ih (fun i hi => hall i (Finset.mem_insert_of_mem hi)) hr
      have hmin : min (padicValRat p (f a)) (padicValRat p (∑ i ∈ s, f i)) ≤
          padicValRat p (f a + ∑ i ∈ s, f i) :=
        padicValRat.min_le_padicValRat_add hqr
      omega

/-- Product bound (doubled form). -/
theorem val_two_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) (C : ι → ℤ)
    (hall : ∀ a ∈ s, C a ≤ 2 * padicValRat p (f a))
    (hnonpos : ∀ a ∈ s, C a ≤ 0) :
    ∑ a ∈ s, C a ≤ 2 * padicValRat p (∏ a ∈ s, f a) := by
  induction s using Finset.induction with
  | empty => simp [padicValRat.one]
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    exact val_two_mul (hall a (Finset.mem_insert_self a s))
      (ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
        (fun i hi => hnonpos i (Finset.mem_insert_of_mem hi)))
      (hnonpos a (Finset.mem_insert_self a s))
      (Finset.sum_nonpos (fun i hi => hnonpos i (Finset.mem_insert_of_mem hi)))

/-- The sign factor in the Leibniz sum is a unit, hence has valuation zero. -/
theorem val_sign {n : Type*} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    padicValRat p (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) = 0 := by
  obtain h | h := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · rw [h]
    simp [padicValRat.one]
  · rw [h]
    have h2 : ((((-1 : ℤˣ) : ℤ)) : ℚ) = -1 := by
      have hval : (((-1 : ℤˣ) : ℤ)) = -1 := rfl
      rw [hval]
      norm_cast
    rw [h2, padicValRat.neg, padicValRat.one]

/-- Valuation of `p⁻¹`. -/
theorem val_pinv : padicValRat p (p : ℚ)⁻¹ = -1 := by
  rw [padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]

/-- `(p : ℚ)` is nonzero. -/
theorem Rat_cast_prime_ne_zero : (p : ℚ) ≠ 0 := by
  have hpos : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  exact_mod_cast hpos

/-- Doubled valuation bound for entries of `(p⁻¹ • L)` with `L` integral. -/
theorem val_two_smul_pinv_entry (L : Matrix (Fin h) (Fin h) ℚ)
    (hL : ∀ i j, 0 ≤ padicValRat p (L i j)) (i j : Fin h) :
    -2 ≤ 2 * padicValRat p (((p : ℚ)⁻¹ • L) i j) := by
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hLij : L i j = 0
  · rw [hLij, mul_zero, padicValRat.zero]
    norm_num
  · have hpinv : (p : ℚ)⁻¹ ≠ 0 := inv_ne_zero Rat_cast_prime_ne_zero
    rw [padicValRat.mul hpinv hLij, val_pinv]
    have h0 := hL i j
    linarith

/-! ## Leibniz expansion grouped by fibers -/

/-- Leibniz formula with the permutation acting on column indices. -/
theorem det_leibniz (M : Matrix (Fin h) (Fin h) ℚ) :
    M.det = ∑ σ : Equiv.Perm (Fin h),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1

/-- Expanding a product of sums over `univ` as a sum over subsets. -/
theorem prod_add_univ (f g : Fin h → ℚ) :
    ∏ i, (f i + g i) = ∑ S : Finset (Fin h), (∏ i ∈ S, f i) * ∏ i ∈ Sᶜ, g i := by
  have h1 := Finset.prod_add f g (Finset.univ : Finset (Fin h))
  have hpuset : (Finset.univ : Finset (Fin h)).powerset = Finset.univ := by
    ext t
    simp [Finset.mem_powerset]
  rw [hpuset] at h1
  have hcompl : ∀ t : Finset (Fin h), (Finset.univ \ t) = tᶜ :=
    fun t => (Finset.compl_eq_univ_sdiff t).symm
  simp only [hcompl] at h1
  exact h1

/-- Summand of the Leibniz expansion grouped by row set `S`. -/
noncomputable def fiberTerm (A B : Matrix (Fin h) (Fin h) ℚ) (S : Finset (Fin h))
    (σ : Equiv.Perm (Fin h)) : ℚ :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ)
    * ((∏ i ∈ S, B i (σ i)) * ∏ i ∈ Sᶜ, A i (σ i))

/-- Sum over the fiber of permutations mapping `S` onto `R`. -/
noncomputable def fiberSum (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) : ℚ :=
  ∑ σ ∈ Finset.univ.filter (fun σ => S.map σ.toEmbedding = R), fiberTerm A B S σ

theorem sum_fiber_partition (A B : Matrix (Fin h) (Fin h) ℚ) (S : Finset (Fin h)) :
    ∑ σ : Equiv.Perm (Fin h), fiberTerm A B S σ
      = ∑ R : Finset (Fin h), fiberSum A B S R := by
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Equiv.Perm (Fin h)))
    (fun σ => S.map σ.toEmbedding) (fiberTerm A B S)
  exact h.symm

theorem det_eq_sum_fiberSum (A B : Matrix (Fin h) (Fin h) ℚ) :
    (A + B).det
      = ∑ S : Finset (Fin h), ∑ R : Finset (Fin h), fiberSum A B S R := by
  rw [det_leibniz]
  have hexpand : ∀ σ : Equiv.Perm (Fin h),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∏ i, (A + B) i (σ i)
      = ∑ S : Finset (Fin h), fiberTerm A B S σ := by
    intro σ
    have hcomm : ∀ i : Fin h, (A + B) i (σ i) = B i (σ i) + A i (σ i) := by
      intro i
      rw [Matrix.add_apply, add_comm]
    calc (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∏ i, (A + B) i (σ i)
        = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ)
          * ∏ i, (B i (σ i) + A i (σ i)) := by
          simp only [hcomm]
      _ = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∑ S : Finset (Fin h),
          (∏ i ∈ S, B i (σ i)) * ∏ i ∈ Sᶜ, A i (σ i) := by
          simp only [prod_add_univ]
      _ = ∑ S : Finset (Fin h), fiberTerm A B S σ := by
          simp only [Finset.mul_sum, fiberTerm]
  simp only [hexpand]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => sum_fiber_partition A B S

/-! ## Fiber sums reindexed by minor permutations -/

instance fiberPropDecidable (S R : Finset (Fin h)) :
    DecidablePred (FiberProp S R) := fun σ => by
  show Decidable (∀ i, σ i ∈ R ↔ i ∈ S)
  apply Fintype.decidableForallFintype

theorem map_image_eq_iff_fiber (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h)) :
    S.map σ.toEmbedding = R ↔ FiberProp S R σ := by
  constructor
  · intro hmap i
    constructor
    · intro hi
      rw [← hmap] at hi
      rw [Finset.mem_map] at hi
      obtain ⟨a, ha, heq⟩ := hi
      have heq' : σ a = σ i := heq
      have hai : a = i := σ.injective heq'
      rwa [hai] at ha
    · intro hi
      rw [← hmap]
      rw [Finset.mem_map]
      exact ⟨i, hi, rfl⟩
  · intro hf
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨a, ha, heq⟩ := hx
      have heq' : σ a = x := heq
      rw [← heq']
      exact (hf a).mpr ha
    · intro hx
      rw [Finset.mem_map]
      refine ⟨σ.symm x, ?_, ?_⟩
      · have hmem : σ (σ.symm x) ∈ R := by
          rw [Equiv.apply_symm_apply]
          exact hx
        exact (hf (σ.symm x)).mp hmem
      · show σ.toEmbedding (σ.symm x) = x
        exact Equiv.apply_symm_apply σ x

theorem fiberNonempty_card (S R : Finset (Fin h)) (σ : Equiv.Perm (Fin h))
    (hf : FiberProp S R σ) : R.card = S.card := by
  have h := Fintype.card_congr (fiberSubEquiv S R σ hf)
  rw [Fintype.card_coe, Fintype.card_coe] at h
  exact h.symm

theorem fiberSum_eq_zero_of_cards_ne (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) (hR : R.card ≠ S.card) :
    fiberSum A B S R = 0 := by
  unfold fiberSum
  have hempty : Finset.univ.filter (fun σ : Equiv.Perm (Fin h) => S.map σ.toEmbedding = R)
      = ∅ :=
    Finset.filter_false_of_mem (fun σ _ hmap =>
      hR (fiberNonempty_card S R σ ((map_image_eq_iff_fiber S R σ).mp hmap)))
  rw [hempty, Finset.sum_empty]

theorem fiber_apply_S (S R : Finset (Fin h)) (hR : R.card = S.card)
    (x : { σ : Equiv.Perm (Fin h) // FiberProp S R σ }) (a : Fin S.card) :
    x.1 (finEmb S a) = finEmbOf R S hR (((fiberEquiv S R hR) x).1 a) := by
  obtain ⟨σ, hf⟩ := x
  have hρ : (((fiberEquiv S R hR) ⟨σ, hf⟩).1) a
      = (finIsoOf R S hR).toEquiv.symm (fiberSubEquiv S R σ hf ((finIso S) a)) := rfl
  have hcan : ∀ (y : ↥R),
      (finIsoOf R S hR) ((finIsoOf R S hR).toEquiv.symm y) = y := by
    intro y
    show ((finIsoOf R S hR).toEquiv) ((finIsoOf R S hR).toEquiv.symm y) = y
    exact Equiv.apply_symm_apply _ _
  calc σ (finEmb S a)
      = ↑(fiberSubEquiv S R σ hf ((finIso S) a)) := by
        rw [coe_fiberSubEquiv, coe_finIso]
    _ = finEmbOf R S hR (((fiberEquiv S R hR) ⟨σ, hf⟩).1 a) := by
        rw [← coe_finIsoOf R S hR, hρ, hcan]

theorem fiber_apply_Sc (S R : Finset (Fin h)) (hR : R.card = S.card)
    (x : { σ : Equiv.Perm (Fin h) // FiberProp S R σ }) (b : Fin (h - S.card)) :
    x.1 (finEmbCompl S b)
      = finEmbComplOf R S hR (((fiberEquiv S R hR) x).2 b) := by
  obtain ⟨σ, hf⟩ := x
  have hρ : (((fiberEquiv S R hR) ⟨σ, hf⟩).2) b
      = (finIsoComplOf R S hR).toEquiv.symm
        (fiberSubEquivCompl S R σ hf ((finIsoCompl S) b)) := rfl
  have hcan : ∀ (y : ↥Rᶜ),
      (finIsoComplOf R S hR) ((finIsoComplOf R S hR).toEquiv.symm y) = y := by
    intro y
    show ((finIsoComplOf R S hR).toEquiv) ((finIsoComplOf R S hR).toEquiv.symm y) = y
    exact Equiv.apply_symm_apply _ _
  calc σ (finEmbCompl S b)
      = ↑(fiberSubEquivCompl S R σ hf ((finIsoCompl S) b)) := by
        rw [coe_fiberSubEquivCompl, coe_finIsoCompl]
    _ = finEmbComplOf R S hR (((fiberEquiv S R hR) ⟨σ, hf⟩).2 b) := by
        rw [← coe_finIsoComplOf R S hR, hρ, hcan]

theorem fiber_prod_S_eq (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    ∏ i ∈ S, B i ((((fiberEquiv S R hR).symm ρ).1) i)
      = ∏ a, B (finEmb S a) (finEmbOf R S hR (ρ.1 a)) := by
  have hρ1 : (((fiberEquiv S R hR) (((fiberEquiv S R hR).symm ρ))).1) = ρ.1 := by
    rw [Equiv.apply_symm_apply]
  calc ∏ i ∈ S, B i ((((fiberEquiv S R hR).symm ρ).1) i)
      = ∏ a, B (finEmb S a) ((((fiberEquiv S R hR).symm ρ).1) (finEmb S a)) :=
        (prod_orderEmbOfFin rfl _).symm
    _ = ∏ a, B (finEmb S a) (finEmbOf R S hR (ρ.1 a)) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [fiber_apply_S S R hR ((fiberEquiv S R hR).symm ρ) a, hρ1]

theorem fiber_prod_Sc_eq (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    ∏ i ∈ Sᶜ, A i ((((fiberEquiv S R hR).symm ρ).1) i)
      = ∏ b, A (finEmbCompl S b) (finEmbComplOf R S hR (ρ.2 b)) := by
  have hρ2 : (((fiberEquiv S R hR) (((fiberEquiv S R hR).symm ρ))).2) = ρ.2 := by
    rw [Equiv.apply_symm_apply]
  calc ∏ i ∈ Sᶜ, A i ((((fiberEquiv S R hR).symm ρ).1) i)
      = ∏ b, A (finEmbCompl S b)
        ((((fiberEquiv S R hR).symm ρ).1) (finEmbCompl S b)) :=
        (prod_orderEmbOfFin (compl_card_fin S) _).symm
    _ = ∏ b, A (finEmbCompl S b) (finEmbComplOf R S hR (ρ.2 b)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [fiber_apply_Sc S R hR ((fiberEquiv S R hR).symm ρ) b, hρ2]

theorem fiberSum_eq_reindex (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) (hR : R.card = S.card) :
    fiberSum A B S R = ∑ ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)),
      (((Equiv.Perm.sign (((fiberEquiv S R hR).symm ρ).1) : ℤˣ) : ℤ) : ℚ)
      * (((∏ a, B (finEmb S a) (finEmbOf R S hR (ρ.1 a))))
        * (∏ b, A (finEmbCompl S b) (finEmbComplOf R S hR (ρ.2 b)))) := by
  have hmem : ∀ σ : Equiv.Perm (Fin h),
      σ ∈ Finset.univ.filter (fun σ => S.map σ.toEmbedding = R)
        ↔ FiberProp S R σ := by
    intro σ
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact map_image_eq_iff_fiber S R σ
  have hsub := Finset.sum_subtype (F := Subtype.fintype (FiberProp S R)) _ hmem
    (fiberTerm A B S)
  calc fiberSum A B S R
      = ∑ x : { σ : Equiv.Perm (Fin h) // FiberProp S R σ },
        fiberTerm A B S x.1 := hsub
    _ = ∑ ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)),
        fiberTerm A B S (((fiberEquiv S R hR).symm ρ).1) :=
        (Equiv.sum_comp (fiberEquiv S R hR).symm (fun x => fiberTerm A B S x.1)).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        unfold fiberTerm
        rw [fiber_prod_S_eq A B S R hR ρ, fiber_prod_Sc_eq A B S R hR ρ]

/-! ## Minors and the shuffle sign -/

/-- Determinant of the submatrix of `M` with rows `r` and columns `c`. -/
noncomputable def submatrixDet (M : Matrix (Fin h) (Fin h) ℚ) {k : ℕ}
    (r c : Fin k → Fin h) : ℚ :=
  Matrix.det (fun a₁ a₂ => M (r a₁) (c a₂))

/-- Leibniz expansion of a minor with the permutation on column indices. -/
theorem submatrixDet_eq_leibniz (M : Matrix (Fin h) (Fin h) ℚ) {k : ℕ}
    (r c : Fin k → Fin h) :
    submatrixDet M r c = ∑ ρ : Equiv.Perm (Fin k),
      (((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℚ) * ∏ a, M (r a) (c (ρ a)) := by
  have hleib : ∀ N : Matrix (Fin k) (Fin k) ℚ,
      N.det = ∑ ρ : Equiv.Perm (Fin k),
        (((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℚ) * ∏ a, N a (ρ a) := by
    intro N
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
  exact hleib _

/-- The shuffle sign: sign of the order-preserving base permutation. -/
noncomputable def shufflePairSign (S R : Finset (Fin h))
    (hR : R.card = S.card) : ℚ :=
  (((Equiv.Perm.sign (minorBase S R hR) : ℤˣ) : ℤ) : ℚ)

/-- The twist: minor permutations acting on the `S`-blocks, as a permutation of `Fin h`. -/
noncomputable def fiberTwist (S : Finset (Fin h))
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    Equiv.Perm (Fin h) :=
  Equiv.Perm.subtypeCongr
    ((finIso S).toEquiv.permCongr ρ.1)
    ((complEquiv S).permCongr ((finIsoCompl S).toEquiv.permCongr ρ.2))

theorem fiberTwist_apply_of_pos (S : Finset (Fin h))
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)))
    {i : Fin h} (hi : i ∈ S) :
    fiberTwist S ρ i = ↑(((finIso S).toEquiv.permCongr ρ.1) ⟨i, hi⟩) := by
  unfold fiberTwist
  rw [Equiv.Perm.subtypeCongr.left_apply _ _ hi]

theorem fiberTwist_apply_of_neg (S : Finset (Fin h))
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card)))
    {i : Fin h} (hi : i ∉ S) :
    fiberTwist S ρ i
      = ↑(((complEquiv S).permCongr ((finIsoCompl S).toEquiv.permCongr ρ.2)) ⟨i, hi⟩) := by
  unfold fiberTwist
  rw [Equiv.Perm.subtypeCongr.right_apply _ _ hi]

theorem sign_fiberTwist (S : Finset (Fin h))
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    Equiv.Perm.sign (fiberTwist S ρ)
      = Equiv.Perm.sign ρ.1 * Equiv.Perm.sign ρ.2 := by
  simp only [fiberTwist, Equiv.Perm.sign_subtypeCongr, Equiv.Perm.sign_permCongr]

theorem complEquiv_apply (S : Finset (Fin h)) (x : ↥Sᶜ) :
    (complEquiv S) x = ⟨↑x, Finset.mem_compl.mp x.2⟩ := rfl

theorem fiberInvFun_eq_minorBase_mul (S R : Finset (Fin h))
    (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    (fiberInvFun S R hR ρ).1 = minorBase S R hR * fiberTwist S ρ := by
  obtain ⟨ρ₁, ρ₂⟩ := ρ
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply]
  by_cases hi : i ∈ S
  · show Equiv.subtypeCongr _ _ i
        = minorBase S R hR (fiberTwist S (ρ₁, ρ₂) i)
    rw [subtypeCongr_apply_of_pos _ _ hi, fiberTwist_apply_of_pos _ _ hi]
    have hmem : (↑(((finIso S).toEquiv.permCongr ρ₁) ⟨i, hi⟩) : Fin h) ∈ S :=
      (((finIso S).toEquiv.permCongr ρ₁) ⟨i, hi⟩).2
    show (↑_ : Fin h) = Equiv.subtypeCongr _ _ ↑_
    rw [subtypeCongr_apply_of_pos _ _ hmem]
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, subtype_mk_coe,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · show Equiv.subtypeCongr _ _ i
        = minorBase S R hR (fiberTwist S (ρ₁, ρ₂) i)
    rw [subtypeCongr_apply_of_neg _ _ hi, fiberTwist_apply_of_neg _ _ hi]
    have hmem : (↑(((complEquiv S).permCongr
        ((finIsoCompl S).toEquiv.permCongr ρ₂)) ⟨i, hi⟩) : Fin h) ∉ S :=
      (((complEquiv S).permCongr ((finIsoCompl S).toEquiv.permCongr ρ₂)) ⟨i, hi⟩).2
    show (↑_ : Fin h) = Equiv.subtypeCongr _ _ ↑_
    rw [subtypeCongr_apply_of_neg _ _ hmem]
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, complEquiv_apply,
      complEquiv_symm_apply, coe_complEquiv, coe_complEquiv_symm, subtype_coe_mk,
      subtype_mk_coe, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem fiberSign_decomp (S R : Finset (Fin h)) (hR : R.card = S.card)
    (ρ : Equiv.Perm (Fin S.card) × Equiv.Perm (Fin (h - S.card))) :
    (((Equiv.Perm.sign (((fiberEquiv S R hR).symm ρ).1) : ℤˣ) : ℤ) : ℚ)
      = shufflePairSign S R hR
        * ((((Equiv.Perm.sign ρ.1 : ℤˣ) : ℤ) : ℚ)
          * (((Equiv.Perm.sign ρ.2 : ℤˣ) : ℤ) : ℚ)) := by
  have hσ : (((fiberEquiv S R hR).symm ρ).1)
      = minorBase S R hR * fiberTwist S ρ :=
    fiberInvFun_eq_minorBase_mul S R hR ρ
  rw [hσ, Equiv.Perm.sign_mul, sign_fiberTwist]
  unfold shufflePairSign
  simp only [Units.val_mul, Int.cast_mul]

theorem fiberSum_eq_minors (A B : Matrix (Fin h) (Fin h) ℚ)
    (S R : Finset (Fin h)) (hR : R.card = S.card) :
    fiberSum A B S R
      = shufflePairSign S R hR
        * ((submatrixDet B (finEmb S) (finEmbOf R S hR))
          * (submatrixDet A (finEmbCompl S) (finEmbComplOf R S hR))) := by
  rw [fiberSum_eq_reindex A B S R hR,
    submatrixDet_eq_leibniz B (finEmb S) (finEmbOf R S hR),
    submatrixDet_eq_leibniz A (finEmbCompl S) (finEmbComplOf R S hR)]
  rw [Fintype.sum_mul_sum _ _]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun ρ₁ _ => Finset.sum_congr rfl fun ρ₂ _ => ?_
  rw [fiberSign_decomp S R hR (ρ₁, ρ₂)]
  dsimp only []
  ring

/-! ## Valuation bounds for minors -/

/-- The shuffle sign has valuation zero. -/
theorem val_shuffle (S R : Finset (Fin h)) (hR : R.card = S.card) :
    padicValRat p (shufflePairSign S R hR) = 0 := by
  unfold shufflePairSign
  exact val_sign _

/-- A minor of a scalar multiple: the scalar factors out with multiplicity `k`. -/
theorem submatrixDet_smul {k : ℕ} (t : ℚ) (L : Matrix (Fin h) (Fin h) ℚ)
    (r s : Fin k → Fin h) :
    submatrixDet (t • L) r s = t ^ k * submatrixDet L r s := by
  rw [submatrixDet_eq_leibniz, submatrixDet_eq_leibniz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- Doubled valuation bound for powers of `p⁻¹`. -/
theorem val_two_pow_pinv (k : ℕ) :
    (-2 * (k : ℤ)) ≤ 2 * padicValRat p (((p : ℚ)⁻¹) ^ k) := by
  have h : padicValRat p (((p : ℚ)⁻¹) ^ k) = -(k : ℤ) := by
    rw [padicValRat.pow, val_pinv]
    ring
  rw [h]
  linarith

/-- Doubled valuation bound for the determinant of an integral matrix. -/
theorem val_two_det_integral {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ)
    (hM : ∀ a b, 0 ≤ padicValRat p (M a b)) :
    (0 : ℤ) ≤ 2 * padicValRat p (M.det) := by
  by_cases hdet : M.det = 0
  · rw [hdet, padicValRat.zero]
    norm_num
  · have hne : (∑ σ : Equiv.Perm (Fin k),
        ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∏ i, M (σ i) i)) ≠ 0 := by
      have h := hdet
      rwa [Matrix.det_apply'] at h
    rw [Matrix.det_apply']
    refine val_two_sum _ _ _ (fun σ _ => ?_) hne
    have h1 : (0 : ℤ) ≤ 2 * padicValRat p ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ)) := by
      rw [val_sign σ]
      norm_num
    have h2 : (0 : ℤ) ≤ 2 * padicValRat p (∏ i, M (σ i) i) := by
      have h := val_two_prod Finset.univ (fun i => M (σ i) i) (fun _ => (0 : ℤ))
        (fun a _ => by have := hM (σ a) a; linarith) (fun a _ => le_refl (0 : ℤ))
      simpa [Finset.sum_const_zero] using h
    have hmul := val_two_mul h1 h2 (le_refl (0 : ℤ)) (le_refl (0 : ℤ))
    simpa using hmul

/-- Doubled valuation bound for a minor of `A` in terms of weights. -/
theorem val_two_det_weighted {k : ℕ} (w : Fin h → ℤ) (A : Matrix (Fin h) (Fin h) ℚ)
    (hw0 : ∀ i, w i ≤ 0)
    (hA : ∀ i j, w i + w j ≤ 2 * padicValRat p (A i j))
    (r s : Fin k → Fin h) :
    ∑ a, (w (r a) + w (s a)) ≤ 2 * padicValRat p (submatrixDet A r s) := by
  by_cases hdet : submatrixDet A r s = 0
  · rw [hdet, padicValRat.zero]
    have hnonpos : ∀ a : Fin k, w (r a) + w (s a) ≤ 0 := fun a => by
      have e1 := hw0 (r a)
      have e2 := hw0 (s a)
      linarith
    have hle := Finset.sum_nonpos (fun a (_ : a ∈ Finset.univ) => hnonpos a)
    simpa using hle
  · have hne : (∑ ρ : Equiv.Perm (Fin k),
        ((((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℚ) * ∏ a, A (r a) (s (ρ a)))) ≠ 0 := by
      have h := hdet
      rwa [submatrixDet_eq_leibniz] at h
    rw [submatrixDet_eq_leibniz]
    refine val_two_sum _ _ _ (fun ρ _ => ?_) hne
    have hprod : ∑ a, (w (r a) + w (s (ρ a)))
        ≤ 2 * padicValRat p (∏ a, A (r a) (s (ρ a))) :=
      val_two_prod Finset.univ (fun a => A (r a) (s (ρ a)))
        (fun a => w (r a) + w (s (ρ a)))
        (fun a _ => hA (r a) (s (ρ a)))
        (fun a _ => by have e1 := hw0 (r a); have e2 := hw0 (s (ρ a)); linarith)
    have hre : ∑ a, (w (r a) + w (s (ρ a))) = ∑ a, (w (r a) + w (s a)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      exact Equiv.sum_comp ρ (fun a => w (s a))
    have hprod' : ∑ a, (w (r a) + w (s a))
        ≤ 2 * padicValRat p (∏ a, A (r a) (s (ρ a))) := by
      rw [← hre]
      exact hprod
    have hW0 : ∑ a, (w (r a) + w (s a)) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => by
        have e1 := hw0 (r a); have e2 := hw0 (s a); linarith)
    have hsign : (0 : ℤ) ≤ 2 * padicValRat p ((((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℚ)) := by
      rw [val_sign ρ]
      norm_num
    have hmul := val_two_mul hsign hprod' (le_refl (0 : ℤ)) hW0
    simpa using hmul

/-- A minor of `L` larger than the rank vanishes. -/
theorem submatrixDet_L_eq_zero {k r : ℕ} (L : Matrix (Fin h) (Fin h) ℚ)
    (hr : Matrix.rank L ≤ r) (hk : r < k)
    (rr s : Fin k → Fin h) :
    submatrixDet L rr s = 0 := by
  have hmat : L.submatrix rr s = (fun a₁ a₂ => L (rr a₁) (s a₂)) := by
    ext i j
    rfl
  by_contra hne
  unfold submatrixDet at hne
  rw [← hmat] at hne
  have hrank := Matrix.rank_of_det_ne_zero hne
  rw [Fintype.card_fin] at hrank
  have hle := Matrix.rank_submatrix_le L rr s
  omega

/-- A weight sum over any set is bounded via the zero-weight count. -/
theorem sum_weights_le (w : Fin h → ℤ) {z : ℕ}
    (hw0 : ∀ i, w i ≤ 0)
    (hz : (Finset.univ.filter (fun i => w i = 0)).card = z)
    (S : Finset (Fin h)) :
    ∑ i ∈ S, w i ≤ -(S.card : ℤ) + (z : ℤ) := by
  have hpoint : ∀ i ∈ S, w i ≤ (if w i = 0 then (0 : ℤ) else -1) := by
    intro i _
    by_cases h0 : w i = 0
    · simp [h0]
    · simp only [h0]
      have e := hw0 i
      omega
  have h2 := Finset.sum_le_sum hpoint
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun i => w i = 0)
    (fun i => if w i = 0 then (0 : ℤ) else -1)
  have hA : ∑ x ∈ S.filter (fun i => w i = 0),
      (if w x = 0 then (0 : ℤ) else -1) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]
  have hB : ∑ x ∈ S.filter (fun i => ¬ w i = 0),
      (if w x = 0 then (0 : ℤ) else -1)
      = -((S.filter (fun i => ¬ w i = 0)).card : ℤ) := by
    have hterm : ∀ x ∈ S.filter (fun i => ¬ w i = 0),
        (if w x = 0 then (0 : ℤ) else -1) = -1 :=
      fun x hx => by simp [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard2 : (S.filter (fun i => w i = 0)).card
      + (S.filter (fun i => ¬ w i = 0)).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun i => w i = 0)
  have hcard : (S.filter (fun i => w i = 0)).card ≤ z := by
    rw [← hz]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ x, hx.2⟩
  simp only [hA, hB] at hsplit
  omega

/-! ## Per-term bound and main theorem -/

/-- Doubled valuation bound for each complementary-minor term. -/
theorem fiberSum_val_bound {r z : ℕ} (w : Fin h → ℤ) (A L : Matrix (Fin h) (Fin h) ℚ)
    (hw0 : ∀ i, w i ≤ 0)
    (hz : (Finset.univ.filter (fun i => w i = 0)).card = z)
    (hA : ∀ i j, w i + w j ≤ 2 * padicValRat p (A i j))
    (hL : ∀ i j, 0 ≤ padicValRat p (L i j))
    (hr : Matrix.rank L ≤ r)
    (S R : Finset (Fin h)) :
    2 * (∑ i, w i) - 2 * ↑(min r z)
      ≤ 2 * padicValRat p (fiberSum A ((p : ℚ)⁻¹ • L) S R) := by
  have hsum0 : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => hw0 i
  have hmin0 : (0 : ℤ) ≤ ((min r z : ℕ) : ℤ) := Nat.cast_nonneg _
  have hC0 : 2 * (∑ i, w i) - 2 * ↑(min r z) ≤ 0 := by linarith
  by_cases hR : R.card = S.card
  · rw [fiberSum_eq_minors A _ S R hR]
    by_cases hk : S.card ≤ r
    · have hsh : (0 : ℤ) ≤ 2 * padicValRat p (shufflePairSign S R hR) := by
        rw [val_shuffle S R hR]
        norm_num
      have hcard0 : (0 : ℤ) ≤ (S.card : ℤ) := Nat.cast_nonneg _
      have hB : (-2 * (S.card : ℤ))
          ≤ 2 * padicValRat p
            (submatrixDet ((p : ℚ)⁻¹ • L) (finEmb S) (finEmbOf R S hR)) := by
        rw [submatrixDet_smul]
        have hpow : (-2 * (S.card : ℤ))
            ≤ 2 * padicValRat p (((p : ℚ)⁻¹) ^ S.card) :=
          val_two_pow_pinv (S.card)
        have hdet0 : (0 : ℤ) ≤ 2 * padicValRat p
            (submatrixDet L (finEmb S) (finEmbOf R S hR)) :=
          val_two_det_integral _ (fun a b => hL _ _)
        have hmul := val_two_mul hpow hdet0 (by linarith) (le_refl (0 : ℤ))
        simpa using hmul
      have hAmin : ∑ b, (w (finEmbCompl S b) + w (finEmbComplOf R S hR b))
          ≤ 2 * padicValRat p
            (submatrixDet A (finEmbCompl S) (finEmbComplOf R S hR)) :=
        val_two_det_weighted w A hw0 hA _ _
      have hW : ∑ b, (w (finEmbCompl S b) + w (finEmbComplOf R S hR b))
          = ∑ i ∈ Sᶜ, w i + ∑ j ∈ Rᶜ, w j := by
        rw [Finset.sum_add_distrib]
        congr 1
        · exact sum_orderEmbOfFin (compl_card_fin S) w
        · have hk2 : (Rᶜ).card = h - S.card := by rw [compl_card_fin R, hR]
          exact sum_orderEmbOfFin hk2 w
      have hAmin' : ∑ i ∈ Sᶜ, w i + ∑ j ∈ Rᶜ, w j
          ≤ 2 * padicValRat p
            (submatrixDet A (finEmbCompl S) (finEmbComplOf R S hR)) := by
        rw [← hW]
        exact hAmin
      have hW0 : ∑ i ∈ Sᶜ, w i + ∑ j ∈ Rᶜ, w j ≤ 0 := by
        rw [← hW]
        exact Finset.sum_nonpos (fun b _ => by
          have e1 := hw0 (finEmbCompl S b)
          have e2 := hw0 (finEmbComplOf R S hR b)
          linarith)
      have hBA : (-2 * (S.card : ℤ)) + (∑ i ∈ Sᶜ, w i + ∑ j ∈ Rᶜ, w j)
          ≤ 2 * padicValRat p
            (submatrixDet ((p : ℚ)⁻¹ • L) (finEmb S) (finEmbOf R S hR)
              * submatrixDet A (finEmbCompl S) (finEmbComplOf R S hR)) :=
        val_two_mul hB hAmin' (by linarith) hW0
      have htot := val_two_mul hsh hBA (le_refl (0 : ℤ)) (by linarith)
      have hSc : ∑ i ∈ Sᶜ, w i = ∑ i, w i - ∑ i ∈ S, w i := by
        have h := Finset.sum_compl_add_sum S w
        linarith
      have hRc : ∑ j ∈ Rᶜ, w j = ∑ j, w j - ∑ j ∈ R, w j := by
        have h := Finset.sum_compl_add_sum R w
        linarith
      have hfin : 2 * (∑ i, w i) - 2 * ↑(min r z)
          ≤ 0 + (-2 * (S.card : ℤ) + (∑ i ∈ Sᶜ, w i + ∑ j ∈ Rᶜ, w j)) := by
        have hS0 : ∑ i ∈ S, w i ≤ 0 := Finset.sum_nonpos fun i _ => hw0 i
        have hR0 : ∑ j ∈ R, w j ≤ 0 := Finset.sum_nonpos fun j _ => hw0 j
        have hWS := sum_weights_le w hw0 hz S
        have hWR := sum_weights_le w hw0 hz R
        have hRcard : (R.card : ℤ) = (S.card : ℤ) := by rw [hR]
        have hcardr : (S.card : ℤ) ≤ (r : ℤ) := by exact_mod_cast hk
        rcases le_total r z with hrz | hrz
        · have hmin : min r z = r := Nat.min_eq_left hrz
          rw [hmin]
          linarith [hSc, hRc, hS0, hR0, hcardr]
        · have hmin : min r z = z := Nat.min_eq_right hrz
          rw [hmin]
          linarith [hSc, hRc, hWS, hWR, hRcard]
      linarith [hfin, htot]
    · have hkr : r < S.card := lt_of_not_ge hk
      have hB0 : submatrixDet ((p : ℚ)⁻¹ • L) (finEmb S) (finEmbOf R S hR) = 0 := by
        rw [submatrixDet_smul]
        have hL0 := submatrixDet_L_eq_zero L hr hkr (finEmb S) (finEmbOf R S hR)
        rw [hL0, mul_zero]
      rw [hB0, zero_mul, mul_zero, padicValRat.zero]
      linarith [hC0]
  · rw [fiberSum_eq_zero_of_cards_ne A _ S R hR, padicValRat.zero]
    linarith [hC0]

/-! ## Main theorem: Lemma 4.5 (rank lemma) -/

/-- Lemma 4.5 (rank lemma), doubled integer weights formulation:
`∑ w i - min r z ≤ v_p (det (A + p⁻¹ L))`. -/
theorem rank_lemma {r z : ℕ}
    (w : Fin h → ℤ) (A L : Matrix (Fin h) (Fin h) ℚ)
    (hw0 : ∀ i, w i ≤ 0)
    (hz : (Finset.univ.filter (fun i => w i = 0)).card = z)
    (hA : ∀ i j, w i + w j ≤ 2 * padicValRat p (A i j))
    (hL : ∀ i j, 0 ≤ padicValRat p (L i j))
    (hr : Matrix.rank L ≤ r) :
    ∑ i, w i - ↑(min r z) ≤ padicValRat p ((A + (p : ℚ)⁻¹ • L).det) := by
  have hsum0 : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => hw0 i
  have hmin0 : (0 : ℤ) ≤ ((min r z : ℕ) : ℤ) := Nat.cast_nonneg _
  have hC0 : 2 * (∑ i, w i) - 2 * ↑(min r z) ≤ 0 := by linarith
  have hterm := fiberSum_val_bound w A L hw0 hz hA hL hr
  have hinner : ∀ S ∈ (Finset.univ : Finset (Finset (Fin h))),
      2 * (∑ i, w i) - 2 * ↑(min r z)
        ≤ 2 * padicValRat p (∑ R, fiberSum A ((p : ℚ)⁻¹ • L) S R) := by
    intro S _
    by_cases h0 : (∑ R, fiberSum A ((p : ℚ)⁻¹ • L) S R) = 0
    · rw [h0, padicValRat.zero]
      linarith [hC0]
    · exact val_two_sum _ _ _ (fun R _ => hterm S R) h0
  have houter : 2 * (∑ i, w i) - 2 * ↑(min r z)
      ≤ 2 * padicValRat p (∑ S, ∑ R, fiberSum A ((p : ℚ)⁻¹ • L) S R) := by
    by_cases h0 : (∑ S, ∑ R, fiberSum A ((p : ℚ)⁻¹ • L) S R) = 0
    · rw [h0, padicValRat.zero]
      linarith [hC0]
    · exact val_two_sum _ _ _ hinner h0
  have hdet : (A + (p : ℚ)⁻¹ • L).det
      = ∑ S, ∑ R, fiberSum A ((p : ℚ)⁻¹ • L) S R :=
    det_eq_sum_fiberSum A _
  by_cases h0 : (A + (p : ℚ)⁻¹ • L).det = 0
  · rw [h0, padicValRat.zero]
    linarith [hsum0, hmin0]
  · rw [hdet]
    linarith [houter]

end ZetaSeven
