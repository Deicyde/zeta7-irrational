import ZetaSeven.OuterRangeData

/-!
# Outer weight family (paper Section 4.2, equation (56), proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2: the proof of Proposition 4.6 applies the
rank lemma (Lemma 4.5) "to the weights (56)". The paper gives no weights for the zero-class
rows and no indexing of the rows, since it defers the basis to its `ζ(5)` predecessor; the
zero-class weights and the indexing below are reconstructed by this project.

* `outerZeroWeight`: the zero-class weights `w^out_{0,0} = -1/2` when `K < 2p`,
  `w^out_{0,0} = -3/2` when `K ≥ 2p`, and `w^out_{0,i} = 0` for `i ≥ 1`;
  `outerZeroWeightDbl` is twice it in `ℤ` (`outerZeroWeightDbl_eq_two_mul`).
* `outerLen`: the number of pairs of a class, `⌊K/p⌋` for the zero class and
  `ℓ_K(c) - δ_c` for a class `1 ≤ c ≤ m`.
* `outerIdx`: the index type of the family, the zero-class pairs `(0, i)` with
  `0 ≤ i < ⌊K/p⌋` and the class pairs `(c, i)` with `1 ≤ c ≤ m` and `0 ≤ i < ℓ_K(c) - δ_c`.
* `outerFamWeight`: the weight of a pair, the outer weight `w^out_{c,i}` (56) for `c ≥ 1`
  and the zero-class weight `w^out_{0,i}` for `c = 0`; the family is
  `fun ρ : outerIdx n p => outerFamWeight n p ρ.1 ρ.2`. `outerFamWeightDbl` is twice it in
  `ℤ` (`outerFamWeightDbl_eq_two_mul`), the convention of `ZetaSeven.rank_lemma`.
* The remarks of the article: every weight is a nonpositive half-integer
  (`outerFamWeight_nonpos`, `outerFamWeight_half_int`, `outerFamWeightDbl_nonpos`), and under
  (52) `⌊K/p⌋` is `1` when `K < 2p` and `2` when `K ≥ 2p` (`OuterRange.mK_eq_one`,
  `OuterRange.mK_eq_two`), with the zero-class weights `outerZeroWeight_zero_of_lt`,
  `outerZeroWeight_zero_of_le` and `outerZeroWeight_of_ne_zero`.
* Sums over the family by classes: `sum_outerIdx`, `card_outerIdx`.

The definitions are total: they need neither that `p` is prime nor (52).
-/

namespace ZetaSeven

open Finset

/-! ## The zero-class weights -/

/-- The zero-class weights: `w^out_{0,0} = -1/2` when `K < 2p`, `w^out_{0,0} = -3/2` when
`K ≥ 2p`, and `w^out_{0,i} = 0` for `i ≥ 1`. -/
def outerZeroWeight (n p i : ℕ) : ℚ :=
  if i = 0 then (if K n < 2 * p then -1 / 2 else -3 / 2) else 0

/-- Twice the zero-class weight, as an integer: at `i = 0` it is `-1` when `K < 2p` and `-3`
when `K ≥ 2p`, and it is `0` for `i ≥ 1` (`outerZeroWeightDbl_eq_two_mul`). -/
def outerZeroWeightDbl (n p i : ℕ) : ℤ :=
  if i = 0 then (if K n < 2 * p then -1 else -3) else 0

/-- The doubled zero-class weight is twice the zero-class weight. -/
theorem outerZeroWeightDbl_eq_two_mul (n p i : ℕ) :
    (outerZeroWeightDbl n p i : ℚ) = 2 * outerZeroWeight n p i := by
  unfold outerZeroWeightDbl outerZeroWeight
  split_ifs <;> norm_num

/-- `w^out_{0,0} = -1/2` when `K < 2p`. -/
theorem outerZeroWeight_zero_of_lt {n p : ℕ} (h : K n < 2 * p) :
    outerZeroWeight n p 0 = -1 / 2 := by
  unfold outerZeroWeight
  rw [if_pos rfl, if_pos h]

/-- `w^out_{0,0} = -3/2` when `K ≥ 2p`. -/
theorem outerZeroWeight_zero_of_le {n p : ℕ} (h : 2 * p ≤ K n) :
    outerZeroWeight n p 0 = -3 / 2 := by
  unfold outerZeroWeight
  rw [if_pos rfl, if_neg (Nat.not_lt.mpr h)]

/-- `w^out_{0,i} = 0` for `i ≥ 1`. -/
theorem outerZeroWeight_of_ne_zero (n p : ℕ) {i : ℕ} (hi : i ≠ 0) :
    outerZeroWeight n p i = 0 := by
  unfold outerZeroWeight
  rw [if_neg hi]

/-- The zero-class weights are at most `0`. -/
theorem outerZeroWeight_nonpos (n p i : ℕ) : outerZeroWeight n p i ≤ 0 := by
  unfold outerZeroWeight
  split_ifs <;> norm_num

/-- The outer weights (56) are at most `0`. -/
theorem outerWeight_nonpos (n p a i : ℕ) : outerWeight n p a i ≤ 0 := by
  unfold outerWeight
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-! ## The index type and the weights of the family -/

/-- The number of pairs of the class `c` in the outer weight family: `⌊K/p⌋ = mK n p` for the
zero class `c = 0`, and `ℓ_K(c) - δ_c` for a class `1 ≤ c ≤ m`. The natural subtraction agrees
with the source: if `ℓ_K(c) < δ_c`, both give no pairs. -/
def outerLen (n p c : ℕ) : ℕ :=
  if c = 0 then mK n p else ell p (K n) c - classDelta n c

/-- The zero class has `⌊K/p⌋` pairs. -/
theorem outerLen_zero (n p : ℕ) : outerLen n p 0 = mK n p := by
  unfold outerLen
  rw [if_pos rfl]

/-- A class `c ≥ 1` has `ℓ_K(c) - δ_c` pairs. -/
theorem outerLen_of_ne_zero (n p : ℕ) {c : ℕ} (hc : c ≠ 0) :
    outerLen n p c = ell p (K n) c - classDelta n c := by
  unfold outerLen
  rw [if_neg hc]

/-- The index type of the outer weight family: the pairs `(c, i)` with `0 ≤ c ≤ m`
(`m = mHalf p`) and `0 ≤ i < outerLen n p c`, that is, the zero-class pairs `(0, i)` with
`0 ≤ i < ⌊K/p⌋` and the class pairs `(c, i)` with `1 ≤ c ≤ m` and `0 ≤ i < ℓ_K(c) - δ_c`. -/
abbrev outerIdx (n p : ℕ) : Type :=
  Σ c : Fin (mHalf p + 1), Fin (outerLen n p c)

/-- The weight of the pair `(c, i)` in the outer weight family: the zero-class weight
`w^out_{0,i}` for `c = 0` and the outer weight `w^out_{c,i}` (56) for `c ≥ 1`. The family on
its index type is `fun ρ : outerIdx n p => outerFamWeight n p ρ.1 ρ.2`. -/
def outerFamWeight (n p c i : ℕ) : ℚ :=
  if c = 0 then outerZeroWeight n p i else outerWeight n p c i

/-- Twice the weight of the pair `(c, i)`, as an integer: `outerZeroWeightDbl` for `c = 0`
and `outerWeightDbl` for `c ≥ 1` (`outerFamWeightDbl_eq_two_mul`). `ZetaSeven.rank_lemma`
takes doubled weights. -/
def outerFamWeightDbl (n p c i : ℕ) : ℤ :=
  if c = 0 then outerZeroWeightDbl n p i
  else outerWeightDbl (ell p (K n) c) (classDelta n c) i

/-- The doubled family weight is twice the family weight. -/
theorem outerFamWeightDbl_eq_two_mul (n p c i : ℕ) :
    (outerFamWeightDbl n p c i : ℚ) = 2 * outerFamWeight n p c i := by
  unfold outerFamWeightDbl outerFamWeight
  split_ifs
  · exact outerZeroWeightDbl_eq_two_mul n p i
  · exact outerWeightDbl_eq_two_mul n p c i

/-- The zero class gets the zero-class weights. -/
theorem outerFamWeight_zero (n p i : ℕ) : outerFamWeight n p 0 i = outerZeroWeight n p i := by
  unfold outerFamWeight
  rw [if_pos rfl]

/-- A class `c ≥ 1` gets the outer weights (56). -/
theorem outerFamWeight_of_ne_zero (n p : ℕ) {c : ℕ} (hc : c ≠ 0) (i : ℕ) :
    outerFamWeight n p c i = outerWeight n p c i := by
  unfold outerFamWeight
  rw [if_neg hc]

/-! ## The remarks: nonpositive half-integer weights, and `⌊K/p⌋` under (52) -/

/-- Every weight of the family is at most `0`. -/
theorem outerFamWeight_nonpos (n p c i : ℕ) : outerFamWeight n p c i ≤ 0 := by
  unfold outerFamWeight
  split_ifs
  · exact outerZeroWeight_nonpos n p i
  · exact outerWeight_nonpos n p c i

/-- Every weight of the family is a half-integer. -/
theorem outerFamWeight_half_int (n p c i : ℕ) :
    ∃ k : ℤ, outerFamWeight n p c i = k / 2 :=
  ⟨outerFamWeightDbl n p c i, by rw [outerFamWeightDbl_eq_two_mul]; ring⟩

/-- Every doubled weight of the family is at most `0`. -/
theorem outerFamWeightDbl_nonpos (n p c i : ℕ) : outerFamWeightDbl n p c i ≤ 0 := by
  have h0 := outerFamWeight_nonpos n p c i
  have h : (outerFamWeightDbl n p c i : ℚ) ≤ 0 := by
    rw [outerFamWeightDbl_eq_two_mul]
    linarith
  exact_mod_cast h

/-- Under (52), `⌊K/p⌋ = 1` when `K < 2p`. -/
theorem OuterRange.mK_eq_one {n p : ℕ} (hR : OuterRange n p) (h : K n < 2 * p) :
    mK n p = 1 := by
  have h1 := hR.le_K
  unfold mK
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Under (52), `⌊K/p⌋ = 2` when `K ≥ 2p`. -/
theorem OuterRange.mK_eq_two {n p : ℕ} (hR : OuterRange n p) (h : 2 * p ≤ K n) :
    mK n p = 2 := by
  have h3 := hR.K_lt
  unfold mK
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-! ## Sums over the family -/

/-- A sum over the outer weight family, by classes. -/
theorem sum_outerIdx {M : Type*} [AddCommMonoid M] (n p : ℕ) (f : ℕ → ℕ → M) :
    ∑ ρ : outerIdx n p, f ρ.1 ρ.2
      = ∑ c ∈ range (mHalf p + 1), ∑ i ∈ range (outerLen n p c), f c i := by
  calc ∑ ρ : outerIdx n p, f ρ.1 ρ.2
      = ∑ c : Fin (mHalf p + 1), ∑ i : Fin (outerLen n p c), f c i :=
        Fintype.sum_sigma _
    _ = ∑ c ∈ range (mHalf p + 1), ∑ i ∈ range (outerLen n p c), f c i := by
        rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ i ∈ range (outerLen n p c), f c i)]
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Fin.sum_univ_eq_sum_range (fun i => f c i) _

/-- The family has `∑_{0 ≤ c ≤ m} outerLen n p c` members. -/
theorem card_outerIdx (n p : ℕ) :
    Fintype.card (outerIdx n p) = ∑ c ∈ range (mHalf p + 1), outerLen n p c := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun c => outerLen n p c) (mHalf p + 1)]

end ZetaSeven
