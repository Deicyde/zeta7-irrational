import ZetaSeven.OuterWeightFamily

/-!
# Outer weight sum (paper Section 4.2.3, equations (56)-(59), proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2.3 and the proof of Proposition 4.6:
"Applying Lemma 4.5 to the weights (56) and summing over classes yields `γ^out_p`". The paper
gives (59) without the count, deferring it to its `ζ(5)` predecessor; the count below is
reconstructed by this project.

Let `p` be a prime satisfying the outer-range hypothesis (52), `w` the outer weight family and
`z` its number of zero weights. Then `2 ∑ w - min(r_p, z) ≥ γ^out_p`:

* `outer_weight_sum`: the doubled form `∑ 2w - min(r_p, z) ≥ γ^out_p`, with the doubled
  integer weights `outerFamWeightDbl` that `ZetaSeven.rank_lemma` takes; its conclusion
  `∑ i, w i - ↑(min r z)` has this shape, so the outer estimate composes the two directly.
* `outer_weight_sum_rat`: the same bound for the weights `outerFamWeight` in `ℚ`, verbatim.
* `outer_weight_sum_eq_of_lt_two_mul`, `outer_weight_sum_eq_of_two_mul_le`: equality when
  `K < 2p`, and a margin of `3` when `K ≥ 2p`.
* The closed forms `2∑w = -9(K - p) + 8t_p - 1`, `z = p - 1 - N + u` when `K < 2p`
  (`sum_outerFamWeightDbl_of_lt_two_mul`, `card_zero_outerFamWeightDbl_of_lt_two_mul`), and
  `2∑w = -9(K - p) + 6 + 16N + 7t_p`, `z = p + u` when `K ≥ 2p`
  (`sum_outerFamWeightDbl_of_two_mul_le`, `card_zero_outerFamWeightDbl_of_two_mul_le`).
* The steps of the count: `N < p/3` (`OuterRange.three_mul_N_lt`); the only `j ≤ N` in the
  class `a` is `a` itself when `δ_a = 1`, that is `ℓ_N(a) = δ_a`
  (`OuterRange.ell_N_eq_classDelta`); the closed form of `ℓ_K(a)`
  (`OuterRange.ell_K_eq`) and `ℓ_K(a) ≤ 6` (`OuterRange.ell_K_le_six`);
  `∑_a (ℓ_K(a) - 2) = K - ⌊K/p⌋ - (p - 1)` (`OuterRange.sum_ell_K_sub_two`); and the
  contribution of a class to `2∑w` and to `z` (`sum_outerWeightDbl_delta_zero`,
  `card_zero_outerWeightDbl_delta_zero`, `sum_outerWeightDbl_delta_one`,
  `card_zero_outerWeightDbl_delta_one`).
-/

namespace ZetaSeven

open Finset

variable {n p : ℕ}

/-! ## The range facts under (52) -/

/-- Under (52), `p` is odd: `2m + 1 = p` for `m = (p - 1)/2`. -/
theorem OuterRange.two_mul_mHalf [hp : Fact p.Prime] (hR : OuterRange n p) :
    2 * mHalf p + 1 = p := by
  have h1 := hR.eleven_le
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · unfold mHalf
    omega

/-- Under (52), `N < p/3`, written `3N < p`. -/
theorem OuterRange.three_mul_N_lt (hR : OuterRange n p) : 3 * N n < p := by
  have h1 := hR.seven_mul_N_le
  have h2 := hR.eleven_le
  omega

/-- Under (52), `N ≤ m`: every `a ≤ N` with `a ≥ 1` is a class. -/
theorem OuterRange.N_le_mHalf [Fact p.Prime] (hR : OuterRange n p) : N n ≤ mHalf p := by
  have h1 := hR.three_mul_N_lt
  have h2 := hR.two_mul_mHalf
  omega

/-- Under (52), `⌊K/p⌋` is `1` or `2`. -/
theorem OuterRange.mK_eq_one_or_two (hR : OuterRange n p) : mK n p = 1 ∨ mK n p = 2 := by
  rcases lt_or_ge (K n) (2 * p) with h | h
  · exact Or.inl (hR.mK_eq_one h)
  · exact Or.inr (hR.mK_eq_two h)

/-- `K = p⌊K/p⌋ + v` (58). -/
theorem mul_mK_add_classV (n p : ℕ) : p * mK n p + classV n p = K n := by
  rw [classV_eq_mod]
  exact Nat.div_add_mod (K n) p

/-- `v < p`. -/
theorem classV_lt (n : ℕ) (hp : 0 < p) : classV n p < p := by
  rw [classV_eq_mod]
  exact Nat.mod_lt _ hp

/-! ## The class counts -/

/-- Under (52), the only `j ≤ N` in the class `a` (`1 ≤ a ≤ m`) is `a` itself when `δ_a = 1`,
and there is none when `δ_a = 0`: `ℓ_N(a) = δ_a`. -/
theorem OuterRange.ell_N_eq_classDelta [Fact p.Prime] (hR : OuterRange n p) {a : ℕ}
    (ha1 : 1 ≤ a) (ham : a ≤ mHalf p) : ell p (N n) a = classDelta n a := by
  have hm := hR.two_mul_mHalf
  have h3 := hR.three_mul_N_lt
  have hp0 : 0 < p := by omega
  obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique hp0).mpr
    (⟨by omega, by omega⟩ : N n + 1 + p * 0 = N n + 1 ∧ N n + 1 < p)
  rw [ell_eq_count hm (N n) a ha1 ham, hd, hmod]
  unfold classDelta
  split_ifs <;> omega

/-- Under (52), the class count of a class `1 ≤ a ≤ m` is
`ℓ_K(a) = 2⌊K/p⌋ + [a ≤ v] + [a ≥ p - v]`: the base value `2⌊K/p⌋`, which is `2` when
`K < 2p` and `4` when `K ≥ 2p` (`OuterRange.mK_eq_one`, `OuterRange.mK_eq_two`), plus one
if `a ≤ v` and one more if `a ≥ p - v`. -/
theorem OuterRange.ell_K_eq [Fact p.Prime] (hR : OuterRange n p) {a : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) :
    ell p (K n) a = 2 * mK n p + (if a ≤ classV n p then 1 else 0)
      + (if p - classV n p ≤ a then 1 else 0) := by
  have hm := hR.two_mul_mHalf
  have hp0 : 0 < p := by omega
  have hKv := mul_mK_add_classV n p
  have hv := classV_lt n hp0
  rw [ell_eq_count hm (K n) a ha1 ham]
  by_cases hv1 : classV n p + 1 < p
  · obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique hp0).mpr
      (⟨by omega, hv1⟩ : classV n p + 1 + p * mK n p = K n + 1 ∧ classV n p + 1 < p)
    rw [hd, hmod]
    split_ifs <;> omega
  · have hpq : p * (mK n p + 1) = p * mK n p + p := by ring
    obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique hp0).mpr
      (⟨by omega, hp0⟩ : 0 + p * (mK n p + 1) = K n + 1 ∧ 0 < p)
    rw [hd, hmod]
    split_ifs <;> omega

/-- Under (52), `ℓ_K(a) ≤ 6` for every class `1 ≤ a ≤ m`. -/
theorem OuterRange.ell_K_le_six [Fact p.Prime] (hR : OuterRange n p) {a : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) : ell p (K n) a ≤ 6 := by
  have hq := hR.mK_eq_one_or_two
  rw [hR.ell_K_eq ha1 ham]
  split_ifs <;> omega

/-- Under (52), `∑_{a=1}^m (ℓ_K(a) - 2) = K - ⌊K/p⌋ - (p - 1)`. -/
theorem OuterRange.sum_ell_K_sub_two [Fact p.Prime] (hR : OuterRange n p) :
    ∑ a ∈ Icc 1 (mHalf p), ((ell p (K n) a : ℤ) - 2) = (K n : ℤ) - mK n p - (p - 1) := by
  have hm := hR.two_mul_mHalf
  have hs : ∑ a ∈ Icc 1 (mHalf p), ell p (K n) a = K n - mK n p := sum_ell hm (K n)
  have hle : mK n p ≤ K n := Nat.div_le_self _ _
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hs, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul]
  omega

/-! ## The contribution of a class: the article's table -/

/-- A class with `δ = 0` and `2 ≤ ℓ ≤ 6` has `ℓ` weights, all those below `ℓ - 2` negative:
it contributes `-9(ℓ - 2)` to `2∑w`. -/
theorem sum_outerWeightDbl_delta_zero {l : ℕ} (h2 : 2 ≤ l) (h6 : l ≤ 6) :
    ∑ i ∈ range l, outerWeightDbl l 0 i = -9 * ((l : ℤ) - 2) := by
  interval_cases l <;> decide

/-- A class with `δ = 0` and `2 ≤ ℓ ≤ 6` has two zero weights. -/
theorem card_zero_outerWeightDbl_delta_zero {l : ℕ} (h2 : 2 ≤ l) (h6 : l ≤ 6) :
    ((range l).filter fun i => outerWeightDbl l 0 i = 0).card = 2 := by
  interval_cases l <;> decide

/-- A class with `δ = 1` has `ℓ - 1` weights; for `ℓ = 2, …, 6` it contributes
`0, -1, -2, -4, -6` to `2∑w`. -/
theorem sum_outerWeightDbl_delta_one :
    ∑ i ∈ range 1, outerWeightDbl 2 1 i = 0 ∧ ∑ i ∈ range 2, outerWeightDbl 3 1 i = -1 ∧
      ∑ i ∈ range 3, outerWeightDbl 4 1 i = -2 ∧ ∑ i ∈ range 4, outerWeightDbl 5 1 i = -4 ∧
      ∑ i ∈ range 5, outerWeightDbl 6 1 i = -6 := by
  decide

/-- A class with `δ = 1` and `ℓ = 2, …, 6` has `1, 1, 2, 2, 3` zero weights. -/
theorem card_zero_outerWeightDbl_delta_one :
    ((range 1).filter fun i => outerWeightDbl 2 1 i = 0).card = 1 ∧
      ((range 2).filter fun i => outerWeightDbl 3 1 i = 0).card = 1 ∧
      ((range 3).filter fun i => outerWeightDbl 4 1 i = 0).card = 2 ∧
      ((range 4).filter fun i => outerWeightDbl 5 1 i = 0).card = 2 ∧
      ((range 5).filter fun i => outerWeightDbl 6 1 i = 0).card = 3 := by
  decide

/-! ## The contribution of a class, in terms of `[a ≤ v]` and `[a ≥ p - v]` -/

/-- `[a ≤ v]`, the first extra term of the class count `ℓ_K(a)` (`OuterRange.ell_K_eq`). -/
def classLow (n p a : ℕ) : ℕ := if a ≤ classV n p then 1 else 0

/-- `[a ≥ p - v]`, the second extra term of the class count `ℓ_K(a)` (`OuterRange.ell_K_eq`). -/
def classHigh (n p a : ℕ) : ℕ := if p - classV n p ≤ a then 1 else 0

theorem classLow_le_one (n p a : ℕ) : classLow n p a ≤ 1 := by
  unfold classLow
  split_ifs <;> omega

theorem classHigh_le_one (n p a : ℕ) : classHigh n p a ≤ 1 := by
  unfold classHigh
  split_ifs <;> omega

theorem classDelta_le_one (n a : ℕ) : classDelta n a ≤ 1 := by
  unfold classDelta
  split_ifs <;> omega

/-- `ℓ_K(a) = 2⌊K/p⌋ + [a ≤ v] + [a ≥ p - v]`, with the indicators named. -/
theorem OuterRange.ell_K_eq_classLow [Fact p.Prime] (hR : OuterRange n p) {a : ℕ}
    (ha1 : 1 ≤ a) (ham : a ≤ mHalf p) :
    ell p (K n) a = 2 * mK n p + classLow n p a + classHigh n p a :=
  hR.ell_K_eq ha1 ham

/-- Under (52), `δ_a = 1` and `a ≥ p - v` give `a ≤ v`, since `a ≤ N < p - N`. -/
theorem OuterRange.classDelta_mul_classHigh_le (hR : OuterRange n p) (a : ℕ) :
    classDelta n a * classHigh n p a ≤ classLow n p a := by
  have h3 := hR.three_mul_N_lt
  unfold classDelta classHigh classLow
  split_ifs <;> omega

/-- A class with `ℓ = 2 + x + y` and indicator `d` contributes `-9(x + y) + 8(dx + dy)` to
`2∑w`. -/
theorem sum_outerWeightDbl_two_add {x y d : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hd : d ≤ 1) :
    ∑ i ∈ range (2 + x + y - d), outerWeightDbl (2 + x + y) d i
      = -9 * ((x : ℤ) + y) + 8 * ((d : ℤ) * x + (d : ℤ) * y) := by
  interval_cases x <;> interval_cases y <;> interval_cases d <;> decide

/-- A class with `ℓ = 2 + x + y` and indicator `d`, where `dy ≤ x`, has `2 - d + dy` zero
weights. -/
theorem sum_zero_outerWeightDbl_two_add {x y d : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hd : d ≤ 1)
    (hxy : d * y ≤ x) :
    ∑ i ∈ range (2 + x + y - d), (if outerWeightDbl (2 + x + y) d i = 0 then (1 : ℤ) else 0)
      = 2 - (d : ℤ) + (d : ℤ) * y := by
  interval_cases x <;> interval_cases y <;> interval_cases d <;> first | omega | decide

/-- A class with `ℓ = 4 + x + y` and indicator `d` contributes
`-9(2 + x + y) + 7(dx + dy) + 16d` to `2∑w`. -/
theorem sum_outerWeightDbl_four_add {x y d : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hd : d ≤ 1) :
    ∑ i ∈ range (4 + x + y - d), outerWeightDbl (4 + x + y) d i
      = -9 * (2 + (x : ℤ) + y) + (7 * ((d : ℤ) * x + (d : ℤ) * y) + 16 * (d : ℤ)) := by
  interval_cases x <;> interval_cases y <;> interval_cases d <;> decide

/-- A class with `ℓ = 4 + x + y` and indicator `d`, where `dy ≤ x`, has `2 + dy` zero
weights. -/
theorem sum_zero_outerWeightDbl_four_add {x y d : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hd : d ≤ 1)
    (hxy : d * y ≤ x) :
    ∑ i ∈ range (4 + x + y - d), (if outerWeightDbl (4 + x + y) d i = 0 then (1 : ℤ) else 0)
      = 2 + (d : ℤ) * y := by
  interval_cases x <;> interval_cases y <;> interval_cases d <;> first | omega | decide

/-- The family weights of a class `c ≥ 1` are the outer weights (56). -/
theorem outerFamWeightDbl_eq_outerWeightDbl (n p : ℕ) {c : ℕ} (hc : c ≠ 0) (i : ℕ) :
    outerFamWeightDbl n p c i = outerWeightDbl (ell p (K n) c) (classDelta n c) i := by
  unfold outerFamWeightDbl
  rw [ite_eq_right hc]

/-- Under (52) with `K < 2p`, the class `1 ≤ c ≤ m` contributes
`-9([c ≤ v] + [c ≥ p - v]) + 8(δ_c [c ≤ v] + δ_c [c ≥ p - v])` to `2∑w`. -/
theorem OuterRange.class_sum_of_lt_two_mul [Fact p.Prime] (hR : OuterRange n p)
    (h : K n < 2 * p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ∑ i ∈ range (ell p (K n) c - classDelta n c), outerFamWeightDbl n p c i
      = -9 * ((classLow n p c : ℤ) + classHigh n p c)
        + 8 * ((classDelta n c : ℤ) * classLow n p c
          + (classDelta n c : ℤ) * classHigh n p c) := by
  have hl : ell p (K n) c = 2 + classLow n p c + classHigh n p c := by
    have := hR.ell_K_eq_classLow hc1 hcm
    rw [hR.mK_eq_one h] at this
    omega
  simp only [outerFamWeightDbl_eq_outerWeightDbl n p (show c ≠ 0 by omega)]
  rw [hl]
  exact sum_outerWeightDbl_two_add (classLow_le_one n p c) (classHigh_le_one n p c)
    (classDelta_le_one n c)

/-- Under (52) with `K < 2p`, the class `1 ≤ c ≤ m` has `2 - δ_c + δ_c [c ≥ p - v]` zero
weights. -/
theorem OuterRange.class_zero_of_lt_two_mul [Fact p.Prime] (hR : OuterRange n p)
    (h : K n < 2 * p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ∑ i ∈ range (ell p (K n) c - classDelta n c),
        (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
      = 2 - (classDelta n c : ℤ) + (classDelta n c : ℤ) * classHigh n p c := by
  have hl : ell p (K n) c = 2 + classLow n p c + classHigh n p c := by
    have := hR.ell_K_eq_classLow hc1 hcm
    rw [hR.mK_eq_one h] at this
    omega
  simp only [outerFamWeightDbl_eq_outerWeightDbl n p (show c ≠ 0 by omega)]
  rw [hl]
  exact sum_zero_outerWeightDbl_two_add (classLow_le_one n p c) (classHigh_le_one n p c)
    (classDelta_le_one n c) (hR.classDelta_mul_classHigh_le c)

/-- Under (52) with `K ≥ 2p`, the class `1 ≤ c ≤ m` contributes
`-9(2 + [c ≤ v] + [c ≥ p - v]) + 7(δ_c [c ≤ v] + δ_c [c ≥ p - v]) + 16δ_c` to `2∑w`. -/
theorem OuterRange.class_sum_of_two_mul_le [Fact p.Prime] (hR : OuterRange n p)
    (h : 2 * p ≤ K n) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ∑ i ∈ range (ell p (K n) c - classDelta n c), outerFamWeightDbl n p c i
      = -9 * (2 + (classLow n p c : ℤ) + classHigh n p c)
        + (7 * ((classDelta n c : ℤ) * classLow n p c
          + (classDelta n c : ℤ) * classHigh n p c) + 16 * (classDelta n c : ℤ)) := by
  have hl : ell p (K n) c = 4 + classLow n p c + classHigh n p c := by
    have := hR.ell_K_eq_classLow hc1 hcm
    rw [hR.mK_eq_two h] at this
    omega
  simp only [outerFamWeightDbl_eq_outerWeightDbl n p (show c ≠ 0 by omega)]
  rw [hl]
  exact sum_outerWeightDbl_four_add (classLow_le_one n p c) (classHigh_le_one n p c)
    (classDelta_le_one n c)

/-- Under (52) with `K ≥ 2p`, the class `1 ≤ c ≤ m` has `2 + δ_c [c ≥ p - v]` zero
weights. -/
theorem OuterRange.class_zero_of_two_mul_le [Fact p.Prime] (hR : OuterRange n p)
    (h : 2 * p ≤ K n) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ∑ i ∈ range (ell p (K n) c - classDelta n c),
        (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
      = 2 + (classDelta n c : ℤ) * classHigh n p c := by
  have hl : ell p (K n) c = 4 + classLow n p c + classHigh n p c := by
    have := hR.ell_K_eq_classLow hc1 hcm
    rw [hR.mK_eq_two h] at this
    omega
  simp only [outerFamWeightDbl_eq_outerWeightDbl n p (show c ≠ 0 by omega)]
  rw [hl]
  exact sum_zero_outerWeightDbl_four_add (classLow_le_one n p c) (classHigh_le_one n p c)
    (classDelta_le_one n c) (hR.classDelta_mul_classHigh_le c)

/-! ## Sums over the classes -/

/-- Under (52), `∑_{c=1}^m ([c ≤ v] + [c ≥ p - v]) = v`, from `∑_c ℓ_K(c) = K - ⌊K/p⌋`. -/
theorem OuterRange.sum_classLow_add_classHigh [Fact p.Prime] (hR : OuterRange n p) :
    ∑ c ∈ Icc 1 (mHalf p), (classLow n p c + classHigh n p c) = classV n p := by
  have hm := hR.two_mul_mHalf
  have hs : ∑ c ∈ Icc 1 (mHalf p), ell p (K n) c = K n - mK n p := sum_ell hm (K n)
  have hsum : ∑ c ∈ Icc 1 (mHalf p), ell p (K n) c
      = ∑ c ∈ Icc 1 (mHalf p), (2 * mK n p + (classLow n p c + classHigh n p c)) :=
    Finset.sum_congr rfl fun c hc =>
      (hR.ell_K_eq_classLow (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2).trans
        (Nat.add_assoc _ _ _)
  rw [hs, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    smul_eq_mul] at hsum
  have hKv := mul_mK_add_classV n p
  rcases hR.mK_eq_one_or_two with hq | hq <;> rw [hq] at hsum hKv <;> omega

/-- Under (52), `∑_{c=1}^m δ_c = N`. -/
theorem OuterRange.sum_classDelta [Fact p.Prime] (hR : OuterRange n p) :
    ∑ c ∈ Icc 1 (mHalf p), classDelta n c = N n := by
  have hNm := hR.N_le_mHalf
  unfold classDelta
  rw [← Finset.card_filter]
  have h2 : (Icc 1 (mHalf p)).filter (fun c => c ≤ N n) = Icc 1 (N n) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h2, Nat.card_Icc, Nat.add_sub_cancel]

/-- Under (52), `∑_{c=1}^m δ_c [c ≤ v] = min(N, v)`. -/
theorem OuterRange.sum_classDelta_mul_classLow [Fact p.Prime] (hR : OuterRange n p) :
    ∑ c ∈ Icc 1 (mHalf p), classDelta n c * classLow n p c = min (N n) (classV n p) := by
  have hNm := hR.N_le_mHalf
  have h1 : ∀ c ∈ Icc 1 (mHalf p), classDelta n c * classLow n p c
      = if c ≤ min (N n) (classV n p) then 1 else 0 := by
    intro c _
    unfold classDelta classLow
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h1, ← Finset.card_filter]
  have h2 : (Icc 1 (mHalf p)).filter (fun c => c ≤ min (N n) (classV n p))
      = Icc 1 (min (N n) (classV n p)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h2, Nat.card_Icc, Nat.add_sub_cancel]

/-- Under (52), `∑_{c=1}^m δ_c [c ≥ p - v] = max(0, N + 1 - (p - v))`, which is `u`. -/
theorem OuterRange.sum_classDelta_mul_classHigh [Fact p.Prime] (hR : OuterRange n p) :
    ∑ c ∈ Icc 1 (mHalf p), classDelta n c * classHigh n p c = N n + 1 - (p - classV n p) := by
  have hNm := hR.N_le_mHalf
  have hv := classV_lt n (p := p) (by have := hR.eleven_le; omega)
  have h1 : ∀ c ∈ Icc 1 (mHalf p), classDelta n c * classHigh n p c
      = if p - classV n p ≤ c ∧ c ≤ N n then 1 else 0 := by
    intro c _
    unfold classDelta classHigh
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h1, ← Finset.card_filter]
  have h2 : (Icc 1 (mHalf p)).filter (fun c => p - classV n p ≤ c ∧ c ≤ N n)
      = Icc (p - classV n p) (N n) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h2, Nat.card_Icc]

/-! ## The zero class -/

/-- Under (52) with `K < 2p`, the zero class has the single doubled weight `-1`. -/
theorem OuterRange.sum_zero_class_of_lt_two_mul (hR : OuterRange n p) (h : K n < 2 * p) :
    ∑ i ∈ range (mK n p), outerFamWeightDbl n p 0 i = -1 := by
  rw [hR.mK_eq_one h, Finset.sum_range_one]
  simp [outerFamWeightDbl, outerZeroWeightDbl, h]

/-- Under (52) with `K < 2p`, the zero class has no zero weight. -/
theorem OuterRange.zero_class_zero_of_lt_two_mul (hR : OuterRange n p) (h : K n < 2 * p) :
    ∑ i ∈ range (mK n p), (if outerFamWeightDbl n p 0 i = 0 then (1 : ℤ) else 0) = 0 := by
  rw [hR.mK_eq_one h, Finset.sum_range_one]
  simp [outerFamWeightDbl, outerZeroWeightDbl, h]

/-- Under (52) with `K ≥ 2p`, the zero class has the doubled weights `-3, 0`. -/
theorem OuterRange.sum_zero_class_of_two_mul_le (hR : OuterRange n p) (h : 2 * p ≤ K n) :
    ∑ i ∈ range (mK n p), outerFamWeightDbl n p 0 i = -3 := by
  rw [hR.mK_eq_two h, Finset.sum_range_succ, Finset.sum_range_one]
  simp [outerFamWeightDbl, outerZeroWeightDbl, not_lt.mpr h]

/-- Under (52) with `K ≥ 2p`, the zero class has one zero weight. -/
theorem OuterRange.zero_class_zero_of_two_mul_le (hR : OuterRange n p) (h : 2 * p ≤ K n) :
    ∑ i ∈ range (mK n p), (if outerFamWeightDbl n p 0 i = 0 then (1 : ℤ) else 0) = 1 := by
  rw [hR.mK_eq_two h, Finset.sum_range_succ, Finset.sum_range_one]
  simp [outerFamWeightDbl, outerZeroWeightDbl, not_lt.mpr h]

/-- A sum over the outer weight family: the zero class and the classes `1 ≤ c ≤ m`. -/
theorem sum_outerIdx_eq {M : Type*} [AddCommMonoid M] (n p : ℕ) (f : ℕ → ℕ → M) :
    ∑ ρ : outerIdx n p, f ρ.1 ρ.2 = ∑ i ∈ range (mK n p), f 0 i
      + ∑ c ∈ Icc 1 (mHalf p), ∑ i ∈ range (ell p (K n) c - classDelta n c), f c i := by
  rw [sum_outerIdx, Finset.sum_range_eq_add_Ico _ (Nat.add_one_pos (mHalf p)),
    Finset.Ico_add_one_right_eq_Icc, outerLen_zero]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [outerLen_of_ne_zero n p (by simp only [Finset.mem_Icc] at hc; omega)]

/-! ## The closed forms of `2∑w` and `z` -/

/-- Under (52) with `K < 2p`: `2∑w = -9(K - p) + 8t_p - 1`. -/
theorem OuterRange.sum_outerFamWeightDbl_of_lt_two_mul [Fact p.Prime] (hR : OuterRange n p)
    (h : K n < 2 * p) :
    ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2
      = -9 * ((K n : ℤ) - p) + 8 * classT n p - 1 := by
  have hv := classV_lt n (p := p) (by have := hR.eleven_le; omega)
  have hKv := mul_mK_add_classV n p
  rw [hR.mK_eq_one h] at hKv
  have hcl : ∀ c ∈ Icc 1 (mHalf p),
      ∑ i ∈ range (ell p (K n) c - classDelta n c), outerFamWeightDbl n p c i
        = -9 * ((classLow n p c : ℤ) + classHigh n p c)
          + 8 * ((classDelta n c : ℤ) * classLow n p c
            + (classDelta n c : ℤ) * classHigh n p c) :=
    fun c hc => hR.class_sum_of_lt_two_mul h (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2
  have hc : ∑ c ∈ Icc 1 (mHalf p), (-9 * ((classLow n p c : ℤ) + classHigh n p c)
        + 8 * ((classDelta n c : ℤ) * classLow n p c
          + (classDelta n c : ℤ) * classHigh n p c))
      = -9 * ∑ c ∈ Icc 1 (mHalf p), ((classLow n p c : ℤ) + classHigh n p c)
        + 8 * (∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classLow n p c
          + ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have e1 : ∑ c ∈ Icc 1 (mHalf p), ((classLow n p c : ℤ) + classHigh n p c)
      = ((classV n p : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classLow_add_classHigh
  have e2 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classLow n p c
      = ((min (N n) (classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classLow
  have e3 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c
      = ((N n + 1 - (p - classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classHigh
  rw [sum_outerIdx_eq n p (outerFamWeightDbl n p), hR.sum_zero_class_of_lt_two_mul h,
    Finset.sum_congr rfl hcl, hc, e1, e2, e3]
  unfold classT classU
  omega

/-- Under (52) with `K < 2p`: `z = p - 1 - N + u`. -/
theorem OuterRange.card_zero_outerFamWeightDbl_of_lt_two_mul [Fact p.Prime]
    (hR : OuterRange n p) (h : K n < 2 * p) :
    ((univ.filter fun ρ : outerIdx n p => outerFamWeightDbl n p ρ.1 ρ.2 = 0).card : ℤ)
      = p - 1 - N n + classU n p := by
  have hm := hR.two_mul_mHalf
  have hv := classV_lt n (p := p) (by omega)
  have hsplit : (∑ ρ : outerIdx n p, if outerFamWeightDbl n p ρ.1 ρ.2 = 0 then (1 : ℤ) else 0)
      = ∑ i ∈ range (mK n p), (if outerFamWeightDbl n p 0 i = 0 then (1 : ℤ) else 0)
        + ∑ c ∈ Icc 1 (mHalf p), ∑ i ∈ range (ell p (K n) c - classDelta n c),
            (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0) :=
    sum_outerIdx_eq n p (fun c i => if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
  have hcl : ∀ c ∈ Icc 1 (mHalf p),
      ∑ i ∈ range (ell p (K n) c - classDelta n c),
          (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
        = 2 - (classDelta n c : ℤ) + (classDelta n c : ℤ) * classHigh n p c :=
    fun c hc => hR.class_zero_of_lt_two_mul h (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2
  have hc : ∑ c ∈ Icc 1 (mHalf p),
        (2 - (classDelta n c : ℤ) + (classDelta n c : ℤ) * classHigh n p c)
      = 2 * ((mHalf p : ℕ) : ℤ) - ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ)
        + ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have e0 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) = ((N n : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta
  have e3 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c
      = ((N n + 1 - (p - classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classHigh
  rw [Finset.natCast_card_filter, hsplit, hR.zero_class_zero_of_lt_two_mul h,
    Finset.sum_congr rfl hcl, hc, e0, e3]
  unfold classU
  omega

/-- Under (52) with `K ≥ 2p`: `2∑w = -9(K - p) + 6 + 16N + 7t_p`. -/
theorem OuterRange.sum_outerFamWeightDbl_of_two_mul_le [Fact p.Prime] (hR : OuterRange n p)
    (h : 2 * p ≤ K n) :
    ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2
      = -9 * ((K n : ℤ) - p) + 6 + 16 * N n + 7 * classT n p := by
  have hm := hR.two_mul_mHalf
  have hv := classV_lt n (p := p) (by omega)
  have hKv := mul_mK_add_classV n p
  rw [hR.mK_eq_two h] at hKv
  have hcl : ∀ c ∈ Icc 1 (mHalf p),
      ∑ i ∈ range (ell p (K n) c - classDelta n c), outerFamWeightDbl n p c i
        = -9 * (2 + (classLow n p c : ℤ) + classHigh n p c)
          + (7 * ((classDelta n c : ℤ) * classLow n p c
            + (classDelta n c : ℤ) * classHigh n p c) + 16 * (classDelta n c : ℤ)) :=
    fun c hc => hR.class_sum_of_two_mul_le h (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2
  have hc : ∑ c ∈ Icc 1 (mHalf p), (-9 * (2 + (classLow n p c : ℤ) + classHigh n p c)
        + (7 * ((classDelta n c : ℤ) * classLow n p c
          + (classDelta n c : ℤ) * classHigh n p c) + 16 * (classDelta n c : ℤ)))
      = -18 * ((mHalf p : ℕ) : ℤ)
        + -9 * ∑ c ∈ Icc 1 (mHalf p), ((classLow n p c : ℤ) + classHigh n p c)
        + 7 * (∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classLow n p c
          + ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c)
        + 16 * ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add, Finset.sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have e0 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) = ((N n : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta
  have e1 : ∑ c ∈ Icc 1 (mHalf p), ((classLow n p c : ℤ) + classHigh n p c)
      = ((classV n p : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classLow_add_classHigh
  have e2 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classLow n p c
      = ((min (N n) (classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classLow
  have e3 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c
      = ((N n + 1 - (p - classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classHigh
  rw [sum_outerIdx_eq n p (outerFamWeightDbl n p), hR.sum_zero_class_of_two_mul_le h,
    Finset.sum_congr rfl hcl, hc, e0, e1, e2, e3]
  unfold classT classU
  omega

/-- Under (52) with `K ≥ 2p`: `z = p + u`. -/
theorem OuterRange.card_zero_outerFamWeightDbl_of_two_mul_le [Fact p.Prime]
    (hR : OuterRange n p) (h : 2 * p ≤ K n) :
    ((univ.filter fun ρ : outerIdx n p => outerFamWeightDbl n p ρ.1 ρ.2 = 0).card : ℤ)
      = p + classU n p := by
  have hm := hR.two_mul_mHalf
  have hv := classV_lt n (p := p) (by omega)
  have hsplit : (∑ ρ : outerIdx n p, if outerFamWeightDbl n p ρ.1 ρ.2 = 0 then (1 : ℤ) else 0)
      = ∑ i ∈ range (mK n p), (if outerFamWeightDbl n p 0 i = 0 then (1 : ℤ) else 0)
        + ∑ c ∈ Icc 1 (mHalf p), ∑ i ∈ range (ell p (K n) c - classDelta n c),
            (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0) :=
    sum_outerIdx_eq n p (fun c i => if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
  have hcl : ∀ c ∈ Icc 1 (mHalf p),
      ∑ i ∈ range (ell p (K n) c - classDelta n c),
          (if outerFamWeightDbl n p c i = 0 then (1 : ℤ) else 0)
        = 2 + (classDelta n c : ℤ) * classHigh n p c :=
    fun c hc => hR.class_zero_of_two_mul_le h (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2
  have hc : ∑ c ∈ Icc 1 (mHalf p), (2 + (classDelta n c : ℤ) * classHigh n p c)
      = 2 * ((mHalf p : ℕ) : ℤ)
        + ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul]
    ring
  have e3 : ∑ c ∈ Icc 1 (mHalf p), (classDelta n c : ℤ) * classHigh n p c
      = ((N n + 1 - (p - classV n p) : ℕ) : ℤ) := by
    exact_mod_cast hR.sum_classDelta_mul_classHigh
  rw [Finset.natCast_card_filter, hsplit, hR.zero_class_zero_of_two_mul_le h,
    Finset.sum_congr rfl hcl, hc, e3]
  unfold classU
  omega

/-! ## The weight sum -/

/-- Under (52) with `K < 2p`, the bound holds with equality:
`2∑w - min(r_p, z) = γ^out_p`, with doubled weights. -/
theorem OuterRange.outer_weight_sum_eq_of_lt_two_mul [Fact p.Prime] (hR : OuterRange n p)
    (h : K n < 2 * p) :
    ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2
      - (min (rankCorr n p) (univ.filter fun ρ : outerIdx n p =>
          outerFamWeightDbl n p ρ.1 ρ.2 = 0).card : ℕ) = gammaOut n p := by
  have hs := hR.sum_outerFamWeightDbl_of_lt_two_mul h
  have hz := hR.card_zero_outerFamWeightDbl_of_lt_two_mul h
  rw [gammaOut_of_lt_two_mul hR.le_K h]
  omega

/-- Under (52) with `K ≥ 2p`, the bound holds with a margin of `3`:
`2∑w - min(r_p, z) = γ^out_p + 3`, with doubled weights. -/
theorem OuterRange.outer_weight_sum_eq_of_two_mul_le [Fact p.Prime] (hR : OuterRange n p)
    (h : 2 * p ≤ K n) :
    ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2
      - (min (rankCorr n p) (univ.filter fun ρ : outerIdx n p =>
          outerFamWeightDbl n p ρ.1 ρ.2 = 0).card : ℕ) = gammaOut n p + 3 := by
  have hs := hR.sum_outerFamWeightDbl_of_two_mul_le h
  have hz := hR.card_zero_outerFamWeightDbl_of_two_mul_le h
  rw [gammaOut_of_two_mul_le h]
  omega

/-- **Outer weight sum.** Let `p` be a prime satisfying the outer-range hypothesis (52), let
`w` be the outer weight family and `z` its number of zero weights. Then
`2∑w - min(r_p, z) ≥ γ^out_p`. The weights are doubled (`outerFamWeightDbl`, twice
`outerFamWeight` by `outerFamWeightDbl_eq_two_mul`), so `∑ 2w = 2∑w`, and a weight is zero
exactly when its double is; this is the form of the conclusion of `ZetaSeven.rank_lemma`.
`outer_weight_sum_rat` states the bound for the weights in `ℚ`. -/
theorem outer_weight_sum [Fact p.Prime] (hR : OuterRange n p) :
    gammaOut n p ≤ ∑ ρ : outerIdx n p, outerFamWeightDbl n p ρ.1 ρ.2
      - (min (rankCorr n p) (univ.filter fun ρ : outerIdx n p =>
          outerFamWeightDbl n p ρ.1 ρ.2 = 0).card : ℕ) := by
  rcases lt_or_ge (K n) (2 * p) with h | h
  · exact (hR.outer_weight_sum_eq_of_lt_two_mul h).ge
  · have := hR.outer_weight_sum_eq_of_two_mul_le h
    omega

/-- **Outer weight sum**, for the weights in `ℚ`: under (52), with `w` the outer weight family
and `z` its number of zero weights, `2∑w - min(r_p, z) ≥ γ^out_p`. -/
theorem outer_weight_sum_rat [Fact p.Prime] (hR : OuterRange n p) :
    (gammaOut n p : ℚ) ≤ 2 * ∑ ρ : outerIdx n p, outerFamWeight n p ρ.1 ρ.2
      - (min (rankCorr n p) (univ.filter fun ρ : outerIdx n p =>
          outerFamWeight n p ρ.1 ρ.2 = 0).card : ℕ) := by
  have h := outer_weight_sum hR
  have hsum : (∑ ρ : outerIdx n p, (outerFamWeightDbl n p ρ.1 ρ.2 : ℚ))
      = 2 * ∑ ρ : outerIdx n p, outerFamWeight n p ρ.1 ρ.2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => outerFamWeightDbl_eq_two_mul n p _ _
  have hz : (univ.filter fun ρ : outerIdx n p => outerFamWeight n p ρ.1 ρ.2 = 0)
      = univ.filter fun ρ : outerIdx n p => outerFamWeightDbl n p ρ.1 ρ.2 = 0 := by
    refine Finset.filter_congr fun ρ _ => ?_
    have e := outerFamWeightDbl_eq_two_mul n p ρ.1 ρ.2
    constructor
    · intro h0
      rw [h0, mul_zero] at e
      exact_mod_cast e
    · intro h0
      rw [h0, Int.cast_zero] at e
      linarith
  rw [hz, ← hsum]
  exact_mod_cast h

end ZetaSeven
