import ZetaSeven.OuterClassRows

/-!
# Outer class basis (paper Section 4.2, proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2, proof of Proposition 4.6: "Together with the
zero-class rows, these form a `ℤ_p`-unimodular basis." The paper gives no proof, since it defers
the basis to its `ζ(5)` predecessor; the statement and the proof below are reconstructed by this
project.

Let `p` be a prime satisfying the outer-range hypothesis (52). The outer class rows
`outerRow n p ρ`, indexed by the index type `outerIdx n p` of the outer weight family, are
exactly `h` integer polynomials of degree less than `h`, and for every enumeration of the rows
the integer matrix `U` of their coefficients in the monomial basis `1, t, …, t^{h-1}` has
`det U` prime to `p`:

* `outer_class_basis`: the three claims together;
* `OuterRange.card_outerIdx_eq_hDim`: there are `h` rows;
* `OuterRange.natDegree_outerRow_lt`: every row has degree less than `h`;
* `OuterRange.outerRow_unimodular`: `p ∤ det U`.

The steps of the proof:

* `|S_c| = ℓ_K(c) - δ_c` for `1 ≤ c ≤ m` and `|S_0| = ⌊K/p⌋`, that is `|S_c|` is the number of
  pairs of the class `c` (`OuterRange.card_outerClassSet_of_ne_zero`,
  `OuterRange.card_outerClassSet_zero`, `OuterRange.card_outerClassSet`), and
  `∑_{0 ≤ c ≤ m} |S_c| = K - N = h` (`OuterRange.sum_card_outerClassSet`);
* `E_c` has degree `ℓ_K(c) - 2` (`OuterRange.card_filter_outerClassSet_add_two`), so `q_{c,i}`
  has degree `i` (`OuterRange.natDegree_outerQ`) and the row of `(c, i)` has degree
  `∑_{d ≠ c} |S_d| + i` (`OuterRange.natDegree_outerRowPoly`);
* modulo `p`, `F_c ≡ (t + c²)^{|S_c|}` and `E_c ≡ (t + c²)^{ℓ_K(c) - 2}`
  (`map_outerClassPoly`, `map_outerHighPoly`, `map_outerCofactor`), so `q_{c,i} ≡ (t + c²)^i`
  (`OuterRange.map_outerQ`) and the row of `(c, i)` reduces to
  `∏_{d ≠ c} (t + d²)^{|S_d|} (t + c²)^i` (`OuterRange.map_outerRowPoly`);
* the reduced rows are linearly independent over `𝔽_p`, by the Chinese remainder decomposition
  for the pairwise coprime powers of `t + d²` (`OuterRange.linearIndependent_map_outerRow`), so
  the reduced matrix `U mod p` is invertible (`OuterRange.det_map_outerRow_ne_zero`).
-/

namespace ZetaSeven

open Polynomial Finset

variable {n p : ℕ}

/-! ## The class sets under (52) -/

/-- Under (52), `p` is odd: `2m + 1 = p`. -/
private theorem two_mul_mHalf_add_one [hp : Fact p.Prime] (hR : OuterRange n p) :
    2 * mHalf p + 1 = p := by
  have h1 := hR.eleven_le
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · unfold mHalf
    omega

/-- Under (52), `N < p/3`. -/
private theorem three_mul_N_lt_of_outerRange (hR : OuterRange n p) : 3 * N n < p := by
  have h1 := hR.seven_mul_N_le
  have h2 := hR.eleven_le
  omega

/-- `ℓ_B(c) = ℓ_A(c) + #{A < j ≤ B : j ≡ ±c (mod p)}` for `A ≤ B`. -/
private theorem ell_eq_ell_add_card {A B : ℕ} (c : ℕ) (hAB : A ≤ B) :
    ell p B c = ell p A c + ((Icc (A + 1) B).filter
      fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c).card := by
  unfold ell
  rw [← card_union_of_disjoint]
  · congr 1
    ext j
    simp only [mem_union, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hj : j ≤ A
      · exact Or.inl ⟨⟨h1, hj⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  · refine disjoint_left.mpr fun j hj1 hj2 => ?_
    simp only [mem_filter, mem_Icc] at hj1 hj2
    omega

/-- Under (52), `ℓ_N(c) = δ_c` for a class `1 ≤ c ≤ m`: the only `j ≤ N` congruent to `±c` is
`c` itself, when `c ≤ N`. -/
private theorem ell_N_eq_classDelta_of_outerRange [Fact p.Prime] (hR : OuterRange n p) {c : ℕ}
    (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) : ell p (N n) c = classDelta n c := by
  have hm := two_mul_mHalf_add_one hR
  have h3 := three_mul_N_lt_of_outerRange hR
  rw [ell_eq_count hm (N n) c hc1 hcm, Nat.div_eq_of_lt (by omega : N n + 1 < p),
    Nat.mod_eq_of_lt (by omega : N n + 1 < p)]
  unfold classDelta
  split_ifs <;> omega

/-- `ℓ_p(c) = 2` for a class `1 ≤ c ≤ m`: the `j ≤ p` congruent to `±c` are `c` and `p - c`. -/
private theorem ell_self_eq_two [Fact p.Prime] (hR : OuterRange n p) {c : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) : ell p p c = 2 := by
  have hm := two_mul_mHalf_add_one hR
  have hp0 : 0 < p := by omega
  obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique hp0).mpr
    (⟨by omega, by omega⟩ : 1 + p * 1 = p + 1 ∧ 1 < p)
  rw [ell_eq_count hm p c hc1 hcm, hd, hmod]
  split_ifs <;> omega

/-- Under (52), `|S_c| = ℓ_K(c) - δ_c` for a class `1 ≤ c ≤ m`. -/
theorem OuterRange.card_outerClassSet_of_ne_zero [Fact p.Prime] (hR : OuterRange n p) {c : ℕ}
    (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    (outerClassSet n p c).card = ell p (K n) c - classDelta n c := by
  have h3 := three_mul_N_lt_of_outerRange hR
  have hpK := hR.le_K
  have h := ell_eq_ell_add_card (p := p) c (show N n ≤ K n by omega)
  rw [ell_N_eq_classDelta_of_outerRange hR hc1 hcm] at h
  have h' : ell p (K n) c = classDelta n c + (outerClassSet n p c).card := h
  omega

/-- Under (52), `|S_0| = ⌊K/p⌋`: the multiples of `p` in `(N, K]` are those in `(0, K]`. -/
theorem OuterRange.card_outerClassSet_zero (hR : OuterRange n p) :
    (outerClassSet n p 0).card = mK n p := by
  have h3 := three_mul_N_lt_of_outerRange hR
  rw [outerClassSet_zero, mK, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨by omega, h2⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    have := Nat.le_of_dvd h1 h4
    exact ⟨⟨by omega, h2⟩, h4⟩

/-- Under (52), `|S_c|` is the number of pairs of the class `c` in the outer weight family, for
every `0 ≤ c ≤ m`. -/
theorem OuterRange.card_outerClassSet [Fact p.Prime] (hR : OuterRange n p) {c : ℕ}
    (hcm : c ≤ mHalf p) : (outerClassSet n p c).card = outerLen n p c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [outerLen_zero, hR.card_outerClassSet_zero]
  · rw [outerLen_of_ne_zero n p (by omega), hR.card_outerClassSet_of_ne_zero (by omega) hcm]

/-- Under (52), `∑_{0 ≤ c ≤ m} |S_c| = K - N = h`. -/
theorem OuterRange.sum_card_outerClassSet [Fact p.Prime] (hR : OuterRange n p) :
    ∑ c ∈ range (mHalf p + 1), (outerClassSet n p c).card = hDim n := by
  have hm := two_mul_mHalf_add_one hR
  have h3 := three_mul_N_lt_of_outerRange hR
  have hpK := hR.le_K
  have hNK : N n ≤ K n := by omega
  have hsplit : ∑ c ∈ Icc 1 (mHalf p), ell p (K n) c
      = ∑ c ∈ Icc 1 (mHalf p), ell p (N n) c
        + ∑ c ∈ Icc 1 (mHalf p), (outerClassSet n p c).card := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun c _ => ell_eq_ell_add_card c hNK
  rw [sum_ell hm, sum_ell hm, Nat.div_eq_of_lt (by omega : N n < p)] at hsplit
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < mHalf p + 1), Finset.Ico_add_one_right_eq_Icc,
    hR.card_outerClassSet_zero]
  have hdiv : K n / p ≤ K n := Nat.div_le_self _ _
  have hh : hDim n = K n - N n := by
    unfold hDim K N
    omega
  unfold mK
  omega

/-- Under (52), `|{j ∈ S_c : j > p}| + 2 = ℓ_K(c)` for a class `1 ≤ c ≤ m`: the elements of the
class `±c` in `[1, K]` that are at most `p` are `c` and `p - c`, and all those above `p` lie in
`S_c`. So `E_c` has degree `ℓ_K(c) - 2`. -/
theorem OuterRange.card_filter_outerClassSet_add_two [Fact p.Prime] (hR : OuterRange n p)
    {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) :
    ((outerClassSet n p c).filter (fun j => p < j)).card + 2 = ell p (K n) c := by
  have h3 := three_mul_N_lt_of_outerRange hR
  have h := ell_eq_ell_add_card (p := p) c hR.le_K
  rw [ell_self_eq_two hR hc1 hcm] at h
  have hset : (outerClassSet n p c).filter (fun j => p < j)
      = (Icc (p + 1) (K n)).filter
          fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c := by
    ext j
    simp only [outerClassSet, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨_, h2⟩, h4⟩, h5⟩
      exact ⟨⟨by omega, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      exact ⟨⟨⟨by omega, h2⟩, h4⟩, by omega⟩
  rw [hset]
  omega

/-! ## The degrees of the rows -/

/-- Under (52), `q_{c,i}` has degree `i` for a class `1 ≤ c ≤ m`: in the second case `E_c` has
degree `ℓ_K(c) - 2`. -/
theorem OuterRange.natDegree_outerQ [Fact p.Prime] (hR : OuterRange n p) {c : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) (i : ℕ) : (outerQ n p c i).natDegree = i := by
  have he := hR.card_filter_outerClassSet_add_two hc1 hcm
  by_cases h : i < ell p (K n) c - 2
  · exact natDegree_outerQ_of_lt h
  · rw [natDegree_outerQ_of_le (not_lt.mp h)]
    omega

/-- Under (52), the row of the pair `(c, i)`, `0 ≤ c ≤ m`, has degree `∑_{d ≠ c} |S_d| + i`. -/
theorem OuterRange.natDegree_outerRowPoly [Fact p.Prime] (hR : OuterRange n p) {c : ℕ}
    (hcm : c ≤ mHalf p) (i : ℕ) :
    (outerRowPoly n p c i).natDegree
      = (∑ d ∈ (range (mHalf p + 1)).erase c, (outerClassSet n p d).card) + i := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [natDegree_outerRowPoly_zero, natDegree_outerCofactor]
  · rw [natDegree_outerRowPoly_of_ne_zero n p (by omega), natDegree_outerCofactor,
      hR.natDegree_outerQ (by omega) hcm]

/-- Under (52), every outer class row has degree less than `h`. -/
theorem OuterRange.natDegree_outerRow_lt [Fact p.Prime] (hR : OuterRange n p)
    (ρ : outerIdx n p) : (outerRow n p ρ).natDegree < hDim n := by
  have hcm : (ρ.1 : ℕ) ≤ mHalf p := by
    have := ρ.1.isLt
    omega
  have hi : (ρ.2 : ℕ) < (outerClassSet n p ρ.1).card := by
    rw [hR.card_outerClassSet hcm]
    exact ρ.2.isLt
  have hsum := hR.sum_card_outerClassSet
  rw [← add_sum_erase _ _ (mem_range.mpr ρ.1.isLt)] at hsum
  rw [outerRow, hR.natDegree_outerRowPoly hcm]
  omega

/-- Under (52), there are exactly `h` outer class rows. -/
theorem OuterRange.card_outerIdx_eq_hDim [Fact p.Prime] (hR : OuterRange n p) :
    Fintype.card (outerIdx n p) = hDim n := by
  rw [card_outerIdx, ← hR.sum_card_outerClassSet]
  refine sum_congr rfl fun c hc => ?_
  exact (hR.card_outerClassSet (by have := mem_range.mp hc; omega)).symm

/-! ## The rows modulo `p` -/

/-- For `j ∈ S_c`, `j² ≡ c² (mod p)`. -/
private theorem sq_eq_of_mem_outerClassSet {c j : ℕ} (hj : j ∈ outerClassSet n p c) :
    (j : ZMod p) ^ 2 = (c : ZMod p) ^ 2 := by
  rcases (mem_outerClassSet.mp hj).2 with h | h
  · have h' := (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr h
    push_cast at h'
    rw [sub_eq_zero.mp h']
  · have h' := (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr h
    push_cast at h'
    rw [eq_neg_of_add_eq_zero_left h', neg_sq]

/-- The factor `t + x²` modulo `p`. -/
private theorem map_X_add_C_natCast_sq (p x : ℕ) :
    (X + C ((x : ℤ) ^ 2)).map (Int.castRingHom (ZMod p)) = X + C ((x : ZMod p) ^ 2) := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, map_pow, map_natCast]

/-- Modulo `p`, `F_c ≡ (t + c²)^{|S_c|}`. -/
theorem map_outerClassPoly (n p c : ℕ) :
    (outerClassPoly n p c).map (Int.castRingHom (ZMod p))
      = (X + C ((c : ZMod p) ^ 2)) ^ (outerClassSet n p c).card := by
  rw [outerClassPoly, Polynomial.map_prod, ← Finset.prod_const]
  refine prod_congr rfl fun j hj => ?_
  rw [map_X_add_C_natCast_sq, sq_eq_of_mem_outerClassSet hj]

/-- Modulo `p`, `E_c ≡ (t + c²)^{|{j ∈ S_c : j > p}|}`. -/
theorem map_outerHighPoly (n p c : ℕ) :
    (outerHighPoly n p c).map (Int.castRingHom (ZMod p))
      = (X + C ((c : ZMod p) ^ 2)) ^ ((outerClassSet n p c).filter (fun j => p < j)).card := by
  rw [outerHighPoly, Polynomial.map_prod, ← Finset.prod_const]
  refine prod_congr rfl fun j hj => ?_
  rw [map_X_add_C_natCast_sq, sq_eq_of_mem_outerClassSet (mem_filter.mp hj).1]

/-- Modulo `p`, `P_c ≡ ∏_{0 ≤ d ≤ m, d ≠ c} (t + d²)^{|S_d|}`. -/
theorem map_outerCofactor (n p c : ℕ) :
    (outerCofactor n p c).map (Int.castRingHom (ZMod p))
      = ∏ d ∈ (range (mHalf p + 1)).erase c,
          (X + C ((d : ZMod p) ^ 2)) ^ (outerClassSet n p d).card := by
  rw [outerCofactor, Polynomial.map_prod]
  exact prod_congr rfl fun d _ => map_outerClassPoly n p d

/-- Under (52), modulo `p`, `q_{c,i} ≡ (t + c²)^i` for a class `1 ≤ c ≤ m`. -/
theorem OuterRange.map_outerQ [Fact p.Prime] (hR : OuterRange n p) {c : ℕ} (hc1 : 1 ≤ c)
    (hcm : c ≤ mHalf p) (i : ℕ) :
    (outerQ n p c i).map (Int.castRingHom (ZMod p)) = (X + C ((c : ZMod p) ^ 2)) ^ i := by
  have he := hR.card_filter_outerClassSet_add_two hc1 hcm
  by_cases h : i < ell p (K n) c - 2
  · rw [outerQ_of_lt h, Polynomial.map_pow, map_X_add_C_natCast_sq]
  · rw [outerQ_of_le (not_lt.mp h), Polynomial.map_mul, map_outerHighPoly, Polynomial.map_pow,
      map_X_add_C_natCast_sq, ← pow_add]
    congr 1
    omega

/-- Under (52), modulo `p` the row of the pair `(c, i)`, `0 ≤ c ≤ m`, is
`∏_{0 ≤ d ≤ m, d ≠ c} (t + d²)^{|S_d|} (t + c²)^i`. -/
theorem OuterRange.map_outerRowPoly [Fact p.Prime] (hR : OuterRange n p) {c : ℕ}
    (hcm : c ≤ mHalf p) (i : ℕ) :
    (outerRowPoly n p c i).map (Int.castRingHom (ZMod p))
      = (∏ d ∈ (range (mHalf p + 1)).erase c,
          (X + C ((d : ZMod p) ^ 2)) ^ (outerClassSet n p d).card)
        * (X + C ((c : ZMod p) ^ 2)) ^ i := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [outerRowPoly_zero, Polynomial.map_mul, map_outerCofactor, Polynomial.map_pow,
      Polynomial.map_X]
    congr 1
    simp
  · rw [outerRowPoly_of_ne_zero n p (by omega), Polynomial.map_mul, map_outerCofactor,
      hR.map_outerQ (by omega) hcm]

/-! ## The Chinese remainder basis modulo `p` -/

/-- The squares `c²`, `0 ≤ c ≤ m`, are distinct modulo `p`. -/
private theorem natCast_sq_ne_of_le [Fact p.Prime] (hm : 2 * mHalf p + 1 = p) {a c : ℕ}
    (ha : a ≤ mHalf p) (hc : c ≤ mHalf p) (hac : c ≠ a) :
    (c : ZMod p) ^ 2 ≠ (a : ZMod p) ^ 2 := by
  intro h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h'
    exact hac h'
  · have h2 : ((c + a : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add, h', neg_add_cancel]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega

/-- The Chinese remainder basis: for `a_0, …, a_m` in a field with `a_c ≠ a_d` for `c ≠ d`, and
exponents `len c ≤ L c`, the polynomials `∏_{d ≠ c} (t + a_d)^{L d} (t + a_c)^i`,
`0 ≤ c ≤ m`, `0 ≤ i < len c`, are linearly independent. -/
private theorem linearIndependent_crt {F : Type*} [Field F] (m : ℕ) (a : ℕ → F)
    (L len : ℕ → ℕ) (ha : ∀ c d, c ≤ m → d ≤ m → c ≠ d → a c ≠ a d)
    (hlen : ∀ c, c ≤ m → len c ≤ L c) :
    LinearIndependent F fun ρ : (Σ c : Fin (m + 1), Fin (len c)) =>
      (∏ d ∈ (range (m + 1)).erase ρ.1, (X + C (a d)) ^ L d) * (X + C (a ρ.1)) ^ (ρ.2 : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg ρ0
  obtain ⟨a0, i0⟩ := ρ0
  have ha0 : (a0 : ℕ) ≤ m := by
    have := a0.isLt
    omega
  rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at hg
  dsimp only at hg
  have hdvd : (X + C (a a0)) ^ L a0 ∣
      ∑ c ∈ Finset.univ.erase a0, ∑ i : Fin (len c),
        g ⟨c, i⟩ • ((∏ d ∈ (range (m + 1)).erase c, (X + C (a d)) ^ L d)
          * (X + C (a c)) ^ (i : ℕ)) := by
    refine Finset.dvd_sum fun c hc => Finset.dvd_sum fun i _ => ?_
    rw [Polynomial.smul_eq_C_mul]
    refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem
      (fun d : ℕ => (X + C (a d)) ^ L d) ?_) _) _
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hc).1 (Fin.ext h.symm),
      Finset.mem_range.mpr a0.isLt⟩
  have hsplit : ∑ i : Fin (len a0), g ⟨a0, i⟩ •
        ((∏ d ∈ (range (m + 1)).erase a0, (X + C (a d)) ^ L d) * (X + C (a a0)) ^ (i : ℕ))
      = (∏ d ∈ (range (m + 1)).erase a0, (X + C (a d)) ^ L d)
        * ∑ i : Fin (len a0), g ⟨a0, i⟩ • (X + C (a a0)) ^ (i : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm]
  have hdvd2 : (X + C (a a0)) ^ L a0 ∣
      (∏ d ∈ (range (m + 1)).erase a0, (X + C (a d)) ^ L d)
        * ∑ i : Fin (len a0), g ⟨a0, i⟩ • (X + C (a a0)) ^ (i : ℕ) := by
    rw [← hsplit, eq_neg_of_add_eq_zero_left hg]
    exact (dvd_neg).mpr hdvd
  have hcop : IsCoprime ((X + C (a a0)) ^ L a0)
      (∏ d ∈ (range (m + 1)).erase a0, (X + C (a d)) ^ L d) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun d hd => IsCoprime.pow_right ?_)
    obtain ⟨hda, hdr⟩ := Finset.mem_erase.mp hd
    have hdm : d ≤ m := by
      have := Finset.mem_range.mp hdr
      omega
    rw [← sub_neg_eq_add, ← sub_neg_eq_add X, ← C_neg, ← C_neg]
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [sub_eq_add_neg, neg_neg]
    exact isUnit_iff_ne_zero.mpr fun h => ha d a0 hdm ha0 hda (by linear_combination h)
  have hQdvd := hcop.dvd_of_dvd_mul_left hdvd2
  have hmonic : (X + C (a a0)).Monic := monic_X_add_C _
  have hL : len a0 ≤ L a0 := hlen a0 ha0
  have hQ0 : ∑ i : Fin (len a0), g ⟨a0, i⟩ • (X + C (a a0)) ^ (i : ℕ) = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hQdvd ?_
    rw [hmonic.natDegree_pow, natDegree_X_add_C, mul_one]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := len a0 - 1)
      fun i _ => ?_) (by have := i0.isLt; omega)
    refine (natDegree_smul_le _ _).trans (natDegree_pow_le.trans ?_)
    rw [natDegree_X_add_C, mul_one]
    have := i.isLt
    omega
  have hcomp := congrArg (fun q : F[X] => (q.comp (X - C (a a0))).coeff i0) hQ0
  simp only [Polynomial.sum_comp, smul_comp, pow_comp, add_comp, X_comp, C_comp, sub_add_cancel,
    finsetSum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Fin.val_inj, zero_comp, coeff_zero] at hcomp
  rwa [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i0)] at hcomp

/-- Under (52), the outer class rows are linearly independent modulo `p`: the reduced rows are
the Chinese remainder basis for the pairwise coprime powers `(t + d²)^{|S_d|}`, `0 ≤ d ≤ m`. -/
theorem OuterRange.linearIndependent_map_outerRow [Fact p.Prime] (hR : OuterRange n p) :
    LinearIndependent (ZMod p)
      fun ρ : outerIdx n p => (outerRow n p ρ).map (Int.castRingHom (ZMod p)) := by
  have hm := two_mul_mHalf_add_one hR
  have hfun : (fun ρ : outerIdx n p => (outerRow n p ρ).map (Int.castRingHom (ZMod p)))
      = fun ρ : outerIdx n p =>
        (∏ d ∈ (range (mHalf p + 1)).erase ρ.1,
          (X + C ((d : ZMod p) ^ 2)) ^ (outerClassSet n p d).card)
          * (X + C (((ρ.1 : ℕ) : ZMod p) ^ 2)) ^ (ρ.2 : ℕ) := by
    funext ρ
    exact hR.map_outerRowPoly (by have := ρ.1.isLt; omega) ρ.2
  rw [hfun]
  exact linearIndependent_crt (mHalf p) (fun d => (d : ZMod p) ^ 2)
    (fun d => (outerClassSet n p d).card) (outerLen n p)
    (fun c d hc hd hcd => natCast_sq_ne_of_le hm hd hc hcd)
    (fun c hc => (hR.card_outerClassSet hc).ge)

/-- Under (52), for every enumeration `e` of the rows, the coefficient matrix of the rows modulo
`p` in the monomial basis `1, t, …, t^{h-1}` is invertible. -/
theorem OuterRange.det_map_outerRow_ne_zero [Fact p.Prime] (hR : OuterRange n p)
    (e : outerIdx n p ≃ Fin (hDim n)) :
    (Matrix.of fun k l : Fin (hDim n) =>
      ((outerRow n p (e.symm k)).map (Int.castRingHom (ZMod p))).coeff l).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro g hg k
  have hli := Fintype.linearIndependent_iff.mp hR.linearIndependent_map_outerRow
    (fun ρ => g (e ρ))
  have hzero : ∑ ρ : outerIdx n p,
      g (e ρ) • (outerRow n p ρ).map (Int.castRingHom (ZMod p)) = 0 := by
    ext l
    rw [finsetSum_coeff, coeff_zero]
    by_cases hl : l < hDim n
    · have h := congrFun hg ⟨l, hl⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, Matrix.of_apply, smul_eq_mul,
        Pi.zero_apply] at h
      rw [← h, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [coeff_smul, smul_eq_mul, Equiv.symm_apply_apply]
    · refine Finset.sum_eq_zero fun ρ _ => ?_
      have hdeg : ((outerRow n p ρ).map (Int.castRingHom (ZMod p))).natDegree < hDim n :=
        natDegree_map_le.trans_lt (hR.natDegree_outerRow_lt ρ)
      rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]
  have := hli hzero (e.symm k)
  rwa [Equiv.apply_symm_apply] at this

/-- Under (52), for every enumeration `e` of the rows, the integer matrix `U` of the
coefficients of the outer class rows in the monomial basis `1, t, …, t^{h-1}` has `det U` prime
to `p`. -/
theorem OuterRange.outerRow_unimodular [Fact p.Prime] (hR : OuterRange n p)
    (e : outerIdx n p ≃ Fin (hDim n)) :
    ¬ (p : ℤ) ∣ (Matrix.of fun k l : Fin (hDim n) => (outerRow n p (e.symm k)).coeff l).det := by
  intro hdvd
  apply hR.det_map_outerRow_ne_zero e
  have hmap : (Int.castRingHom (ZMod p)).mapMatrix
      (Matrix.of fun k l : Fin (hDim n) => (outerRow n p (e.symm k)).coeff l)
      = Matrix.of fun k l : Fin (hDim n) =>
        ((outerRow n p (e.symm k)).map (Int.castRingHom (ZMod p))).coeff l := by
    ext k l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coeff_map]
  rw [← hmap, ← RingHom.map_det, eq_intCast, (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr hdvd]

/-! ## The outer class basis -/

/-- **Outer class basis** (Section 4.2, proof of Proposition 4.6). Let `p` be a prime
satisfying the outer-range hypothesis (52). The outer class rows are exactly `h` integer
polynomials of degree less than `h`, and for every enumeration `e` of the rows the integer
matrix `U` of their coefficients in the monomial basis `1, t, …, t^{h-1}` has `det U` prime to
`p`: the rows are a `ℤ_p`-unimodular basis of the polynomials of degree less than `h`. -/
theorem outer_class_basis [Fact p.Prime] (hR : OuterRange n p) :
    Fintype.card (outerIdx n p) = hDim n
      ∧ (∀ ρ : outerIdx n p, (outerRow n p ρ).natDegree < hDim n)
      ∧ ∀ e : outerIdx n p ≃ Fin (hDim n),
        ¬ (p : ℤ) ∣ (Matrix.of fun k l : Fin (hDim n) => (outerRow n p (e.symm k)).coeff l).det :=
  ⟨hR.card_outerIdx_eq_hDim, hR.natDegree_outerRow_lt, hR.outerRow_unimodular⟩

end ZetaSeven
