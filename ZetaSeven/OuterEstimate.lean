import ZetaSeven.MatrixDet
import ZetaSeven.RankLemma

/-!
# Outer range estimate (paper Section 4.2, Proposition 4.6, equations (52)-(59))

Prince Anand, "Zeta 7 is Irrational", Section 4.2: in the outer range
(hypothesis (52)) the determinant valuation bound `v^G_p(Δ_K) ≥ γ^out_p`,
with the rank correction `r_p` (54), the outer weights (56) and the
removed-class costs (57); for `p > K` the determinant is `p`-integral.

This file records the statement data (52)-(59) and proves the
self-contained parts of the argument:

* the `p`-integral rationals `pInt p` and the Gauss valuation `gaussVal`;
* the von Staudt-Clausen corollaries `v_p(B_{2k}) ≥ -1`, and `≥ 0` unless
  `(p - 1) ∣ 2k`, from `Bernoulli.vonStaudt_clausen`;
* `p`-integrality of the polynomial moments `μ(t^e)` for `e < 3p - 4`
  (Section 4.2.1: von Staudt-Clausen plus the divisibility offset);
* the rank-correction arithmetic `2h - T = K + 6N - 3p + 4` (54);
* the polynomial part of each entry of `G_K` is `p`-integral when its
  degree is below `3p - 4`.

## Weight convention

`ZetaSeven.rank_lemma` uses doubled integer weights
(`w i + w j ≤ 2 * padicValRat p (A i j)`), i.e. twice the paper's
half-integer weights. The outer weights (56) are therefore stored
doubled: `outerWeightDbl ell delta i = 2 * w^out_{a,i}`.

## Status

Proposition 4.6 itself is not proved here. The paper's decomposition (53)
claims `A` is integral, which is false in the monomial basis; the
integrality the rank lemma needs holds only in a class-adapted basis with
weights. See the article's implementation note for the computation and
the proposed decomposition.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## Statement data: equations (52)-(59) -/

/-- Equation (52): the outer-range hypothesis. -/
def OuterRange (n p : ℕ) : Prop :=
  11 ≤ p ∧ (K n : ℚ) / 3 < p ∧ p ≤ K n ∧ 2 * K n < p ^ 2 ∧ 7 * N n ≤ 2 * p - 2

/-- The Gauss valuation `v^G_p` on `ℚ[X]` (Section 2.1): the minimum of
the `p`-adic valuations of the coefficients. The paper sets
`v^G_p(0) = +∞`; we use the junk value `0` for the zero polynomial. -/
noncomputable def gaussVal (p : ℕ) [Fact p.Prime] (P : Polynomial ℚ) : ℤ :=
  if h : P = 0 then 0
  else
    (P.support.image fun e => padicValRat p (P.coeff e)).min'
      (Finset.image_nonempty.mpr (Polynomial.support_nonempty.mpr h))

/-- Section 4.2.1: the vanishing threshold `T := K - 8N + 3p - 4`.
`L_ij = 0` whenever `i + j < T`. -/
def Tparam (n p : ℕ) : ℤ := (K n : ℤ) - 8 * N n + 3 * p - 4

/-- Equation (54): the rank correction `r_p := min(h, max(0, K + 6N - 3p + 4))`. -/
def rankCorr (n p : ℕ) : ℕ :=
  min (hDim n) (Int.toNat ((K n : ℤ) + 6 * N n - 3 * p + 4))

/-- Equation (56), doubled: `2 * w^out_{a,i}` for a class with `ℓ` poles
and `δ = 1_{a ≤ N}`. The paper's weight is
`min(0, i + 4δ - (ℓ+6)/2)` for `i < ℓ - 2` and `0` above; doubling
clears the half-integers for use with `ZetaSeven.rank_lemma`. -/
def outerWeightDbl (ell delta i : ℕ) : ℤ :=
  if i < ell - 2 then min 0 (2 * (i : ℤ) + 8 * delta - ell - 6) else 0

/-- Equation (57): removed-class costs by class size `ℓ ∈ {2,…,6}`
(the table `0, 0, 0, 1, 2`); junk `0` outside. -/
def removedCost : ℕ → ℤ
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | _ => 0

/-- Below (57): the unremoved-class cost `7(ℓ - 2)`. -/
def unremovedCost (ell : ℕ) : ℤ := 7 * ((ell : ℤ) - 2)

/-- Equation (58): `v = K - p⌊K/p⌋`, i.e. `K % p`. -/
def classV (n p : ℕ) : ℕ := K n % p

/-- Equation (58): `u = max(0, N + v - p + 1)`. -/
def classU (n p : ℕ) : ℤ := max 0 ((N n : ℤ) + classV n p - p + 1)

/-- Equation (58): `t_p = min(N, v) + u`. -/
def classT (n p : ℕ) : ℤ := min (N n : ℤ) (classV n p : ℤ) + classU n p

/-- Equation (59): the outer exponent `γ^out_p`. -/
def gammaOut (n p : ℕ) : ℤ :=
  if K n < 2 * p then
    -9 * ((K n : ℤ) - p) + 8 * classT n p - 1
      - min (rankCorr n p : ℤ) ((p : ℤ) - 1 - N n + classU n p)
  else
    -9 * ((K n : ℤ) - p) + 3 + 16 * N n + 7 * classT n p
      - min (rankCorr n p : ℤ) ((p : ℤ) + classU n p)

/-- Equation (54) arithmetic: with `T = K - 8N + 3p - 4`,
`2h - T = K + 6N - 3p + 4`, the quantity clipped in `rankCorr`. -/
theorem two_hDim_sub_Tparam (n p : ℕ) :
    2 * (hDim n : ℤ) - Tparam n p = K n + 6 * N n - 3 * p + 4 := by
  simp only [hDim, Tparam, K, N]
  push_cast
  ring

/-! ## `p`-integral rationals -/

/-- The subring `ℚ ∩ ℤ_p` of `p`-integral rationals: the valuation ring of
`Rat.padicValuation p`. -/
def pInt (p : ℕ) [Fact p.Prime] : Subring ℚ := (Rat.padicValuation p).integer

theorem mem_pInt {p : ℕ} [Fact p.Prime] {x : ℚ} :
    x ∈ pInt p ↔ Rat.padicValuation p x ≤ 1 := Iff.rfl

theorem mem_pInt_iff_den {p : ℕ} [Fact p.Prime] {x : ℚ} : x ∈ pInt p ↔ ¬ p ∣ x.den := by
  rw [mem_pInt, Rat.padicValuation_le_one_iff]

theorem mem_pInt_iff_padicValRat {p : ℕ} [hp : Fact p.Prime] {x : ℚ} :
    x ∈ pInt p ↔ 0 ≤ padicValRat p x := by
  rw [mem_pInt_iff_den, padicValRat_def]
  constructor
  · intro h
    rw [padicValNat.eq_zero_of_not_dvd h]
    omega
  · intro h hdvd
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      rw [Int.natCast_dvd] at hn
      exact Nat.not_coprime_of_dvd_of_dvd hp.out.one_lt hn hdvd x.reduced
    rw [padicValInt.eq_zero_of_not_dvd hnum] at h
    have := one_le_padicValNat_of_dvd (p := p) x.den_pos.ne' hdvd
    omega

theorem intCast_mem_pInt {p : ℕ} [Fact p.Prime] (x : ℤ) : (x : ℚ) ∈ pInt p := by
  rw [mem_pInt, Rat.padicValuation_cast]
  exact Int.padicValuation_le_one p x

theorem natCast_mem_pInt {p : ℕ} [Fact p.Prime] (x : ℕ) : (x : ℚ) ∈ pInt p := by
  have h := intCast_mem_pInt (p := p) (x : ℤ)
  rwa [Int.cast_natCast] at h

theorem inv_intCast_mem_pInt {p : ℕ} [Fact p.Prime] {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    (x : ℚ)⁻¹ ∈ pInt p := by
  rw [mem_pInt, map_inv₀, Rat.padicValuation_cast, Int.padicValuation_eq_one_iff.mpr hx]
  simp

theorem inv_natCast_mem_pInt {p : ℕ} [Fact p.Prime] {x : ℕ} (hx : ¬ p ∣ x) :
    (x : ℚ)⁻¹ ∈ pInt p := by
  have h := inv_intCast_mem_pInt (p := p) (x := (x : ℤ)) (by rwa [Int.natCast_dvd_natCast])
  rwa [Int.cast_natCast] at h

/-- Coefficientwise `p`-integrality gives a nonnegative Gauss valuation. -/
theorem gaussVal_nonneg {p : ℕ} [Fact p.Prime] {P : Polynomial ℚ}
    (h : ∀ i, P.coeff i ∈ pInt p) : 0 ≤ gaussVal p P := by
  unfold gaussVal
  split_ifs with hP
  · exact le_rfl
  · rw [Finset.le_min'_iff]
    intro y hy
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hy
    exact mem_pInt_iff_padicValRat.mp (h e)

/-! ## Von Staudt-Clausen corollaries -/

/-- Von Staudt-Clausen: `B_{2k}` is `p`-integral unless `(p - 1) ∣ 2k`. -/
theorem bernoulli_mem_pInt {p k : ℕ} [hp : Fact p.Prime] (hpk : ¬ (p - 1) ∣ 2 * k) :
    _root_.bernoulli (2 * k) ∈ pInt p := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  rw [eq_sub_of_add_eq hz.symm]
  refine sub_mem (intCast_mem_pInt z) (sum_mem fun q hq => ?_)
  obtain ⟨-, hqprime, hqdvd⟩ := Finset.mem_filter.mp hq
  have hqp : q ≠ p := by
    rintro rfl
    exact hpk hqdvd
  rw [one_div]
  exact inv_natCast_mem_pInt fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp.out hqprime).mp h).symm

/-- Von Staudt-Clausen: `p B_{2k}` is `p`-integral, i.e. `v_p(B_{2k}) ≥ -1`. -/
theorem p_mul_bernoulli_mem_pInt {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    (p : ℚ) * _root_.bernoulli (2 * k) ∈ pInt p := by
  by_cases hpk : (p - 1) ∣ 2 * k
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [mul_zero, _root_.bernoulli_zero, mul_one]
      exact natCast_mem_pInt p
    · have hB := Bernoulli.padicValRat_bernoulli (p := p) hk hpk
      have hB0 : _root_.bernoulli (2 * k) ≠ 0 := by
        intro h
        rw [h, padicValRat.zero] at hB
        omega
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      rw [mem_pInt_iff_padicValRat, padicValRat.mul hp0 hB0, hB, padicValRat.self hp.out.one_lt]
      norm_num
  · exact mul_mem (natCast_mem_pInt p) (bernoulli_mem_pInt hpk)

/-! ## Polynomial moments below `3p - 4` (Section 4.2.1) -/

/-- The integer factor `(2e+3)(2e+4)(2e+5)(2e+6)(2e+7)` of the moment (5). -/
def momentFactor (e : ℕ) : ℕ := ∏ i ∈ range 5, (2 * e + 3 + i)

theorem muMonomial_eq (e : ℕ) :
    muMonomial e = (-1) ^ e * _root_.bernoulli (2 * (e + 1)) * (momentFactor e : ℚ) / 720 := by
  rw [muMonomial, momentFactor, show 2 * e + 2 = 2 * (e + 1) by ring]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

theorem not_dvd_720 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ∣ 720 := by
  intro hd
  rw [show (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hd)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hd)
      omega
  · have := Nat.le_of_dvd (by norm_num) hd
    omega

/-- Section 4.2.1: the polynomial moment `μ(t^e)` is `p`-integral for
`e < 3p - 4`. If `(p - 1) ∤ 2e + 2`, von Staudt-Clausen makes `B_{2e+2}`
`p`-integral; otherwise `2e + 2 = k(p - 1)` with `1 ≤ k ≤ 5` and the factor
`2e + 2 + k = kp` of `(2e+3)⋯(2e+7)` cancels the `p⁻¹` of `B_{2e+2}`. -/
theorem muMonomial_mem_pInt {p e : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p)
    (he : e < 3 * p - 4) : muMonomial e ∈ pInt p := by
  rw [muMonomial_eq, div_eq_mul_inv]
  have h720 : ((720 : ℚ))⁻¹ ∈ pInt p := by
    have h := inv_natCast_mem_pInt (p := p) (not_dvd_720 hp.out hp7)
    exact_mod_cast h
  have hsign : ((-1 : ℚ)) ^ e ∈ pInt p := pow_mem (neg_mem (one_mem _)) e
  by_cases hpk : (p - 1) ∣ 2 * (e + 1)
  · obtain ⟨k, hk⟩ := hpk
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk
        omega
      · exact h0
    have hk5 : k ≤ 5 := by
      by_contra hcon
      have h6 : (p - 1) * 6 ≤ (p - 1) * k := Nat.mul_le_mul_left _ (by omega)
      omega
    have hdvd : p ∣ momentFactor e := by
      have hmem : k - 1 ∈ range 5 := Finset.mem_range.mpr (by omega)
      refine dvd_trans ⟨k, ?_⟩ (Finset.dvd_prod_of_mem (fun i => 2 * e + 3 + i) hmem)
      show 2 * e + 3 + (k - 1) = p * k
      interval_cases k <;> omega
    obtain ⟨F, hF⟩ := hdvd
    rw [hF, Nat.cast_mul,
      show ∀ a b c d : ℚ, a * b * (c * d) * (720 : ℚ)⁻¹ = a * (c * b) * d * (720 : ℚ)⁻¹ from
        fun a b c d => by ring]
    exact mul_mem (mul_mem (mul_mem hsign (p_mul_bernoulli_mem_pInt (e + 1)))
      (natCast_mem_pInt F)) h720
  · exact mul_mem (mul_mem (mul_mem hsign (bernoulli_mem_pInt hpk)) (natCast_mem_pInt _)) h720

/-! ## Polynomials with `p`-integral coefficients -/

/-- Polynomials over `ℚ` with `p`-integral coefficients. -/
def pIntPoly (p : ℕ) [Fact p.Prime] : Subring (Polynomial ℚ) :=
  Polynomial.liftsRing (pInt p).subtype

theorem mem_pIntPoly {p : ℕ} [Fact p.Prime] {P : Polynomial ℚ} :
    P ∈ pIntPoly p ↔ ∀ i, P.coeff i ∈ pInt p := by
  rw [pIntPoly, ← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

theorem C_mem_pIntPoly {p : ℕ} [Fact p.Prime] {a : ℚ} (ha : a ∈ pInt p) :
    C a ∈ pIntPoly p := by
  rw [mem_pIntPoly]
  intro i
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem X_mem_pIntPoly {p : ℕ} [Fact p.Prime] : (X : Polynomial ℚ) ∈ pIntPoly p := by
  rw [mem_pIntPoly]
  intro i
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/-- A determinant of a matrix with entries in a subring lies in the subring. -/
theorem det_mem_of_entries_mem {R : Type*} [CommRing R] (S : Subring R) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

/-! ## The polynomial part of `G_K` over `ℤ` -/

/-- `D_m` over `ℤ`. -/
noncomputable def DpolyZ (m : ℕ) : Polynomial ℤ :=
  ∏ j ∈ range m, (X + C (((j : ℤ) + 1) ^ 2))

/-- The tail divisor `D_tail` over `ℤ`. -/
noncomputable def DtailZ (n : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Icc (N n + 1) (K n), (X + C ((j : ℤ) ^ 2))

/-- The numerator `D_N⁷ t^{i+j}` over `ℤ`. -/
noncomputable def RnumZ (n i j : ℕ) : Polynomial ℤ := DpolyZ (N n) ^ 7 * X ^ (i + j)

theorem map_DpolyZ (m : ℕ) : (DpolyZ m).map (Int.castRingHom ℚ) = Dpoly m := by
  simp [DpolyZ, Dpoly, Polynomial.map_prod]

theorem map_DtailZ (n : ℕ) : (DtailZ n).map (Int.castRingHom ℚ) = Dtail n := by
  simp [DtailZ, Dtail, Polynomial.map_prod]

theorem map_RnumZ (n i j : ℕ) : (RnumZ n i j).map (Int.castRingHom ℚ) = Rnum n i j := by
  simp [RnumZ, Rnum, map_DpolyZ]

theorem monic_DtailZ (n : ℕ) : (DtailZ n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- The polynomial part of `R_{ij}` is the image of an integer polynomial. -/
theorem polyPart_eq_map (n i j : ℕ) :
    polyPart n i j = (RnumZ n i j /ₘ DtailZ n).map (Int.castRingHom ℚ) := by
  have hm : (Dtail n).Monic := by
    rw [← map_DtailZ]
    exact (monic_DtailZ n).map _
  show Rnum n i j / Dtail n = _
  rw [Polynomial.map_divByMonic _ (monic_DtailZ n), map_RnumZ, map_DtailZ,
    Polynomial.divByMonic_eq_div _ hm]

theorem polyPart_coeff_mem {p : ℕ} [Fact p.Prime] (n i j e : ℕ) :
    (polyPart n i j).coeff e ∈ pInt p := by
  rw [polyPart_eq_map, coeff_map, eq_intCast]
  exact intCast_mem_pInt _

theorem natDegree_DpolyZ_le (m : ℕ) : (DpolyZ m).natDegree ≤ m := by
  unfold DpolyZ
  refine (natDegree_prod_le _ _).trans ?_
  simp [natDegree_X_add_C]

theorem natDegree_RnumZ_le (n i j : ℕ) : (RnumZ n i j).natDegree ≤ 7 * N n + (i + j) := by
  unfold RnumZ
  have h1 : (DpolyZ (N n) ^ 7).natDegree ≤ 7 * N n :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 7 (natDegree_DpolyZ_le _))
  have h2 : (X ^ (i + j) : Polynomial ℤ).natDegree ≤ i + j := natDegree_X_pow_le _
  exact natDegree_mul_le.trans (Nat.add_le_add h1 h2)

theorem natDegree_polyPart_le (n i j : ℕ) :
    (polyPart n i j).natDegree ≤ 7 * N n + (i + j) := by
  rw [polyPart_eq_map]
  refine natDegree_map_le.trans ?_
  rw [natDegree_divByMonic _ (monic_DtailZ n)]
  exact (Nat.sub_le _ _).trans (natDegree_RnumZ_le n i j)

/-- The polynomial-part contribution `μ(P_{ij})` to `G_K(i,j)` is `p`-integral
when `7N + i + j < 3p - 4`. -/
theorem polySum_mem {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (n i j : ℕ)
    (hdeg : 7 * N n + (i + j) < 3 * p - 4) :
    (polyPart n i j).sum (fun e a => C a * C (muMonomial e)) ∈ pIntPoly p := by
  rw [Polynomial.sum_def]
  refine sum_mem fun e he => mul_mem (C_mem_pIntPoly (polyPart_coeff_mem n i j e))
    (C_mem_pIntPoly (muMonomial_mem_pInt hp7 ?_))
  have h1 := le_natDegree_of_mem_supp e he
  have h2 := natDegree_polyPart_le n i j
  omega

/-! ## Pole values below `p` -/

/-- `H⁷_j` is `p`-integral for `j < p`. -/
theorem H7_mem_pInt {p j : ℕ} [hp : Fact p.Prime] (hj : j < p) : H7 j ∈ pInt p := by
  unfold H7
  refine sum_mem fun v hv => ?_
  rw [Finset.mem_range] at hv
  have hnd : ¬ p ∣ (v + 1) ^ 7 := fun h =>
    absurd (Nat.le_of_dvd (Nat.succ_pos v) (hp.out.dvd_of_dvd_pow h)) (by omega)
  have h := inv_natCast_mem_pInt hnd
  rw [one_div]
  exact_mod_cast h

/-- The pole value `μ_X(1/(t + j²))` has `p`-integral coefficients for `1 ≤ j < p`. -/
theorem muPole_mem {p j : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hj1 : 1 ≤ j) (hj : j < p) :
    muPole j ∈ pIntPoly p := by
  unfold muPole
  refine add_mem (mul_mem (pow_mem (C_mem_pIntPoly (natCast_mem_pInt j)) 6)
    (sub_mem X_mem_pIntPoly (C_mem_pIntPoly (H7_mem_pInt hj)))) (C_mem_pIntPoly ?_)
  refine sub_mem ?_ ?_
  · have hnd : ¬ p ∣ 2 * j := by
      intro h
      rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by omega) h
        omega
    have h := inv_natCast_mem_pInt hnd
    rw [one_div]
    exact_mod_cast h
  · have hnd : ¬ p ∣ 6 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have h := inv_natCast_mem_pInt hnd
    rw [one_div]
    exact_mod_cast h

end ZetaSeven
