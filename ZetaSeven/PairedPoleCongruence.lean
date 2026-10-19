import ZetaSeven.FunctionalMu

/-!
# Paired-pole congruence (paper Section 4.2, proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational". Let `p ≥ 7` be prime, `1 ≤ a ≤ (p - 1)/2` and
`a' = p - a`. The pole values `π_b = μ_X(1/(t + b²)) = b⁶ (X - H⁷_b) + 1/(2b) - 1/6`
(`ZetaSeven.muPole`, equation (6)) satisfy:

1. `muPole_paired_congruence`: `π_a` and `π_{a'}` have `p`-integral coefficients and are
   congruent modulo `p`, coefficientwise. The key input is `H7_reflect_congruence`,
   `H⁷_{p-a} ≡ H⁷_{a-1} (mod p)`.
2. `paired_residues`: let `S` be a finite set of natural numbers containing `a` and `a'` and no
   other integer congruent to `±a` modulo `p`, `T(t) = ∏_{b ∈ S} (t + b²)`, and `Q` a polynomial
   with `p`-integral rational coefficients. The residues `ρ_b = Q(-b²)/T'(-b²)` of `Q/T`
   (`poleResidue`) at `b = a, a'` satisfy `v_p(ρ_b) ≥ -1`, with equality for both when `Q(-a²)`
   is a `p`-unit; `ρ_a + ρ_{a'}` is `p`-integral; and `ρ_a π_a + ρ_{a'} π_{a'}` has `p`-integral
   coefficients.

The paper asserts the congruence of the two pole values in passing ("the two remaining pole
values at `a` and `p - a` are integral and congruent modulo `p`") and, in the case `p > K`,
treats each residue as `p`-integral; source-map erratum 7 records that single residues can have
valuation `-1`, so the two poles must be paired.

Conventions: valuations are `padicValRat p`. "`p`-integral" is `0 ≤ padicValRat p x`, which
also holds for `x = 0` (where the paper has `v_p(0) = +∞`), and "congruent modulo `p`" for two
coefficients `c, c'` is `1 ≤ padicValRat p (c - c')` whenever `c ≠ c'`. The proofs work in the
subring `pInt p` of `p`-integral rationals (`mem_pInt_iff_padicValRat`), where `x ≡ 0 (mod p)`
is `x / p ∈ pInt p`. The power sum `∑_{v=1}^{p-1} v⁻⁷ ≡ 0 (mod p)` is proved by pairing `v`
with `p - v`: `v⁷ + (p - v)⁷` is divisible by `p` because `7` is odd.
-/

namespace ZetaSeven

open Polynomial

/-! ## `p`-integral rationals -/

/-- The subring of `p`-integral rationals: the valuation ring of `Rat.padicValuation p`. -/
noncomputable def pInt (p : ℕ) [Fact p.Prime] : Subring ℚ := (Rat.padicValuation p).integer

/-- Polynomials over `ℚ` with `p`-integral coefficients. -/
noncomputable def pIntPoly (p : ℕ) [Fact p.Prime] : Subring (Polynomial ℚ) :=
  Polynomial.liftsRing (pInt p).subtype

section PInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_pInt_iff_den {x : ℚ} : x ∈ pInt p ↔ ¬ p ∣ x.den := by
  rw [pInt, Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff]

/-- Membership in `pInt p` is `0 ≤ v_p`. -/
theorem mem_pInt_iff_padicValRat {x : ℚ} : x ∈ pInt p ↔ 0 ≤ padicValRat p x := by
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
    have := one_le_padicValNat_of_dvd (p := p) x.den_nz hdvd
    omega

theorem inv_natCast_mem_pInt {x : ℕ} (hx : ¬ p ∣ x) : (x : ℚ)⁻¹ ∈ pInt p := by
  rw [mem_pInt_iff_padicValRat, padicValRat.inv, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hx]
  simp

theorem mem_pInt_of_padicValRat_eq_zero {x : ℚ} (h : padicValRat p x = 0) : x ∈ pInt p :=
  mem_pInt_iff_padicValRat.mpr h.ge

theorem inv_mem_pInt_of_padicValRat_eq_zero {x : ℚ} (h : padicValRat p x = 0) :
    x⁻¹ ∈ pInt p := by
  rw [mem_pInt_iff_padicValRat, padicValRat.inv]
  omega

omit hp in
/-- An integer prime to `p` is a nonzero rational of valuation `0`. -/
theorem intCast_ne_zero_and_padicValRat_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) :
    (z : ℚ) ≠ 0 ∧ padicValRat p (z : ℚ) = 0 := by
  refine ⟨Int.cast_ne_zero.mpr fun h0 => h (by rw [h0]; exact dvd_zero _), ?_⟩
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h, Nat.cast_zero]

/-- `x ≡ 0 (mod p)` with `x ≠ 0` gives `v_p(x) ≥ 1`. -/
theorem one_le_padicValRat_of_div_mem {x : ℚ} (h : x / p ∈ pInt p) (hx : x ≠ 0) :
    1 ≤ padicValRat p x := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h' := mem_pInt_iff_padicValRat.mp h
  rw [padicValRat.div hx hp0, padicValRat.self hp.out.one_lt] at h'
  omega

theorem one_le_padicValRat_of_eq_mul {x d : ℚ} (hd : d ∈ pInt p) (hx : x = p * d)
    (hx0 : x ≠ 0) : 1 ≤ padicValRat p x := by
  refine one_le_padicValRat_of_div_mem ?_ hx0
  rw [hx, mul_div_cancel_left₀ d (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
  exact hd

/-- `p x` is `p`-integral exactly when `v_p(x) ≥ -1`; this is the direction used. -/
theorem neg_one_le_padicValRat_of_mul_mem {x : ℚ} (h : (p : ℚ) * x ∈ pInt p) :
    -1 ≤ padicValRat p x := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx, padicValRat.zero]
    norm_num
  · have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have h' := mem_pInt_iff_padicValRat.mp h
    rw [padicValRat.mul hp0 hx, padicValRat.self hp.out.one_lt] at h'
    omega

/-- A rational congruent modulo `p` to a `p`-unit is a `p`-unit. -/
theorem padicValRat_eq_zero_of_congr {x y : ℚ} (hx0 : x ≠ 0) (hxv : padicValRat p x = 0)
    (hxy : (x - y) / p ∈ pInt p) : y ≠ 0 ∧ padicValRat p y = 0 := by
  rcases eq_or_ne (y - x) 0 with hd | hd
  · rw [sub_eq_zero.mp hd]
    exact ⟨hx0, hxv⟩
  · have hdv : 1 ≤ padicValRat p (y - x) := by
      refine one_le_padicValRat_of_div_mem ?_ hd
      have e : (y - x) / p = -((x - y) / p) := by ring
      rw [e]
      exact neg_mem hxy
    have hy : y = x + (y - x) := by ring
    have hy0 : x + (y - x) ≠ 0 := by
      intro h0
      have h1 : y - x = -x := by linear_combination h0
      rw [h1, padicValRat.neg, hxv] at hdv
      omega
    refine ⟨by rw [hy]; exact hy0, ?_⟩
    rw [hy, padicValRat.add_eq_of_lt (p := p) hy0 hx0 hd (by omega), hxv]

/-! ## Polynomials with `p`-integral coefficients -/

theorem mem_pIntPoly {P : Polynomial ℚ} : P ∈ pIntPoly p ↔ ∀ i, P.coeff i ∈ pInt p := by
  rw [pIntPoly, ← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

theorem C_mem_pIntPoly {a : ℚ} (ha : a ∈ pInt p) : C a ∈ pIntPoly p := by
  rw [mem_pIntPoly]
  intro i
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem X_mem_pIntPoly : (X : Polynomial ℚ) ∈ pIntPoly p := by
  rw [mem_pIntPoly]
  intro i
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem eval_mem_pInt {Q : ℚ[X]} (hQ : ∀ i, Q.coeff i ∈ pInt p) {x : ℚ} (hx : x ∈ pInt p) :
    Q.eval x ∈ pInt p := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hQ i) (pow_mem hx i)

/-- If `x ≡ y (mod p)` then `Q(x) ≡ Q(y) (mod p)` for `Q` with `p`-integral coefficients. -/
theorem eval_sub_eval_div_mem {Q : ℚ[X]} (hQ : ∀ i, Q.coeff i ∈ pInt p) {x y : ℚ}
    (hx : x ∈ pInt p) (hy : y ∈ pInt p) (hxy : (x - y) / p ∈ pInt p) :
    (Q.eval x - Q.eval y) / p ∈ pInt p := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine sum_mem fun i _ => ?_
  have e : (Q.coeff i * x ^ i - Q.coeff i * y ^ i) / p
      = Q.coeff i * (∑ k ∈ Finset.range i, x ^ k * y ^ (i - 1 - k)) * ((x - y) / p) := by
    rw [← mul_sub, ← geom_sum₂_mul]
    ring
  rw [e]
  exact mul_mem (mul_mem (hQ i) (sum_mem fun k _ => mul_mem (pow_mem hx k) (pow_mem hy _))) hxy

/-- If `f i ≡ g i (mod p)` termwise, with all terms `p`-integral, the products are congruent. -/
theorem prod_sub_prod_div_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℚ}
    (hf : ∀ i, f i ∈ pInt p) (hg : ∀ i, g i ∈ pInt p) (hfg : ∀ i, (f i - g i) / p ∈ pInt p) :
    (∏ i ∈ s, f i - ∏ i ∈ s, g i) / p ∈ pInt p := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, sub_self, zero_div]
    exact zero_mem _
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have e : (f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, g i) / (p : ℚ)
        = (f j - g j) / p * ∏ i ∈ s, f i + g j * ((∏ i ∈ s, f i - ∏ i ∈ s, g i) / p) := by
      ring
    rw [e]
    exact add_mem (mul_mem (hfg j) (prod_mem fun i _ => hf i)) (mul_mem (hg j) ih)

/-! ## The harmonic sums `H⁷_j` modulo `p` -/

theorem H7_succ (j : ℕ) : H7 (j + 1) = H7 j + 1 / ((j : ℚ) + 1) ^ 7 := by
  simp only [H7, Finset.sum_range_succ]

/-- `H⁷_j` is `p`-integral for `j < p`: its denominators are the `v⁷` with `1 ≤ v ≤ j`. -/
theorem H7_mem_pInt {j : ℕ} (hj : j < p) : H7 j ∈ pInt p := by
  rw [H7]
  refine sum_mem fun v hv => ?_
  have hv' := Finset.mem_range.mp hv
  have hinv := inv_natCast_mem_pInt (p := p) (Nat.not_dvd_of_pos_of_lt (show 0 < v + 1 by omega)
    (show v + 1 < p by omega))
  push_cast at hinv
  rw [one_div, ← inv_pow]
  exact pow_mem hinv 7

/-- `w⁻⁷ + u⁻⁷ ≡ 0 (mod p)` when `w + u = p` with `w, u ≥ 1`, since `w + u` divides
`w⁷ + u⁷`. -/
theorem pair_div_mem_pInt {w u : ℕ} (hw : 1 ≤ w) (hu : 1 ≤ u) (hwu : w + u = p) :
    (1 / (w : ℚ) ^ 7 + 1 / (u : ℚ) ^ 7) / p ∈ pInt p := by
  have hwp : ¬ p ∣ w := Nat.not_dvd_of_pos_of_lt hw (by omega)
  have hup : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt hu (by omega)
  obtain ⟨k, hk⟩ := Odd.add_dvd_pow_add_pow (w : ℤ) (u : ℤ) (⟨3, by norm_num⟩ : Odd 7)
  have hkQ : (w : ℚ) ^ 7 + (u : ℚ) ^ 7 = p * k := by
    have h1 : (w : ℤ) + u = p := by exact_mod_cast hwu
    rw [h1] at hk
    exact_mod_cast hk
  have hw0 : (w : ℚ) ^ 7 ≠ 0 := pow_ne_zero 7 (Nat.cast_ne_zero.mpr (by omega))
  have hu0 : (u : ℚ) ^ 7 ≠ 0 := pow_ne_zero 7 (Nat.cast_ne_zero.mpr (by omega))
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have e : (1 / (w : ℚ) ^ 7 + 1 / (u : ℚ) ^ 7) / p = k / ((w : ℚ) ^ 7 * (u : ℚ) ^ 7) := by
    rw [div_add_div _ _ hw0 hu0, div_div,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hw0 hu0) hp0) (mul_ne_zero hw0 hu0)]
    linear_combination ((w : ℚ) ^ 7 * (u : ℚ) ^ 7) * hkQ
  rw [e, div_eq_mul_inv, mul_inv, ← inv_pow, ← inv_pow]
  exact mul_mem (intCast_mem _ k)
    (mul_mem (pow_mem (inv_natCast_mem_pInt hwp) 7) (pow_mem (inv_natCast_mem_pInt hup) 7))

/-- The power sum `∑_{v=1}^{p-1} v⁻⁷ = H⁷_{p-1}` vanishes modulo `p`: pairing `v` with `p - v`
shows that `2 H⁷_{p-1} ≡ 0`. -/
theorem H7_pred_div_mem_pInt (hp2 : p ≠ 2) : H7 (p - 1) / p ∈ pInt p := by
  have hrefl : ∑ j ∈ Finset.range (p - 1), 1 / (((p - 1 - 1 - j : ℕ) : ℚ) + 1) ^ 7
      = H7 (p - 1) :=
    Finset.sum_range_reflect (fun v : ℕ => 1 / ((v : ℚ) + 1) ^ 7) (p - 1)
  have hsum : 2 * H7 (p - 1) / p ∈ pInt p := by
    have e : 2 * H7 (p - 1) / p = ∑ v ∈ Finset.range (p - 1),
        (1 / ((v : ℚ) + 1) ^ 7 + 1 / (((p - 1 - 1 - v : ℕ) : ℚ) + 1) ^ 7) / p := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, hrefl, H7]
      ring
    rw [e]
    refine sum_mem fun v hv => ?_
    have hv' := Finset.mem_range.mp hv
    have h := pair_div_mem_pInt (p := p) (w := v + 1) (u := p - 1 - 1 - v + 1) (by omega)
      (by omega) (by omega)
    exact_mod_cast h
  have h2 : (2 : ℚ)⁻¹ ∈ pInt p := by
    have h := inv_natCast_mem_pInt (p := p) (x := 2)
      (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h))
    exact_mod_cast h
  have e2 : H7 (p - 1) / p = 2 * H7 (p - 1) / p * (2 : ℚ)⁻¹ := by ring
  rw [e2]
  exact mul_mem hsum h2

/-- The key input of the first part: `H⁷_{p-a} ≡ H⁷_{a-1} (mod p)`, as `p`-integrality of
`(H⁷_{p-a} - H⁷_{a-1})/p`. -/
theorem H7_sub_div_mem_pInt (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    (H7 (p - a) - H7 (a - 1)) / p ∈ pInt p := by
  have hsplit : H7 (p - 1) = H7 (p - a)
      + ∑ x ∈ Finset.range (a - 1), 1 / (((p - a + x : ℕ) : ℚ) + 1) ^ 7 := by
    rw [show p - 1 = p - a + (a - 1) by omega]
    simp only [H7]
    rw [Finset.sum_range_add]
  have hrefl : ∑ x ∈ Finset.range (a - 1), 1 / (((a - 1 - 1 - x : ℕ) : ℚ) + 1) ^ 7
      = H7 (a - 1) :=
    Finset.sum_range_reflect (fun v : ℕ => 1 / ((v : ℚ) + 1) ^ 7) (a - 1)
  have e : (H7 (p - a) - H7 (a - 1)) / p = H7 (p - 1) / p - ∑ x ∈ Finset.range (a - 1),
      (1 / (((p - a + x : ℕ) : ℚ) + 1) ^ 7 + 1 / (((a - 1 - 1 - x : ℕ) : ℚ) + 1) ^ 7) / p := by
    rw [hsplit, ← hrefl, ← Finset.sum_div, Finset.sum_add_distrib]
    ring
  rw [e]
  refine sub_mem (H7_pred_div_mem_pInt hp2) (sum_mem fun x hx => ?_)
  have hx' := Finset.mem_range.mp hx
  have h := pair_div_mem_pInt (p := p) (w := p - a + x + 1) (u := a - 1 - 1 - x + 1) (by omega)
    (by omega) (by omega)
  exact_mod_cast h

/-- `H⁷_{p-a} ≡ H⁷_{a-1} (mod p)` for `1 ≤ a < p`: the difference has valuation at least one
whenever it is nonzero. -/
theorem H7_reflect_congruence (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    H7 (p - a) - H7 (a - 1) ≠ 0 → 1 ≤ padicValRat p (H7 (p - a) - H7 (a - 1)) :=
  fun h0 => one_le_padicValRat_of_div_mem (H7_sub_div_mem_pInt (by omega) ha1 hap) h0

end PInt

/-! ## Algebraic identities for the pole values -/

/-- The constant coefficient identity behind the congruence `π_a ≡ π_{a'} (mod p)`: with
`q = A + A'`, `H⁷_A = h + A⁻⁷` and `H⁷_{A'} = h + q E`, the constant terms
`1/(2B) - 1/6 - B⁶ H⁷_B` of the two pole values differ by `q` times an explicit expression. -/
theorem pole_const_identity {A A' q h E Ha Ha' : ℚ} (hA : A ≠ 0) (hA' : A' ≠ 0)
    (hpa : q = A + A') (hHa : Ha = h + 1 / A ^ 7) (hHa' : Ha' = h + q * E) :
    1 / (2 * A) - 1 / 6 - A ^ 6 * Ha = 1 / (2 * A') - 1 / 6 - A' ^ 6 * Ha'
      + q * (-(A⁻¹ * A'⁻¹ * 2⁻¹) - (A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4) * h
        + A' ^ 6 * E) := by
  have h1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have h2 : A' * A'⁻¹ = 1 := mul_inv_cancel₀ hA'
  linear_combination (-A ^ 6) * hHa + A' ^ 6 * hHa'
    + ((A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4) * h + A⁻¹ * A'⁻¹ * 2⁻¹) * hpa
    + (A'⁻¹ * 2⁻¹ - (A ^ 5 * A⁻¹ ^ 6 + A ^ 4 * A⁻¹ ^ 5 + A ^ 3 * A⁻¹ ^ 4 + A ^ 2 * A⁻¹ ^ 3
        + A * A⁻¹ ^ 2 + A⁻¹)) * h1
    + (A⁻¹ * 2⁻¹) * h2

/-- The difference of two pole values in the form `C B⁶ * X + C c_B` is `C q` times an explicit
linear polynomial. -/
theorem linear_sub_eq {A A' q h E Ha Ha' : ℚ} (hA : A ≠ 0) (hA' : A' ≠ 0) (hpa : q = A + A')
    (hHa : Ha = h + 1 / A ^ 7) (hHa' : Ha' = h + q * E) :
    C (A ^ 6) * X + C (1 / (2 * A) - 1 / 6 - A ^ 6 * Ha)
        - (C (A' ^ 6) * X + C (1 / (2 * A') - 1 / 6 - A' ^ 6 * Ha'))
      = C q * (C ((A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4)) * X
        + C (-(A⁻¹ * A'⁻¹ * 2⁻¹) - (A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4) * h
          + A' ^ 6 * E)) := by
  have e1 : A ^ 6 = A' ^ 6 + q * ((A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4)) := by
    linear_combination (-((A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4))) * hpa
  have h1 : C (A ^ 6) = C (A' ^ 6) + C q * C ((A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4)) := by
    rw [← map_mul, ← map_add]
    exact congrArg C e1
  have h0 : C (1 / (2 * A) - 1 / 6 - A ^ 6 * Ha) = C (1 / (2 * A') - 1 / 6 - A' ^ 6 * Ha')
      + C q * C (-(A⁻¹ * A'⁻¹ * 2⁻¹) - (A - A') * (A ^ 4 + A ^ 2 * A' ^ 2 + A' ^ 4) * h
        + A' ^ 6 * E) := by
    rw [← map_mul, ← map_add]
    exact congrArg C (pole_const_identity hA hA' hpa hHa hHa')
  rw [h1, h0]
  ring

/-- Equation (6) in the form `μ_X(1/(t + j²)) = C j⁶ * X + C (1/(2j) - 1/6 - j⁶ H⁷_j)`. -/
theorem muPole_eq (j : ℕ) :
    muPole j = C ((j : ℚ) ^ 6) * X + C (1 / (2 * (j : ℚ)) - 1 / 6 - (j : ℚ) ^ 6 * H7 j) := by
  simp only [muPole, map_sub, map_mul, map_pow]
  ring

section PairedPoles

variable {p : ℕ} [hp : Fact p.Prime]

/-- For `1 ≤ j < p` and `p ≥ 7` the pole value `μ_X(1/(t + j²))` has `p`-integral
coefficients: its denominators divide `2 j⁷ · 6 · lcm(1, …, j)⁷`. -/
theorem muPole_mem_pIntPoly (hp7 : 7 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) :
    muPole j ∈ pIntPoly p := by
  have hjd : ¬ p ∣ j := Nat.not_dvd_of_pos_of_lt hj1 hjp
  have h2j : ¬ p ∣ 2 * j := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hjd h
  have h6 : ¬ p ∣ 6 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have h1 : (2 * (j : ℚ))⁻¹ ∈ pInt p := by exact_mod_cast inv_natCast_mem_pInt (p := p) h2j
  have h2 : (6 : ℚ)⁻¹ ∈ pInt p := by exact_mod_cast inv_natCast_mem_pInt (p := p) h6
  have hc : 1 / (2 * (j : ℚ)) - 1 / 6 ∈ pInt p := by
    rw [one_div, one_div]
    exact sub_mem h1 h2
  rw [muPole]
  exact add_mem (mul_mem (pow_mem (C_mem_pIntPoly (natCast_mem _ j)) 6)
    (sub_mem X_mem_pIntPoly (C_mem_pIntPoly (H7_mem_pInt hjp)))) (C_mem_pIntPoly hc)

/-- The difference `π_a - π_{a'}` of the two paired pole values is `p` times a polynomial with
`p`-integral coefficients. -/
theorem muPole_sub_eq (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : 2 * a < p) :
    ∃ Dl ∈ pIntPoly p, muPole a - muPole (p - a) = C (p : ℚ) * Dl := by
  have hp2 : p ≠ 2 := by omega
  have hap' : a < p := by omega
  have hq0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hA0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hA'0 : ((p - a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpa : (p : ℚ) = a + ((p - a : ℕ) : ℚ) := by
    rw [Nat.cast_sub hap'.le]
    ring
  have hHa : H7 a = H7 (a - 1) + 1 / (a : ℚ) ^ 7 := by
    have h := H7_succ (a - 1)
    rw [Nat.sub_add_cancel ha1] at h
    rw [h, Nat.cast_sub ha1, Nat.cast_one, sub_add_cancel]
  have hHa' : H7 (p - a) = H7 (a - 1) + (p : ℚ) * ((H7 (p - a) - H7 (a - 1)) / p) := by
    have hpp : (p : ℚ) * (p : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hq0
    linear_combination (H7 (a - 1) - H7 (p - a)) * hpp
  have hAi : (a : ℚ)⁻¹ ∈ pInt p :=
    inv_natCast_mem_pInt (Nat.not_dvd_of_pos_of_lt (by omega) hap')
  have hA'i : ((p - a : ℕ) : ℚ)⁻¹ ∈ pInt p :=
    inv_natCast_mem_pInt (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have h2i : (2 : ℚ)⁻¹ ∈ pInt p := by
    have h := inv_natCast_mem_pInt (p := p) (x := 2)
      (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h))
    exact_mod_cast h
  have hh : H7 (a - 1) ∈ pInt p := H7_mem_pInt (by omega)
  have hE : (H7 (p - a) - H7 (a - 1)) / p ∈ pInt p := H7_sub_div_mem_pInt hp2 ha1 hap'
  have hF : ((a : ℚ) - ((p - a : ℕ) : ℚ)) * ((a : ℚ) ^ 4 + (a : ℚ) ^ 2 * ((p - a : ℕ) : ℚ) ^ 2
      + ((p - a : ℕ) : ℚ) ^ 4) ∈ pInt p :=
    mul_mem (sub_mem (natCast_mem _ _) (natCast_mem _ _))
      (add_mem (add_mem (pow_mem (natCast_mem _ _) _)
        (mul_mem (pow_mem (natCast_mem _ _) _) (pow_mem (natCast_mem _ _) _)))
        (pow_mem (natCast_mem _ _) _))
  rw [muPole_eq, muPole_eq]
  refine ⟨_, ?_, linear_sub_eq hA0 hA'0 hpa hHa hHa'⟩
  exact add_mem (mul_mem (C_mem_pIntPoly hF) X_mem_pIntPoly)
    (C_mem_pIntPoly (add_mem (sub_mem (neg_mem (mul_mem (mul_mem hAi hA'i) h2i)) (mul_mem hF hh))
      (mul_mem (pow_mem (natCast_mem _ _) _) hE)))

/-- **Paired-pole congruence, part 1.** For a prime `p ≥ 7` and `1 ≤ a ≤ (p - 1)/2`, the pole
values `π_a = μ_X(1/(t + a²))` and `π_{a'}`, `a' = p - a`, have `p`-integral coefficients and are
congruent modulo `p` coefficientwise. -/
theorem muPole_paired_congruence (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ (p - 1) / 2) :
    (∀ i, 0 ≤ padicValRat p ((muPole a).coeff i)) ∧
      (∀ i, 0 ≤ padicValRat p ((muPole (p - a)).coeff i)) ∧
      ∀ i, (muPole a - muPole (p - a)).coeff i ≠ 0 →
        1 ≤ padicValRat p ((muPole a - muPole (p - a)).coeff i) := by
  have hap : 2 * a < p := by omega
  refine ⟨fun i => mem_pInt_iff_padicValRat.mp
      (mem_pIntPoly.mp (muPole_mem_pIntPoly hp7 ha1 (by omega)) i),
    fun i => mem_pInt_iff_padicValRat.mp
      (mem_pIntPoly.mp (muPole_mem_pIntPoly hp7 (by omega) (by omega)) i), ?_⟩
  obtain ⟨Dl, hDl, hdiff⟩ := muPole_sub_eq hp7 ha1 hap
  intro i hi
  rw [hdiff, coeff_C_mul] at hi ⊢
  exact one_le_padicValRat_of_eq_mul (mem_pIntPoly.mp hDl i) rfl hi

/-! ## Paired residues -/

/-- The residue `ρ_b = Q(-b²)/T'(-b²)` of `Q/T` at `t = -b²`, where `T(t) = ∏_{c ∈ S} (t + c²)`. -/
noncomputable def poleResidue (S : Finset ℕ) (Q : ℚ[X]) (b : ℕ) : ℚ :=
  Q.eval (-((b : ℚ) ^ 2)) / (derivative (∏ c ∈ S, (X + C ((c : ℚ) ^ 2)))).eval (-((b : ℚ) ^ 2))

/-- `T'(-b²) = ∏_{c ∈ S, c ≠ b} (c² - b²)` for `b ∈ S`. -/
theorem derivative_prod_eval (S : Finset ℕ) {b : ℕ} (hb : b ∈ S) :
    (derivative (∏ c ∈ S, (X + C ((c : ℚ) ^ 2)))).eval (-((b : ℚ) ^ 2))
      = ∏ c ∈ S.erase b, ((c : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
  have hT : (∏ c ∈ S, (X + C ((c : ℚ) ^ 2)))
      = Lagrange.nodal S (fun c : ℕ => -((c : ℚ) ^ 2)) := by
    rw [Lagrange.nodal_eq]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [C_neg, sub_neg_eq_add]
  have h : (derivative (Lagrange.nodal S (fun c : ℕ => -((c : ℚ) ^ 2)))).eval (-((b : ℚ) ^ 2))
      = (Lagrange.nodal (S.erase b) (fun c : ℕ => -((c : ℚ) ^ 2))).eval (-((b : ℚ) ^ 2)) :=
    Lagrange.eval_nodal_derivative_eval_node_eq hb
  rw [hT, h, Lagrange.eval_nodal]
  refine Finset.prod_congr rfl fun c _ => ?_
  ring

/-- `c² ≢ b² (mod p)` when `c ≢ ±b (mod p)`. -/
theorem not_dvd_sq_sub_sq {c b : ℕ} (h1 : (c : ZMod p) ≠ b) (h2 : (c : ZMod p) ≠ -(b : ZMod p)) :
    ¬ (p : ℤ) ∣ (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
  intro hdvd
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] at h
  have h0 : ((c : ZMod p) - b) * ((c : ZMod p) + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact h1 (sub_eq_zero.mp h')
  · exact h2 (eq_neg_of_add_eq_zero_left h')

/-- The arithmetic core of part 2. With `ρ = Q_a/(p M D)` and `ρ' = -Q_{a'}/(p M D')`, where
`M`, `D`, `D'` are `p`-units, `D ≡ D'` and `Q_a ≡ Q_{a'}` modulo `p`, both `p ρ` and `p ρ'` are
`p`-integral, `ρ + ρ'` is `p`-integral, and `v_p(ρ) = v_p(ρ') = -1` when `Q_a` is a `p`-unit. -/
theorem pair_core {M D D' Qa Qa' ρ ρ' : ℚ} (hM0 : M ≠ 0) (hMv : padicValRat p M = 0)
    (hD0 : D ≠ 0) (hDv : padicValRat p D = 0) (hD'0 : D' ≠ 0) (hD'v : padicValRat p D' = 0)
    (hDD : (D - D') / p ∈ pInt p) (hQa : Qa ∈ pInt p) (hQa' : Qa' ∈ pInt p)
    (hQQ : (Qa - Qa') / p ∈ pInt p) (hρ : ρ = Qa / (p * M * D))
    (hρ' : ρ' = -(Qa' / (p * M * D'))) :
    (p : ℚ) * ρ ∈ pInt p ∧ (p : ℚ) * ρ' ∈ pInt p ∧ ρ + ρ' ∈ pInt p ∧
      (Qa ≠ 0 → padicValRat p Qa = 0 → padicValRat p ρ = -1 ∧ padicValRat p ρ' = -1) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpp : (p : ℚ) * (p : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hp0
  have hMi := inv_mem_pInt_of_padicValRat_eq_zero hMv
  have hDi := inv_mem_pInt_of_padicValRat_eq_zero hDv
  have hD'i := inv_mem_pInt_of_padicValRat_eq_zero hD'v
  have hD'm := mem_pInt_of_padicValRat_eq_zero hD'v
  have hy : (p : ℚ) * ρ = Qa * M⁻¹ * D⁻¹ := by
    rw [hρ]
    linear_combination (Qa * M⁻¹ * D⁻¹) * hpp
  have hy' : (p : ℚ) * ρ' = -(Qa' * M⁻¹ * D'⁻¹) := by
    rw [hρ']
    linear_combination (-(Qa' * M⁻¹ * D'⁻¹)) * hpp
  have hx : (Qa * D⁻¹ - Qa' * D'⁻¹) / p
      = ((Qa - Qa') / p * D' - Qa' * ((D - D') / p)) * D⁻¹ * D'⁻¹ := by
    have h1 : D * D⁻¹ = 1 := mul_inv_cancel₀ hD0
    have h2 : D' * D'⁻¹ = 1 := mul_inv_cancel₀ hD'0
    linear_combination (Qa' * D'⁻¹ / p) * h1 - (Qa * D⁻¹ / p) * h2
  have hsum : ρ + ρ' = (Qa * D⁻¹ - Qa' * D'⁻¹) / p * M⁻¹ := by
    rw [hρ, hρ']
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hy]
    exact mul_mem (mul_mem hQa hMi) hDi
  · rw [hy']
    exact neg_mem (mul_mem (mul_mem hQa' hMi) hD'i)
  · rw [hsum, hx]
    exact mul_mem (mul_mem (mul_mem (sub_mem (mul_mem hQQ hD'm) (mul_mem hQa' hDD)) hDi) hD'i)
      hMi
  · intro hQa0 hQav
    obtain ⟨hQa'0, hQa'v⟩ := padicValRat_eq_zero_of_congr hQa0 hQav hQQ
    have e := padicValRat.div (p := p) hQa0 (mul_ne_zero (mul_ne_zero hp0 hM0) hD0)
    rw [padicValRat.mul (mul_ne_zero hp0 hM0) hD0, padicValRat.mul hp0 hM0,
      padicValRat.self hp.out.one_lt] at e
    have e' := padicValRat.div (p := p) hQa'0 (mul_ne_zero (mul_ne_zero hp0 hM0) hD'0)
    rw [padicValRat.mul (mul_ne_zero hp0 hM0) hD'0, padicValRat.mul hp0 hM0,
      padicValRat.self hp.out.one_lt] at e'
    constructor
    · rw [hρ]
      omega
    · rw [hρ', padicValRat.neg]
      omega

/-- **Paired-pole congruence, part 2.** Let `p ≥ 7` be prime, `1 ≤ a ≤ (p - 1)/2`, `a' = p - a`,
let `S` be a finite set of natural numbers containing `a` and `a'` and no other integer
congruent to `±a` modulo `p`, and let `Q` have `p`-integral coefficients. The residues
`ρ_b = Q(-b²)/T'(-b²)` of `Q/T`, `T(t) = ∏_{b ∈ S} (t + b²)`, satisfy `v_p(ρ_a) ≥ -1` and
`v_p(ρ_{a'}) ≥ -1`, both with equality when `Q(-a²)` is a `p`-unit; `ρ_a + ρ_{a'}` is
`p`-integral; and `ρ_a π_a + ρ_{a'} π_{a'}` has `p`-integral coefficients. -/
theorem paired_residues (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ (p - 1) / 2)
    {S : Finset ℕ} (haS : a ∈ S) (ha'S : p - a ∈ S)
    (hS : ∀ b ∈ S, ((b : ZMod p) = a ∨ (b : ZMod p) = -(a : ZMod p)) → b = a ∨ b = p - a)
    {Q : ℚ[X]} (hQ : ∀ i, 0 ≤ padicValRat p (Q.coeff i)) :
    -1 ≤ padicValRat p (poleResidue S Q a) ∧ -1 ≤ padicValRat p (poleResidue S Q (p - a)) ∧
      (Q.eval (-((a : ℚ) ^ 2)) ≠ 0 → padicValRat p (Q.eval (-((a : ℚ) ^ 2))) = 0 →
        padicValRat p (poleResidue S Q a) = -1 ∧
          padicValRat p (poleResidue S Q (p - a)) = -1) ∧
      0 ≤ padicValRat p (poleResidue S Q a + poleResidue S Q (p - a)) ∧
      ∀ i, 0 ≤ padicValRat p
        ((C (poleResidue S Q a) * muPole a
          + C (poleResidue S Q (p - a)) * muPole (p - a)).coeff i) := by
  have hap : 2 * a < p := by omega
  have hap' : a < p := by omega
  have hq0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hA' : ((p - a : ℕ) : ℚ) = p - a := Nat.cast_sub hap'.le
  have hM : ((p - 2 * a : ℕ) : ℚ) = p - 2 * a := by
    rw [Nat.cast_sub hap.le]
    push_cast
    ring
  have hsq : ((p - a : ℕ) : ℚ) ^ 2 - (a : ℚ) ^ 2 = p * ((p - 2 * a : ℕ) : ℚ) := by
    rw [hA', hM]
    ring
  have hsq' : (a : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2 = -((p : ℚ) * ((p - 2 * a : ℕ) : ℚ)) := by
    linear_combination -hsq
  -- the factor `p - 2a` is a `p`-unit
  have hMnd : ¬ p ∣ p - 2 * a := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hM0 : ((p - 2 * a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMv : padicValRat p ((p - 2 * a : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hMnd, Nat.cast_zero]
  -- the other factors of `T'(-a²)` and `T'(-a'²)` are `p`-units
  have hAz : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
    rw [Nat.cast_sub hap'.le, ZMod.natCast_self, zero_sub]
  have hcR : ∀ c ∈ (S.erase a).erase (p - a),
      (c : ZMod p) ≠ a ∧ (c : ZMod p) ≠ -(a : ZMod p) := by
    intro c hc
    have hc' := Finset.mem_erase.mp hc
    have hc'' := Finset.mem_erase.mp hc'.2
    constructor
    · intro h
      rcases hS c hc''.2 (Or.inl h) with h' | h'
      · exact hc''.1 h'
      · exact hc'.1 h'
    · intro h
      rcases hS c hc''.2 (Or.inr h) with h' | h'
      · exact hc''.1 h'
      · exact hc'.1 h'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hDaZ : ¬ (p : ℤ) ∣ ∏ c ∈ (S.erase a).erase (p - a), ((c : ℤ) ^ 2 - (a : ℤ) ^ 2) :=
    Prime.not_dvd_finsetProd hpZ fun c hc => not_dvd_sq_sub_sq (hcR c hc).1 (hcR c hc).2
  have hDa'Z : ¬ (p : ℤ) ∣ ∏ c ∈ (S.erase a).erase (p - a),
      ((c : ℤ) ^ 2 - ((p - a : ℕ) : ℤ) ^ 2) := by
    refine Prime.not_dvd_finsetProd hpZ fun c hc => not_dvd_sq_sub_sq ?_ ?_
    · rw [hAz]
      exact (hcR c hc).2
    · rw [hAz, neg_neg]
      exact (hcR c hc).1
  have hDa := intCast_ne_zero_and_padicValRat_eq_zero hDaZ
  have hDa' := intCast_ne_zero_and_padicValRat_eq_zero hDa'Z
  simp only [Int.cast_prod, Int.cast_sub, Int.cast_pow, Int.cast_natCast] at hDa hDa'
  -- `D_a ≡ D_{a'}` and `Q(-a²) ≡ Q(-a'²)` modulo `p`
  have hMmem : ((p - 2 * a : ℕ) : ℚ) ∈ pInt p := natCast_mem _ _
  have hfg : ∀ c : ℕ, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2 - ((c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2)) / p
      ∈ pInt p := by
    intro c
    have e : (c : ℚ) ^ 2 - (a : ℚ) ^ 2 - ((c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2)
        = p * ((p - 2 * a : ℕ) : ℚ) := by
      linear_combination hsq
    rw [e, mul_div_cancel_left₀ _ hq0]
    exact hMmem
  have hDD := prod_sub_prod_div_mem (p := p) ((S.erase a).erase (p - a))
    (f := fun c : ℕ => (c : ℚ) ^ 2 - (a : ℚ) ^ 2)
    (g := fun c : ℕ => (c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2)
    (fun c => sub_mem (pow_mem (natCast_mem _ c) 2) (pow_mem (natCast_mem _ a) 2))
    (fun c => sub_mem (pow_mem (natCast_mem _ c) 2) (pow_mem (natCast_mem _ _) 2)) hfg
  have hQ' : ∀ i, Q.coeff i ∈ pInt p := fun i => mem_pInt_iff_padicValRat.mpr (hQ i)
  have hxA : -((a : ℚ) ^ 2) ∈ pInt p := neg_mem (pow_mem (natCast_mem _ a) 2)
  have hxA' : -(((p - a : ℕ) : ℚ) ^ 2) ∈ pInt p := neg_mem (pow_mem (natCast_mem _ _) 2)
  have hxx : (-((a : ℚ) ^ 2) - -(((p - a : ℕ) : ℚ) ^ 2)) / p ∈ pInt p := by
    have e : -((a : ℚ) ^ 2) - -(((p - a : ℕ) : ℚ) ^ 2) = p * ((p - 2 * a : ℕ) : ℚ) := by
      linear_combination hsq
    rw [e, mul_div_cancel_left₀ _ hq0]
    exact hMmem
  -- the residues in closed form
  have ha'mem : p - a ∈ S.erase a := Finset.mem_erase.mpr ⟨by omega, ha'S⟩
  have hamem : a ∈ S.erase (p - a) := Finset.mem_erase.mpr ⟨by omega, haS⟩
  have hsplit : ∏ c ∈ S.erase a, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)
      = (((p - a : ℕ) : ℚ) ^ 2 - (a : ℚ) ^ 2)
        * ∏ c ∈ (S.erase a).erase (p - a), ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) :=
    (Finset.mul_prod_erase (S.erase a) (fun c : ℕ => (c : ℚ) ^ 2 - (a : ℚ) ^ 2) ha'mem).symm
  have hsplit' : ∏ c ∈ S.erase (p - a), ((c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2)
      = ((a : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2)
        * ∏ c ∈ (S.erase a).erase (p - a), ((c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2) := by
    rw [Finset.erase_right_comm]
    exact (Finset.mul_prod_erase (S.erase (p - a))
      (fun c : ℕ => (c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2) hamem).symm
  have hρa : poleResidue S Q a = Q.eval (-((a : ℚ) ^ 2)) / ((p : ℚ) * ((p - 2 * a : ℕ) : ℚ)
      * ∏ c ∈ (S.erase a).erase (p - a), ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) := by
    rw [poleResidue, derivative_prod_eval S haS, hsplit, hsq]
  have hρa' : poleResidue S Q (p - a) = -(Q.eval (-(((p - a : ℕ) : ℚ) ^ 2))
      / ((p : ℚ) * ((p - 2 * a : ℕ) : ℚ)
        * ∏ c ∈ (S.erase a).erase (p - a), ((c : ℚ) ^ 2 - ((p - a : ℕ) : ℚ) ^ 2))) := by
    rw [poleResidue, derivative_prod_eval S ha'S, hsplit', hsq', neg_mul, div_neg]
  obtain ⟨hy, hy', hsum, heq⟩ := pair_core hM0 hMv hDa.1 hDa.2 hDa'.1 hDa'.2 hDD
    (eval_mem_pInt hQ' hxA) (eval_mem_pInt hQ' hxA') (eval_sub_eval_div_mem hQ' hxA hxA' hxx)
    hρa hρa'
  refine ⟨neg_one_le_padicValRat_of_mul_mem hy, neg_one_le_padicValRat_of_mul_mem hy', heq,
    mem_pInt_iff_padicValRat.mp hsum, fun i => ?_⟩
  -- `ρ_a π_a + ρ_{a'} π_{a'} = (p ρ_a) (π_a - π_{a'})/p + (ρ_a + ρ_{a'}) π_{a'}`
  obtain ⟨Dl, hDl, hdiff⟩ := muPole_sub_eq hp7 ha1 hap
  have hpoly : C (poleResidue S Q a) * muPole a + C (poleResidue S Q (p - a)) * muPole (p - a)
      = C ((p : ℚ) * poleResidue S Q a) * Dl
        + C (poleResidue S Q a + poleResidue S Q (p - a)) * muPole (p - a) := by
    rw [map_mul, map_add]
    linear_combination C (poleResidue S Q a) * hdiff
  rw [hpoly]
  refine mem_pInt_iff_padicValRat.mp (mem_pIntPoly.mp ?_ i)
  exact add_mem (mul_mem (C_mem_pIntPoly hy) hDl)
    (mul_mem (C_mem_pIntPoly hsum) (muPole_mem_pIntPoly hp7 (by omega) (by omega)))

end PairedPoles

end ZetaSeven
