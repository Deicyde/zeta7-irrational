import ZetaSeven.MatrixDet
import ZetaSeven.DegreeLemma
import ZetaSeven.InnerEstimate
import ZetaSeven.OuterRangeData
import ZetaSeven.SmallPrimeEstimate
import ZetaSeven.OuterEstimate

/-!
# Normalization and integrality (paper Section 5.1, Proposition 5.1, equations (60)-(63))

Prince Anand, "Zeta 7 is Irrational", Section 5.1. For `M ∈ 40ℤ_{>0}` and `K ≥ 200 M²` the
local estimates of Section 4 combine into a positive rational factor `m_{K,M}` for which
`Q_{K,M} = m_{K,M} F_K` has integer coefficients.

* `innerExtraRows`: a fixed admissible choice of extra rows (Definition 4.1), which fixes the
  inner exponent `γ^in_p` used in (60) (`innerExtraRows_spec`).
* `LpKM`: the branch exponents `L_p(K, M)` of (60), with the branch equations `LpKM_of_le`,
  `LpKM_of_inner`, `LpKM_of_outer`.
* `mKM`: the normalization factor `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}` of (61), a positive
  rational (`mKM_pos`) with `v_p(m_{K,M}) = -L_p(K,M)` for `p ≤ 2h` and `0` for `p > 2h`
  (`padicValRat_mKM`).
* `padicValRat_SK_legendre`: Legendre's formula (62) for `v_p(S_K)`, at every prime.
* `QKM`: the polynomial `Q_{K,M} = m_{K,M} F_K = m_{K,M} S_K Δ_K` of (63) (`QKM_eq`), of degree
  exactly `h` for `K > 0` (`natDegree_QKM`, the last sentence of Lemma 2.3).
* `outerRange_of_K_lt_three_mul`: a prime `p ≤ K` with `3p > K` satisfies (52).
* **Proposition 5.1**: `v_p(Q_{K,M}) ≥ 0` coefficientwise at every prime
  (`padicValRat_QKM_nonneg`), hence `Q_{K,M} ∈ ℤ[X]` (`normalization_integrality`).

The valuation `v_p` of a coefficient is `padicValRat`, as in `ZetaSeven.inner_estimate`.
`K = 40n` (`ZetaSeven.K`), so `K ∈ 40ℤ_{>0}` is `n ≥ 1`, which `K ≥ 200 M²` forces. The
statements assume `M ≥ 40` in place of `M ∈ 40ℤ_{>0}`, as `ZetaSeven.InnerRange` does; the proof
uses no divisibility of `M`.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The branch exponents (60), the factor (61) and the polynomial (63) -/

/-- A fixed admissible choice of extra rows for the inner exponent (Definition 4.1). The paper
orders the classes by decreasing `ℓ_K` with ties broken arbitrarily, so `γ^in_p` depends on a
choice; this is the choice `Classical.epsilon (ExtraRows n M p)`. Under (44) admissible choices
exist (`exists_extraRows`), so this one is admissible (`innerExtraRows_spec`); the inner
estimate `ZetaSeven.inner_estimate` and the inner limiting bound `ZetaSeven.gammaIn_approx` hold
for every admissible choice. Outside (44) the value is unspecified and unused. -/
noncomputable def innerExtraRows (n M p : ℕ) : ℕ → ℕ :=
  Classical.epsilon (ExtraRows n M p)

/-- Under (44) the fixed choice `innerExtraRows` is admissible (Definition 4.1). -/
theorem innerExtraRows_spec {n M p : ℕ} (hR : InnerRange n M p) [Fact p.Prime] :
    ExtraRows n M p (innerExtraRows n M p) :=
  Classical.epsilon_spec (exists_extraRows hR)

/-- (60): the branch exponent `L_p(K, M)`:
* `-8h⌊log_p(5K)⌋ - h v_p(720)` if `pM ≤ K` (the crude branch, (41));
* `v_p(S_K) + γ^in_p` if `pM > K` and `3p ≤ K` (the inner branch, (49)), with the inner exponent
  `γ^in_p = gammaIn n M p (innerExtraRows n M p)`;
* `v_p(S_K) + γ^out_p` if `3p > K` (the outer branch, (59)), with `γ^out_p = gammaOut n p`,
  which is `0` for `p > K` (Section 5.1, first sentence; `gammaOut_of_K_lt`).

Here `⌊log_p(5K)⌋ = Nat.log p (5K)` and `v_p(S_K) = padicValRat p (SK n)`, given by Legendre's
formula (62) (`padicValRat_SK_legendre`). For `M ≥ 3` the three conditions of (60) are disjoint
and cover every `p`; the definition tests them in this order. -/
noncomputable def LpKM (n M p : ℕ) : ℤ :=
  if M * p ≤ K n then
    -(8 * (hDim n : ℤ) * (Nat.log p (5 * K n) : ℤ)) - (hDim n : ℤ) * (padicValNat p 720 : ℤ)
  else if 3 * p ≤ K n then padicValRat p (SK n) + gammaIn n M p (innerExtraRows n M p)
  else padicValRat p (SK n) + gammaOut n p

/-- (60), crude branch `pM ≤ K`. -/
theorem LpKM_of_le {n M p : ℕ} (h : M * p ≤ K n) :
    LpKM n M p = -(8 * (hDim n : ℤ) * (Nat.log p (5 * K n) : ℤ))
      - (hDim n : ℤ) * (padicValNat p 720 : ℤ) := by
  rw [LpKM, ite_eq_left h]

/-- (60), inner branch `pM > K`, `3p ≤ K`. -/
theorem LpKM_of_inner {n M p : ℕ} (h1 : K n < M * p) (h3 : 3 * p ≤ K n) :
    LpKM n M p = padicValRat p (SK n) + gammaIn n M p (innerExtraRows n M p) := by
  rw [LpKM, ite_eq_right (not_le.mpr h1), ite_eq_left h3]

/-- (60), outer branch `3p > K` (for `M ≥ 3`, which makes `pM > K` automatic). -/
theorem LpKM_of_outer {n M p : ℕ} (hM : 3 ≤ M) (h3 : K n < 3 * p) :
    LpKM n M p = padicValRat p (SK n) + gammaOut n p := by
  have hMp : 3 * p ≤ M * p := Nat.mul_le_mul_right p hM
  rw [LpKM, ite_eq_right (show ¬ M * p ≤ K n by omega),
    ite_eq_right (show ¬ 3 * p ≤ K n by omega)]

/-- (61): the normalization factor `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`, the product over the
primes `p ≤ 2h`. It is a positive rational (`mKM_pos`). -/
noncomputable def mKM (n M : ℕ) : ℚ :=
  ∏ p ∈ (Iic (2 * hDim n)).filter Nat.Prime, (p : ℚ) ^ (-LpKM n M p)

/-- (63): the final polynomial `Q_{K,M} = m_{K,M} F_K`. -/
noncomputable def QKM (n M : ℕ) : ℚ[X] := C (mKM n M) * FK n

/-- (63): `Q_{K,M} = m_{K,M} S_K Δ_K`. -/
theorem QKM_eq (n M : ℕ) : QKM n M = C (mKM n M * SK n) * DeltaK n := by
  rw [QKM, FK, ← mul_assoc, ← C_mul]

/-! ## Valuations of products, of `S_K` (Legendre's formula (62)) and of `m_{K,M}` -/

private theorem ni_padicValRat_prod {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private theorem ni_padicValRat_prime {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) :
    padicValRat p (q : ℚ) = if q = p then 1 else 0 := by
  rw [padicValRat.of_nat]
  split_ifs with h
  · rw [h, padicValNat_self, Nat.cast_one]
  · rw [padicValNat.eq_zero_of_not_dvd
      fun hd => h ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp hd).symm, Nat.cast_zero]

private theorem ni_factorial_ne_zero (j : ℕ) : (Nat.factorial j : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)

private theorem ni_SK_ne_zero (n : ℕ) : SK n ≠ 0 := by
  rw [SK]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (ni_factorial_ne_zero _)) (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero (pow_ne_zero _ (ni_factorial_ne_zero _))
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ni_factorial_ne_zero _)))

/-- **Legendre's formula (62)** for `v_p(S_K)`, at every prime `p`:
`v_p(S_K) = 2h ∑_{a≥1} ⌊K/p^a⌋ - 16h ∑_{a≥1} ⌊N/p^a⌋ - 2 ∑_{i=1}^{h-1} ∑_{a≥1} ⌊2i/p^a⌋
+ (h-1) v_p(4)`.
The sums over `a ≥ 1` are finite: every term with `p^a > 2h` vanishes, since `K`, `N` and
`2i` are at most `2h`. They are written over `Ico 1 b` for any `b > log_p(2h)`, as in Mathlib's
`padicValNat_factorial`. The exponent `h - 1` is the one of `4^{h-1}` in (8). -/
theorem padicValRat_SK_legendre (n p : ℕ) [Fact p.Prime] {b : ℕ}
    (hb : Nat.log p (2 * hDim n) < b) :
    padicValRat p (SK n) =
      2 * hDim n * ∑ a ∈ Ico 1 b, ((K n / p ^ a : ℕ) : ℤ)
        - 16 * hDim n * ∑ a ∈ Ico 1 b, ((N n / p ^ a : ℕ) : ℤ)
        - 2 * ∑ i ∈ Icc 1 (hDim n - 1), ∑ a ∈ Ico 1 b, ((2 * i / p ^ a : ℕ) : ℤ)
        + ((hDim n - 1 : ℕ) : ℤ) * (padicValNat p 4 : ℤ) := by
  have hfac : ∀ j : ℕ, j ≤ 2 * hDim n →
      padicValRat p (Nat.factorial j : ℚ) = ∑ a ∈ Ico 1 b, ((j / p ^ a : ℕ) : ℤ) := by
    intro j hj
    rw [padicValRat.of_nat, padicValNat_factorial ((Nat.log_mono_right hj).trans_lt hb),
      Nat.cast_sum]
  have hKdef : K n = 40 * n := rfl
  have hNdef : N n = 3 * n := rfl
  have hhdef : hDim n = 37 * n := rfl
  have hK : K n ≤ 2 * hDim n := by omega
  have hN : N n ≤ 2 * hDim n := by omega
  have h4 : padicValRat p (4 : ℚ) = (padicValNat p 4 : ℤ) := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  have hprod : (∏ i ∈ Icc 1 (hDim n - 1), (Nat.factorial (2 * i) : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ni_factorial_ne_zero _)
  have h4ne : (4 : ℚ) ^ (hDim n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [SK, padicValRat.div (mul_ne_zero (pow_ne_zero _ (ni_factorial_ne_zero _)) h4ne)
      (mul_ne_zero (pow_ne_zero _ (ni_factorial_ne_zero _)) hprod),
    padicValRat.mul (pow_ne_zero _ (ni_factorial_ne_zero _)) h4ne,
    padicValRat.mul (pow_ne_zero _ (ni_factorial_ne_zero _)) hprod,
    padicValRat.pow, padicValRat.pow, padicValRat.pow, h4, hfac _ hK, hfac _ hN,
    ni_padicValRat_prod (Icc 1 (hDim n - 1)) (fun i => (Nat.factorial (2 * i) : ℚ) ^ 2)
      fun i _ => pow_ne_zero _ (ni_factorial_ne_zero _)]
  have hsum : ∑ i ∈ Icc 1 (hDim n - 1), padicValRat p ((Nat.factorial (2 * i) : ℚ) ^ 2)
      = ∑ i ∈ Icc 1 (hDim n - 1), 2 * ∑ a ∈ Ico 1 b, ((2 * i / p ^ a : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi2 : 2 * i ≤ 2 * hDim n := by have := (Finset.mem_Icc.mp hi).2; omega
    rw [padicValRat.pow, hfac _ hi2]
    norm_num
  rw [hsum, ← Finset.mul_sum]
  push_cast
  ring

/-- For a prime `p > 2h` every factorial in `S_K` is a `p`-unit: `v_p(S_K) = 0`. -/
theorem padicValRat_SK_of_lt {n p : ℕ} [Fact p.Prime] (h : 2 * hDim n < p) :
    padicValRat p (SK n) = 0 := by
  have hKdef : K n = 40 * n := rfl
  have hNdef : N n = 3 * n := rfl
  have hhdef : hDim n = 37 * n := rfl
  have hz : ∀ m c : ℕ, m ≤ 2 * hDim n → ∑ a ∈ Ico 1 c, ((m / p ^ a : ℕ) : ℤ) = 0 := by
    intro m c hm
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha1 : a ≠ 0 := by have := (Finset.mem_Ico.mp ha).1; omega
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hm.trans_lt h) (Nat.le_self_pow ha1 p)),
      Nat.cast_zero]
  have hi : ∑ i ∈ Icc 1 (hDim n - 1),
      ∑ a ∈ Ico 1 (Nat.log p (2 * hDim n) + 1), ((2 * i / p ^ a : ℕ) : ℤ) = 0 :=
    Finset.sum_eq_zero fun i hi => hz (2 * i) _ (by have := (Finset.mem_Icc.mp hi).2; omega)
  have h4 : ((hDim n - 1 : ℕ) : ℤ) * (padicValNat p 4 : ℤ) = 0 := by
    by_cases hp4 : p ∣ 4
    · have hp4' : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
      have h0 : hDim n - 1 = 0 := by omega
      rw [h0, Nat.cast_zero, zero_mul]
    · rw [padicValNat.eq_zero_of_not_dvd hp4, Nat.cast_zero, mul_zero]
  have hK : K n ≤ 2 * hDim n := by omega
  have hN : N n ≤ 2 * hDim n := by omega
  rw [padicValRat_SK_legendre n p (b := Nat.log p (2 * hDim n) + 1) (Nat.lt_add_one _),
    hz (K n) _ hK, hz (N n) _ hN, hi, h4]
  ring

/-- `m_{K,M}` is a positive rational. -/
theorem mKM_pos (n M : ℕ) : 0 < mKM n M := by
  rw [mKM]
  exact Finset.prod_pos fun q hq => zpow_pos (Nat.cast_pos.mpr (Finset.mem_filter.mp hq).2.pos) _

/-- Lemma 2.3, last sentence: `Q_{K,M} = m_{K,M} S_K Δ_K` also has degree exactly `h`, since
`m_{K,M} S_K ≠ 0`. -/
theorem natDegree_QKM (n M : ℕ) (hn : 0 < n) : (QKM n M).natDegree = hDim n := by
  have hS : 0 < SK n := by
    unfold SK
    positivity
  rw [QKM_eq, natDegree_C_mul (mul_pos (mKM_pos n M) hS).ne']
  exact (degreeLemma n hn).1

/-- `v_p(m_{K,M}) = -L_p(K, M)` for a prime `p ≤ 2h`, and `p ∤ m_{K,M}` for a prime `p > 2h`. -/
theorem padicValRat_mKM (n M p : ℕ) [hp : Fact p.Prime] :
    padicValRat p (mKM n M) = if p ≤ 2 * hDim n then -LpKM n M p else 0 := by
  have hne : ∀ q ∈ (Iic (2 * hDim n)).filter Nat.Prime, (q : ℚ) ^ (-LpKM n M q) ≠ 0 :=
    fun q hq => zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hq).2.ne_zero)
  have hterm : ∀ q ∈ (Iic (2 * hDim n)).filter Nat.Prime,
      padicValRat p ((q : ℚ) ^ (-LpKM n M q)) = if q = p then -LpKM n M q else 0 := by
    intro q hq
    rw [padicValRat.zpow, ni_padicValRat_prime (Finset.mem_filter.mp hq).2]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]
  have hmem : p ∈ (Iic (2 * hDim n)).filter Nat.Prime ↔ p ≤ 2 * hDim n := by
    simp [hp.out]
  rw [mKM, ni_padicValRat_prod _ _ hne, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases h : p ≤ 2 * hDim n
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hmem.mp h), ite_eq_right h]

/-! ## The outer-range hypothesis in the outer branch -/

/-- A prime `p ≤ K` with `3p > K` satisfies the outer-range hypothesis (52). The article
derives this from `K ≥ 200 M² ≥ 320000`; no bound on `K` is needed: `3p > K = 40n` gives
`p ≥ 13n + 1`, and `p ≤ K` forces `n ≥ 1`, so `p ≥ 14`; hence `p ≥ 11`, `p² > 2K` and
`7N ≤ 2p - 2`. -/
theorem outerRange_of_K_lt_three_mul {n p : ℕ} (h3 : K n < 3 * p) (hpK : p ≤ K n) :
    OuterRange n p := by
  have hKdef : K n = 40 * n := rfl
  have hNdef : N n = 3 * n := rfl
  have h1 : 13 * n + 1 ≤ p := by omega
  have h2 : 14 ≤ p := by omega
  refine ⟨by omega, h3, hpK, ?_, by omega⟩
  calc 2 * K n < (13 * n + 1) * 14 := by omega
    _ ≤ p * p := Nat.mul_le_mul h1 h2
    _ = p ^ 2 := (sq p).symm

/-! ## Proposition 5.1 -/

/-- `v_p(F_K) = v_p(S_K) + v_p(Δ_K)` on every coefficient of `F_K = S_K Δ_K` with
`Δ_K` coefficient nonzero. -/
private theorem ni_padicValRat_FK_coeff {n p : ℕ} [Fact p.Prime] {k : ℕ}
    (hD : (DeltaK n).coeff k ≠ 0) :
    padicValRat p ((FK n).coeff k) = padicValRat p (SK n) + padicValRat p ((DeltaK n).coeff k) := by
  rw [FK, coeff_C_mul, padicValRat.mul (ni_SK_ne_zero n) hD]

/-- **Proposition 5.1**, prime by prime. For `M ≥ 40` and `K = 40n ≥ 200 M²`, every coefficient
of `Q_{K,M}` has nonnegative `p`-adic valuation at every prime `p`: for `p ≤ 2h` each branch of
(60) cancels against its local estimate (the crude bound (41), the inner estimate
(Proposition 4.4), the outer estimate (Proposition 4.6) under (52) for `K/3 < p ≤ K`, and its
large-prime clause for `K < p ≤ 2h`, where `γ^out_p = 0`); for `p > 2h`, `p ∤ m_{K,M}`,
`v_p(S_K) = 0` and `Δ_K` is `p`-integral. (For the coefficient `0` this is Lean's
`padicValRat p 0 = 0`.) -/
theorem padicValRat_QKM_nonneg {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (p : ℕ)
    [Fact p.Prime] (k : ℕ) : 0 ≤ padicValRat p ((QKM n M).coeff k) := by
  have hKdef : K n = 40 * n := rfl
  have hhdef : hDim n = 37 * n := rfl
  rw [QKM, coeff_C_mul]
  rcases eq_or_ne ((FK n).coeff k) 0 with h0 | h0
  · simp [h0]
  have hD : (DeltaK n).coeff k ≠ 0 := by
    intro hD
    rw [FK, coeff_C_mul, hD, mul_zero] at h0
    exact h0 rfl
  have hvF := ni_padicValRat_FK_coeff (p := p) hD
  rw [padicValRat.mul (mKM_pos n M).ne' h0, padicValRat_mKM]
  split_ifs with h2h
  · rw [LpKM]
    split_ifs with hc hi
    · -- crude branch `pM ≤ K`: the global bound (41)
      have := FK_small_prime_bound n p k
      linarith
    · -- inner branch `pM > K`, `3p ≤ K`: Proposition 4.4
      have hR : InnerRange n M p := ⟨hM, hK, not_le.mp hc, hi⟩
      have := inner_estimate hR (innerExtraRows_spec hR) k hD
      rw [hvF]
      linarith
    · -- outer branch `3p > K`
      rw [hvF]
      by_cases hpK : p ≤ K n
      · -- `K/3 < p ≤ K`: (52) holds, Proposition 4.6
        have := outer_estimate (outerRange_of_K_lt_three_mul (not_le.mp hi) hpK) k hD
        linarith
      · -- `K < p ≤ 2h`: `γ^out_p = 0`, large-prime clause of Proposition 4.6
        rw [gammaOut_of_K_lt (not_le.mp hpK)]
        have := outer_estimate_of_K_lt (n := n) (not_le.mp hpK) k
        linarith
  · -- `p > 2h`: `S_K` is a `p`-unit and `Δ_K` is `p`-integral
    have hp2h : 2 * hDim n < p := not_le.mp h2h
    rw [hvF, padicValRat_SK_of_lt hp2h]
    have := outer_estimate_of_K_lt (n := n) (p := p) (by omega) k
    linarith

private theorem ni_den_eq_one {q : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) :
    q.den = 1 := by
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have : Fact p.Prime := ⟨hp⟩
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    rw [Int.natCast_dvd] at hn
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hn hpd q.reduced
  have h1 := h p hp
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at h1
  have := one_le_padicValNat_of_dvd (p := p) q.den_nz hpd
  omega

/-- **Proposition 5.1** (integrality). For `M ≥ 40` and `K = 40n ≥ 200 M²`, the polynomial
`Q_{K,M} = m_{K,M} F_K = m_{K,M} S_K Δ_K` of (63) belongs to `ℤ[X]`: it is the image of an
integer polynomial. The source states it for `M ∈ 40ℤ_{>0}`, a special case of `M ≥ 40`. -/
theorem normalization_integrality {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) :
    ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = QKM n M := by
  refine (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr fun k => ?_)
  have hden : ((QKM n M).coeff k).den = 1 := ni_den_eq_one fun p hp => by
    have : Fact p.Prime := ⟨hp⟩
    exact padicValRat_QKM_nonneg hM hK p k
  exact ⟨((QKM n M).coeff k).num, by rw [eq_intCast]; exact Rat.coe_int_num_of_den_eq_one hden⟩

end ZetaSeven
