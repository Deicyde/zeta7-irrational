import ZetaSeven.InnerEstimate

/-!
# Outer range data (paper Section 4.2, equations (52), (54), (56), (58)-(59))

Prince Anand, "Zeta 7 is Irrational", Section 4.2, and Section 5.1, first sentence: the
statement data of the outer range, shared by the outer-range nodes.

* `OuterRange`: the outer-range hypothesis (52).
* `rankCorr`: the rank correction `r_p` (54), with `rankCorr_cast`.
* `classDelta`: the class indicator `δ_a = 1_{a ≤ N}` of Section 4.2.3.
* `outerWeight`: the outer weights (56) of a class, half-integers in `ℚ`; `outerWeightDbl`
  is twice (56) in `ℤ`, the convention of `ZetaSeven.rank_lemma`
  (`outerWeightDbl_eq_two_mul`).
* `classV`, `classU`, `classT`: `v`, `u` and `t_p` of (58).
* `gammaOut`: the outer exponent `γ^out_p`, which is (59) for `K/3 < p ≤ K`
  (`gammaOut_of_lt_two_mul`, `gammaOut_of_two_mul_le`) and `0` for `p > K`
  (`gammaOut_of_K_lt`, Section 5.1).

The half-range `m = mHalf p`, `⌊K/p⌋ = mK n p` and the class counts
`ℓ_K(a) = ell p (K n) a` are those of the local range data (42)-(43).
-/

namespace ZetaSeven

/-! ## The outer-range hypothesis and the rank correction -/

/-- The outer-range hypothesis (52): `p ≥ 11`, `K/3 < p ≤ K`, `p² > 2K` and `7N ≤ 2p - 2`.
`K/3 < p` is written `K < 3p`; the natural subtraction `2p - 2` does not truncate, since
`p ≥ 11`. -/
structure OuterRange (n p : ℕ) : Prop where
  eleven_le : 11 ≤ p
  K_lt : K n < 3 * p
  le_K : p ≤ K n
  two_mul_K_lt : 2 * K n < p ^ 2
  seven_mul_N_le : 7 * N n ≤ 2 * p - 2

/-- (54): the rank correction `r_p = min(h, max(0, K + 6N - 3p + 4))`, as a natural number
(`Int.toNat x = max(0, x)`; see `rankCorr_cast`). -/
def rankCorr (n p : ℕ) : ℕ :=
  min (hDim n) (Int.toNat ((K n : ℤ) + 6 * N n - 3 * p + 4))

/-- (54) verbatim: `r_p = min(h, max(0, K + 6N - 3p + 4))` in `ℤ`. -/
theorem rankCorr_cast (n p : ℕ) :
    (rankCorr n p : ℤ) = min (hDim n : ℤ) (max 0 ((K n : ℤ) + 6 * N n - 3 * p + 4)) := by
  unfold rankCorr
  omega

/-! ## The class indicator and the outer weights (56) -/

/-- The class indicator `δ_a = 1` if `a ≤ N` and `δ_a = 0` otherwise (Section 4.2.3,
`δ = 1_{a ≤ N}`). The source uses it for the classes `1 ≤ a ≤ m`; the definition is total. -/
def classDelta (n a : ℕ) : ℕ := if a ≤ N n then 1 else 0

/-- (56): the outer weight `w^out_{a,i}` of the class `a`, with `ℓ = ℓ_K(a) = ell p (K n) a`
and `δ = δ_a = classDelta n a`: `min(0, i + 4δ - (ℓ + 6)/2)` if `i < ℓ - 2` and `0` if
`i ≥ ℓ - 2`. The weights are half-integers, so the value is in `ℚ`. The source uses the
classes `1 ≤ a ≤ m` and the indices `0 ≤ i < ℓ - δ`; the definition is total. The natural
subtraction `ℓ - 2` agrees with the source: for `ℓ < 2` both make the first case empty. -/
def outerWeight (n p a i : ℕ) : ℚ :=
  if i < ell p (K n) a - 2 then
    min 0 ((i : ℚ) + 4 * classDelta n a - ((ell p (K n) a : ℚ) + 6) / 2)
  else 0

/-- Twice the outer weight (56) of a class with `l` poles and indicator `d`, as an integer:
`min(0, 2i + 8d - l - 6)` if `i < l - 2` and `0` if `i ≥ l - 2`. With `l = ell p (K n) a`
and `d = classDelta n a` it is `2 w^out_{a,i}` (`outerWeightDbl_eq_two_mul`);
`ZetaSeven.rank_lemma` takes doubled weights. -/
def outerWeightDbl (l d i : ℕ) : ℤ :=
  if i < l - 2 then min 0 (2 * (i : ℤ) + 8 * d - l - 6) else 0

/-- The doubled weight of the class `a` is twice its weight (56). -/
theorem outerWeightDbl_eq_two_mul (n p a i : ℕ) :
    (outerWeightDbl (ell p (K n) a) (classDelta n a) i : ℚ) = 2 * outerWeight n p a i := by
  unfold outerWeightDbl outerWeight
  split_ifs
  · rw [Int.cast_min, mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 2)]
    congr 1
    · simp
    · push_cast
      ring
  · simp

/-! ## The class data (58) and the outer exponent (59) -/

/-- (58): `v = K - p⌊K/p⌋`, with `⌊K/p⌋ = mK n p`. The natural subtraction does not
truncate, since `p⌊K/p⌋ ≤ K`; `v` is `K mod p` (`classV_eq_mod`). -/
def classV (n p : ℕ) : ℕ := K n - p * mK n p

/-- `v = K mod p`. -/
theorem classV_eq_mod (n p : ℕ) : classV n p = K n % p := by
  unfold classV mK
  exact (Nat.mod_def _ _).symm

/-- (58): `u = max(0, N + v - p + 1)`. -/
def classU (n p : ℕ) : ℤ := max 0 ((N n : ℤ) + classV n p - p + 1)

/-- (58): `t_p = min(N, v) + u`. -/
def classT (n p : ℕ) : ℤ := min (N n : ℤ) (classV n p : ℤ) + classU n p

/-- The outer exponent `γ^out_p`. For `K/3 < p ≤ K` it is (59):
`-9(K - p) + 8t_p - 1 - min(r_p, p - 1 - N + u)` when `K < 2p`, and
`-9(K - p) + 3 + 16N + 7t_p - min(r_p, p + u)` when `K ≥ 2p`. For `p > K` it is `0`
(Section 5.1, first sentence). For `p ≤ K/3`, where the source leaves `γ^out_p`
unspecified, it is the `K ≥ 2p` formula of (59). -/
def gammaOut (n p : ℕ) : ℤ :=
  if K n < p then 0
  else if K n < 2 * p then
    -9 * ((K n : ℤ) - p) + 8 * classT n p - 1
      - min (rankCorr n p : ℤ) ((p : ℤ) - 1 - N n + classU n p)
  else
    -9 * ((K n : ℤ) - p) + 3 + 16 * N n + 7 * classT n p
      - min (rankCorr n p : ℤ) ((p : ℤ) + classU n p)

/-- Section 5.1: `γ^out_p = 0` for `p > K`. -/
theorem gammaOut_of_K_lt {n p : ℕ} (h : K n < p) : gammaOut n p = 0 := by
  unfold gammaOut
  rw [ite_eq_left h]

/-- (59), case `K < 2p` (which gives `K/3 < p`), for `p ≤ K`. -/
theorem gammaOut_of_lt_two_mul {n p : ℕ} (hp : p ≤ K n) (h : K n < 2 * p) :
    gammaOut n p = -9 * ((K n : ℤ) - p) + 8 * classT n p - 1
      - min (rankCorr n p : ℤ) ((p : ℤ) - 1 - N n + classU n p) := by
  unfold gammaOut
  rw [ite_eq_right (Nat.not_lt.mpr hp), ite_eq_left h]

/-- (59), case `K ≥ 2p`. With `K/3 < p` this is the second clause of (59); for `p ≤ K/3`
it is the value the definition gives outside the source's range. -/
theorem gammaOut_of_two_mul_le {n p : ℕ} (h : 2 * p ≤ K n) :
    gammaOut n p = -9 * ((K n : ℤ) - p) + 3 + 16 * N n + 7 * classT n p
      - min (rankCorr n p : ℤ) ((p : ℤ) + classU n p) := by
  unfold gammaOut
  rw [ite_eq_right (show ¬ K n < p by omega), ite_eq_right (show ¬ K n < 2 * p by omega)]

end ZetaSeven
