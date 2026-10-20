import ZetaSeven.OuterWeightFamily

/-!
# Outer class rows (paper Section 4.2, proof of Proposition 4.6)

Prince Anand, "Zeta 7 is Irrational", Section 4.2, proof of Proposition 4.6: "For an ordinary
square class `a`, we use the rows `P_a q_{a,i}` where `q_{a,i}(t) = (t + a²)^i` for
`0 ≤ i < ℓ - 2` and `q_{a,i}(t) = E_a(t)(t + a²)^{i-(ℓ-2)}` for `ℓ - 2 ≤ i < ℓ - δ`, with `E_a`
the product of the class factors with `j > p`. Together with the zero-class rows, these form a
`ℤ_p`-unimodular basis." The paper defines neither `P_a` nor the zero-class rows, since it
defers the basis to its `ζ(5)` predecessor; `S_c`, `F_c`, `P_c` and the zero-class rows are
reconstructed by this project.

All polynomials are integer polynomials, in `ℤ[X]` (the variable `t` is `X`).

* `outerClassSet`: `S_c = {N < j ≤ K : j ≡ ±c (mod p)}`; `S_0` is the set of multiples of `p`
  in `(N, K]` (`outerClassSet_zero`).
* `outerClassPoly`: `F_c(t) = ∏_{j ∈ S_c} (t + j²)`.
* `outerCofactor`: `P_c = ∏_{0 ≤ d ≤ m, d ≠ c} F_d`, with `m = mHalf p`.
* `outerHighPoly`: `E_c(t) = ∏_{j ∈ S_c, j > p} (t + j²)`.
* `outerQ`: `q_{c,i}`, with `ℓ = ℓ_K(c)` (`outerQ_of_lt`, `outerQ_of_le`, `outerQ_exp_cast`).
* `outerRowPoly`, `outerRow`: the outer class rows, indexed by the index type `outerIdx` of the
  outer weight family: the class row `P_c q_{c,i}` at a class pair `(c, i)`, `c ≥ 1`
  (`outerRow_of_val_ne_zero`), and the zero-class row `P_0 t^i` at a zero-class pair `(0, i)`
  (`outerRow_of_val_eq_zero`).
* Every row is monic, with its degree computed from the sizes of the sets `S_d`
  (`monic_outerRowPoly`, `natDegree_outerRowPoly_zero`, `natDegree_outerRowPoly_of_ne_zero`).

The definitions are total: they need neither that `p` is prime nor the outer-range
hypothesis (52), and they are defined for every `c` and `i`.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The class sets and the class polynomials -/

/-- `S_c = {N < j ≤ K : j ≡ c or j ≡ -c (mod p)}`, written with the integer divisibilities of
the class counts `ell` (43). For `c = 0` it is the set of multiples of `p` in `(N, K]`
(`outerClassSet_zero`). The source uses `0 ≤ c ≤ m`; the definition is total. -/
def outerClassSet (n p c : ℕ) : Finset ℕ :=
  (Icc (N n + 1) (K n)).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c

/-- `F_c(t) = ∏_{j ∈ S_c} (t + j²)`, an integer polynomial. -/
noncomputable def outerClassPoly (n p c : ℕ) : ℤ[X] :=
  ∏ j ∈ outerClassSet n p c, (X + C ((j : ℤ) ^ 2))

/-- `P_c = ∏_{0 ≤ d ≤ m, d ≠ c} F_d`, with `m = mHalf p`, an integer polynomial. -/
noncomputable def outerCofactor (n p c : ℕ) : ℤ[X] :=
  ∏ d ∈ (range (mHalf p + 1)).erase c, outerClassPoly n p d

/-- `E_c(t) = ∏_{j ∈ S_c, j > p} (t + j²)`, the product of the class factors with `j > p`, an
integer polynomial. The source uses `1 ≤ c ≤ m`; the definition is total. -/
noncomputable def outerHighPoly (n p c : ℕ) : ℤ[X] :=
  ∏ j ∈ (outerClassSet n p c).filter (fun j => p < j), (X + C ((j : ℤ) ^ 2))

/-- `q_{c,i}`, with `ℓ = ℓ_K(c) = ell p (K n) c`: `(t + c²)^i` for `i < ℓ - 2`, and
`E_c(t) (t + c²)^{i - (ℓ - 2)}` for `i ≥ ℓ - 2`. The exponent `i - (ℓ - 2)` is written
`i + 2 - ℓ`, which does not truncate in the second case and is the integer `i - (ℓ - 2)`
(`outerQ_exp_cast`), also when `ℓ < 2`. The natural subtraction `ℓ - 2` in the case split
agrees with the source: for `ℓ < 2` both make the first case empty. The source uses
`1 ≤ c ≤ m` and `0 ≤ i < ℓ - δ_c`; the definition is total. -/
noncomputable def outerQ (n p c i : ℕ) : ℤ[X] :=
  if i < ell p (K n) c - 2 then (X + C ((c : ℤ) ^ 2)) ^ i
  else outerHighPoly n p c * (X + C ((c : ℤ) ^ 2)) ^ (i + 2 - ell p (K n) c)

/-! ## The outer class rows -/

/-- The outer class row of the pair `(c, i)`: the zero-class row `P_0 t^i` for `c = 0`, and the
class row `P_c q_{c,i}` for `c ≥ 1`. The rows on the index type of the outer weight family are
`outerRow`. -/
noncomputable def outerRowPoly (n p c i : ℕ) : ℤ[X] :=
  if c = 0 then outerCofactor n p 0 * X ^ i else outerCofactor n p c * outerQ n p c i

/-- The outer class rows, indexed by the index type `outerIdx n p` of the outer weight family:
the class row `P_c q_{c,i}` at a class pair `(c, i)` with `1 ≤ c ≤ m` and
`0 ≤ i < ℓ_K(c) - δ_c`, and the zero-class row `P_0 t^i` at a zero-class pair `(0, i)` with
`0 ≤ i < ⌊K/p⌋`. -/
noncomputable def outerRow (n p : ℕ) (ρ : outerIdx n p) : ℤ[X] :=
  outerRowPoly n p ρ.1 ρ.2

/-! ## The definitions, case by case -/

/-- Membership in `S_c`: `N < j ≤ K` and `j ≡ c` or `j ≡ -c (mod p)`. -/
theorem mem_outerClassSet {n p c j : ℕ} :
    j ∈ outerClassSet n p c ↔
      (N n < j ∧ j ≤ K n) ∧ ((p : ℤ) ∣ (j : ℤ) - c ∨ (p : ℤ) ∣ (j : ℤ) + c) := by
  simp only [outerClassSet, Finset.mem_filter, Finset.mem_Icc, Nat.add_one_le_iff]

/-- `S_0` is the set of multiples of `p` in `(N, K]`. -/
theorem outerClassSet_zero (n p : ℕ) :
    outerClassSet n p 0 = (Icc (N n + 1) (K n)).filter fun j => p ∣ j := by
  ext j
  simp only [outerClassSet, Finset.mem_filter, Nat.cast_zero, sub_zero, add_zero, or_self,
    Int.natCast_dvd_natCast]

/-- `q_{c,i} = (t + c²)^i` for `i < ℓ - 2`, with `ℓ = ℓ_K(c)`. -/
theorem outerQ_of_lt {n p c i : ℕ} (h : i < ell p (K n) c - 2) :
    outerQ n p c i = (X + C ((c : ℤ) ^ 2)) ^ i := by
  unfold outerQ
  rw [ite_eq_left h]

/-- `q_{c,i} = E_c(t) (t + c²)^{i - (ℓ - 2)}` for `i ≥ ℓ - 2`, with `ℓ = ℓ_K(c)`; the exponent
`i + 2 - ℓ` is the integer `i - (ℓ - 2)` (`outerQ_exp_cast`). -/
theorem outerQ_of_le {n p c i : ℕ} (h : ell p (K n) c - 2 ≤ i) :
    outerQ n p c i = outerHighPoly n p c * (X + C ((c : ℤ) ^ 2)) ^ (i + 2 - ell p (K n) c) := by
  unfold outerQ
  rw [ite_eq_right (Nat.not_lt.mpr h)]

/-- In the second case of `q_{c,i}`, the exponent `i + 2 - ℓ` is the integer `i - (ℓ - 2)`. -/
theorem outerQ_exp_cast {n p c i : ℕ} (h : ell p (K n) c - 2 ≤ i) :
    ((i + 2 - ell p (K n) c : ℕ) : ℤ) = (i : ℤ) - ((ell p (K n) c : ℤ) - 2) := by
  omega

/-- The row of a zero-class pair `(0, i)` is `P_0 t^i`. -/
theorem outerRowPoly_zero (n p i : ℕ) : outerRowPoly n p 0 i = outerCofactor n p 0 * X ^ i := by
  unfold outerRowPoly
  rw [ite_eq_left rfl]

/-- The row of a class pair `(c, i)` with `c ≥ 1` is `P_c q_{c,i}`. -/
theorem outerRowPoly_of_ne_zero (n p : ℕ) {c : ℕ} (hc : c ≠ 0) (i : ℕ) :
    outerRowPoly n p c i = outerCofactor n p c * outerQ n p c i := by
  unfold outerRowPoly
  rw [ite_eq_right hc]

/-- On the index type of the outer weight family, the zero-class pair `(0, i)` carries the
zero-class row `P_0 t^i`. -/
theorem outerRow_of_val_eq_zero (n p : ℕ) (ρ : outerIdx n p) (h : (ρ.1 : ℕ) = 0) :
    outerRow n p ρ = outerCofactor n p 0 * X ^ (ρ.2 : ℕ) := by
  rw [outerRow, outerRowPoly, ite_eq_left h]

/-- On the index type of the outer weight family, the class pair `(c, i)` with `c ≥ 1` carries
the class row `P_c q_{c,i}`. -/
theorem outerRow_of_val_ne_zero (n p : ℕ) (ρ : outerIdx n p) (h : (ρ.1 : ℕ) ≠ 0) :
    outerRow n p ρ = outerCofactor n p ρ.1 * outerQ n p ρ.1 ρ.2 := by
  rw [outerRow, outerRowPoly, ite_eq_right h]

/-! ## Monicity and degrees -/

/-- `F_c` is monic. -/
theorem monic_outerClassPoly (n p c : ℕ) : (outerClassPoly n p c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- `F_c` has degree `|S_c|`. -/
theorem natDegree_outerClassPoly (n p c : ℕ) :
    (outerClassPoly n p c).natDegree = (outerClassSet n p c).card := by
  unfold outerClassPoly
  rw [natDegree_prod_of_monic (h := fun (j : ℕ) _ => monic_X_add_C ((j : ℤ) ^ 2))]
  simp only [natDegree_X_add_C]
  exact (Finset.card_eq_sum_ones _).symm

/-- `P_c` is monic. -/
theorem monic_outerCofactor (n p c : ℕ) : (outerCofactor n p c).Monic :=
  monic_prod_of_monic _ _ fun d _ => monic_outerClassPoly n p d

/-- `P_c` has degree `∑_{0 ≤ d ≤ m, d ≠ c} |S_d|`. -/
theorem natDegree_outerCofactor (n p c : ℕ) :
    (outerCofactor n p c).natDegree
      = ∑ d ∈ (range (mHalf p + 1)).erase c, (outerClassSet n p d).card := by
  unfold outerCofactor
  rw [natDegree_prod_of_monic (h := fun d _ => monic_outerClassPoly n p d)]
  exact Finset.sum_congr rfl fun d _ => natDegree_outerClassPoly n p d

/-- `E_c` is monic. -/
theorem monic_outerHighPoly (n p c : ℕ) : (outerHighPoly n p c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- `E_c` has degree `|{j ∈ S_c : j > p}|`. -/
theorem natDegree_outerHighPoly (n p c : ℕ) :
    (outerHighPoly n p c).natDegree = ((outerClassSet n p c).filter (fun j => p < j)).card := by
  unfold outerHighPoly
  rw [natDegree_prod_of_monic (h := fun (j : ℕ) _ => monic_X_add_C ((j : ℤ) ^ 2))]
  simp only [natDegree_X_add_C]
  exact (Finset.card_eq_sum_ones _).symm

/-- `q_{c,i}` is monic. -/
theorem monic_outerQ (n p c i : ℕ) : (outerQ n p c i).Monic := by
  unfold outerQ
  split_ifs
  · exact (monic_X_add_C _).pow _
  · exact (monic_outerHighPoly n p c).mul ((monic_X_add_C _).pow _)

/-- `q_{c,i}` has degree `i` for `i < ℓ - 2`. -/
theorem natDegree_outerQ_of_lt {n p c i : ℕ} (h : i < ell p (K n) c - 2) :
    (outerQ n p c i).natDegree = i := by
  rw [outerQ_of_lt h, natDegree_pow_X_add_C]

/-- `q_{c,i}` has degree `|{j ∈ S_c : j > p}| + (i - (ℓ - 2))` for `i ≥ ℓ - 2`. -/
theorem natDegree_outerQ_of_le {n p c i : ℕ} (h : ell p (K n) c - 2 ≤ i) :
    (outerQ n p c i).natDegree
      = ((outerClassSet n p c).filter (fun j => p < j)).card + (i + 2 - ell p (K n) c) := by
  rw [outerQ_of_le h, (monic_outerHighPoly n p c).natDegree_mul ((monic_X_add_C _).pow _),
    natDegree_outerHighPoly, natDegree_pow_X_add_C]

/-- Every outer class row is monic. -/
theorem monic_outerRowPoly (n p c i : ℕ) : (outerRowPoly n p c i).Monic := by
  unfold outerRowPoly
  split_ifs
  · exact (monic_outerCofactor n p 0).mul (monic_X_pow i)
  · exact (monic_outerCofactor n p c).mul (monic_outerQ n p c i)

/-- The zero-class row `P_0 t^i` has degree `deg P_0 + i`. -/
theorem natDegree_outerRowPoly_zero (n p i : ℕ) :
    (outerRowPoly n p 0 i).natDegree = (outerCofactor n p 0).natDegree + i := by
  rw [outerRowPoly_zero, (monic_outerCofactor n p 0).natDegree_mul (monic_X_pow i),
    natDegree_X_pow]

/-- The class row `P_c q_{c,i}`, `c ≥ 1`, has degree `deg P_c + deg q_{c,i}`. -/
theorem natDegree_outerRowPoly_of_ne_zero (n p : ℕ) {c : ℕ} (hc : c ≠ 0) (i : ℕ) :
    (outerRowPoly n p c i).natDegree
      = (outerCofactor n p c).natDegree + (outerQ n p c i).natDegree := by
  rw [outerRowPoly_of_ne_zero n p hc,
    (monic_outerCofactor n p c).natDegree_mul (monic_outerQ n p c i)]

end ZetaSeven
