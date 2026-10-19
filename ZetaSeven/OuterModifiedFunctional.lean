import ZetaSeven.MatrixDet

/-!
# Outer modified functional (paper Section 4.2.1, equation (53))

Prince Anand, "Zeta 7 is Irrational", Section 4.2.1, second paragraph and
equation (53). Fix a prime `p`. The correction `c_e ∈ {0, …, p - 1}` is `0` for
`e < 3p - 4`; for `e ≥ 3p - 4`, writing `p μ(t^e) = u/v` in lowest terms, it is the
representative of `u v⁻¹` modulo `p`, and `0` when `p ∣ v`. The modified functional
`μ_0` has the shape of `μ_X` (`ZetaSeven.muFunctional`), with the monomial values
`μ_0(t^e) = μ(t^e) - c_e/p` and the pole values of `μ_X`. With `P_{ij}` the polynomial
part of `D_N⁸ t^{i+j}/D_K` (`ZetaSeven.polyPart`) and `ρ_{ij,a}` its residues
(`ZetaSeven.resCoeff`), equation (53) names the `h × h` matrices
`A_{ij} = μ_0(D_N⁸ t^{i+j}/D_K)` and `L_{ij} = ∑_e c_e [t^e] P_{ij}`.

`MatrixDet` computes `P_{ij}` as the quotient of `D_N⁷ t^{i+j}` by `D_tail = D_K/D_N`;
`polyPart_eq_divByMonic` shows it is the quotient of `D_N⁸ t^{i+j}` by `D_K`, and
`entry_partialFraction` is the decomposition
`D_N⁸ t^{i+j}/D_K = P_{ij} + ∑_{N<a≤K} ρ_{ij,a}/(t + a²)` in `RatFunc ℚ`.
The partial-fraction argument is the one of `ZetaSeven.Rnum_eq_partialFractions`
(positive integral representation), which this node's dependencies do not reach.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## The corrections `c_e` -/

/-- Section 4.2.1: the correction `c_e`. It is `0` for `e < 3p - 4`; otherwise, with
`p μ(t^e) = u/v` in lowest terms (`Rat.num`, `Rat.den`), it is the representative in
`{0, …, p - 1}` of `u v⁻¹` modulo `p`. Since `ZMod`'s inverse of `0` is `0`, this is `0`
when `p ∣ v` (`outerCe_of_dvd`). -/
def outerCe (p e : ℕ) : ℕ :=
  if e < 3 * p - 4 then 0
  else
    ((((p : ℚ) * muMonomial e).num : ZMod p) *
      ((((p : ℚ) * muMonomial e).den : ℕ) : ZMod p)⁻¹).val

/-- `c_e = 0` for `e < 3p - 4`. -/
theorem outerCe_of_lt {p e : ℕ} (he : e < 3 * p - 4) : outerCe p e = 0 :=
  ite_eq_left he

/-- `c_e ∈ {0, …, p - 1}`. -/
theorem outerCe_lt {p : ℕ} (hp : p.Prime) (e : ℕ) : outerCe p e < p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  unfold outerCe
  split_ifs
  · exact hp.pos
  · exact ZMod.val_lt _

/-- For `e ≥ 3p - 4`, `c_e = 0` when `p` divides the reduced denominator `v` of
`p μ(t^e)`. -/
theorem outerCe_of_dvd {p e : ℕ} (he : 3 * p - 4 ≤ e)
    (hv : p ∣ ((p : ℚ) * muMonomial e).den) : outerCe p e = 0 := by
  unfold outerCe
  rw [ite_eq_right (not_lt.mpr he), (ZMod.natCast_eq_zero_iff _ _).mpr hv, ZMod.inv_zero,
    mul_zero, ZMod.val_zero]

/-- For `e ≥ 3p - 4` and `p ∤ v`, where `p μ(t^e) = u/v` in lowest terms,
`c_e v ≡ u (mod p)`, i.e. `c_e ≡ u v⁻¹ (mod p)`. -/
theorem outerCe_spec {p e : ℕ} (hp : p.Prime) (he : 3 * p - 4 ≤ e)
    (hv : ¬ p ∣ ((p : ℚ) * muMonomial e).den) :
    (outerCe p e : ZMod p) * (((p : ℚ) * muMonomial e).den : ZMod p) =
      (((p : ℚ) * muMonomial e).num : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hv0 : ((((p : ℚ) * muMonomial e).den : ℕ) : ZMod p) ≠ 0 := fun h =>
    hv ((ZMod.natCast_eq_zero_iff _ _).mp h)
  unfold outerCe
  rw [ite_eq_right (not_lt.mpr he), ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hv0, mul_one]

/-- For `e ≥ 3p - 4` and `p ∤ v`, `c_e` is the unique `c ∈ {0, …, p - 1}` with
`c v ≡ u (mod p)`, where `p μ(t^e) = u/v` in lowest terms. -/
theorem outerCe_eq_iff {p e c : ℕ} (hp : p.Prime) (he : 3 * p - 4 ≤ e)
    (hv : ¬ p ∣ ((p : ℚ) * muMonomial e).den) (hc : c < p) :
    outerCe p e = c ↔
      (c : ZMod p) * (((p : ℚ) * muMonomial e).den : ZMod p) =
        (((p : ℚ) * muMonomial e).num : ZMod p) := by
  constructor
  · rintro rfl
    exact outerCe_spec hp he hv
  · intro h
    have : Fact p.Prime := ⟨hp⟩
    have hv0 : ((((p : ℚ) * muMonomial e).den : ℕ) : ZMod p) ≠ 0 := fun h0 =>
      hv ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have hcast : (outerCe p e : ZMod p) = (c : ZMod p) :=
      mul_right_cancel₀ hv0 ((outerCe_spec hp he hv).trans h.symm)
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (outerCe_lt hp e),
      Nat.mod_eq_of_lt hc] at hcast
    exact hcast

/-! ## The modified functional `μ_0` -/

/-- Section 4.2.1: the modified monomial moment `μ_0(t^e) = μ(t^e) - c_e/p`. -/
def muZeroMonomial (p e : ℕ) : ℚ := muMonomial e - (outerCe p e : ℚ) / p

/-- Section 4.2.1: the modified functional `μ_0`, defined like `μ_X`
(`ZetaSeven.muFunctional`) on partial-fraction data `(P, c)`, with the monomial values
`μ_0(t^e)` and the pole values `μ_X(1/(t + j²))` of `μ_X`. -/
noncomputable def muZeroFunctional (p : ℕ) (P : Polynomial ℚ) (c : ℕ →₀ ℚ) :
    Polynomial ℚ :=
  P.sum (fun e a => C a * C (muZeroMonomial p e)) + c.sum (fun j a => C a * muPole j)

/-- `μ_0(t^e) = μ(t^e) - c_e/p`. -/
theorem muZeroFunctional_X_pow (p e : ℕ) :
    muZeroFunctional p (X ^ e) 0 = C (muMonomial e - (outerCe p e : ℚ) / p) := by
  unfold muZeroFunctional muZeroMonomial
  rw [X_pow_eq_monomial, sum_monomial_index _ _ (by simp), Finsupp.sum_zero_index, add_zero,
    C_1, one_mul]

/-- `μ_0(1/(t + j²)) = μ_X(1/(t + j²))`, the pole value (6) `ZetaSeven.muPole`. -/
theorem muZeroFunctional_single (p j : ℕ) :
    muZeroFunctional p 0 (Finsupp.single j 1) = muPole j := by
  unfold muZeroFunctional
  rw [sum_zero_index, zero_add, Finsupp.sum_single_index (by simp), C_1, one_mul]

/-! ## The polynomial part `P_{ij}` and the residues `ρ_{ij,a}` -/

private theorem outer_monic_Dpoly (m : ℕ) : (Dpoly m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

private theorem outer_monic_Dtail (n : ℕ) : (Dtail n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- `D_K = D_N · D_tail`. -/
private theorem outer_Dpoly_K_eq (n : ℕ) : Dpoly (K n) = Dpoly (N n) * Dtail n := by
  have hNK : N n ≤ K n := by unfold N K; omega
  unfold Dpoly Dtail
  rw [← Finset.prod_range_mul_prod_Ico _ hNK, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.prod_Ico_add' (fun j : ℕ => (X + C ((j : ℚ) ^ 2) : ℚ[X])) (N n) (K n) 1]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Nat.cast_add, Nat.cast_one]

/-- `D_N⁸ t^{i+j} = D_N · R` with `R = D_N⁷ t^{i+j}` the numerator `Rnum`. -/
private theorem outer_DN8_eq (n i j : ℕ) :
    Dpoly (N n) ^ 8 * X ^ (i + j) = Dpoly (N n) * Rnum n i j := by
  unfold Rnum
  ring

private theorem outer_mul_divByMonic_mul (c f g : ℚ[X]) (hc : c.Monic) (hg : g.Monic) :
    (c * f) /ₘ (c * g) = f /ₘ g := by
  refine (div_modByMonic_unique (f /ₘ g) (c * (f %ₘ g)) (hc.mul hg) ⟨?_, ?_⟩).1
  · rw [mul_assoc, ← mul_add, modByMonic_add_div]
  · rw [degree_mul, degree_mul]
    exact WithBot.add_lt_add_left (fun h => hc.ne_zero (degree_eq_bot.mp h))
      (degree_modByMonic_lt f hg)

/-- `P_{ij}` (`ZetaSeven.polyPart`, the quotient of `D_N⁷ t^{i+j}` by `D_tail`) is the
polynomial part of `D_N⁸ t^{i+j}/D_K`: the quotient of `D_N⁸ t^{i+j}` by `D_K`. -/
theorem polyPart_eq_divByMonic (n i j : ℕ) :
    polyPart n i j = (Dpoly (N n) ^ 8 * X ^ (i + j)) /ₘ Dpoly (K n) := by
  rw [outer_DN8_eq, outer_Dpoly_K_eq,
    outer_mul_divByMonic_mul _ _ _ (outer_monic_Dpoly _) (outer_monic_Dtail n)]
  exact (divByMonic_eq_div _ (outer_monic_Dtail n)).symm

/-- The nodes `-a²` of the tail divisor. -/
private def outerTailNode (a : ℕ) : ℚ := -((a : ℚ) ^ 2)

private theorem outer_nodal_tailNode (t : Finset ℕ) :
    Lagrange.nodal t outerTailNode = ∏ b ∈ t, (X + C ((b : ℚ) ^ 2)) := by
  rw [Lagrange.nodal_eq]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [outerTailNode, map_neg, sub_neg_eq_add]

private theorem outer_injOn_tailNode (t : Finset ℕ) : Set.InjOn outerTailNode t := by
  intro a _ b _ h
  have h1 : -((a : ℚ) ^ 2) = -((b : ℚ) ^ 2) := h
  have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast neg_inj.mp h1
  exact Nat.pow_left_injective two_ne_zero h2

private theorem outer_Dtail_eq_nodal (n : ℕ) :
    Dtail n = Lagrange.nodal (Finset.Icc (N n + 1) (K n)) outerTailNode := by
  rw [outer_nodal_tailNode, Dtail]

/-- Partial fractions of `D_N⁷ t^{i+j}/D_tail` (Lagrange interpolation at the nodes
`-a²`), as in `ZetaSeven.Rnum_eq_partialFractions`. -/
private theorem outer_Rnum_partialFraction (n i j : ℕ) :
    Rnum n i j = Dtail n * polyPart n i j +
      ∑ a ∈ Finset.Icc (N n + 1) (K n), C (resCoeff n i j a) *
        ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a, (X + C ((b : ℚ) ^ 2)) := by
  have hD := outer_Dtail_eq_nodal n
  have hmonic : (Dtail n).Monic := outer_monic_Dtail n
  have hroot : ∀ a ∈ Finset.Icc (N n + 1) (K n), (Dtail n).eval (outerTailNode a) = 0 := by
    intro a ha
    rw [hD]
    exact Lagrange.eval_nodal_at_node ha
  have hreval : ∀ a ∈ Finset.Icc (N n + 1) (K n),
      (Rnum n i j %ₘ Dtail n).eval (outerTailNode a) =
        (Rnum n i j).eval (outerTailNode a) := by
    intro a ha
    have h := congrArg (eval (outerTailNode a)) (modByMonic_add_div (Rnum n i j) (Dtail n))
    rw [eval_add, eval_mul, hroot a ha, zero_mul, add_zero] at h
    exact h
  have hdeg : (Rnum n i j %ₘ Dtail n).degree < (Finset.Icc (N n + 1) (K n)).card := by
    rw [← Lagrange.degree_nodal (v := outerTailNode), ← hD]
    exact degree_modByMonic_lt _ hmonic
  have hrem : Rnum n i j %ₘ Dtail n = ∑ a ∈ Finset.Icc (N n + 1) (K n),
      C (resCoeff n i j a) *
        ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a, (X + C ((b : ℚ) ^ 2)) := by
    rw [Lagrange.eq_interpolate (outer_injOn_tailNode _) hdeg, Lagrange.interpolate_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div ha, ← Lagrange.nodal_erase_eq_nodal_div ha,
      Lagrange.nodalWeight_eq_eval_derivative_nodal ha, ← hD, outer_nodal_tailNode,
      hreval a ha, ← mul_assoc, ← C_mul, resCoeff, div_eq_mul_inv]
    rfl
  have hpoly : polyPart n i j = Rnum n i j /ₘ Dtail n := (divByMonic_eq_div _ hmonic).symm
  rw [← hrem, hpoly, add_comm]
  exact (modByMonic_add_div (Rnum n i j) (Dtail n)).symm

/-- `D_K/(t + a²) = D_N ∏_{N<b≤K, b≠a} (t + b²)` for `N < a ≤ K`. -/
private theorem outer_Dpoly_K_eq_mul_erase (n : ℕ) {a : ℕ}
    (ha : a ∈ Finset.Icc (N n + 1) (K n)) :
    Dpoly (K n) = (X + C ((a : ℚ) ^ 2)) *
      (Dpoly (N n) * ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a, (X + C ((b : ℚ) ^ 2))) := by
  have hprod : ∏ b ∈ Finset.Icc (N n + 1) (K n), (X + C ((b : ℚ) ^ 2)) =
      (X + C ((a : ℚ) ^ 2)) *
        ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a, (X + C ((b : ℚ) ^ 2)) :=
    (Finset.mul_prod_erase _ (fun b : ℕ => (X + C ((b : ℚ) ^ 2) : ℚ[X])) ha).symm
  rw [outer_Dpoly_K_eq, Dtail, hprod]
  ring

/-- Partial fractions with the denominators cleared:
`D_N⁸ t^{i+j} = D_K P_{ij} + ∑_{N<a≤K} ρ_{ij,a} D_K/(t + a²)`, where
`D_K/(t + a²) = D_N ∏_{b ≠ a} (t + b²)`. -/
private theorem outer_DN8_partialFraction (n i j : ℕ) :
    Dpoly (N n) ^ 8 * X ^ (i + j) = Dpoly (K n) * polyPart n i j +
      ∑ a ∈ Finset.Icc (N n + 1) (K n), C (resCoeff n i j a) *
        (Dpoly (N n) *
          ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a, (X + C ((b : ℚ) ^ 2))) := by
  rw [outer_DN8_eq, outer_Rnum_partialFraction n i j, outer_Dpoly_K_eq, mul_add,
    Finset.mul_sum]
  exact congrArg₂ (· + ·) (mul_assoc _ _ _).symm
    (Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _)

/-- The partial-fraction decomposition of the article:
`D_N⁸ t^{i+j}/D_K = P_{ij}(t) + ∑_{N<a≤K} ρ_{ij,a}/(t + a²)` in `RatFunc ℚ`, with
`P_{ij} = ZetaSeven.polyPart n i j` and `ρ_{ij,a} = ZetaSeven.resCoeff n i j a`. -/
theorem entry_partialFraction (n i j : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (N n) ^ 8 * X ^ (i + j)) /
        algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)) =
      algebraMap ℚ[X] (RatFunc ℚ) (polyPart n i j) +
        ∑ a ∈ Finset.Icc (N n + 1) (K n),
          algebraMap ℚ[X] (RatFunc ℚ) (C (resCoeff n i j a)) /
            algebraMap ℚ[X] (RatFunc ℚ) (X + C ((a : ℚ) ^ 2)) := by
  have hK : algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (outer_monic_Dpoly _).ne_zero
  have h := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) (outer_DN8_partialFraction n i j)
  rw [map_add, map_mul (algebraMap ℚ[X] (RatFunc ℚ)) (Dpoly (K n)), map_sum] at h
  rw [div_eq_iff hK, h, add_mul, Finset.sum_mul,
    mul_comm (algebraMap ℚ[X] (RatFunc ℚ) (Dpoly (K n)))]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun a ha => ?_)
  have hX : algebraMap ℚ[X] (RatFunc ℚ) (X + C ((a : ℚ) ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_add_C_ne_zero _)
  rw [outer_Dpoly_K_eq_mul_erase n ha]
  simp only [map_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hX]
  ring

/-! ## The matrices `A` and `L` of (53) -/

/-- Equation (53): the entry `A_{ij} = μ_0(D_N⁸ t^{i+j}/D_K)`, applying `μ_0` to the
partial-fraction data (`entry_partialFraction`) of `D_N⁸ t^{i+j}/D_K`, as
`ZetaSeven.Gentry` does for `μ_X`. -/
noncomputable def outerAentry (p n i j : ℕ) : Polynomial ℚ :=
  muZeroFunctional p (polyPart n i j) (poleCoeffs n i j)

/-- Equation (53): the `h × h` matrix `A`. -/
noncomputable def outerAmat (p n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) (Polynomial ℚ) :=
  Matrix.of fun i j => outerAentry p n i.val j.val

/-- Equation (53): the entry `L_{ij} = ∑_e c_e [t^e] P_{ij}`. -/
noncomputable def outerLentry (p n i j : ℕ) : ℚ :=
  (polyPart n i j).sum fun e a => (outerCe p e : ℚ) * a

/-- Equation (53): the `h × h` matrix `L`. -/
noncomputable def outerLmat (p n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun i j => outerLentry p n i.val j.val

end ZetaSeven
