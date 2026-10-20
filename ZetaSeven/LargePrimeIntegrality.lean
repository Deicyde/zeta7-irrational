import ZetaSeven.MatrixDet
import ZetaSeven.OuterMomentIntegrality
import ZetaSeven.PairedPoleCongruence

/-!
# Large-prime integrality (paper Section 4.2, Proposition 4.6, case `p > K`)

Prince Anand, "Zeta 7 is Irrational", Proposition 4.6 and its proof, case `p > K` (p. 21).
For every prime `p > K` and `i, j < h`, the entry `G_K(i,j) = μ_X(D_N⁸ t^{i+j}/D_K)`
(`ZetaSeven.Gentry`, `ZetaSeven.Gmat`) has `p`-integral coefficients as a polynomial in `X`
(`Gentry_mem_pIntPoly`, `large_prime_integrality`).

The entry is `μ_X(P) + ∑_{N<a≤K} ρ_a π_a`, where `P` (`ZetaSeven.polyPart`) is the polynomial
part of `R/D_tail`, `R = D_N⁷ t^{i+j}` (`ZetaSeven.Rnum`), `D_tail = ∏_{N<b≤K} (t + b²)`
(`ZetaSeven.Dtail`), `ρ_a = R(-a²)/D_tail'(-a²)` (`ZetaSeven.resCoeff`) and
`π_a = μ_X(1/(t + a²))` (`ZetaSeven.muPole`).

* `P` has integer coefficients (`exists_intCast_eq_coeff_polyPart`), since `D_tail` is monic in
  `ℤ[t]`, and degree at most `7N + h - 2 < 3p - 4` (`natDegree_polyPart_le`), so `μ_X(P)` is
  `p`-integral by the outer moment integrality (`muFunctional_polyPart_mem_pIntPoly`).
* Every pole `-a²` has `N < a ≤ K < p`, so `π_a` is `p`-integral (`muPole_mem_pIntPoly`).
* A factor `b² - a²` of `D_tail'(-a²)` is divisible by `p` only for `b = p - a`, so `ρ_a` is
  `p`-integral when `p - a ∉ (N, K]` (`resCoeff_mem_pInt_of_unpaired`).
* A pair `a < p - a` in `(N, K]` contributes `ρ_a π_a + ρ_{p-a} π_{p-a}`, which has
  `p`-integral coefficients by the paired-pole congruence (`paired_residues` with
  `S = (N, K]` and `Q = R`), although each of the two residues can have valuation `-1`
  (`resCoeff_pair_mem_pIntPoly`).

The paper's proof treats every residue as `p`-integral; source-map erratum 7 records that only
the pairs are. "`p`-integral" means `0 ≤ padicValRat p`, which also holds for the coefficient
`0` (where the paper has `v_p(0) = +∞`).
-/

namespace ZetaSeven

open Polynomial

/-! ## The polynomial part -/

private theorem lp_Dpoly_mem_lifts (m : ℕ) : Dpoly m ∈ lifts (Int.castRingHom ℚ) := by
  unfold Dpoly
  refine prod_mem fun j _ => add_mem (X_mem_lifts _) ?_
  have h : ((j : ℚ) + 1) ^ 2 = Int.castRingHom ℚ (((j : ℤ) + 1) ^ 2) := by simp
  rw [h]
  exact C_mem_lifts _ _

private theorem lp_Dtail_mem_lifts (n : ℕ) : Dtail n ∈ lifts (Int.castRingHom ℚ) := by
  unfold Dtail
  refine prod_mem fun j _ => add_mem (X_mem_lifts _) ?_
  have h : (j : ℚ) ^ 2 = Int.castRingHom ℚ ((j : ℤ) ^ 2) := by simp
  rw [h]
  exact C_mem_lifts _ _

private theorem lp_Rnum_mem_lifts (n i j : ℕ) : Rnum n i j ∈ lifts (Int.castRingHom ℚ) := by
  unfold Rnum
  exact mul_mem (pow_mem (lp_Dpoly_mem_lifts _) 7) (pow_mem (X_mem_lifts _) _)

private theorem lp_monic_Dtail (n : ℕ) : (Dtail n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

private theorem lp_polyPart_eq (n i j : ℕ) : polyPart n i j = Rnum n i j /ₘ Dtail n :=
  (divByMonic_eq_div _ (lp_monic_Dtail n)).symm

private theorem lp_polyPart_mem_lifts (n i j : ℕ) :
    polyPart n i j ∈ lifts (Int.castRingHom ℚ) := by
  obtain ⟨q, hq, -, hqm⟩ :=
    lifts_and_degree_eq_and_monic (lp_Dtail_mem_lifts n) (lp_monic_Dtail n)
  obtain ⟨r, hr⟩ := (mem_lifts _).mp (lp_Rnum_mem_lifts n i j)
  refine (mem_lifts _).mpr ⟨r /ₘ q, ?_⟩
  rw [map_divByMonic _ hqm, hr, hq, lp_polyPart_eq]

/-- A polynomial with integer coefficients has `p`-integral coefficients. -/
private theorem lp_coeff_mem_pInt {p : ℕ} [Fact p.Prime] {P : ℚ[X]}
    (hP : P ∈ lifts (Int.castRingHom ℚ)) (k : ℕ) : P.coeff k ∈ pInt p := by
  obtain ⟨z, hz⟩ := (lifts_iff_coeff_lifts P).mp hP k
  have hz' : P.coeff k = (z : ℚ) := by
    rw [← hz]
    simp
  rw [hz']
  exact intCast_mem _ z

/-- The polynomial part `P` of `R/D_tail`, `R = D_N⁷ t^{i+j}`, has integer coefficients:
`D_tail` is monic with integer coefficients. -/
theorem exists_intCast_eq_coeff_polyPart (n i j k : ℕ) :
    ∃ z : ℤ, (polyPart n i j).coeff k = z := by
  obtain ⟨z, hz⟩ := (lifts_iff_coeff_lifts _).mp (lp_polyPart_mem_lifts n i j) k
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

private theorem lp_natDegree_Dpoly_le (m : ℕ) : (Dpoly m).natDegree ≤ m := by
  unfold Dpoly
  refine (natDegree_prod_le _ _).trans ?_
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    le_refl]

private theorem lp_natDegree_Dtail (n : ℕ) : (Dtail n).natDegree = K n - N n := by
  unfold Dtail
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

/-- For `i, j < h` the polynomial part `P` of `R/D_tail` has degree at most `7N + h - 2`:
`deg R ≤ 7N + i + j` and `deg D_tail = K - N = h`. -/
theorem natDegree_polyPart_le {n i j : ℕ} (hi : i < hDim n) (hj : j < hDim n) :
    (polyPart n i j).natDegree ≤ 7 * N n + hDim n - 2 := by
  have hK : K n = 40 * n := rfl
  have hN : N n = 3 * n := rfl
  have hh : hDim n = 37 * n := rfl
  have hR : (Rnum n i j).natDegree ≤ 7 * N n + (i + j) := by
    unfold Rnum
    exact natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_pow_le.trans (Nat.mul_le_mul_left 7 (lp_natDegree_Dpoly_le _)))
      (natDegree_X_pow_le _))
  rw [lp_polyPart_eq, natDegree_divByMonic _ (lp_monic_Dtail n), lp_natDegree_Dtail]
  omega

/-- For a prime `p > K` and `i, j < h`, the `μ`-value `μ_X(P)` of the polynomial part has
`p`-integral coefficients: `P` has integer coefficients and degree below `3p - 4`, where
`μ(t^e)` is `p`-integral by the outer moment integrality. -/
theorem muFunctional_polyPart_mem_pIntPoly {n p : ℕ} [Fact p.Prime] (hpK : K n < p)
    {i j : ℕ} (hi : i < hDim n) (hj : j < hDim n) :
    muFunctional (polyPart n i j) 0 ∈ pIntPoly p := by
  have hK : K n = 40 * n := rfl
  have hN : N n = 3 * n := rfl
  have hh : hDim n = 37 * n := rfl
  have hp7 : 7 ≤ p := by omega
  unfold muFunctional
  rw [Finsupp.sum_zero_index, add_zero, Polynomial.sum_def]
  refine sum_mem fun e he => mul_mem (C_mem_pIntPoly ?_) (C_mem_pIntPoly ?_)
  · exact lp_coeff_mem_pInt (lp_polyPart_mem_lifts n i j) e
  · refine mem_pInt_iff_padicValRat.mpr (muMonomial_padicValRat_nonneg hp7 ?_)
    have h1 := le_natDegree_of_mem_supp e he
    have h2 := natDegree_polyPart_le hi hj
    omega

/-! ## The poles -/

/-- `b ≡ a` or `b ≡ -a (mod p)` with `1 ≤ a < p` and `b < p` forces `b = a` or `b = p - a`. -/
private theorem lp_eq_of_natCast_eq {p : ℕ} [hp : Fact p.Prime] {a b : ℕ} (ha1 : 1 ≤ a)
    (hap : a < p) (hbp : b < p) :
    ((b : ZMod p) = a → b = a) ∧ ((b : ZMod p) = -(a : ZMod p) → b = p - a) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hap, ZMod.val_zero] at h'
    omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hbp, ZMod.val_natCast_of_lt hap] at h'
  · have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hbp, ZMod.neg_val, if_neg ha0, ZMod.val_natCast_of_lt hap] at h'

/-- For a prime `p > K` and `N < a ≤ K` with `p - a ∉ (N, K]`, the residue
`ρ_a = R(-a²)/D_tail'(-a²)` is `p`-integral: no factor `b² - a²`, `b ∈ (N, K]`, `b ≠ a`, of
`D_tail'(-a²)` is divisible by `p`. -/
theorem resCoeff_mem_pInt_of_unpaired {n p : ℕ} [hp : Fact p.Prime] (hpK : K n < p)
    (i j : ℕ) {a : ℕ} (ha : a ∈ Finset.Icc (N n + 1) (K n))
    (hpa : p - a ∉ Finset.Icc (N n + 1) (K n)) : resCoeff n i j a ∈ pInt p := by
  have haS := Finset.mem_Icc.mp ha
  have hap : a < p := by omega
  have ha1 : 1 ≤ a := by omega
  have hcR : ∀ c ∈ (Finset.Icc (N n + 1) (K n)).erase a,
      (c : ZMod p) ≠ a ∧ (c : ZMod p) ≠ -(a : ZMod p) := by
    intro c hc
    obtain ⟨hca, hcS⟩ := Finset.mem_erase.mp hc
    have hcp : c < p := by
      have := Finset.mem_Icc.mp hcS
      omega
    obtain ⟨h1, h2⟩ := lp_eq_of_natCast_eq (p := p) ha1 hap hcp
    exact ⟨fun h => hca (h1 h), fun h => hpa (by rw [← h2 h]; exact hcS)⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hDZ : ¬ (p : ℤ) ∣ ∏ c ∈ (Finset.Icc (N n + 1) (K n)).erase a,
      ((c : ℤ) ^ 2 - (a : ℤ) ^ 2) :=
    Prime.not_dvd_finsetProd hpZ fun c hc => not_dvd_sq_sub_sq (hcR c hc).1 (hcR c hc).2
  have hD := intCast_ne_zero_and_padicValRat_eq_zero hDZ
  simp only [Int.cast_prod, Int.cast_sub, Int.cast_pow, Int.cast_natCast] at hD
  have hQ : ∀ k, (Rnum n i j).coeff k ∈ pInt p :=
    fun k => lp_coeff_mem_pInt (lp_Rnum_mem_lifts n i j) k
  rw [resCoeff, Dtail, derivative_prod_eval _ ha, div_eq_mul_inv]
  exact mul_mem (eval_mem_pInt hQ (neg_mem (pow_mem (natCast_mem _ a) 2)))
    (inv_mem_pInt_of_padicValRat_eq_zero hD.2)

/-- For a prime `p > K` and a pair `a < p - a` of poles in `(N, K]`, the contribution
`ρ_a π_a + ρ_{p-a} π_{p-a}` has `p`-integral coefficients: this is the paired-pole congruence
(`paired_residues`) with `S = (N, K]` and `Q = R = D_N⁷ t^{i+j}`. -/
theorem resCoeff_pair_mem_pIntPoly {n p : ℕ} [Fact p.Prime] (hpK : K n < p) (i j : ℕ) {a : ℕ}
    (ha : a ∈ Finset.Icc (N n + 1) (K n)) (hpa : p - a ∈ Finset.Icc (N n + 1) (K n))
    (h2a : 2 * a < p) :
    C (resCoeff n i j a) * muPole a + C (resCoeff n i j (p - a)) * muPole (p - a)
      ∈ pIntPoly p := by
  have hK : K n = 40 * n := rfl
  have haS := Finset.mem_Icc.mp ha
  have hp7 : 7 ≤ p := by omega
  have hap : a < p := by omega
  have ha1 : 1 ≤ a := by omega
  have hS : ∀ b ∈ Finset.Icc (N n + 1) (K n),
      ((b : ZMod p) = a ∨ (b : ZMod p) = -(a : ZMod p)) → b = a ∨ b = p - a := by
    intro b hb hba
    have hbp : b < p := by
      have := Finset.mem_Icc.mp hb
      omega
    obtain ⟨h1, h2⟩ := lp_eq_of_natCast_eq (p := p) ha1 hap hbp
    rcases hba with h | h
    · exact Or.inl (h1 h)
    · exact Or.inr (h2 h)
  have hQ : ∀ k, 0 ≤ padicValRat p ((Rnum n i j).coeff k) := fun k =>
    mem_pInt_iff_padicValRat.mp (lp_coeff_mem_pInt (lp_Rnum_mem_lifts n i j) k)
  have hres : ∀ b, resCoeff n i j b
      = poleResidue (Finset.Icc (N n + 1) (K n)) (Rnum n i j) b := fun b => rfl
  have h := (paired_residues hp7 ha1 (by omega) ha hpa hS hQ).2.2.2.2
  rw [hres, hres]
  exact mem_pIntPoly.mpr fun k => mem_pInt_iff_padicValRat.mpr (h k)

/-! ## The entries -/

/-- Split a sum over `S` into the terms with `p - a ∉ S` and the pairs `a, p - a ∈ S` with
`2a < p`, when no `a ∈ S` has `2a = p` and every `a ∈ S` is at most `p`. -/
private theorem lp_sum_eq_unpaired_add_pairs {M : Type*} [AddCommMonoid M] {p : ℕ}
    (S : Finset ℕ) (hS : ∀ a ∈ S, 2 * a ≠ p ∧ a ≤ p) (f : ℕ → M) :
    ∑ a ∈ S, f a = ∑ a ∈ S.filter (fun a => p - a ∉ S), f a
      + ∑ a ∈ S.filter (fun a => p - a ∈ S ∧ 2 * a < p), (f a + f (p - a)) := by
  have h3 : ∑ a ∈ S.filter (fun a => p - a ∈ S ∧ ¬ 2 * a < p), f a
      = ∑ a ∈ S.filter (fun a => p - a ∈ S ∧ 2 * a < p), f (p - a) := by
    refine Finset.sum_nbij' (fun a => p - a) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨haS, hpa, h2a⟩ := Finset.mem_filter.mp ha
      obtain ⟨h2ne, hle⟩ := hS a haS
      refine Finset.mem_filter.mpr ⟨hpa, ?_, by omega⟩
      rwa [Nat.sub_sub_self hle]
    · intro a ha
      obtain ⟨haS, hpa, h2a⟩ := Finset.mem_filter.mp ha
      obtain ⟨-, hle⟩ := hS a haS
      refine Finset.mem_filter.mpr ⟨hpa, ?_, by omega⟩
      rwa [Nat.sub_sub_self hle]
    · intro a ha
      exact Nat.sub_sub_self (hS a (Finset.mem_filter.mp ha).1).2
    · intro a ha
      exact Nat.sub_sub_self (hS a (Finset.mem_filter.mp ha).1).2
    · intro a ha
      rw [Nat.sub_sub_self (hS a (Finset.mem_filter.mp ha).1).2]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => p - a ∈ S),
    ← Finset.sum_filter_add_sum_filter_not (S.filter (fun a => p - a ∈ S)) (fun a => 2 * a < p),
    Finset.filter_filter, Finset.filter_filter, h3, Finset.sum_add_distrib]
  exact add_comm _ _

private theorem lp_poleCoeffs_sum (n i j : ℕ) (g : ℕ → ℚ → Polynomial ℚ)
    (h0 : ∀ a, g a 0 = 0) (hadd : ∀ a b₁ b₂, g a (b₁ + b₂) = g a b₁ + g a b₂) :
    (poleCoeffs n i j).sum g = ∑ a ∈ Finset.Icc (N n + 1) (K n), g a (resCoeff n i j a) := by
  unfold poleCoeffs
  rw [← Finsupp.sum_finsetSum_index h0 hadd]
  exact Finset.sum_congr rfl fun a _ => Finsupp.sum_single_index (h0 a)

/-- **Large-prime integrality** (Proposition 4.6, case `p > K`), membership form. For a prime
`p > K` and `i, j < h`, the entry `G_K(i,j) = μ_X(D_N⁸ t^{i+j}/D_K)` has `p`-integral
coefficients as a polynomial in `X`. -/
theorem Gentry_mem_pIntPoly {n p : ℕ} [hp : Fact p.Prime] (hpK : K n < p) {i j : ℕ}
    (hi : i < hDim n) (hj : j < hDim n) : Gentry n i j ∈ pIntPoly p := by
  have hK : K n = 40 * n := rfl
  have hh : hDim n = 37 * n := rfl
  have hp7 : 7 ≤ p := by omega
  have hsplit : Gentry n i j = muFunctional (polyPart n i j) 0
      + ∑ a ∈ Finset.Icc (N n + 1) (K n), C (resCoeff n i j a) * muPole a := by
    have hpole : (poleCoeffs n i j).sum (fun a c => C c * muPole a)
        = ∑ a ∈ Finset.Icc (N n + 1) (K n), C (resCoeff n i j a) * muPole a :=
      lp_poleCoeffs_sum n i j _ (fun a => by simp) (fun a b₁ b₂ => by simp [add_mul])
    rw [Gentry, ← hpole]
    unfold muFunctional
    rw [Finsupp.sum_zero_index, add_zero]
  have hS : ∀ a ∈ Finset.Icc (N n + 1) (K n), 2 * a ≠ p ∧ a ≤ p := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    refine ⟨fun h2 => ?_, by omega⟩
    rcases hp.out.eq_one_or_self_of_dvd 2 ⟨a, h2.symm⟩ with h | h <;> omega
  rw [hsplit, lp_sum_eq_unpaired_add_pairs _ hS]
  refine add_mem (muFunctional_polyPart_mem_pIntPoly hpK hi hj)
    (add_mem (sum_mem fun a ha => ?_) (sum_mem fun a ha => ?_))
  · obtain ⟨haS, hpa⟩ := Finset.mem_filter.mp ha
    have haS' := Finset.mem_Icc.mp haS
    exact mul_mem (C_mem_pIntPoly (resCoeff_mem_pInt_of_unpaired hpK i j haS hpa))
      (muPole_mem_pIntPoly hp7 (by omega) (by omega))
  · obtain ⟨haS, hpa, h2a⟩ := Finset.mem_filter.mp ha
    exact resCoeff_pair_mem_pIntPoly hpK i j haS hpa h2a

/-- **Large-prime integrality** (Proposition 4.6, case `p > K`). For every prime `p > K`, each
entry `G_K(i,j) = μ_X(D_N⁸ t^{i+j}/D_K)` of the `h × h` matrix `G_K` has `p`-integral
coefficients as a polynomial in `X`: `v_p ≥ 0` for every coefficient. -/
theorem large_prime_integrality {n p : ℕ} [Fact p.Prime] (hpK : K n < p)
    (i j : Fin (hDim n)) (k : ℕ) : 0 ≤ padicValRat p ((Gmat n i j).coeff k) := by
  simp only [Gmat, Matrix.of_apply]
  exact mem_pInt_iff_padicValRat.mp (mem_pIntPoly.mp (Gentry_mem_pIntPoly hpK i.isLt j.isLt) k)

end ZetaSeven
