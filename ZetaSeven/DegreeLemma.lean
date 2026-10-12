import ZetaSeven.MatrixDet

/-!
# Degree lemma (paper Section 2.4, Lemma 2.3, equations (10)-(15))

For every `K ∈ 40ℤ_{>0}` (i.e. `K = 40 * n` with `0 < n`), the determinant
`Δ_K(X)` is a polynomial of degree exactly `h = 37 * n`, with leading
coefficient `(-1)^{h(h-1)/2} ∏_{j=N+1}^K j^6 D_N(-j^2)^7`.

Following the paper: each entry of `G_K(X)` is affine in `X`, so
`G_K(X) = A + XB`; the `X`-coefficient matrix factors as
`B = Vᵀ diag(γ) V` with Vandermonde `V` over the nodes `v_a = -a^2`;
`det B` is computed from the Vandermonde determinant and the
tail-divisor derivative identity.
-/

namespace ZetaSeven

open Polynomial Finset

/-! ## Parameter identities -/

theorem NK_succ_le_K_of_pos (n : ℕ) (hn : 0 < n) : N n + 1 ≤ K n := by
  unfold N K
  omega

theorem card_Icc_NK (n : ℕ) (hn : 0 < n) :
    (Finset.Icc (N n + 1) (K n)).card = hDim n := by
  rw [Nat.card_Icc]
  unfold K N hDim
  omega

theorem sub_NK_eq_hDim (n : ℕ) : K n - N n = hDim n := by
  unfold K N hDim
  omega

theorem hDim_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < hDim n := by
  unfold hDim
  omega

theorem hDim_le_K (n : ℕ) : hDim n ≤ K n := by
  unfold hDim K
  omega

/-! ## Finsupp sums over single-coefficient data -/

theorem coeff_poly_sum {p : Polynomial ℚ} {g : ℕ → ℚ → Polynomial ℚ} {k : ℕ} :
    (p.sum g).coeff k = ∑ e ∈ p.support, (g e (p.coeff e)).coeff k := by
  have h : p.sum g = ∑ e ∈ p.support, g e (p.coeff e) := rfl
  rw [h, Polynomial.finsetSum_coeff]

theorem poleCoeffs_sum (n i j : ℕ) (g : ℕ → ℚ → Polynomial ℚ)
    (h0 : ∀ a, g a 0 = 0)
    (hadd : ∀ a b₁ b₂, g a (b₁ + b₂) = g a b₁ + g a b₂) :
    (poleCoeffs n i j).sum g
      = ∑ a ∈ Finset.Icc (N n + 1) (K n), g a (resCoeff n i j a) := by
  calc (poleCoeffs n i j).sum g
      = ∑ a ∈ Finset.Icc (N n + 1) (K n),
          (Finsupp.single a (resCoeff n i j a)).sum g := by
        unfold poleCoeffs
        exact (Finsupp.sum_finsetSum_index h0 hadd).symm
    _ = ∑ a ∈ Finset.Icc (N n + 1) (K n), g a (resCoeff n i j a) :=
        Finset.sum_congr rfl (fun a _ => Finsupp.sum_single_index (h0 a))

/-! ## The `X`-coefficient of a matrix entry -/

theorem coeff_one_muPole (a : ℕ) : (muPole a).coeff 1 = (a : ℚ) ^ 6 := by
  have hX : (X - C (H7 a) : Polynomial ℚ).coeff 1 = 1 := by simp
  have h0 : (C (1 / (2 * (a : ℚ)) - 1 / 6) : Polynomial ℚ).coeff 1 = 0 := by simp
  unfold muPole
  rw [Polynomial.coeff_add, ← map_pow, Polynomial.coeff_C_mul, hX, h0, mul_one,
    add_zero]

theorem Gentry_coeff_one (n i j : ℕ) :
    (Gentry n i j).coeff 1
      = ∑ a ∈ Finset.Icc (N n + 1) (K n), resCoeff n i j a * (a : ℚ) ^ 6 := by
  have hpoly : ((polyPart n i j).sum (fun e a => C a * C (muMonomial e))).coeff 1
      = 0 := by
    rw [coeff_poly_sum]
    apply Finset.sum_eq_zero
    intro e _
    rw [← Polynomial.C_mul]
    simp
  have hpole : ((poleCoeffs n i j).sum (fun j a => C a * muPole j)).coeff 1
      = ∑ a ∈ Finset.Icc (N n + 1) (K n), resCoeff n i j a * (a : ℚ) ^ 6 := by
    rw [poleCoeffs_sum n i j (fun j a => C a * muPole j) (fun a => by simp)
      (fun a b₁ b₂ => by rw [map_add, add_mul]), Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro a _
    rw [Polynomial.coeff_C_mul, coeff_one_muPole]
  unfold Gentry muFunctional
  rw [Polynomial.coeff_add, hpoly, hpole, zero_add]

/-! ## Entries are affine in `X` -/

theorem natDegree_C_le_one (c : ℚ) : (C c : Polynomial ℚ).natDegree ≤ 1 :=
  (Polynomial.natDegree_C c).le.trans zero_le_one

theorem natDegree_muPole_le (a : ℕ) : (muPole a).natDegree ≤ 1 := by
  have hX : (X : Polynomial ℚ).natDegree ≤ 1 := Polynomial.natDegree_X_le
  have hsub : (X - C (H7 a) : Polynomial ℚ).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [max_le_iff]
    exact ⟨hX, natDegree_C_le_one _⟩
  have hmul : (C (a : ℚ) ^ 6 * (X - C (H7 a)) : Polynomial ℚ).natDegree ≤ 1 := by
    have h6 : (C (a : ℚ) ^ 6 : Polynomial ℚ).natDegree ≤ 0 := by
      rw [← map_pow]
      exact (Polynomial.natDegree_C _).le
    refine le_trans Polynomial.natDegree_mul_le ?_
    calc (C (a : ℚ) ^ 6).natDegree + (X - C (H7 a)).natDegree
        ≤ 0 + 1 := Nat.add_le_add h6 hsub
      _ = 1 := rfl
  unfold muPole
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  exact ⟨hmul, natDegree_C_le_one _⟩

theorem natDegree_Gentry_le (n i j : ℕ) : (Gentry n i j).natDegree ≤ 1 := by
  have hpoly : ((polyPart n i j).sum
      (fun e a => C a * C (muMonomial e))).natDegree ≤ 1 := by
    have hsum : (polyPart n i j).sum (fun e a => C a * C (muMonomial e))
        = ∑ e ∈ (polyPart n i j).support,
          C ((polyPart n i j).coeff e) * C (muMonomial e) := rfl
    rw [hsum]
    refine le_trans (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) zero_le_one
    intro e _
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_C, add_zero]
  have hpole : ((poleCoeffs n i j).sum
      (fun j a => C a * muPole j)).natDegree ≤ 1 := by
    have hsum : (poleCoeffs n i j).sum (fun j a => C a * muPole j)
        = ∑ a ∈ (poleCoeffs n i j).support,
          C ((poleCoeffs n i j) a) * muPole a := rfl
    rw [hsum]
    refine le_trans (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) le_rfl
    intro a _
    refine le_trans Polynomial.natDegree_mul_le ?_
    calc (C ((poleCoeffs n i j) a)).natDegree + (muPole a).natDegree
        ≤ 0 + 1 := Nat.add_le_add (Polynomial.natDegree_C _).le
          (natDegree_muPole_le a)
      _ = 1 := rfl
  unfold Gentry muFunctional
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  exact ⟨hpoly, hpole⟩

theorem Gentry_affine (n i j : ℕ) :
    Gentry n i j
      = C ((Gentry n i j).coeff 0) + X * C ((Gentry n i j).coeff 1) := by
  have hdeg : (Gentry n i j).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_Gentry_le n i j) (by norm_num)
  have h := Polynomial.as_sum_range_C_mul_X_pow' (Gentry n i j) hdeg
  conv_lhs => rw [h]
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    mul_one]
  ring

/-! ## The constant and linear coefficient matrices -/

/-- The `X`-coefficient matrix `B` (paper equation (12)). -/
noncomputable def Bmat (n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun i j =>
    ∑ a ∈ Finset.Icc (N n + 1) (K n), resCoeff n i.val j.val a * (a : ℚ) ^ 6

/-- The constant matrix `A`. -/
noncomputable def Amat (n : ℕ) : Matrix (Fin (hDim n)) (Fin (hDim n)) ℚ :=
  Matrix.of fun i j => (Gentry n i.val j.val).coeff 0

/-- `G_K(X) = A + XB` entrywise. -/
theorem Gmat_eq_affine (n : ℕ) :
    Gmat n
      = Matrix.of fun i j => C (Amat n i j) + X * C (Bmat n i j) := by
  apply Matrix.ext
  intro i j
  simp only [Gmat, Amat, Bmat, Matrix.of_apply]
  conv_lhs => rw [Gentry_affine n i.val j.val, Gentry_coeff_one n i.val j.val]

/-! ## Determinant of an affine matrix pencil -/

theorem natDegree_affine_entry (a b : ℚ) :
    (C a + X * C b : Polynomial ℚ).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  refine ⟨natDegree_C_le_one _, ?_⟩
  refine le_trans Polynomial.natDegree_mul_le ?_
  calc (X : Polynomial ℚ).natDegree + (C b).natDegree
      ≤ 1 + 0 := Nat.add_le_add Polynomial.natDegree_X_le
        (Polynomial.natDegree_C _).le
    _ = 1 := rfl

theorem natDegree_prod_affine {ι : Type*} (s : Finset ι) (a b : ι → ℚ) :
    (∏ i ∈ s, (C (a i) + X * C (b i) : Polynomial ℚ)).natDegree ≤ s.card := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul s _ 1 ?_) ?_
  · intro i _
    exact natDegree_affine_entry (a i) (b i)
  · simp

theorem coeff_prod_affine {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℚ) :
    (∏ i ∈ s, (C (a i) + X * C (b i) : Polynomial ℚ)).coeff s.card
      = ∏ i ∈ s, b i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Finset.card_insert_of_notMem hi]
    have hPdeg : (∏ k ∈ s, (C (a k) + X * C (b k) : Polynomial ℚ)).natDegree
        ≤ s.card := natDegree_prod_affine s a b
    have hPtop : (∏ k ∈ s, (C (a k) + X * C (b k) : Polynomial ℚ)).coeff
        (s.card + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hPdeg (Nat.lt_succ_self _))
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, hPtop, mul_zero,
      zero_add]
    have hrew : ((X * C (b i)) *
        (∏ k ∈ s, (C (a k) + X * C (b k) : Polynomial ℚ)) : Polynomial ℚ)
        = X * (C (b i) * ∏ k ∈ s, (C (a k) + X * C (b k) : Polynomial ℚ)) := by
      ring
    rw [hrew, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, ih]

theorem coeff_det_affine {h : ℕ} (A B : Matrix (Fin h) (Fin h) ℚ) :
    (Matrix.of fun i j => (C (A i j) + X * C (B i j) : Polynomial ℚ)).det.coeff h
      = B.det := by
  have hcard : (Finset.univ : Finset (Fin h)).card = h := by simp
  rw [Matrix.det_apply', Matrix.det_apply', Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  have hC : (((Equiv.Perm.sign σ : ℤ) : Polynomial ℚ))
      = C (((Equiv.Perm.sign σ : ℤ) : ℚ)) :=
    (map_intCast (C : ℚ →+* Polynomial ℚ) _).symm
  have hmain := coeff_prod_affine (Finset.univ : Finset (Fin h))
    (fun i => A (σ i) i) (fun i => B (σ i) i)
  rw [hcard] at hmain
  rw [hC, Polynomial.coeff_C_mul]
  congr 1
  simp only [Matrix.of_apply]
  exact hmain

theorem natDegree_det_affine_le {h : ℕ} (A B : Matrix (Fin h) (Fin h) ℚ) :
    (Matrix.of fun i j =>
      (C (A i j) + X * C (B i j) : Polynomial ℚ)).det.natDegree ≤ h := by
  have hcard : (Finset.univ : Finset (Fin h)).card = h := by simp
  rw [Matrix.det_apply']
  refine le_trans (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) le_rfl
  intro σ _
  have hC : (((Equiv.Perm.sign σ : ℤ) : Polynomial ℚ))
      = C (((Equiv.Perm.sign σ : ℤ) : ℚ)) :=
    (map_intCast (C : ℚ →+* Polynomial ℚ) _).symm
  rw [hC]
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hP : (∏ i, ((Matrix.of fun i j =>
      (C (A i j) + X * C (B i j) : Polynomial ℚ)) (σ i) i)).natDegree ≤ h := by
    simp only [Matrix.of_apply]
    have hmain := natDegree_prod_affine (Finset.univ : Finset (Fin h))
      (fun i => A (σ i) i) (fun i => B (σ i) i)
    rwa [hcard] at hmain
  calc (C (((Equiv.Perm.sign σ : ℤ) : ℚ))).natDegree
        + (∏ i, ((Matrix.of fun i j =>
          (C (A i j) + X * C (B i j) : Polynomial ℚ)) (σ i) i)).natDegree
      ≤ 0 + h := Nat.add_le_add (Polynomial.natDegree_C _).le hP
    _ = h := zero_add h

/-! ## Node enumeration and Vandermonde data -/

/-- Order enumeration of the pole indices `N < a ≤ K`. -/
noncomputable def nodeEmb (n : ℕ) (hn : 0 < n) : Fin (hDim n) ↪o ℕ :=
  Finset.orderEmbOfFin (Finset.Icc (N n + 1) (K n)) (card_Icc_NK n hn)

theorem nodeEmb_mem (n : ℕ) (hn : 0 < n) (k : Fin (hDim n)) :
    nodeEmb n hn k ∈ Finset.Icc (N n + 1) (K n) :=
  Finset.orderEmbOfFin_mem _ _ k

theorem orderEmb_symm_apply (s : Finset ℕ) {k : ℕ} (hk : s.card = k)
    (x : ↥s) :
    Finset.orderEmbOfFin s hk ((Finset.orderIsoOfFin s hk).symm x) = x.val := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  have hcan : (Finset.orderIsoOfFin s hk)
      (((Finset.orderIsoOfFin s hk).symm) x) = x := by
    show ((Finset.orderIsoOfFin s hk).toEquiv)
      (((Finset.orderIsoOfFin s hk).toEquiv).symm x) = x
    exact Equiv.apply_symm_apply _ _
  rw [hcan]
  rfl

theorem prod_nodeEmb (n : ℕ) (hn : 0 < n) {M : Type*} [CommMonoid M]
    (g : ℕ → M) :
    ∏ k : Fin (hDim n), g (nodeEmb n hn k)
      = ∏ a ∈ Finset.Icc (N n + 1) (K n), g a := by
  unfold nodeEmb
  refine Finset.prod_bij
    (fun k _ => Finset.orderEmbOfFin _ (card_Icc_NK n hn) k) ?hi ?inj ?surj ?h
  · intro k _
    exact Finset.orderEmbOfFin_mem _ _ k
  · intro k₁ _ k₂ _ heq
    exact (Finset.orderEmbOfFin _ (card_Icc_NK n hn)).injective heq
  · intro a ha
    exact ⟨(Finset.orderIsoOfFin _ (card_Icc_NK n hn)).symm ⟨a, ha⟩,
      Finset.mem_univ _,
      orderEmb_symm_apply _ (card_Icc_NK n hn) ⟨a, ha⟩⟩
  · intro k _
    rfl

theorem sum_nodeEmb (n : ℕ) (hn : 0 < n) {M : Type*} [AddCommMonoid M]
    (g : ℕ → M) :
    ∑ k : Fin (hDim n), g (nodeEmb n hn k)
      = ∑ a ∈ Finset.Icc (N n + 1) (K n), g a := by
  unfold nodeEmb
  refine Finset.sum_bij
    (fun k _ => Finset.orderEmbOfFin _ (card_Icc_NK n hn) k) ?hi ?inj ?surj ?h
  · intro k _
    exact Finset.orderEmbOfFin_mem _ _ k
  · intro k₁ _ k₂ _ heq
    exact (Finset.orderEmbOfFin _ (card_Icc_NK n hn)).injective heq
  · intro a ha
    exact ⟨(Finset.orderIsoOfFin _ (card_Icc_NK n hn)).symm ⟨a, ha⟩,
      Finset.mem_univ _,
      orderEmb_symm_apply _ (card_Icc_NK n hn) ⟨a, ha⟩⟩
  · intro k _
    rfl

/-- Vandermonde nodes `v_a = -a^2` (paper equation (12)). -/
noncomputable def nodeVal (n : ℕ) (hn : 0 < n) (k : Fin (hDim n)) : ℚ :=
  -((nodeEmb n hn k : ℚ)) ^ 2

/-- Diagonal weights `γ_a = a^6 D_N(-a^2)^7 / D'_tail(-a^2)`. -/
noncomputable def nodeGam (n : ℕ) (hn : 0 < n) (k : Fin (hDim n)) : ℚ :=
  (nodeEmb n hn k : ℚ) ^ 6 * (Dpoly (N n)).eval (-(nodeEmb n hn k : ℚ) ^ 2) ^ 7
    / (derivative (Dtail n)).eval (-(nodeEmb n hn k : ℚ) ^ 2)

theorem nat_eq_of_sq_eq {a b : ℕ} (h : (a : ℚ) ^ 2 = (b : ℚ) ^ 2) : a = b := by
  have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have hpow : a ^ 2 < b ^ 2 := pow_lt_pow_left' two_ne_zero hlt
    omega
  · exact heq
  · exfalso
    have hpow : b ^ 2 < a ^ 2 := pow_lt_pow_left' two_ne_zero hgt
    omega

theorem nodeVal_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (nodeVal n hn) := by
  intro k₁ k₂ hkk
  unfold nodeVal at hkk
  have hsq : ((nodeEmb n hn k₁ : ℕ) : ℚ) ^ 2
      = ((nodeEmb n hn k₂ : ℕ) : ℚ) ^ 2 := neg_inj.mp hkk
  have heq : nodeEmb n hn k₁ = nodeEmb n hn k₂ := nat_eq_of_sq_eq hsq
  exact (nodeEmb n hn).injective heq

theorem resCoeff_eq (n : ℕ) (i j a : ℕ) :
    resCoeff n i j a
      = (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7 * (-(a : ℚ) ^ 2) ^ (i + j)
        / (derivative (Dtail n)).eval (-(a : ℚ) ^ 2) := by
  unfold resCoeff Rnum
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow,
    Polynomial.eval_X]

theorem Bmat_apply (n : ℕ) (hn : 0 < n) (i j : Fin (hDim n)) :
    Bmat n i j
      = ∑ k : Fin (hDim n), nodeGam n hn k * (nodeVal n hn k) ^ (i.val)
        * (nodeVal n hn k) ^ (j.val) := by
  unfold Bmat
  simp only [Matrix.of_apply]
  calc ∑ a ∈ Finset.Icc (N n + 1) (K n),
          resCoeff n i.val j.val a * (a : ℚ) ^ 6
        = ∑ k : Fin (hDim n),
            resCoeff n i.val j.val (nodeEmb n hn k)
              * ((nodeEmb n hn k : ℚ)) ^ 6 :=
          (sum_nodeEmb n hn _).symm
      _ = ∑ k : Fin (hDim n), nodeGam n hn k * (nodeVal n hn k) ^ (i.val)
          * (nodeVal n hn k) ^ (j.val) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [resCoeff_eq]
          unfold nodeGam nodeVal
          rw [pow_add]
          ring

theorem Bmat_eq (n : ℕ) (hn : 0 < n) :
    Bmat n
      = (Matrix.vandermonde (nodeVal n hn))ᵀ
        * Matrix.diagonal (nodeGam n hn)
        * Matrix.vandermonde (nodeVal n hn) := by
  have hVD : ∀ i k : Fin (hDim n),
      (((Matrix.vandermonde (nodeVal n hn))ᵀ
        * Matrix.diagonal (nodeGam n hn)) i k)
        = ((Matrix.vandermonde (nodeVal n hn))ᵀ i k
          * nodeGam n hn k) := by
    intro i k
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ext i j
  rw [Bmat_apply n hn i j, Matrix.mul_apply]
  simp only [hVD, Matrix.transpose_apply, Matrix.vandermonde_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem det_Bmat (n : ℕ) (hn : 0 < n) :
    (Bmat n).det
      = ((Matrix.vandermonde (nodeVal n hn)).det) ^ 2
        * ∏ k, nodeGam n hn k := by
  rw [Bmat_eq n hn, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose]
  ring

/-! ## The tail-divisor derivative identity -/

theorem Dtail_deriv_eval (n : ℕ) (a : ℕ)
    (ha : a ∈ Finset.Icc (N n + 1) (K n)) :
    (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)
      = ∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a,
        ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
  have hderiv : derivative (Dtail n)
      = ∑ i ∈ Finset.Icc (N n + 1) (K n),
        ((∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase i,
          (X + C ((b : ℚ) ^ 2) : Polynomial ℚ))
          * derivative (X + C ((i : ℚ) ^ 2) : Polynomial ℚ)) := by
    unfold Dtail
    rw [Polynomial.derivative_prod_finset]
  have h1 : ∀ c : ℚ, derivative (X + C c : Polynomial ℚ) = 1 := by
    intro c
    simp
  rw [hderiv, Polynomial.eval_finsetSum]
  simp only [h1, mul_one]
  have hsum : (∑ i ∈ Finset.Icc (N n + 1) (K n),
        ((∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase i,
          (X + C ((b : ℚ) ^ 2) : Polynomial ℚ))).eval (-(a : ℚ) ^ 2))
      = ((∏ b ∈ (Finset.Icc (N n + 1) (K n)).erase a,
        (X + C ((b : ℚ) ^ 2) : Polynomial ℚ))).eval (-(a : ℚ) ^ 2) := by
    apply Finset.sum_eq_single a
    · intro i hi hia
      rw [Polynomial.eval_prod]
      have hmem : a ∈ (Finset.Icc (N n + 1) (K n)).erase i := by
        rw [Finset.mem_erase]
        exact ⟨Ne.symm hia, ha⟩
      refine Finset.prod_eq_zero hmem ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring
    · intro hcon
      exact absurd ha hcon
  rw [hsum, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro b _
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-! ## Pair products -/

/-- Ordered pairs `(a, b)` of pole indices with `a < b`. -/
noncomputable def pairLT (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc (N n + 1) (K n)) ×ˢ (Finset.Icc (N n + 1) (K n))).filter
    (fun p => p.1 < p.2)

theorem erase_eq_filter_union (n : ℕ) (t : ℕ)
    (ht : t ∈ Finset.Icc (N n + 1) (K n)) :
    (Finset.Icc (N n + 1) (K n)).erase t
      = (Finset.Icc (N n + 1) (K n)).filter (· < t)
        ∪ (Finset.Icc (N n + 1) (K n)).filter (fun u => t < u) := by
  ext u
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hne, hu⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  · rintro (⟨hu, h⟩ | ⟨hu, h⟩)
    · exact ⟨ne_of_lt h, hu⟩
    · exact ⟨ne_of_gt h, hu⟩

theorem filter_lt_gt_disjoint (s : Finset ℕ) (t : ℕ) :
    Disjoint (s.filter (· < t)) (s.filter fun u => t < u) := by
  rw [Finset.disjoint_filter]
  intro u _ h
  exact lt_asymm h.1 h.2

theorem prod_erase_eq (n : ℕ) (t : ℕ)
    (ht : t ∈ Finset.Icc (N n + 1) (K n)) :
    ∏ u ∈ (Finset.Icc (N n + 1) (K n)).erase t, ((u : ℚ) ^ 2 - (t : ℚ) ^ 2)
      = (∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (· < t),
          ((u : ℚ) ^ 2 - (t : ℚ) ^ 2))
        * ∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (fun u => t < u),
          ((u : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
  rw [erase_eq_filter_union n t ht,
    Finset.prod_union (filter_lt_gt_disjoint _ _)]

theorem prod_LT_lower (n : ℕ) :
    ∏ t ∈ Finset.Icc (N n + 1) (K n),
        ∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (· < t),
          ((u : ℚ) ^ 2 - (t : ℚ) ^ 2)
      = ∏ p ∈ pairLT n, ((p.1 : ℚ) ^ 2 - (p.2 : ℚ) ^ 2) := by
  conv_lhs => rw [← Finset.prod_sigma]
  simp only [pairLT]
  apply Finset.prod_bij (fun p _ => (p.2, p.1)) ?hi ?inj ?surj ?h
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨ht, hu, hlt⟩ := hp
    exact ⟨⟨hu, ht⟩, hlt⟩
  · intro p₁ _ p₂ _ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext heq.2 heq.1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hq1, hq2⟩, hlt⟩ := hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨hq2, hq1, hlt⟩
  · intro p _
    rfl

theorem prod_LT_upper (n : ℕ) :
    ∏ t ∈ Finset.Icc (N n + 1) (K n),
        ∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (fun u => t < u),
          ((u : ℚ) ^ 2 - (t : ℚ) ^ 2)
      = ∏ p ∈ pairLT n, ((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2) := by
  conv_lhs => rw [← Finset.prod_sigma]
  simp only [pairLT]
  apply Finset.prod_bij (fun p _ => p) ?hi ?inj ?surj ?h
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨ht, hu, hlt⟩ := hp
    exact ⟨⟨ht, hu⟩, hlt⟩
  · intro p₁ _ p₂ _ heq
    exact heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hq1, hq2⟩, hlt⟩ := hq
    refine ⟨q, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨hq1, hq2, hlt⟩
  · intro p _
    rfl

theorem prod_Dtail_deriv_eq (n : ℕ) :
    ∏ t ∈ Finset.Icc (N n + 1) (K n),
        (derivative (Dtail n)).eval (-(t : ℚ) ^ 2)
      = (-1 : ℚ) ^ ((pairLT n).card)
        * ∏ p ∈ pairLT n, (((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2) ^ 2) := by
  have hstep1 : ∏ t ∈ Finset.Icc (N n + 1) (K n),
        (derivative (Dtail n)).eval (-(t : ℚ) ^ 2)
      = ∏ p ∈ pairLT n,
        (((p.1 : ℚ) ^ 2 - (p.2 : ℚ) ^ 2)
          * ((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2)) := by
    have h1 : ∀ t ∈ Finset.Icc (N n + 1) (K n),
        (derivative (Dtail n)).eval (-(t : ℚ) ^ 2)
          = (∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (· < t),
              ((u : ℚ) ^ 2 - (t : ℚ) ^ 2))
            * ∏ u ∈ (Finset.Icc (N n + 1) (K n)).filter (fun u => t < u),
              ((u : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
      intro t ht
      rw [Dtail_deriv_eval n t ht, prod_erase_eq n t ht]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_LT_lower n,
      prod_LT_upper n, ← Finset.prod_mul_distrib]
  rw [hstep1]
  have h2 : ∀ p ∈ pairLT n,
      (((p.1 : ℚ) ^ 2 - (p.2 : ℚ) ^ 2) * ((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2))
        = (-1) * (((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2) ^ 2) := by
    intro p _
    ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const]

/-- Ordered pairs `(i, j)` of `Fin` indices with `i < j`. -/
noncomputable def pairLTFin (n : ℕ) : Finset (Fin (hDim n) × Fin (hDim n)) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

theorem prod_pairLT_eq_fin (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ pairLT n, (((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2) ^ 2)
      = ∏ q ∈ pairLTFin n,
        ((((nodeEmb n hn q.2 : ℕ) : ℚ) ^ 2
          - ((nodeEmb n hn q.1 : ℕ) : ℚ) ^ 2) ^ 2) := by
  have h : ∏ q ∈ pairLTFin n,
          ((((nodeEmb n hn q.2 : ℕ) : ℚ) ^ 2
            - ((nodeEmb n hn q.1 : ℕ) : ℚ) ^ 2) ^ 2)
        = ∏ p ∈ pairLT n, (((p.2 : ℚ) ^ 2 - (p.1 : ℚ) ^ 2) ^ 2) := by
    simp only [pairLT, pairLTFin]
    apply Finset.prod_bij (fun q _ => (nodeEmb n hn q.1, nodeEmb n hn q.2))
      ?hi ?inj ?surj ?h
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ] at hq
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨nodeEmb_mem n hn q.1, nodeEmb_mem n hn q.2⟩, ?_⟩
      exact (nodeEmb n hn).strictMono hq.2
    · intro q₁ _ q₂ _ heq
      simp only [Prod.mk.injEq] at heq
      have e1 := (nodeEmb n hn).injective heq.1
      have e2 := (nodeEmb n hn).injective heq.2
      exact Prod.ext e1 e2
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hlt⟩ := hp
      set e1 := (Finset.orderIsoOfFin _ (card_Icc_NK n hn)).symm ⟨p.1, hp1⟩
      set e2 := (Finset.orderIsoOfFin _ (card_Icc_NK n hn)).symm ⟨p.2, hp2⟩
      have he1 : nodeEmb n hn e1 = p.1 :=
        orderEmb_symm_apply _ (card_Icc_NK n hn) ⟨p.1, hp1⟩
      have he2 : nodeEmb n hn e2 = p.2 :=
        orderEmb_symm_apply _ (card_Icc_NK n hn) ⟨p.2, hp2⟩
      have hlt' : e1 < e2 := by
        have hiff := (nodeEmb n hn).strictMono.lt_iff_lt (a := e1) (b := e2)
        rw [he1, he2] at hiff
        exact hiff.mp hlt
      refine ⟨(e1, e2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ]
        exact hlt'
      · simp only [he1, he2]
        rfl
    · intro q _
      rfl
  exact h.symm

theorem prod_pairLTFin_eq_det (n : ℕ) (hn : 0 < n) :
    ∏ q ∈ pairLTFin n,
        ((((nodeEmb n hn q.2 : ℕ) : ℚ) ^ 2
          - ((nodeEmb n hn q.1 : ℕ) : ℚ) ^ 2) ^ 2)
      = ((Matrix.vandermonde (nodeVal n hn)).det) ^ 2 := by
  have hdet : (Matrix.vandermonde (nodeVal n hn)).det
      = ∏ i : Fin (hDim n), ∏ j ∈ Finset.Ioi i,
        (((nodeEmb n hn i : ℚ) ^ 2 - (nodeEmb n hn j : ℚ) ^ 2)) := by
    rw [Matrix.det_vandermonde]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    unfold nodeVal
    ring
  have hQ : ∏ q ∈ pairLTFin n,
          ((((nodeEmb n hn q.2 : ℕ) : ℚ) ^ 2
            - ((nodeEmb n hn q.1 : ℕ) : ℚ) ^ 2) ^ 2)
        = ∏ i : Fin (hDim n), ∏ j ∈ Finset.Ioi i,
          ((((nodeEmb n hn j : ℚ) ^ 2 - (nodeEmb n hn i : ℚ) ^ 2)) ^ 2) := by
    have hQeq : pairLTFin n
        = Finset.univ.sigma
          (fun i : Fin (hDim n) => Finset.univ.filter (fun j => i < j)) := by
      ext q
      simp [pairLTFin, Finset.mem_sigma]
    rw [hQeq, Finset.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    have hIoi : Finset.univ.filter (fun j : Fin (hDim n) => i < j)
        = Finset.Ioi i := by
      ext j
      simp
    rw [hIoi]
  rw [hQ, hdet, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem card_pairLT (n : ℕ) (hn : 0 < n) :
    (pairLT n).card = (hDim n) * ((hDim n) - 1) / 2 := by
  have hPeq : pairLT n
      = (Finset.Icc (N n + 1) (K n)).sigma
        (fun a => (Finset.Icc (N n + 1) (K n)).filter (fun b => a < b)) := by
    ext p
    simp only [pairLT, Finset.mem_filter, Finset.mem_product, Finset.mem_sigma]
    constructor
    · rintro ⟨⟨h1, h2⟩, hlt⟩
      exact ⟨h1, h2, hlt⟩
    · rintro ⟨h1, h2, hlt⟩
      exact ⟨⟨h1, h2⟩, hlt⟩
  have hfib : ∀ a ∈ Finset.Icc (N n + 1) (K n),
      ((Finset.Icc (N n + 1) (K n)).filter (fun b => a < b)).card
        = K n - a := by
    intro a ha
    have hset : (Finset.Icc (N n + 1) (K n)).filter (fun b => a < b)
        = Finset.Icc (a + 1) (K n) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hlo, hhi⟩, hlt⟩
        exact ⟨by omega, hhi⟩
      · rintro ⟨hlo, hhi⟩
        have ha1 := (Finset.mem_Icc.mp ha).1
        exact ⟨⟨by omega, hhi⟩, by omega⟩
    rw [hset, Nat.card_Icc]
    omega
  have hKN : K n - N n = hDim n := sub_NK_eq_hDim n
  have hpos : 0 < hDim n := hDim_pos_of_pos n hn
  have hle : hDim n ≤ K n := hDim_le_K n
  have hre : ∑ a ∈ Finset.Icc (N n + 1) (K n), (K n - a)
      = ∑ c ∈ Finset.range (hDim n), c := by
    apply Finset.sum_bij (fun a _ => K n - a) ?hi ?inj ?surj ?h
    · intro a ha
      simp only [Finset.mem_range]
      have hb := Finset.mem_Icc.mp ha
      omega
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 := Finset.mem_Icc.mp ha₁
      have h2 := Finset.mem_Icc.mp ha₂
      omega
    · intro c hc
      simp only [Finset.mem_range] at hc
      refine ⟨K n - c, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · show K n - (K n - c) = c
        have hcK : c ≤ K n := by omega
        omega
    · intro a _
      rfl
  rw [hPeq, Finset.card_sigma, Finset.sum_congr rfl hfib, hre,
    Finset.sum_range_id]

/-! ## Determinant value and nonvanishing -/

theorem prod_gamma_eq (n : ℕ) (hn : 0 < n) :
    ∏ k : Fin (hDim n), nodeGam n hn k
      = (∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7))
        / ∏ a ∈ Finset.Icc (N n + 1) (K n),
          (derivative (Dtail n)).eval (-(a : ℚ) ^ 2) := by
  have hnum : ∏ k : Fin (hDim n),
          ((nodeEmb n hn k : ℚ) ^ 6
            * (Dpoly (N n)).eval (-(nodeEmb n hn k : ℚ) ^ 2) ^ 7)
        = ∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) :=
      prod_nodeEmb n hn
        (fun a => (a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7)
  have hden : ∏ k : Fin (hDim n),
          (derivative (Dtail n)).eval (-(nodeEmb n hn k : ℚ) ^ 2)
        = ∏ a ∈ Finset.Icc (N n + 1) (K n),
          (derivative (Dtail n)).eval (-(a : ℚ) ^ 2) :=
      prod_nodeEmb n hn
        (fun a => (derivative (Dtail n)).eval (-(a : ℚ) ^ 2))
  calc ∏ k : Fin (hDim n), nodeGam n hn k
        = ∏ k : Fin (hDim n),
            (((nodeEmb n hn k : ℚ) ^ 6
              * (Dpoly (N n)).eval (-(nodeEmb n hn k : ℚ) ^ 2) ^ 7)
              / (derivative (Dtail n)).eval (-(nodeEmb n hn k : ℚ) ^ 2)) :=
          Finset.prod_congr rfl (fun k _ => rfl)
      _ = (∏ k : Fin (hDim n),
            ((nodeEmb n hn k : ℚ) ^ 6
              * (Dpoly (N n)).eval (-(nodeEmb n hn k : ℚ) ^ 2) ^ 7))
          / ∏ k : Fin (hDim n),
            (derivative (Dtail n)).eval (-(nodeEmb n hn k : ℚ) ^ 2) :=
          Finset.prod_div_distrib _ _
      _ = _ := by rw [hnum, hden]

theorem prod_Dtail_deriv_value (n : ℕ) (hn : 0 < n) :
    ∏ a ∈ Finset.Icc (N n + 1) (K n),
        (derivative (Dtail n)).eval (-(a : ℚ) ^ 2)
      = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        * ((Matrix.vandermonde (nodeVal n hn)).det) ^ 2 := by
  rw [prod_Dtail_deriv_eq n, prod_pairLT_eq_fin n hn,
    prod_pairLTFin_eq_det n hn, card_pairLT n hn]

theorem det_Bmat_eq (n : ℕ) (hn : 0 < n) :
    (Bmat n).det
      = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        * ∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) := by
  have hVne : (Matrix.vandermonde (nodeVal n hn)).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact nodeVal_injective n hn
  have hV2 : ((Matrix.vandermonde (nodeVal n hn)).det) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hVne
  have hsgn : (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hS2 : (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        * (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2) = 1 := by
    have hexp : (hDim n) * ((hDim n) - 1) / 2
          + (hDim n) * ((hDim n) - 1) / 2
        = 2 * ((hDim n) * ((hDim n) - 1) / 2) := by ring
    rw [← pow_add, hexp, pow_mul]
    norm_num
  have hNum : (∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7))
          / (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
          * ∏ a ∈ Finset.Icc (N n + 1) (K n),
            ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) := by
    rw [div_eq_iff hsgn]
    calc ∏ a ∈ Finset.Icc (N n + 1) (K n),
            ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7)
          = 1 * ∏ a ∈ Finset.Icc (N n + 1) (K n),
            ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) := by
            rw [one_mul]
        _ = ((-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
              * (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2))
            * ∏ a ∈ Finset.Icc (N n + 1) (K n),
              ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) := by
            rw [hS2]
        _ = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
            * (∏ a ∈ Finset.Icc (N n + 1) (K n),
              ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7))
            * (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2) := by
            ring
  rw [det_Bmat n hn, prod_gamma_eq n hn, prod_Dtail_deriv_value n hn,
    mul_div_assoc,
    mul_comm (((Matrix.vandermonde (nodeVal n hn)).det) ^ 2),
    mul_div_mul_right _ _ hV2, hNum]

theorem leadCoeff_ne_zero (n : ℕ) (hn : 0 < n) :
    (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        * ∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7)
        ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  apply mul_ne_zero (pow_ne_zero 6 _) _
  · have ha1 := (Finset.mem_Icc.mp ha).1
    have hpos : 0 < a := by omega
    exact_mod_cast ne_of_gt hpos
  · apply pow_ne_zero 7
    unfold Dpoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hjN : j < N n := Finset.mem_range.mp hj
    have hne : j + 1 ≠ a := by omega
    have hsq : ((j : ℚ) + 1) ^ 2 ≠ (a : ℚ) ^ 2 := by
      intro hcon
      have hcon' : (((j + 1 : ℕ)) : ℚ) ^ 2 = (a : ℚ) ^ 2 := by
        push_cast
        exact hcon
      exact hne (nat_eq_of_sq_eq hcon')
    intro hcon
    apply hsq
    linarith

/-! ## Main theorem -/

/-- Lemma 2.3, equations (10)-(15): `Δ_K` has degree exactly `h` with the
explicit nonzero leading coefficient. -/
theorem degreeLemma (n : ℕ) (hn : 0 < n) :
    (DeltaK n).natDegree = hDim n
      ∧ (DeltaK n).coeff (hDim n)
        = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
          * ∏ a ∈ Finset.Icc (N n + 1) (K n),
            ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7)
      ∧ (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
          * ∏ a ∈ Finset.Icc (N n + 1) (K n),
            ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7)
          ≠ 0 := by
  have hcoeff : (DeltaK n).coeff (hDim n) = (Bmat n).det := by
    unfold DeltaK
    rw [Gmat_eq_affine n]
    exact coeff_det_affine (Amat n) (Bmat n)
  have hdet : (Bmat n).det
      = (-1 : ℚ) ^ ((hDim n) * ((hDim n) - 1) / 2)
        * ∏ a ∈ Finset.Icc (N n + 1) (K n),
          ((a : ℚ) ^ 6 * (Dpoly (N n)).eval (-(a : ℚ) ^ 2) ^ 7) :=
    det_Bmat_eq n hn
  have hne := leadCoeff_ne_zero n hn
  have hdeg_le : (DeltaK n).natDegree ≤ hDim n := by
    unfold DeltaK
    rw [Gmat_eq_affine n]
    exact natDegree_det_affine_le (Amat n) (Bmat n)
  have hdeg_ge : hDim n ≤ (DeltaK n).natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    rw [hcoeff, hdet]
    exact hne
  refine ⟨le_antisymm hdeg_le hdeg_ge, ?_, hne⟩
  rw [hcoeff, hdet]

end ZetaSeven
