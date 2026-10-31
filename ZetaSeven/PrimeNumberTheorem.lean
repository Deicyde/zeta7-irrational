import Mathlib
import PrimeNumberTheoremAnd.Consequences

/-!
# Prime number theorem and prime Riemann sums (paper Section 5.5, proof of Proposition 5.4)

The proof of Proposition 5.4 (the prime-sum bound, equations (87)-(90)) uses the prime number
theorem in the form `θ(x) ~ x` together with partial summation: for `0 < a < b` and a weight
`G` that is bounded on `[a, b]` and continuous there except at finitely many points,
`X⁻¹ ∑_{aX < p ≤ bX} G(p/X) log p → ∫_a^b G(y) dy` as `X → ∞`.

The asymptotic `θ ~[atTop] id` (`ZetaSeven.theta_isEquivalent_id`) is
`chebyshev_asymptotic` from the pinned PrimeNumberTheoremAnd dependency. The Riemann-sum
statement (`ZetaSeven.tendsto_primeRiemannSum`) is proved from that asymptotic alone
(`ZetaSeven.tendsto_primeRiemannSum_of_theta`). The weight is sandwiched between the upper and
lower step functions of the uniform partition of `[a, b]` into `N` pieces: on each piece the
prime sum is `X⁻¹ (θ(dX) - θ(cX)) → d - c` times a constant, since `log p ≥ 0`. The step
integrals converge to `∫_a^b G` as `N → ∞` by dominated convergence, because `G` is bounded and
continuous at almost every point of `[a, b]`.

Here `θ` is Mathlib's `Chebyshev.theta`, and the sum over primes `aX < p ≤ bX` is written as a
sum over `p ∈ Finset.Ioc ⌊aX⌋₊ ⌊bX⌋₊` with `p` prime, which is the same set of primes for
`X > 0`.
-/

namespace ZetaSeven

open Filter Topology Asymptotics MeasureTheory
open scoped Chebyshev

namespace PrimeSum

/-! ## Prime sums over consecutive intervals -/

theorem sum_Ioc_prime_consecutive (F : ℕ → ℝ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (∑ p ∈ Finset.Ioc m n with p.Prime, F p) + ∑ p ∈ Finset.Ioc n k with p.Prime, F p =
      ∑ p ∈ Finset.Ioc m k with p.Prime, F p := by
  simp only [Finset.sum_filter]
  exact Finset.sum_Ioc_consecutive _ hmn hnk

theorem theta_sub_theta_eq_sum {x y : ℝ} (hxy : x ≤ y) :
    θ y - θ x = ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime, Real.log p := by
  have h := sum_Ioc_prime_consecutive (fun p : ℕ => Real.log p) (Nat.zero_le ⌊x⌋₊)
    (Nat.floor_le_floor hxy)
  beta_reduce at h
  unfold Chebyshev.theta
  rw [← h, add_sub_cancel_left]

/-! ## The limit of `θ(vX) / X` -/

theorem tendsto_theta_mul_div (hθ : θ ~[atTop] id) {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun X : ℝ => θ (v * X) / X) atTop (𝓝 v) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp only [zero_mul, Chebyshev.theta_zero, zero_div]
    exact tendsto_const_nhds
  have h1 : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) := by
    have hz : ∀ᶠ x : ℝ in atTop, id x ≠ 0 := eventually_ne_atTop 0
    exact (isEquivalent_iff_tendsto_one hz).1 hθ
  have h2 : Tendsto (fun X : ℝ => v * (θ (v * X) / (v * X))) atTop (𝓝 (v * 1)) :=
    (h1.comp (tendsto_id.const_mul_atTop hv)).const_mul v
  rw [mul_one] at h2
  refine h2.congr fun X => ?_
  rw [← mul_div_assoc, mul_div_mul_left _ _ hv.ne']

theorem tendsto_theta_sub_div (hθ : θ ~[atTop] id) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto (fun X : ℝ => (θ (v * X) - θ (u * X)) / X) atTop (𝓝 (v - u)) :=
  ((tendsto_theta_mul_div hθ hv).sub (tendsto_theta_mul_div hθ hu)).congr fun _ =>
    (sub_div _ _ _).symm

/-! ## The uniform partition of `[a, b]` -/

/-- The `k`-th point `a + k (b - a) / N` of the uniform partition of `[a, b]` into `N` pieces. -/
noncomputable def gridPt (a b : ℝ) (N k : ℕ) : ℝ := a + k * ((b - a) / N)

/-- The index `k` of the piece `(gridPt a b N k, gridPt a b N (k + 1)]` containing `y`. -/
noncomputable def gridIdx (a b : ℝ) (N : ℕ) (y : ℝ) : ℕ := ⌈(y - a) / ((b - a) / N)⌉₊ - 1

/-- The supremum of `G` over the `k`-th piece of the uniform partition. -/
noncomputable def gridSup (G : ℝ → ℝ) (a b : ℝ) (N k : ℕ) : ℝ :=
  sSup (G '' Set.Ioc (gridPt a b N k) (gridPt a b N (k + 1)))

/-- The infimum of `G` over the `k`-th piece of the uniform partition. -/
noncomputable def gridInf (G : ℝ → ℝ) (a b : ℝ) (N k : ℕ) : ℝ :=
  sInf (G '' Set.Ioc (gridPt a b N k) (gridPt a b N (k + 1)))

/-- The infimum of `G` over a piece is minus the supremum of `-G`, so every bound below is proved
for `gridSup` and transferred to `gridInf`. -/
theorem gridInf_eq_neg (G : ℝ → ℝ) (a b : ℝ) (N k : ℕ) :
    gridInf G a b N k = -gridSup (fun y => -G y) a b N k := by
  rw [gridInf, gridSup, Real.sInf_def, ← Set.image_neg_eq_neg, Set.image_image]

theorem gridPt_zero (a b : ℝ) (N : ℕ) : gridPt a b N 0 = a := by
  simp [gridPt]

theorem gridPt_self (a b : ℝ) {N : ℕ} (hN : 0 < N) : gridPt a b N N = b := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  unfold gridPt
  rw [mul_div_cancel₀ _ hNr.ne']
  ring

theorem gridPt_succ_sub (a b : ℝ) (N k : ℕ) :
    gridPt a b N (k + 1) - gridPt a b N k = (b - a) / N := by
  unfold gridPt
  push_cast
  ring

theorem gridPt_le_succ {a b : ℝ} (hab : a ≤ b) {N k : ℕ} :
    gridPt a b N k ≤ gridPt a b N (k + 1) := by
  have h := gridPt_succ_sub a b N k
  have h' : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
  linarith

theorem le_gridPt {a b : ℝ} (hab : a ≤ b) {N k : ℕ} : a ≤ gridPt a b N k := by
  have h : 0 ≤ (k : ℝ) * ((b - a) / N) :=
    mul_nonneg (Nat.cast_nonneg k) (div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N))
  unfold gridPt
  linarith

theorem gridPt_le {a b : ℝ} (hab : a ≤ b) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    gridPt a b N k ≤ b := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have h1 : (k : ℝ) * ((b - a) / N) ≤ (N : ℝ) * ((b - a) / N) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) (div_nonneg (sub_nonneg.2 hab) hNr.le)
  rw [mul_div_cancel₀ _ hNr.ne'] at h1
  unfold gridPt
  linarith

theorem piece_subset {a b : ℝ} (hab : a ≤ b) {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    Set.Ioc (gridPt a b N k) (gridPt a b N (k + 1)) ⊆ Set.Icc a b := fun _ hz =>
  Set.mem_Icc.2 ⟨(le_gridPt hab).trans hz.1.le, hz.2.trans (gridPt_le hab hN hk)⟩

theorem gridIdx_spec {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Set.Ioc a b) :
    gridIdx a b N y < N ∧ gridPt a b N (gridIdx a b N y) < y ∧
      y ≤ gridPt a b N (gridIdx a b N y + 1) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) hNr
  obtain ⟨t, ht⟩ : ∃ t, t = (y - a) / ((b - a) / N) := ⟨_, rfl⟩
  have hidx : gridIdx a b N y = ⌈t⌉₊ - 1 := by
    subst ht
    rfl
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos (sub_pos.2 hy.1) hh
  have htN : t ≤ N := by
    rw [ht, div_le_iff₀ hh, mul_div_cancel₀ _ hNr.ne']
    linarith [hy.2]
  have hc0 : 0 < ⌈t⌉₊ := Nat.ceil_pos.2 ht0
  have hcN : ⌈t⌉₊ ≤ N := Nat.ceil_le.2 htN
  have hcast : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_of_lt hc0), Nat.cast_one]
  have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hle : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  refine ⟨by rw [hidx]; omega, ?_, ?_⟩
  · have h1 : ((gridIdx a b N y : ℕ) : ℝ) < t := by
      rw [hidx, hcast]
      linarith
    rw [ht, lt_div_iff₀ hh] at h1
    unfold gridPt
    linarith
  · have h2 : t ≤ ((gridIdx a b N y + 1 : ℕ) : ℝ) := by
      rw [hidx, Nat.sub_add_cancel (Nat.one_le_of_lt hc0)]
      exact hle
    rw [ht, div_le_iff₀ hh] at h2
    unfold gridPt
    linarith

theorem gridIdx_eq_of_mem {a b : ℝ} {N : ℕ} (hh : 0 < (b - a) / N) {k : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioc (gridPt a b N k) (gridPt a b N (k + 1))) : gridIdx a b N y = k := by
  have hceil : ⌈(y - a) / ((b - a) / N)⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (Nat.add_one_ne_zero k), Nat.add_sub_cancel, lt_div_iff₀ hh,
      div_le_iff₀ hh]
    have h1 := hy.1
    have h2 := hy.2
    unfold gridPt at h1 h2
    constructor <;> linarith
  show ⌈(y - a) / ((b - a) / N)⌉₊ - 1 = k
  rw [hceil, Nat.add_sub_cancel]

/-! ## Step functions on the partition -/

theorem measurable_grid_step (a b : ℝ) (N : ℕ) (V : ℕ → ℝ) :
    Measurable fun y => V (gridIdx a b N y) := by
  have hm : Measurable fun y : ℝ => (y - a) / ((b - a) / N) := by fun_prop
  exact (measurable_from_nat (f := fun n : ℕ => V (n - 1))).comp hm.nat_ceil

theorem integral_grid_step {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) (V : ℕ → ℝ) :
    ∫ y in a..b, V (gridIdx a b N y) = ∑ k ∈ Finset.range N, V k * ((b - a) / N) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have heq : ∀ k : ℕ, Set.EqOn (fun _ : ℝ => V k) (fun y => V (gridIdx a b N y))
      (Set.uIoc (gridPt a b N k) (gridPt a b N (k + 1))) := by
    intro k y hy
    rw [Set.uIoc_of_le (gridPt_le_succ hab.le)] at hy
    simp only [gridIdx_eq_of_mem hh hy]
  have hint : ∀ k < N, IntervalIntegrable (fun y => V (gridIdx a b N y)) volume
      (gridPt a b N k) (gridPt a b N (k + 1)) := fun k _ =>
    (intervalIntegrable_congr (heq k)).1 intervalIntegrable_const
  have hpiece : ∀ k : ℕ, ∫ y in gridPt a b N k..gridPt a b N (k + 1), V (gridIdx a b N y) =
      V k * ((b - a) / N) := by
    intro k
    have h : ∫ y in gridPt a b N k..gridPt a b N (k + 1), V (gridIdx a b N y) =
        ∫ _ in gridPt a b N k..gridPt a b N (k + 1), V k :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => (heq k hy).symm)
    rw [h, intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub, mul_comm]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [gridPt_zero, gridPt_self a b hN] at hsum
  rw [← hsum]
  exact Finset.sum_congr rfl fun k _ => hpiece k

/-! ## Bounds on a single piece -/

theorem bddAbove_piece {a b : ℝ} (hab : a ≤ b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    BddAbove (G '' Set.Ioc (gridPt a b N k) (gridPt a b N (k + 1))) :=
  ⟨C, by
    rintro _ ⟨z, hz, rfl⟩
    exact (abs_le.1 (hC z (piece_subset hab hN hk hz))).2⟩

theorem abs_sSup_image_le {G : ℝ → ℝ} {I : Set ℝ} {C y : ℝ} (hy : y ∈ I)
    (hC : ∀ z ∈ I, |G z| ≤ C) : |sSup (G '' I)| ≤ C := by
  have hbdd : BddAbove (G '' I) := ⟨C, by
    rintro _ ⟨z, hz, rfl⟩
    exact (abs_le.1 (hC z hz)).2⟩
  rw [abs_le]
  refine ⟨(abs_le.1 (hC y hy)).1.trans (le_csSup hbdd (Set.mem_image_of_mem G hy)), ?_⟩
  refine csSup_le ⟨G y, Set.mem_image_of_mem G hy⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (abs_le.1 (hC z hz)).2

theorem div_mem_Ioc {u v X : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hX : 0 < X) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊u * X⌋₊ ⌊v * X⌋₊) : (p : ℝ) / X ∈ Set.Ioc u v := by
  rw [Finset.mem_Ioc] at hp
  refine Set.mem_Ioc.2 ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hX]
    exact (Nat.floor_lt (mul_nonneg hu hX.le)).1 hp.1
  · rw [div_le_iff₀ hX]
    exact (Nat.le_floor_iff (mul_nonneg hv hX.le)).1 hp.2

theorem piece_sum_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {N k : ℕ} (hN : 0 < N) (hk : k < N) {X : ℝ}
    (hX : 0 < X) :
    ∑ p ∈ Finset.Ioc ⌊gridPt a b N k * X⌋₊ ⌊gridPt a b N (k + 1) * X⌋₊ with p.Prime,
        G (p / X) * Real.log p
      ≤ gridSup G a b N k * (θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X)) := by
  have h0 : 0 ≤ gridPt a b N k := ha.trans (le_gridPt hab.le)
  have h1 : 0 ≤ gridPt a b N (k + 1) := ha.trans (le_gridPt hab.le)
  rw [theta_sub_theta_eq_sum (mul_le_mul_of_nonneg_right (gridPt_le_succ hab.le) hX.le),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hmem := div_mem_Ioc h0 h1 hX hp.1
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  exact mul_le_mul_of_nonneg_right
    (le_csSup (bddAbove_piece hab.le hC hN hk) (Set.mem_image_of_mem G hmem)) hlog

/-! ## Bounds on the whole prime sum -/

theorem sum_prime_grid (F : ℕ → ℝ) {a b X : ℝ} (hab : a ≤ b) (hX : 0 ≤ X) (N M : ℕ) :
    ∑ k ∈ Finset.range M,
        ∑ p ∈ Finset.Ioc ⌊gridPt a b N k * X⌋₊ ⌊gridPt a b N (k + 1) * X⌋₊ with p.Prime, F p
      = ∑ p ∈ Finset.Ioc ⌊a * X⌋₊ ⌊gridPt a b N M * X⌋₊ with p.Prime, F p := by
  induction M with
  | zero => simp [gridPt_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    exact sum_Ioc_prime_consecutive F
      (Nat.floor_le_floor (mul_le_mul_of_nonneg_right (le_gridPt hab) hX))
      (Nat.floor_le_floor (mul_le_mul_of_nonneg_right (gridPt_le_succ hab) hX))

theorem primeSum_le_upper {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {N : ℕ} (hN : 0 < N) {X : ℝ} (hX : 0 < X) :
    X⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊ with p.Prime, G (p / X) * Real.log p
      ≤ ∑ k ∈ Finset.range N,
        gridSup G a b N k * ((θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X)) / X) := by
  have hdec := sum_prime_grid (fun p : ℕ => G (p / X) * Real.log p) hab.le hX.le N N
  beta_reduce at hdec
  rw [gridPt_self a b hN] at hdec
  rw [← hdec, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < N := Finset.mem_range.1 hk
  calc _ ≤ X⁻¹ * (gridSup G a b N k *
          (θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X))) :=
        mul_le_mul_of_nonneg_left (piece_sum_le ha hab hC hN hk' hX) (inv_nonneg.2 hX.le)
    _ = gridSup G a b N k * ((θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X)) / X) := by
        ring

theorem lower_le_primeSum {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {N : ℕ} (hN : 0 < N) {X : ℝ} (hX : 0 < X) :
    ∑ k ∈ Finset.range N,
        gridInf G a b N k * ((θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X)) / X)
      ≤ X⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊ with p.Prime, G (p / X) * Real.log p := by
  have h := primeSum_le_upper ha hab (G := fun y => -G y)
    (fun y hy => (abs_neg (G y)).trans_le (hC y hy)) hN hX
  simp only [gridInf_eq_neg, neg_mul, Finset.sum_neg_distrib, mul_neg] at h ⊢
  linarith

theorem tendsto_grid_sum (hθ : θ ~[atTop] id) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ)
    (V : ℕ → ℝ) :
    Tendsto (fun X : ℝ => ∑ k ∈ Finset.range N,
        V k * ((θ (gridPt a b N (k + 1) * X) - θ (gridPt a b N k * X)) / X))
      atTop (𝓝 (∑ k ∈ Finset.range N, V k * ((b - a) / N))) := by
  refine tendsto_finsetSum _ fun k _ => ?_
  have h0 : 0 ≤ gridPt a b N k := ha.trans (le_gridPt hab)
  have h1 : 0 ≤ gridPt a b N (k + 1) := ha.trans (le_gridPt hab)
  rw [← gridPt_succ_sub a b N k]
  exact (tendsto_theta_sub_div hθ h0 h1).const_mul (V k)

/-! ## Convergence of the step integrals -/

theorem eventually_piece_close {a b : ℝ} (hab : a < b) {G : ℝ → ℝ} {y : ℝ}
    (hy : y ∈ Set.Ioc a b) (hcont : ContinuousWithinAt G (Set.Icc a b) y) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ z ∈ Set.Ioc (gridPt a b N (gridIdx a b N y))
      (gridPt a b N (gridIdx a b N y + 1)), |G z - G y| < ε := by
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousWithinAt_iff.1 hcont ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hNr : (b - a) / δ < N := hN₀.trans_le (Nat.cast_le.2 hN)
  have hNpos' : (0 : ℝ) < N := (div_pos (sub_pos.2 hab) hδ).trans hNr
  have hNpos : 0 < N := Nat.cast_pos.1 hNpos'
  have hmesh : (b - a) / N < δ := by
    rw [div_lt_iff₀ hNpos', mul_comm]
    rwa [div_lt_iff₀ hδ] at hNr
  obtain ⟨hk, h1, h2⟩ := gridIdx_spec hab hNpos hy
  have hlen := gridPt_succ_sub a b N (gridIdx a b N y)
  refine ⟨hNpos, fun z hz => ?_⟩
  have hz1 := hz.1
  have hz2 := hz.2
  have hd : dist z y < δ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  have h := hδG (piece_subset hab.le hNpos hk hz) hd
  rwa [Real.dist_eq] at h

theorem tendsto_gridSup {a b : ℝ} (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {y : ℝ} (hy : y ∈ Set.Ioc a b)
    (hcont : ContinuousWithinAt G (Set.Icc a b) y) :
    Tendsto (fun N : ℕ => gridSup G a b N (gridIdx a b N y)) atTop (𝓝 (G y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_piece_close hab hy hcont (half_pos hε)] with N hN
  obtain ⟨hNpos, hz⟩ := hN
  obtain ⟨hk, h1, h2⟩ := gridIdx_spec hab hNpos hy
  have hymem : y ∈ Set.Ioc (gridPt a b N (gridIdx a b N y))
      (gridPt a b N (gridIdx a b N y + 1)) := Set.mem_Ioc.2 ⟨h1, h2⟩
  have hup : gridSup G a b N (gridIdx a b N y) ≤ G y + ε / 2 := by
    refine csSup_le ⟨G y, Set.mem_image_of_mem G hymem⟩ ?_
    rintro _ ⟨z, hz', rfl⟩
    linarith [(abs_lt.1 (hz z hz')).2]
  have hlo : G y ≤ gridSup G a b N (gridIdx a b N y) :=
    le_csSup (bddAbove_piece hab.le hC hNpos hk) (Set.mem_image_of_mem G hymem)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem tendsto_gridInf {a b : ℝ} (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C) {y : ℝ} (hy : y ∈ Set.Ioc a b)
    (hcont : ContinuousWithinAt G (Set.Icc a b) y) :
    Tendsto (fun N : ℕ => gridInf G a b N (gridIdx a b N y)) atTop (𝓝 (G y)) := by
  have h := (tendsto_gridSup hab (G := fun y => -G y)
    (fun y hy => (abs_neg (G y)).trans_le (hC y hy)) hy hcont.neg).neg
  rw [neg_neg] at h
  exact h.congr fun N => (gridInf_eq_neg G a b N _).symm

theorem tendsto_integral_gridSup {a b : ℝ} (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite) :
    Tendsto (fun N : ℕ => ∫ y in a..b, gridSup G a b N (gridIdx a b N y)) atTop
      (𝓝 (∫ y in a..b, G y)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun N =>
      (measurable_grid_step a b N (gridSup G a b N)).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    refine Eventually.of_forall fun y hy => ?_
    rw [Set.uIoc_of_le hab.le] at hy
    obtain ⟨hk, h1, h2⟩ := gridIdx_spec hab hN hy
    rw [Real.norm_eq_abs]
    exact abs_sSup_image_le (Set.mem_Ioc.2 ⟨h1, h2⟩)
      fun z hz => hC z (piece_subset hab.le hN hk hz)
  · filter_upwards [hGc.countable.ae_notMem volume] with y hyS hy
    rw [Set.uIoc_of_le hab.le] at hy
    have hcont : ContinuousWithinAt G (Set.Icc a b) y := by
      by_contra hc
      exact hyS ⟨Set.Ioc_subset_Icc_self hy, hc⟩
    exact tendsto_gridSup hab hC hy hcont

theorem tendsto_integral_gridInf {a b : ℝ} (hab : a < b) {G : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite) :
    Tendsto (fun N : ℕ => ∫ y in a..b, gridInf G a b N (gridIdx a b N y)) atTop
      (𝓝 (∫ y in a..b, G y)) := by
  have h := (tendsto_integral_gridSup hab (G := fun y => -G y)
    (fun y hy => (abs_neg (G y)).trans_le (hC y hy))
    (hGc.subset fun y hy => ⟨hy.1, fun hc => hy.2 hc.neg⟩)).neg
  rw [intervalIntegral.integral_neg, neg_neg] at h
  refine h.congr fun N => ?_
  simp only [gridInf_eq_neg, intervalIntegral.integral_neg]

end PrimeSum

open PrimeSum

/-- Prime Riemann sums from `θ(x) ~ x` (the partial-summation step in the proof of
Proposition 5.4): if `θ ~[atTop] id`, then for `0 < a < b` and a weight `G` that is bounded on
`[a, b]` and continuous there except at finitely many points,
`X⁻¹ ∑_{aX < p ≤ bX} G(p/X) log p → ∫_a^b G(y) dy` as `X → ∞`. -/
theorem tendsto_primeRiemannSum_of_theta (hθ : θ ~[atTop] id) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {G : ℝ → ℝ} (hG : ∃ C, ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite) :
    Tendsto (fun X : ℝ =>
        X⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊ with p.Prime, G (p / X) * Real.log p)
      atTop (𝓝 (∫ y in a..b, G y)) := by
  obtain ⟨C, hC⟩ := hG
  have hU := tendsto_integral_gridSup hab hC hGc
  have hL := tendsto_integral_gridInf hab hC hGc
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨N, hNl, hN⟩ := ((hL.eventually_const_lt hl).and (eventually_gt_atTop 0)).exists
    have hlim := tendsto_grid_sum hθ ha.le hab.le N (gridInf G a b N)
    rw [← integral_grid_step hab hN (gridInf G a b N)] at hlim
    filter_upwards [hlim.eventually_const_lt hNl, eventually_gt_atTop 0] with X hX1 hX2
    exact hX1.trans_le (lower_le_primeSum ha.le hab hC hN hX2)
  · obtain ⟨N, hNu, hN⟩ := ((hU.eventually_lt_const hu).and (eventually_gt_atTop 0)).exists
    have hlim := tendsto_grid_sum hθ ha.le hab.le N (gridSup G a b N)
    rw [← integral_grid_step hab hN (gridSup G a b N)] at hlim
    filter_upwards [hlim.eventually_lt_const hNu, eventually_gt_atTop 0] with X hX1 hX2
    exact (primeSum_le_upper ha.le hab hC hN hX2).trans_lt hX1

/-- The prime number theorem in the form `θ(x) ~ x`: `chebyshev_asymptotic` from the pinned
PrimeNumberTheoremAnd dependency, stated for Mathlib's `Chebyshev.theta`. -/
theorem theta_isEquivalent_id : θ ~[atTop] id :=
  chebyshev_asymptotic

/-- Prime Riemann sums (the prime number theorem with partial summation, as used in the proof of
Proposition 5.4): for `0 < a < b` and a weight `G` that is bounded on `[a, b]` and continuous
there except at finitely many points, `X⁻¹ ∑_{aX < p ≤ bX} G(p/X) log p → ∫_a^b G(y) dy` as
`X → ∞`. -/
theorem tendsto_primeRiemannSum {a b : ℝ} (ha : 0 < a) (hab : a < b) {G : ℝ → ℝ}
    (hG : ∃ C, ∀ y ∈ Set.Icc a b, |G y| ≤ C)
    (hGc : {y ∈ Set.Icc a b | ¬ContinuousWithinAt G (Set.Icc a b) y}.Finite) :
    Tendsto (fun X : ℝ =>
        X⁻¹ * ∑ p ∈ Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊ with p.Prime, G (p / X) * Real.log p)
      atTop (𝓝 (∫ y in a..b, G y)) :=
  tendsto_primeRiemannSum_of_theta theta_isEquivalent_id ha hab hG hGc

end ZetaSeven
