import ZetaSeven.MatrixDet
import ZetaSeven.HermiteHurwitz

/-!
# Positive integral representation (paper Section 2.5, Proposition 2.4, equations (16)-(19))

Prince Anand, "Zeta 7 is Irrational", Proposition 2.4. The weight
`w₇(y) = (2π)⁶/360 · y⁷ ∑_{ℓ ≥ 1} ℓ⁶ e^{-2πℓy}` (16) is positive on `(0, ∞)`, and for every
rational function `R` in the domain of `μ_X`, given by its partial-fraction data `(p, c)`
(`R(t) = p(t) + ∑_j c_j/(t + j²)` with `c_0 = 0`, as in `muFunctional`),
`μ_{ζ(7)}(R) = ∫₀^∞ R(y²) w₇(y) dy` (17), where the integrand is integrable.
Consequently `G_K(ζ(7))` is positive definite and `F_K(ζ(7)) > 0`, so
`Q_{K,M}(ζ(7)) = m_{K,M} F_K(ζ(7)) > 0` for every positive normalization factor.
Here `ζ(7)` is `(riemannZeta 7).re`.

Proof outline:
* even moments (18): term-by-term integration and Euler's formula `hasSum_zeta_nat`;
* simple poles (19): for each exponential term of `w₇`,
  `c⁶ ∫₀^∞ y⁷e^{-cy}/(y² + a²) dy = a⁶ ∫₀^∞ t⁷e^{-at}/(t² + c²) dt`, since both sides equal
  `(ac)⁶ ∫₀^∞ u⁷e^{-acu}/(u² + 1) du` after scaling; then Fubini with the Laplace transforms
  of the sine turns the series into Hermite's integral (`hurwitzZeta7_eq_hermite_integral`),
  and the recurrence `ζ(7, j) = ζ(7) - H⁷_j + j⁻⁷` gives (6) at `X = ζ(7)`. The scaling
  identity replaces the paper's six integrations by parts;
* positivity: the partial-fraction data of `MatrixDet` represent `D_N⁸ t^{i+j}/D_K`
  (`D_K = D_N · D_tail` and Lagrange interpolation at the nodes `-a²`), so the quadratic form
  of `G_K(ζ(7))` at `x ≠ 0` is `∫₀^∞ D_N(y²)⁸ q(y²)²/D_K(y²) w₇(y) dy > 0`.
-/

namespace ZetaSeven

open Real MeasureTheory Set Filter Polynomial

/-! ### The weight `w₇` -/

/-- Equation (16): `w₇(y) = (2π)⁶/360 · y⁷ ∑_{ℓ ≥ 1} ℓ⁶ e^{-2πℓy}`, with the sum written over
`ℓ + 1` for `ℓ : ℕ`. -/
noncomputable def w7 (y : ℝ) : ℝ :=
  (2 * π) ^ 6 / 360 * y ^ 7 *
    ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)

/-- The series in `w₇(y)` converges for `y > 0`. -/
theorem summable_w7_series {y : ℝ} (hy : 0 < y) :
    Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 6 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul 6 (by positivity : 0 < 2 * π * y))
  refine h.congr fun ℓ => ?_
  push_cast
  ring_nf

/-- Proposition 2.4: `w₇(y) > 0` for `y > 0`. -/
theorem w7_pos {y : ℝ} (hy : 0 < y) : 0 < w7 y := by
  have hs : 0 < ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) :=
    (summable_w7_series hy).tsum_pos (fun ℓ => by positivity) 0 (by positivity)
  rw [w7]
  exact mul_pos (mul_pos (by positivity) (pow_pos hy 7)) hs

/-! ### Term-by-term integration against `w₇` -/

/-- Term-by-term integration of `g · w₇` for a weight `g` positive on `(0, ∞)`: if every
exponential term is integrable and the term integrals are summable, then `g · w₇` is integrable
on `(0, ∞)` and its integral is the sum of the term integrals. -/
theorem integral_mul_w7_eq_tsum (g : ℝ → ℝ) (hg : ∀ y, 0 < y → 0 < g y)
    (hint : ∀ ℓ : ℕ, IntegrableOn
      (fun y => g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))) (Ioi 0))
    (hsum : Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 6 *
      ∫ y in Ioi (0 : ℝ), g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))) :
    IntegrableOn (fun y => g y * w7 y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), g y * w7 y = (2 * π) ^ 6 / 360 * ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 *
        ∫ y in Ioi (0 : ℝ), g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) := by
  have hE0 : ∀ ℓ : ℕ, ∀ y ∈ Ioi (0 : ℝ),
      0 ≤ g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) := by
    intro ℓ y hy
    have hy' : (0 : ℝ) < y := hy
    exact mul_nonneg (hg y hy').le (mul_nonneg (pow_nonneg hy'.le 7) (Real.exp_pos _).le)
  have hFint : ∀ ℓ : ℕ, Integrable (fun y => (2 * π) ^ 6 / 360 * (((ℓ : ℝ) + 1) ^ 6 *
      (g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))))) (volume.restrict (Ioi 0)) :=
    fun ℓ => Integrable.const_mul (Integrable.const_mul (hint ℓ) _) _
  have hFnorm : ∀ ℓ : ℕ, ∫ y in Ioi (0 : ℝ), ‖(2 * π) ^ 6 / 360 * (((ℓ : ℝ) + 1) ^ 6 *
      (g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))))‖ =
      (2 * π) ^ 6 / 360 * (((ℓ : ℝ) + 1) ^ 6 *
        ∫ y in Ioi (0 : ℝ), g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))) := by
    intro ℓ
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    exact Real.norm_of_nonneg
      (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hE0 ℓ y hy)))
  have hsum' : Summable fun ℓ : ℕ => ∫ y in Ioi (0 : ℝ), ‖(2 * π) ^ 6 / 360 *
      (((ℓ : ℝ) + 1) ^ 6 * (g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))))‖ := by
    exact (hsum.mul_left ((2 * π) ^ 6 / 360)).congr fun ℓ => (hFnorm ℓ).symm
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ∑' ℓ : ℕ, (2 * π) ^ 6 / 360 * (((ℓ : ℝ) + 1) ^ 6 *
      (g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)))) = g y * w7 y := by
    intro y _
    rw [w7, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun ℓ => by ring
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsum'
  have hval : ∫ y in Ioi (0 : ℝ), g y * w7 y = (2 * π) ^ 6 / 360 * ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 *
      ∫ y in Ioi (0 : ℝ), g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hpt, ← hHas.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun ℓ => ?_
    rw [integral_const_mul, integral_const_mul]
  have hpos0 : 0 < ∫ y in Ioi (0 : ℝ),
      g y * (y ^ 7 * Real.exp (-(2 * π * (((0 : ℕ) : ℝ) + 1)) * y)) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi (hE0 0)) (hint 0)]
    have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun y => g y *
        (y ^ 7 * Real.exp (-(2 * π * (((0 : ℕ) : ℝ) + 1)) * y))) ∩ Ioi 0 := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      refine ⟨?_, hy⟩
      exact (mul_pos (hg y hy') (mul_pos (pow_pos hy' 7) (Real.exp_pos _))).ne'
    calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  have htsum : 0 < ∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 *
      ∫ y in Ioi (0 : ℝ), g y * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) :=
    hsum.tsum_pos (fun ℓ => mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioi (hE0 ℓ))) 0 (mul_pos (by positivity) hpos0)
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  exact (mul_pos (by positivity) htsum).ne'

/-! ### Even moments (18) -/

/-- The exponential-term integral of an even moment:
`∫₀^∞ y^{2e} · y⁷ e^{-cy} dy = (2e + 7)!/c^{2e+8}` with `c = 2π(ℓ + 1)`. -/
private lemma moment_term_integral (e ℓ : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) =
      (Nat.factorial (2 * e + 7) : ℝ) / (2 * π * ((ℓ : ℝ) + 1)) ^ (2 * e + 7 + 1) := by
  have hc : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity
  calc ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))
      = ∫ y in Ioi (0 : ℝ), y ^ (2 * e + 7) * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        beta_reduce
        ring
    _ = _ := integral_pow_mul_exp_neg_mul (2 * e + 7) hc

private lemma moment_term_eq (e ℓ : ℕ) :
    ((ℓ : ℝ) + 1) ^ 6 * ((Nat.factorial (2 * e + 7) : ℝ) /
      (2 * π * ((ℓ : ℝ) + 1)) ^ (2 * e + 7 + 1)) =
      (Nat.factorial (2 * e + 7) : ℝ) / (2 * π) ^ (2 * e + 8) *
        (1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2)) := by
  have hu : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  set u : ℝ := (ℓ : ℝ) + 1
  rw [mul_pow, show 2 * e + 7 + 1 = (2 * e + 2) + 6 by ring, pow_add u (2 * e + 2) 6,
    show 2 * e + 2 + 6 = 2 * e + 8 by ring]
  field

/-- `(2e + 7)! = (2e + 2)! (2e + 3)(2e + 4)(2e + 5)(2e + 6)(2e + 7)`. -/
private lemma factorial_two_mul_add_seven (e : ℕ) :
    (Nat.factorial (2 * e + 7) : ℝ) = (Nat.factorial (2 * e + 2) : ℝ) *
      ((2 * (e : ℝ) + 3) * (2 * (e : ℝ) + 4) * (2 * (e : ℝ) + 5) * (2 * (e : ℝ) + 6) *
        (2 * (e : ℝ) + 7)) := by
  have h : Nat.factorial (2 * e + 7) = Nat.factorial (2 * e + 2) *
      ((2 * e + 3) * (2 * e + 4) * (2 * e + 5) * (2 * e + 6) * (2 * e + 7)) := by
    rw [show 2 * e + 7 = (2 * e + 2) + 1 + 1 + 1 + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    ring
  exact_mod_cast h

/-- Euler's formula, shifted to `ℓ + 1`:
`∑_{ℓ ≥ 0} (ℓ + 1)^{-(2e+2)} = (-1)^e 2^{2e+1} π^{2e+2} B_{2e+2}/(2e + 2)!`. -/
private lemma hasSum_one_div_succ_pow (e : ℕ) :
    HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2))
      ((-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * e + 1) * π ^ (2 * e + 2) *
        (_root_.bernoulli (2 * e + 2) : ℝ) / (Nat.factorial (2 * e + 2) : ℝ)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat (k := e + 1) (Nat.succ_ne_zero e))
  have h0 : (∑ i ∈ Finset.range 1, 1 / ((i : ℕ) : ℝ) ^ (2 * (e + 1))) = 0 := by
    simp
  rw [h0, sub_zero, show 2 * (e + 1) = 2 * e + 2 by ring,
    show 2 * e + 2 - 1 = 2 * e + 1 by omega] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Even moments (18): `∫₀^∞ y^{2e} w₇(y) dy = μ_X(t^e)` (the value (5)), with the integrand
integrable on `(0, ∞)`. -/
theorem integral_moment_w7 (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * w7 y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * w7 y = (muMonomial e : ℝ) := by
  have hint : ∀ ℓ : ℕ, IntegrableOn
      (fun y => y ^ (2 * e) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))) (Ioi 0) := by
    intro ℓ
    refine (integrableOn_pow_mul_exp_neg_mul (2 * e + 7)
      (by positivity : 0 < 2 * π * ((ℓ : ℝ) + 1))).congr_fun (fun y _ => ?_) measurableSet_Ioi
    beta_reduce
    ring
  have hterm : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 6 *
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) =
      (Nat.factorial (2 * e + 7) : ℝ) / (2 * π) ^ (2 * e + 8) *
        (1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2)) := fun ℓ => by
    rw [moment_term_integral, moment_term_eq]
  have hZ := hasSum_one_div_succ_pow e
  have hsum : Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 6 *
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) :=
    (hZ.summable.mul_left ((Nat.factorial (2 * e + 7) : ℝ) / (2 * π) ^ (2 * e + 8))).congr
      fun ℓ => (hterm ℓ).symm
  obtain ⟨hI, hV⟩ := integral_mul_w7_eq_tsum (fun y => y ^ (2 * e))
    (fun y hy => by positivity) hint hsum
  refine ⟨hI, ?_⟩
  rw [hV, tsum_congr hterm, tsum_mul_left, hZ.tsum_eq, factorial_two_mul_add_seven]
  have hfac : (0 : ℝ) < (Nat.factorial (2 * e + 2) : ℝ) := by positivity
  simp only [muMonomial]
  push_cast
  field

/-! ### Simple poles (19) -/

/-- Scaling `y = a u`: `∫₀^∞ y⁷e^{-cy}/(y² + a²) dy = a⁶ ∫₀^∞ u⁷e^{-acu}/(u² + 1) du`. -/
private lemma pole_term_scale {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y)) =
      a ^ 6 * ∫ u in Ioi (0 : ℝ), 1 / (u ^ 2 + 1) * (u ^ 7 * Real.exp (-(a * c) * u)) := by
  have h : ∫ x in Ioi (0 : ℝ),
      1 / ((a * x) ^ 2 + a ^ 2) * ((a * x) ^ 7 * Real.exp (-c * (a * x))) =
      a⁻¹ * ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y)) := by
    have h0 := integral_comp_mul_left_Ioi
      (fun y : ℝ => 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y))) 0 ha
    rw [mul_zero, smul_eq_mul] at h0
    exact h0
  have h2 : ∫ x in Ioi (0 : ℝ),
      1 / ((a * x) ^ 2 + a ^ 2) * ((a * x) ^ 7 * Real.exp (-c * (a * x))) =
      a ^ 5 * ∫ u in Ioi (0 : ℝ), 1 / (u ^ 2 + 1) * (u ^ 7 * Real.exp (-(a * c) * u)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    beta_reduce
    rw [show -c * (a * u) = -(a * c) * u by ring]
    field
  rw [h2] at h
  calc ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y))
      = a * (a⁻¹ * ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y))) := by
        field
    _ = a * (a ^ 5 *
        ∫ u in Ioi (0 : ℝ), 1 / (u ^ 2 + 1) * (u ^ 7 * Real.exp (-(a * c) * u))) := by
        rw [← h]
    _ = _ := by ring

/-- The scaling symmetry behind the pole identity:
`c⁶ ∫₀^∞ y⁷e^{-cy}/(y² + a²) dy = a⁶ ∫₀^∞ t⁷e^{-at}/(t² + c²) dt` for `a, c > 0`. -/
private lemma pole_term_symm {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    c ^ 6 * ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-c * y)) =
      a ^ 6 * ∫ t in Ioi (0 : ℝ), 1 / (t ^ 2 + c ^ 2) * (t ^ 7 * Real.exp (-a * t)) := by
  rw [pole_term_scale ha c, pole_term_scale hc a, mul_comm c a]
  ring

private lemma pole_kernel_bound (a c y t : ℝ) :
    ‖Real.exp (-c * y) * (t ^ 6 * Real.exp (-a * t) * Real.sin (y * t))‖ ≤
      Real.exp (-c * y) * (t ^ 6 * Real.exp (-a * t)) := by
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 6 * Real.exp (-a * t)), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)) (Real.exp_pos _).le

/-- Fubini with the Laplace transforms of the sine:
`∫₀^∞ t⁷e^{-at}/(t² + c²) dt = 720 ∫₀^∞ e^{-cy} y(7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/(y² + a²)⁷ dy`. -/
private lemma pole_term_fubini {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), 1 / (t ^ 2 + c ^ 2) * (t ^ 7 * Real.exp (-a * t)) =
      720 * ∫ y in Ioi (0 : ℝ), Real.exp (-c * y) *
        (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
          (y ^ 2 + a ^ 2) ^ 7) := by
  have hint : Integrable (Function.uncurry fun y t : ℝ =>
        Real.exp (-c * y) * (t ^ 6 * Real.exp (-a * t) * Real.sin (y * t)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun p : ℝ × ℝ => Real.exp (-c * p.1) * (p.2 ^ 6 * Real.exp (-a * p.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (f := fun y : ℝ => Real.exp (-c * y))
        (g := fun t : ℝ => t ^ 6 * Real.exp (-a * t))
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0)
        (integrableOn_pow_mul_exp_neg_mul 6 ha)
    refine hg.mono' ?_ (ae_of_all _ fun p => pole_kernel_bound a c p.1 p.2)
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-c * p.1) *
      (p.2 ^ 6 * Real.exp (-a * p.2) * Real.sin (p.1 * p.2))).aestronglyMeasurable
  have hL : ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      Real.exp (-c * y) * (t ^ 6 * Real.exp (-a * t) * Real.sin (y * t)) =
      720 * ∫ y in Ioi (0 : ℝ), Real.exp (-c * y) *
        (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
          (y ^ 2 + a ^ 2) ^ 7) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    rw [integral_const_mul, integral_pow_six_mul_exp_mul_sin ha y]
    ring
  have hR : ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      Real.exp (-c * y) * (t ^ 6 * Real.exp (-a * t) * Real.sin (y * t)) =
      ∫ t in Ioi (0 : ℝ), 1 / (t ^ 2 + c ^ 2) * (t ^ 7 * Real.exp (-a * t)) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    have hfun : (fun y : ℝ => Real.exp (-c * y) *
        (t ^ 6 * Real.exp (-a * t) * Real.sin (y * t))) =
        fun y : ℝ => t ^ 6 * Real.exp (-a * t) * (Real.sin (y * t) * Real.exp (-c * y)) := by
      funext y
      ring
    rw [hfun, integral_const_mul, integral_sin_mul_exp_neg_mul t hc]
    field
  rw [← hR, ← integral_integral_swap hint, hL]

/-- Geometric series: `∑_{ℓ ≥ 1} e^{-2πℓy} = 1/(e^{2πy} - 1)` for `y > 0`. -/
private lemma tsum_exp_neg_two_pi_mul {y : ℝ} (hy : 0 < y) :
    ∑' ℓ : ℕ, Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) = 1 / (Real.exp (2 * π * y) - 1) := by
  have hq0 : 0 ≤ Real.exp (-(2 * π * y)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * π * y)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hterm : ∀ ℓ : ℕ, Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) =
      Real.exp (-(2 * π * y)) * Real.exp (-(2 * π * y)) ^ ℓ := by
    intro ℓ
    rw [show -(2 * π * ((ℓ : ℝ) + 1)) * y = -(2 * π * y) + ℓ * (-(2 * π * y)) by ring,
      Real.exp_add, Real.exp_nat_mul]
  have hE0 : Real.exp (2 * π * y) ≠ 0 := (Real.exp_pos _).ne'
  have hE1 : Real.exp (2 * π * y) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have hsub : 1 - (Real.exp (2 * π * y))⁻¹ =
      (Real.exp (2 * π * y) - 1) / Real.exp (2 * π * y) := by
    field
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, Real.exp_neg, hsub,
    inv_div]
  field

/-- `|y(7a⁶ - 35a⁴y² + 21a²y⁴ - y⁶)/(y² + a²)⁷| ≤ 35y/a⁸` for `y ≥ 0`. -/
private lemma hermite_integrand_bound {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    |y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) / (y ^ 2 + a ^ 2) ^ 7| ≤
      35 / a ^ 8 * y := by
  have hD : 0 < y ^ 2 + a ^ 2 := by positivity
  have hP : |7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6| ≤
      35 * (y ^ 2 + a ^ 2) ^ 3 := by
    rw [abs_le]
    constructor
    · have h0 : 0 ≤ 34 * y ^ 6 + 126 * a ^ 2 * y ^ 4 + 70 * a ^ 4 * y ^ 2 + 42 * a ^ 6 := by
        positivity
      linarith
    · have h0 : 0 ≤ 36 * y ^ 6 + 84 * a ^ 2 * y ^ 4 + 140 * a ^ 4 * y ^ 2 + 28 * a ^ 6 := by
        positivity
      linarith
  have ha8 : a ^ 8 ≤ (y ^ 2 + a ^ 2) ^ 4 := by
    calc a ^ 8 = (a ^ 2) ^ 4 := by ring
      _ ≤ (y ^ 2 + a ^ 2) ^ 4 := by
        gcongr
        exact le_add_of_nonneg_left (sq_nonneg y)
  calc |y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) / (y ^ 2 + a ^ 2) ^ 7|
      = y * |7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6| /
          (y ^ 2 + a ^ 2) ^ 7 := by
        rw [abs_div, abs_mul, abs_of_nonneg hy, abs_of_pos (pow_pos hD 7)]
    _ ≤ y * (35 * (y ^ 2 + a ^ 2) ^ 3) / (y ^ 2 + a ^ 2) ^ 7 := by gcongr
    _ = 35 * y / (y ^ 2 + a ^ 2) ^ 4 := by field
    _ ≤ 35 * y / a ^ 8 := by gcongr
    _ = 35 / a ^ 8 * y := by ring

/-- Pointwise bound for the exponential terms of the Hermite integrand. -/
private lemma pole_series_term_bound {a c y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    ‖Real.exp (-c * y) * (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7)‖ ≤ 35 / a ^ 8 * (y ^ 1 * Real.exp (-c * y)) := by
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, pow_one]
  calc Real.exp (-c * y) *
        |y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) / (y ^ 2 + a ^ 2) ^ 7|
      ≤ Real.exp (-c * y) * (35 / a ^ 8 * y) :=
        mul_le_mul_of_nonneg_left (hermite_integrand_bound ha hy.le) (Real.exp_pos _).le
    _ = 35 / a ^ 8 * (y * Real.exp (-c * y)) := by ring

private lemma pole_series_integrable {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    Integrable (fun y => Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
      (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (Integrable.const_mul (integrableOn_pow_mul_exp_neg_mul 1
    (by positivity : 0 < 2 * π * ((ℓ : ℝ) + 1))) (35 / a ^ 8)) ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ => Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
      (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7)).aestronglyMeasurable
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => pole_series_term_bound ha hy

private lemma pole_series_summable_norm {a : ℝ} (ha : 0 < a) :
    Summable fun ℓ : ℕ => ∫ y in Ioi (0 : ℝ), ‖Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
      (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7)‖ := by
  have hc : ∀ ℓ : ℕ, 0 < 2 * π * ((ℓ : ℝ) + 1) := fun ℓ => by positivity
  have hB : Summable fun ℓ : ℕ =>
      35 / a ^ 8 * ((Nat.factorial 1 : ℝ) / (2 * π * ((ℓ : ℝ) + 1)) ^ (1 + 1)) := by
    have h := ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left (35 / a ^ 8 / (2 * π) ^ 2)
    refine h.congr fun ℓ => ?_
    simp only [Nat.factorial_one, Nat.cast_one, Nat.cast_add]
    field
  refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun y => norm_nonneg _)
    (fun ℓ => ?_) hB
  rw [← integral_pow_mul_exp_neg_mul 1 (hc ℓ), ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
    (Integrable.const_mul (integrableOn_pow_mul_exp_neg_mul 1 (hc ℓ)) _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  exact pole_series_term_bound ha hy

/-- Summing the exponential terms: the series of Laplace-type integrals is Hermite's integral. -/
private lemma tsum_pole_series {a : ℝ} (ha : 0 < a) :
    ∑' ℓ : ℕ, ∫ y in Ioi (0 : ℝ), Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
        (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
          (y ^ 2 + a ^ 2) ^ 7) =
      ∫ y in Ioi (0 : ℝ), y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7 / (Real.exp (2 * π * y) - 1) := by
  rw [integral_tsum_of_summable_integral_norm (pole_series_integrable ha)
    (pole_series_summable_norm ha)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [tsum_mul_right, tsum_exp_neg_two_pi_mul hy]
  ring

/-- Each exponential term of the pole integral, rewritten through scaling and Fubini. -/
private lemma pole_term_eq {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    ((ℓ : ℝ) + 1) ^ 6 * ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) *
        (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) =
      720 * a ^ 6 / (2 * π) ^ 6 * ∫ y in Ioi (0 : ℝ),
        Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
          (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
            (y ^ 2 + a ^ 2) ^ 7) := by
  have hc : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity
  have h := pole_term_symm ha hc
  rw [pole_term_fubini ha hc] at h
  have h2π : (2 * π) ^ 6 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff h2π]
  linear_combination h

private lemma pole_term_integrable {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    IntegrableOn (fun y => 1 / (y ^ 2 + a ^ 2) *
      (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))) (Ioi 0) := by
  have hc : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity
  refine Integrable.mono'
    (Integrable.const_mul (integrableOn_pow_mul_exp_neg_mul 7 hc) (1 / a ^ 2)) ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ => 1 / (y ^ 2 + a ^ 2) *
      (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy' : (0 : ℝ) < y := hy
    have hA : 0 ≤ y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) := by positivity
    have hB : 0 ≤ 1 / (y ^ 2 + a ^ 2) := by positivity
    have hle : 1 / (y ^ 2 + a ^ 2) ≤ 1 / a ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_left (sq_nonneg y))
    calc ‖1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y))‖
        = 1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) :=
          Real.norm_of_nonneg (mul_nonneg hB hA)
      _ ≤ 1 / a ^ 2 * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) :=
          mul_le_mul_of_nonneg_right hle hA

private lemma pole_series_summable {a : ℝ} (ha : 0 < a) :
    Summable fun ℓ : ℕ => ∫ y in Ioi (0 : ℝ), Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y) *
      (y * (7 * a ^ 6 - 35 * a ^ 4 * y ^ 2 + 21 * a ^ 2 * y ^ 4 - y ^ 6) /
        (y ^ 2 + a ^ 2) ^ 7) :=
  (pole_series_summable_norm ha).of_norm_bounded fun ℓ => norm_integral_le_integral_norm _

private lemma pole_terms_summable {a : ℝ} (ha : 0 < a) :
    Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 6 * ∫ y in Ioi (0 : ℝ),
      1 / (y ^ 2 + a ^ 2) * (y ^ 7 * Real.exp (-(2 * π * ((ℓ : ℝ) + 1)) * y)) :=
  ((pole_series_summable ha).mul_left (720 * a ^ 6 / (2 * π) ^ 6)).congr
    fun ℓ => (pole_term_eq ha ℓ).symm

/-- Equation (19): `∫₀^∞ w₇(y)/(y² + a²) dy = a⁶ ζ(7, a) - 1/(2a) - 1/6` for `a > 0`, with the
integrand integrable on `(0, ∞)`. -/
theorem integral_pole_w7 {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y => 1 / (y ^ 2 + a ^ 2) * w7 y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), 1 / (y ^ 2 + a ^ 2) * w7 y =
        a ^ 6 * hurwitzZeta7 a - 1 / (2 * a) - 1 / 6 := by
  obtain ⟨hI, hV⟩ := integral_mul_w7_eq_tsum (fun y => 1 / (y ^ 2 + a ^ 2))
    (fun y _ => by positivity) (pole_term_integrable ha) (pole_terms_summable ha)
  refine ⟨hI, ?_⟩
  rw [hV, tsum_congr (pole_term_eq ha), tsum_mul_left, tsum_pole_series ha,
    hurwitzZeta7_eq_hermite_integral ha]
  field

end ZetaSeven
