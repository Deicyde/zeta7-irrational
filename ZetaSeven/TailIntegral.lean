import ZetaSeven.InnerLimiting

/-!
# Tail integral bound (paper Section 5.4, equations (74)-(86))

Prince Anand, "Zeta 7 is Irrational", Section 5.4. With `f = {x}`, `g = {αx}`, `τ = {2Hx}`,
`σ = {2x}`, `η = {2λx}` (74), `d(u) = min(u, 1 - u)` (`tailD`) and `ε(u) = ±1` (`tailEps`):

* (75) `A(z) = ℓ(x, z) - 2x` (`tailA`), `B(z) = ℓ(αx, z) - 2αx` (`tailB`);
* (76) `A(z) = ε(f)(1_{z < d(f)} - 2d(f))` away from `z = d(f)` (`tailA_eq`, `tailB_eq`);
* (77)-(79) the integrals of `A`, `B`, `A²`, `B²`, `AB` over `[0, 1/2]`;
* (80)-(82) `R(x) = xF(x) + Q(x)` (`innerR_eq_tail`) with `F = 6λ + 2λf - 16λg` (`tailF`) and
  `Q = [τ(τ - σ) - (τ - σ)₊ + η(1 - η)]/2 + 16∫_0^{1/2} B² - 4∫_0^{1/2} AB` (`tailQ`); the
  coefficient `16` corrects the printed `25` (source-map erratum 11);
* (83) `-1/2 ≤ Q ≤ 27/8` (`tailQ_bounds`);
* (84) the periodic primitives `P` (`tailP`) and `C` (`tailC`) built from
  `G(v) = v(1 - v)(2v - 1)` (`tailG`), with `P' = F + λ`, `C' = P - 11729/720` off the
  breakpoints (`hasDerivAt_tailP`, `hasDerivAt_tailC`) and `|C| < 22` (`abs_tailC_lt`);
* (85) the double integration by parts (`integral_innerR_div_cube_eq`);
* (86) for `M ∈ 40ℤ_{>0}`, `∫_M^∞ R(x)/x³ dx ≥ -λ/M + 11549/(720M²) - 44/M³`
  (`tail_integral_bound`).

## Proof

`A` and `B` are step functions of `z` on `[0, 1/2]` (`tailA_eq`), so every integral in (77)-(79)
and the `z`-integral of `Γ` reduce to integrals of indicator functions `1_{z < d}`
(`integral_step_comb`). Writing every floor `⌊y⌋` as `y - {y}` then turns `R = -Γ - N` into
`xF + Q` by ring arithmetic with `α = 3/40`, `λ = 37/40`, `H = 49/40`. The lower bound
`Q ≥ -1/8` uses `|∫AB| ≤ ∫B²` rather than the termwise bounds of the paper (erratum 11).
For (85), `Φ(x) = λ/x + (P(x) - P̄)/x² + 2C(x)/x³` has derivative `F/x² - 6C/x⁴` off the
countable set where `{x} = 0` or `{αx} = 0`, so the fundamental theorem of calculus with a
countable exceptional set on `[T, X]` and `X → ∞` gives `∫_T^∞ (F/x² - 6C/x⁴) = -Φ(T)`.
-/

namespace ZetaSeven

open MeasureTheory Set Filter Topology

/-! ## Definitions (74)-(75), (81)-(82) -/

section Defs

/-- `d(u) = min(u, 1 - u)`, used for `0 ≤ u < 1`. -/
noncomputable def tailD (u : ℝ) : ℝ := min u (1 - u)

/-- `ε(u) = +1` for `u < 1/2` and `-1` otherwise. The paper leaves `ε(1/2)` undefined; at
`u = 1/2` one has `d(u) = 1/2`, and both signs give the same values in (76) and (79). -/
noncomputable def tailEps (u : ℝ) : ℝ := if u < 1 / 2 then 1 else -1

/-- (75): `A(z) = ℓ(x, z) - 2x`. -/
noncomputable def tailA (x z : ℝ) : ℝ := (ellLim x z : ℝ) - 2 * x

/-- (75): `B(z) = ℓ(αx, z) - 2αx`. -/
noncomputable def tailB (x z : ℝ) : ℝ :=
  (ellLim ((alpha : ℝ) * x) z : ℝ) - 2 * ((alpha : ℝ) * x)

/-- (81): the periodic coefficient `F(x) = 6λ + 2λ{x} - 16λ{αx}`. -/
noncomputable def tailF (x : ℝ) : ℝ :=
  6 * (lam : ℝ) + 2 * (lam : ℝ) * Int.fract x - 16 * (lam : ℝ) * Int.fract ((alpha : ℝ) * x)

/-- (82): the bounded remainder
`Q(x) = [τ(τ - σ) - (τ - σ)₊ + η(1 - η)]/2 + 16 ∫_0^{1/2} B(z)² dz - 4 ∫_0^{1/2} A(z)B(z) dz`
with `τ = {2Hx}`, `σ = {2x}`, `η = {2λx}` (74). The coefficient of `∫ B²` is `16`; the paper
prints `25` (source-map erratum 11). -/
noncomputable def tailQ (x : ℝ) : ℝ :=
  (Int.fract (2 * (bigH : ℝ) * x) * (Int.fract (2 * (bigH : ℝ) * x) - Int.fract (2 * x))
      - max (Int.fract (2 * (bigH : ℝ) * x) - Int.fract (2 * x)) 0
      + Int.fract (2 * (lam : ℝ) * x) * (1 - Int.fract (2 * (lam : ℝ) * x))) / 2
    + 16 * (∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2)
    - 4 * ∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z

theorem tailB_eq_tailA (x z : ℝ) : tailB x z = tailA ((alpha : ℝ) * x) z := rfl

theorem tailD_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 ≤ tailD u ∧ tailD u ≤ 1 / 2 := by
  unfold tailD
  have := min_le_left u (1 - u)
  have := min_le_right u (1 - u)
  exact ⟨le_min h0 (by linarith), by linarith⟩

theorem tailD_fract_mem (y : ℝ) : 0 ≤ tailD (Int.fract y) ∧ tailD (Int.fract y) ≤ 1 / 2 :=
  tailD_mem (Int.fract_nonneg y) (Int.fract_lt_one y)

theorem tailEps_sq (u : ℝ) : tailEps u ^ 2 = 1 := by
  unfold tailEps
  split_ifs <;> norm_num

theorem tailEps_mul_cases (u v : ℝ) : tailEps u * tailEps v = 1 ∨ tailEps u * tailEps v = -1 := by
  unfold tailEps
  split_ifs <;> norm_num

end Defs

/-! ## Step functions on `[0, 1/2]` -/

section Step

theorem antitone_ite_lt (d : ℝ) : Antitone fun z : ℝ => if z < d then (1 : ℝ) else 0 := by
  intro a b hab
  show (if b < d then (1 : ℝ) else 0) ≤ if a < d then 1 else 0
  split_ifs <;> linarith

theorem ite_lt_sq (z d : ℝ) : (if z < d then (1 : ℝ) else 0) ^ 2 = if z < d then 1 else 0 := by
  split_ifs <;> norm_num

theorem ite_lt_mul_ite_lt (z a b : ℝ) :
    (if z < a then (1 : ℝ) else 0) * (if z < b then 1 else 0) = if z < min a b then 1 else 0 := by
  by_cases ha : z < a <;> by_cases hb : z < b <;> simp [ha, hb, lt_min_iff]

/-- `∫_0^{1/2} 1_{z < d} dz = d` for `0 ≤ d ≤ 1/2`. -/
theorem integral_ite_lt {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) :
    ∫ z in (0 : ℝ)..(1 / 2), (if z < d then (1 : ℝ) else 0) = d := by
  have h1 : IntervalIntegrable (fun z : ℝ => if z < d then (1 : ℝ) else 0) volume 0 d :=
    (antitone_ite_lt d).intervalIntegrable
  have h2 : IntervalIntegrable (fun z : ℝ => if z < d then (1 : ℝ) else 0) volume d (1 / 2) :=
    (antitone_ite_lt d).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ z in (0 : ℝ)..d, (if z < d then (1 : ℝ) else 0) = ∫ _ in (0 : ℝ)..d, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume d] with z hz hmem
    rw [Set.uIoc_of_le hd0] at hmem
    show (if z < d then (1 : ℝ) else 0) = 1
    rw [if_pos (lt_of_le_of_ne hmem.2 hz)]
  have e2 : ∫ z in d..(1 / 2), (if z < d then (1 : ℝ) else 0) = ∫ _ in d..(1 / 2), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hd1] at hz
    show (if z < d then (1 : ℝ) else 0) = 0
    rw [if_neg (not_lt.mpr hz.1)]
  rw [e1, e2, intervalIntegral.integral_const, intervalIntegral.integral_zero, smul_eq_mul]
  ring

/-- The integral over `[0, 1/2]` of a combination of three indicators `1_{z < d_i}`. -/
theorem integral_step_comb {c0 c1 c2 c3 d1 d2 d3 : ℝ} (h1 : 0 ≤ d1) (h1' : d1 ≤ 1 / 2)
    (h2 : 0 ≤ d2) (h2' : d2 ≤ 1 / 2) (h3 : 0 ≤ d3) (h3' : d3 ≤ 1 / 2) :
    ∫ z in (0 : ℝ)..(1 / 2), (c0 + c1 * (if z < d1 then 1 else 0) + c2 * (if z < d2 then 1 else 0)
      + c3 * (if z < d3 then 1 else 0)) = c0 / 2 + c1 * d1 + c2 * d2 + c3 * d3 := by
  have i : ∀ d c : ℝ,
      IntervalIntegrable (fun z : ℝ => c * (if z < d then (1 : ℝ) else 0)) volume 0 (1 / 2) :=
    fun d c => ((antitone_ite_lt d).intervalIntegrable).const_mul c
  have i0 : IntervalIntegrable (fun _ : ℝ => c0) volume 0 (1 / 2) := intervalIntegrable_const
  rw [intervalIntegral.integral_add ((i0.add (i d1 c1)).add (i d2 c2)) (i d3 c3),
    intervalIntegral.integral_add (i0.add (i d1 c1)) (i d2 c2),
    intervalIntegral.integral_add i0 (i d1 c1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_ite_lt h1 h1', integral_ite_lt h2 h2', integral_ite_lt h3 h3', smul_eq_mul]
  ring

/-- A function of step form `e(1_{z < d} - 2d)` on `[0, 1/2]` away from `z = d` has mean zero. -/
theorem integral_step_form {φ : ℝ → ℝ} {d e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hφ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d → φ z = e * ((if z < d then 1 else 0) - 2 * d)) :
    ∫ z in (0 : ℝ)..(1 / 2), φ z = 0 := by
  have h : ∫ z in (0 : ℝ)..(1 / 2), φ z = ∫ z in (0 : ℝ)..(1 / 2),
      (-2 * e * d + e * (if z < d then 1 else 0) + 0 * (if z < d then 1 else 0)
        + 0 * (if z < d then 1 else 0)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume d] with z hz hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [hφ z hmem.1.le hmem.2 hz]
    ring
  rw [h, integral_step_comb hd0 hd1 hd0 hd1 hd0 hd1]
  ring

/-- The square of a step form `e(1_{z < d} - 2d)` with `e² = 1` integrates to `d(1 - 2d)`. -/
theorem integral_step_form_sq {φ : ℝ → ℝ} {d e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (he : e ^ 2 = 1)
    (hφ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d → φ z = e * ((if z < d then 1 else 0) - 2 * d)) :
    ∫ z in (0 : ℝ)..(1 / 2), φ z ^ 2 = d * (1 - 2 * d) := by
  have h : ∫ z in (0 : ℝ)..(1 / 2), φ z ^ 2 = ∫ z in (0 : ℝ)..(1 / 2),
      (4 * d ^ 2 + (1 - 4 * d) * (if z < d then 1 else 0) + 0 * (if z < d then 1 else 0)
        + 0 * (if z < d then 1 else 0)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume d] with z hz hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [hφ z hmem.1.le hmem.2 hz]
    have hI := ite_lt_sq z d
    linear_combination ((if z < d then (1 : ℝ) else 0) ^ 2 - 4 * d * (if z < d then (1 : ℝ) else 0)
      + 4 * d ^ 2) * he + hI
  rw [h, integral_step_comb hd0 hd1 hd0 hd1 hd0 hd1]
  ring

/-- The product of two step forms integrates to `e e' (min(d, d') - 2dd')`. -/
theorem integral_step_form_mul {φ ψ : ℝ → ℝ} {d e d' e' : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hd0' : 0 ≤ d') (hd1' : d' ≤ 1 / 2)
    (hφ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d → φ z = e * ((if z < d then 1 else 0) - 2 * d))
    (hψ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d' → ψ z = e' * ((if z < d' then 1 else 0) - 2 * d')) :
    ∫ z in (0 : ℝ)..(1 / 2), φ z * ψ z = e * e' * (min d d' - 2 * d * d') := by
  have h : ∫ z in (0 : ℝ)..(1 / 2), φ z * ψ z = ∫ z in (0 : ℝ)..(1 / 2),
      (4 * e * e' * d * d' + (-2 * e * e' * d') * (if z < d then 1 else 0)
        + (-2 * e * e' * d) * (if z < d' then 1 else 0)
        + e * e' * (if z < min d d' then 1 else 0)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume d, Measure.ae_ne volume d'] with z hz hz' hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [hφ z hmem.1.le hmem.2 hz, hψ z hmem.1.le hmem.2 hz', ← ite_lt_mul_ite_lt]
    ring
  rw [h, integral_step_comb hd0 hd1 hd0' hd1' (le_min hd0 hd0') ((min_le_left d d').trans hd1)]
  ring

/-- The `z`-integrand of `Γ`, written in `A` and `B`, integrates in closed form. -/
theorem integral_quad_step {φ ψ : ℝ → ℝ} {d e d' e' a c : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hd0' : 0 ≤ d') (hd1' : d' ≤ 1 / 2) (he' : e' ^ 2 = 1)
    (hφ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d → φ z = e * ((if z < d then 1 else 0) - 2 * d))
    (hψ : ∀ z, 0 ≤ z → z ≤ 1 / 2 → z ≠ d' → ψ z = e' * ((if z < d' then 1 else 0) - 2 * d')) :
    ∫ z in (0 : ℝ)..(1 / 2),
        (a * c + 4 * a * ψ z - a * φ z - 4 * c * ψ z - 16 * ψ z ^ 2 + 4 * (φ z * ψ z))
      = a * c / 2 - 16 * (d' * (1 - 2 * d')) + 4 * (e * e' * (min d d' - 2 * d * d')) := by
  have h : ∫ z in (0 : ℝ)..(1 / 2),
        (a * c + 4 * a * ψ z - a * φ z - 4 * c * ψ z - 16 * ψ z ^ 2 + 4 * (φ z * ψ z))
      = ∫ z in (0 : ℝ)..(1 / 2),
        ((a * c - 8 * a * e' * d' + 2 * a * e * d + 8 * c * e' * d' - 64 * d' ^ 2
            + 16 * e * e' * d * d')
          + (-a * e - 8 * e * e' * d') * (if z < d then 1 else 0)
          + (4 * a * e' - 4 * c * e' - 16 * (1 - 4 * d') - 8 * e * e' * d)
            * (if z < d' then 1 else 0)
          + 4 * e * e' * (if z < min d d' then 1 else 0)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume d, Measure.ae_ne volume d'] with z hz hz' hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [hφ z hmem.1.le hmem.2 hz, hψ z hmem.1.le hmem.2 hz', ← ite_lt_mul_ite_lt]
    have hI := ite_lt_sq z d'
    linear_combination (-16 * ((if z < d' then (1 : ℝ) else 0) ^ 2
      - 4 * d' * (if z < d' then (1 : ℝ) else 0) + 4 * d' ^ 2)) * he' - 16 * hI
  rw [h, integral_step_comb hd0 hd1 hd0' hd1' (le_min hd0 hd0') ((min_le_left d d').trans hd1)]
  ring

end Step

/-! ## (76)-(79) -/

section AB

/-- (76): for `0 ≤ z ≤ 1/2` with `z ≠ d({x})`, `A(z) = ε({x})(1_{z < d({x})} - 2d({x}))`. -/
theorem tailA_eq (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (hzd : z ≠ tailD (Int.fract x)) :
    tailA x z = tailEps (Int.fract x)
      * ((if z < tailD (Int.fract x) then 1 else 0) - 2 * tailD (Int.fract x)) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  have e1 : ⌊x - z⌋ = ⌊x⌋ + ⌊Int.fract x - z⌋ := by
    have : x - z = (Int.fract x - z) + (⌊x⌋ : ℝ) := by linarith
    rw [this, Int.floor_add_intCast]
    ring
  have e2 : ⌊x + z⌋ = ⌊x⌋ + ⌊Int.fract x + z⌋ := by
    have : x + z = (Int.fract x + z) + (⌊x⌋ : ℝ) := by linarith
    rw [this, Int.floor_add_intCast]
    ring
  simp only [tailA, ellLim, e1, e2]
  push_cast
  unfold tailD tailEps at hzd ⊢
  rcases lt_or_ge (Int.fract x) (1 / 2) with hlt | hge
  · have hd : min (Int.fract x) (1 - Int.fract x) = Int.fract x := min_eq_left (by linarith)
    rw [hd] at hzd ⊢
    rw [if_pos hlt]
    rcases lt_or_gt_of_ne hzd with hz | hz
    · rw [if_pos hz]
      have h1 : ⌊Int.fract x - z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
    · rw [if_neg (not_lt.mpr hz.le)]
      have h1 : ⌊Int.fract x - z⌋ = -1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
  · have hd : min (Int.fract x) (1 - Int.fract x) = 1 - Int.fract x := min_eq_right (by linarith)
    rw [hd] at hzd ⊢
    rw [if_neg (not_lt.mpr hge)]
    rcases lt_or_gt_of_ne hzd with hz | hz
    · rw [if_pos hz]
      have h1 : ⌊Int.fract x - z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
    · rw [if_neg (not_lt.mpr hz.le)]
      have h1 : ⌊Int.fract x - z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith

/-- (76) for `B`: for `0 ≤ z ≤ 1/2` with `z ≠ d({αx})`,
`B(z) = ε({αx})(1_{z < d({αx})} - 2d({αx}))`. -/
theorem tailB_eq (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2)
    (hzd : z ≠ tailD (Int.fract ((alpha : ℝ) * x))) :
    tailB x z = tailEps (Int.fract ((alpha : ℝ) * x))
      * ((if z < tailD (Int.fract ((alpha : ℝ) * x)) then 1 else 0)
        - 2 * tailD (Int.fract ((alpha : ℝ) * x))) :=
  tailA_eq _ z hz0 hz1 hzd

/-- (77): `∫_0^{1/2} A(z) dz = 0`. -/
theorem integral_tailA (x : ℝ) : ∫ z in (0 : ℝ)..(1 / 2), tailA x z = 0 :=
  integral_step_form (tailD_fract_mem x).1 (tailD_fract_mem x).2 (tailA_eq x)

/-- (77): `∫_0^{1/2} B(z) dz = 0`. -/
theorem integral_tailB (x : ℝ) : ∫ z in (0 : ℝ)..(1 / 2), tailB x z = 0 :=
  integral_step_form (tailD_fract_mem _).1 (tailD_fract_mem _).2 (tailB_eq x)

/-- (78): `∫_0^{1/2} A(z)² dz = d({x})(1 - 2d({x}))`. -/
theorem integral_tailA_sq (x : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), tailA x z ^ 2
      = tailD (Int.fract x) * (1 - 2 * tailD (Int.fract x)) :=
  integral_step_form_sq (tailD_fract_mem x).1 (tailD_fract_mem x).2 (tailEps_sq _) (tailA_eq x)

/-- (78): `∫_0^{1/2} B(z)² dz = d({αx})(1 - 2d({αx}))`. -/
theorem integral_tailB_sq (x : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2
      = tailD (Int.fract ((alpha : ℝ) * x)) * (1 - 2 * tailD (Int.fract ((alpha : ℝ) * x))) :=
  integral_step_form_sq (tailD_fract_mem _).1 (tailD_fract_mem _).2 (tailEps_sq _) (tailB_eq x)

/-- (79): `∫_0^{1/2} A(z)B(z) dz = ε(f)ε(g)(min(d(f), d(g)) - 2d(f)d(g))` with `f = {x}`,
`g = {αx}`. -/
theorem integral_tailA_mul_tailB (x : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z
      = tailEps (Int.fract x) * tailEps (Int.fract ((alpha : ℝ) * x))
        * (min (tailD (Int.fract x)) (tailD (Int.fract ((alpha : ℝ) * x)))
          - 2 * tailD (Int.fract x) * tailD (Int.fract ((alpha : ℝ) * x))) :=
  integral_step_form_mul (tailD_fract_mem x).1 (tailD_fract_mem x).2 (tailD_fract_mem _).1
    (tailD_fract_mem _).2 (tailA_eq x) (tailB_eq x)

end AB

/-! ## The decomposition (80) -/

section Decomposition

theorem TLim_eq_fract (x : ℝ) :
    (TLim x : ℝ) = 2 * (bigH : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x) := by
  simp only [TLim]
  exact (Int.self_sub_fract _).symm

/-- The integrand of (66) in terms of `A` and `B`. -/
theorem gammaIntegrand_eq_tail (x z : ℝ) :
    gammaIntegrand x z =
      (2 * (lam : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x))
          * (14 * (alpha : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x) - 7)
        + 4 * (2 * (lam : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x)) * tailB x z
        - (2 * (lam : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x)) * tailA x z
        - 4 * (14 * (alpha : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x) - 7) * tailB x z
        - 16 * tailB x z ^ 2 + 4 * (tailA x z * tailB x z) := by
  simp only [gammaIntegrand, bLim, tailA, tailB, TLim_eq_fract]
  push_cast
  simp only [alpha_real, lam_real, bigH_real]
  ring

/-- The `z`-integral in (66): `∫_0^{1/2} (T - b)(T + b - ℓ - 7) dz
= (2λx - τ)(14αx - τ - 7)/2 - 16 ∫ B² + 4 ∫ AB`, using (77). -/
theorem integral_gammaIntegrand (x : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), gammaIntegrand x z =
      (2 * (lam : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x))
          * (14 * (alpha : ℝ) * x - Int.fract (2 * (bigH : ℝ) * x) - 7) / 2
        - 16 * (∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2)
        + 4 * ∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z := by
  rw [integral_tailB_sq, integral_tailA_mul_tailB]
  simp only [gammaIntegrand_eq_tail]
  exact integral_quad_step (tailD_fract_mem x).1 (tailD_fract_mem x).2 (tailD_fract_mem _).1
    (tailD_fract_mem _).2 (tailEps_sq _) (tailA_eq x) (tailB_eq x)

theorem max_half (w : ℝ) : max (w / 2) 0 = max w 0 / 2 := by
  rcases le_total w 0 with h | h
  · rw [max_eq_right h, max_eq_right (show w / 2 ≤ 0 by linarith)]
    ring
  · rw [max_eq_left h, max_eq_left (show 0 ≤ w / 2 by linarith)]

/-- (80): `R(x) = xF(x) + Q(x)` for every real `x`. -/
theorem innerR_eq_tail (x : ℝ) : innerR x = x * tailF x + tailQ x := by
  have hq : (qLim x : ℝ) = 2 * x - Int.fract (2 * x) := by
    simp only [qLim]
    exact (Int.self_sub_fract _).symm
  have hsn : sLim x - nPlus x = (Int.fract (2 * (bigH : ℝ) * x) - Int.fract (2 * x)) / 2 := by
    simp only [sLim, nPlus, TLim_eq_fract, hq]
    ring
  have hfl : (⌊x⌋ : ℝ) = x - Int.fract x := (Int.self_sub_fract x).symm
  have hfa : (⌊(alpha : ℝ) * x⌋ : ℝ) = (alpha : ℝ) * x - Int.fract ((alpha : ℝ) * x) :=
    (Int.self_sub_fract _).symm
  have hJ : (⌊2 * ((lam : ℝ) * x)⌋ : ℝ) = 2 * (lam : ℝ) * x - Int.fract (2 * (lam : ℝ) * x) := by
    rw [show 2 * ((lam : ℝ) * x) = 2 * (lam : ℝ) * x by ring]
    exact (Int.self_sub_fract _).symm
  unfold innerR innerGamma
  rw [integral_gammaIntegrand, hsn, max_half]
  simp only [innerN, innerJ, sLim, TLim_eq_fract, hq, hfl, hfa, hJ, tailQ, tailF]
  simp only [alpha_real, lam_real, bigH_real]
  ring

end Decomposition

end ZetaSeven
