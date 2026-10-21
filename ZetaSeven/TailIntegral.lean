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
    rw [ite_eq_left (lt_of_le_of_ne hmem.2 hz)]
  have e2 : ∫ z in d..(1 / 2), (if z < d then (1 : ℝ) else 0) = ∫ _ in d..(1 / 2), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hd1] at hz
    show (if z < d then (1 : ℝ) else 0) = 0
    rw [ite_eq_right (not_lt.mpr hz.1)]
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
  unfold tailD at hzd
  unfold tailD tailEps
  rcases lt_or_ge (Int.fract x) (1 / 2) with hlt | hge
  · have hd : min (Int.fract x) (1 - Int.fract x) = Int.fract x := min_eq_left (by linarith)
    rw [hd] at hzd ⊢
    rw [ite_eq_left hlt]
    rcases lt_or_gt_of_ne hzd with hz | hz
    · rw [ite_eq_left hz]
      have h1 : ⌊Int.fract x - z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
    · rw [ite_eq_right (not_lt.mpr hz.le)]
      have h1 : ⌊Int.fract x - z⌋ = -1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
  · have hd : min (Int.fract x) (1 - Int.fract x) = 1 - Int.fract x := min_eq_right (by linarith)
    rw [hd] at hzd ⊢
    rw [ite_eq_right (not_lt.mpr hge)]
    rcases lt_or_gt_of_ne hzd with hz | hz
    · rw [ite_eq_left hz]
      have h1 : ⌊Int.fract x - z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : ⌊Int.fract x + z⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [h1, h2]
      push_cast
      linarith
    · rw [ite_eq_right (not_lt.mpr hz.le)]
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

/-! ## The bounds (83) -/

section QBounds

/-- (82) in closed form, by (78) and (79). -/
theorem tailQ_eq (x : ℝ) :
    tailQ x =
      (Int.fract (2 * (bigH : ℝ) * x) * (Int.fract (2 * (bigH : ℝ) * x) - Int.fract (2 * x))
          - max (Int.fract (2 * (bigH : ℝ) * x) - Int.fract (2 * x)) 0
          + Int.fract (2 * (lam : ℝ) * x) * (1 - Int.fract (2 * (lam : ℝ) * x))) / 2
        + 16 * (tailD (Int.fract ((alpha : ℝ) * x))
          * (1 - 2 * tailD (Int.fract ((alpha : ℝ) * x))))
        - 4 * (tailEps (Int.fract x) * tailEps (Int.fract ((alpha : ℝ) * x))
          * (min (tailD (Int.fract x)) (tailD (Int.fract ((alpha : ℝ) * x)))
            - 2 * tailD (Int.fract x) * tailD (Int.fract ((alpha : ℝ) * x)))) := by
  rw [tailQ, integral_tailB_sq, integral_tailA_mul_tailB]

/-- `0 ≤ min(d, d') - 2dd' ≤ d'(1 - 2d')` for `d, d' ∈ [0, 1/2]`. -/
theorem min_sub_mem {df dg : ℝ} (hdf0 : 0 ≤ df) (hdf1 : df ≤ 1 / 2) (hdg0 : 0 ≤ dg)
    (hdg1 : dg ≤ 1 / 2) :
    0 ≤ min df dg - 2 * df * dg ∧ min df dg - 2 * df * dg ≤ dg * (1 - 2 * dg) := by
  rcases le_total df dg with h | h
  · rw [min_eq_left h]
    constructor
    · nlinarith [mul_nonneg hdf0 (show (0 : ℝ) ≤ 1 - 2 * dg by linarith)]
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ dg - df by linarith)
        (show (0 : ℝ) ≤ 1 - 2 * dg by linarith)]
  · rw [min_eq_right h]
    constructor
    · nlinarith [mul_nonneg hdg0 (show (0 : ℝ) ≤ 1 - 2 * df by linarith)]
    · nlinarith [mul_nonneg hdg0 (show (0 : ℝ) ≤ df - dg by linarith)]

/-- The correlation bound `|∫_0^{1/2} A(z)B(z) dz| ≤ ∫_0^{1/2} B(z)² dz`, from (78)-(79). -/
theorem abs_integral_tailA_mul_tailB_le (x : ℝ) :
    |∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z| ≤ ∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2 := by
  obtain ⟨h1, h2⟩ := min_sub_mem (tailD_fract_mem x).1 (tailD_fract_mem x).2
    (tailD_fract_mem ((alpha : ℝ) * x)).1 (tailD_fract_mem ((alpha : ℝ) * x)).2
  have hm : |tailEps (Int.fract x) * tailEps (Int.fract ((alpha : ℝ) * x))| = 1 := by
    rcases tailEps_mul_cases (Int.fract x) (Int.fract ((alpha : ℝ) * x)) with h | h <;>
      rw [h] <;> norm_num
  rw [integral_tailA_mul_tailB, integral_tailB_sq, abs_mul, hm, one_mul, abs_of_nonneg h1]
  exact h2

/-- Hence `16 ∫_0^{1/2} B² - 4 ∫_0^{1/2} AB ≥ 0`. -/
theorem sixteen_integral_sq_sub_nonneg (x : ℝ) :
    0 ≤ 16 * (∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2)
      - 4 * ∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z := by
  have h := abs_integral_tailA_mul_tailB_le x
  have h0 : 0 ≤ ∫ z in (0 : ℝ)..(1 / 2), tailB x z ^ 2 := by
    rw [integral_tailB_sq]
    obtain ⟨d0, d1⟩ := tailD_fract_mem ((alpha : ℝ) * x)
    exact mul_nonneg d0 (by linarith)
  have h1 := le_abs_self (∫ z in (0 : ℝ)..(1 / 2), tailA x z * tailB x z)
  linarith

theorem tailQ_aux {τ σ η df dg e : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hdf0 : 0 ≤ df) (hdf1 : df ≤ 1 / 2) (hdg0 : 0 ≤ dg)
    (hdg1 : dg ≤ 1 / 2) (he : e = 1 ∨ e = -1) :
    -1 / 8 ≤ (τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η)) / 2 + 16 * (dg * (1 - 2 * dg))
        - 4 * (e * (min df dg - 2 * df * dg)) ∧
      (τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η)) / 2 + 16 * (dg * (1 - 2 * dg))
        - 4 * (e * (min df dg - 2 * df * dg)) ≤ 21 / 8 := by
  have h1 : -1 / 4 ≤ τ * (τ - σ) - max (τ - σ) 0 ∧ τ * (τ - σ) - max (τ - σ) 0 ≤ 0 := by
    rcases le_total (τ - σ) 0 with h | h
    · rw [max_eq_right h]
      constructor
      · nlinarith [sq_nonneg (τ - 1 / 2), mul_nonneg hτ0 (show (0 : ℝ) ≤ 1 - σ by linarith)]
      · nlinarith [mul_nonneg hτ0 (show (0 : ℝ) ≤ σ - τ by linarith)]
    · rw [max_eq_left h]
      constructor
      · nlinarith [sq_nonneg (τ - 1 / 2), mul_nonneg hσ0 (show (0 : ℝ) ≤ 1 - τ by linarith)]
      · nlinarith [mul_nonneg h (show (0 : ℝ) ≤ 1 - τ by linarith)]
  have h2 : 0 ≤ η * (1 - η) ∧ η * (1 - η) ≤ 1 / 4 :=
    ⟨mul_nonneg hη0 (by linarith), by nlinarith [sq_nonneg (η - 1 / 2)]⟩
  have h3 : 0 ≤ dg * (1 - 2 * dg) ∧ dg * (1 - 2 * dg) ≤ 1 / 8 :=
    ⟨mul_nonneg hdg0 (by linarith), by nlinarith [sq_nonneg (dg - 1 / 4)]⟩
  have h4 := min_sub_mem hdf0 hdf1 hdg0 hdg1
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  obtain ⟨h4a, h4b⟩ := h4
  rcases he with rfl | rfl
  · constructor <;> linarith
  · constructor <;> linarith

/-- The sharper bounds `-1/8 ≤ Q(x) ≤ 21/8`; the lower bound uses `|∫AB| ≤ ∫B²` from (78)-(79)
(source-map erratum 11). -/
theorem tailQ_sharp_bounds (x : ℝ) : -1 / 8 ≤ tailQ x ∧ tailQ x ≤ 21 / 8 := by
  obtain ⟨h1, h2⟩ := tailQ_aux (Int.fract_nonneg (2 * (bigH : ℝ) * x))
    (Int.fract_lt_one (2 * (bigH : ℝ) * x)) (Int.fract_nonneg (2 * x)) (Int.fract_lt_one (2 * x))
    (Int.fract_nonneg (2 * (lam : ℝ) * x)) (Int.fract_lt_one (2 * (lam : ℝ) * x))
    (tailD_fract_mem x).1 (tailD_fract_mem x).2 (tailD_fract_mem ((alpha : ℝ) * x)).1
    (tailD_fract_mem ((alpha : ℝ) * x)).2
    (tailEps_mul_cases (Int.fract x) (Int.fract ((alpha : ℝ) * x)))
  rw [tailQ_eq]
  constructor <;> linarith

/-- (83): `-1/2 ≤ Q(x) ≤ 27/8` for every real `x`. -/
theorem tailQ_bounds (x : ℝ) : -1 / 2 ≤ tailQ x ∧ tailQ x ≤ 27 / 8 := by
  obtain ⟨h1, h2⟩ := tailQ_sharp_bounds x
  constructor <;> linarith

end QBounds

/-! ## The periodic primitives (84) -/

section Primitives

/-- (84): `G(v) = v(1 - v)(2v - 1)`. -/
noncomputable def tailG (v : ℝ) : ℝ := v * (1 - v) * (2 * v - 1)

/-- (84): `P(x) = -λ{x}(1 - {x}) + (296/3){αx}(1 - {αx})`. -/
noncomputable def tailP (x : ℝ) : ℝ :=
  -(lam : ℝ) * (Int.fract x * (1 - Int.fract x))
    + 296 / 3 * (Int.fract ((alpha : ℝ) * x) * (1 - Int.fract ((alpha : ℝ) * x)))

/-- (84): `C(x) = -(37/240)G({x}) + (5920/27)G({αx})`. -/
noncomputable def tailC (x : ℝ) : ℝ :=
  -(37 / 240) * tailG (Int.fract x) + 5920 / 27 * tailG (Int.fract ((alpha : ℝ) * x))

theorem continuous_tailG : Continuous tailG := by
  unfold tailG
  fun_prop

/-- `P` is continuous. -/
theorem continuous_tailP : Continuous tailP := by
  have hc : Continuous fun v : ℝ => Int.fract v * (1 - Int.fract v) :=
    ContinuousOn.comp_fract'' (f := fun v : ℝ => v * (1 - v)) (by fun_prop) (by norm_num)
  have hc2 : Continuous fun y : ℝ =>
      Int.fract ((alpha : ℝ) * y) * (1 - Int.fract ((alpha : ℝ) * y)) :=
    hc.comp (continuous_const.mul continuous_id)
  exact (continuous_const.mul hc).add (continuous_const.mul hc2)

/-- `C` is continuous. -/
theorem continuous_tailC : Continuous tailC := by
  have hc : Continuous fun v : ℝ => tailG (Int.fract v) :=
    ContinuousOn.comp_fract'' continuous_tailG.continuousOn (by norm_num [tailG])
  have hc2 : Continuous fun y : ℝ => tailG (Int.fract ((alpha : ℝ) * y)) :=
    hc.comp (continuous_const.mul continuous_id)
  exact (continuous_const.mul hc).add (continuous_const.mul hc2)

theorem fract_add_forty (x : ℝ) :
    Int.fract (x + 40) = Int.fract x ∧
      Int.fract ((alpha : ℝ) * (x + 40)) = Int.fract ((alpha : ℝ) * x) := by
  constructor
  · rw [show x + 40 = x + ((40 : ℕ) : ℝ) by norm_num]
    exact Int.fract_add_natCast x 40
  · rw [show (alpha : ℝ) * (x + 40) = (alpha : ℝ) * x + ((3 : ℕ) : ℝ) by
      rw [alpha_real]; push_cast; ring]
    exact Int.fract_add_natCast _ 3

/-- `F`, `P` and `C` have period `40`. -/
theorem tail_periodic (x : ℝ) :
    tailF (x + 40) = tailF x ∧ tailP (x + 40) = tailP x ∧ tailC (x + 40) = tailC x := by
  obtain ⟨h1, h2⟩ := fract_add_forty x
  refine ⟨?_, ?_, ?_⟩
  · simp only [tailF, h1, h2]
  · simp only [tailP, h1, h2]
  · simp only [tailC, h1, h2]

theorem hasDerivAt_fract {x : ℝ} (h : Int.fract x ≠ 0) : HasDerivAt Int.fract 1 x := by
  have h0 : (⌊x⌋ : ℝ) < x := by
    have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
    have hx := Int.self_sub_floor x
    linarith
  have h1 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hev : Int.fract =ᶠ[𝓝 x] fun y => y - (⌊x⌋ : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h0, h1⟩] with y hy
    have hfl : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
    rw [← Int.self_sub_floor, hfl]
  exact ((hasDerivAt_id' x).sub_const (⌊x⌋ : ℝ)).congr_of_eventuallyEq hev

theorem hasDerivAt_fract_mul {c x : ℝ} (h : Int.fract (c * x) ≠ 0) :
    HasDerivAt (fun y => Int.fract (c * y)) c x := by
  have h1 : HasDerivAt (fun y : ℝ => c * y) c x :=
    ((hasDerivAt_id' x).const_mul c).congr_deriv (mul_one c)
  exact ((hasDerivAt_fract h).comp x h1).congr_deriv (one_mul c)

/-- (84): off the breakpoints, `P' = F + λ`. -/
theorem hasDerivAt_tailP {x : ℝ} (hf : Int.fract x ≠ 0) (hg : Int.fract ((alpha : ℝ) * x) ≠ 0) :
    HasDerivAt tailP (tailF x + lam) x := by
  have h1 := hasDerivAt_fract hf
  have h2 := hasDerivAt_fract_mul hg
  have h := ((h1.mul (h1.const_sub 1)).const_mul (-(lam : ℝ))).add
    ((h2.mul (h2.const_sub 1)).const_mul (296 / 3 : ℝ))
  refine h.congr_deriv ?_
  simp only [tailF, alpha_real, lam_real]
  ring

theorem hasDerivAt_tailG (v : ℝ) : HasDerivAt tailG (6 * v * (1 - v) - 1) v := by
  have h1 := hasDerivAt_id' v
  have h := (h1.mul (h1.const_sub 1)).mul ((h1.const_mul (2 : ℝ)).sub_const 1)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- (84): off the breakpoints, `C' = P - P̄` with the paper's constant `P̄ = 11729/720`. -/
theorem hasDerivAt_tailC {x : ℝ} (hf : Int.fract x ≠ 0) (hg : Int.fract ((alpha : ℝ) * x) ≠ 0) :
    HasDerivAt tailC (tailP x - 11729 / 720) x := by
  have h1 := (hasDerivAt_tailG (Int.fract x)).comp x (hasDerivAt_fract hf)
  have h2 := (hasDerivAt_tailG (Int.fract ((alpha : ℝ) * x))).comp x (hasDerivAt_fract_mul hg)
  have h := (h1.const_mul (-(37 / 240) : ℝ)).add (h2.const_mul (5920 / 27 : ℝ))
  refine h.congr_deriv ?_
  simp only [tailP, alpha_real, lam_real]
  ring

theorem sq_mul_le_aux {w : ℝ} (hw0 : 0 ≤ w) : w ^ 2 * (1 - 4 * w) ≤ (1 / 10) ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg (1 - 6 * w)) (show (0 : ℝ) ≤ 1 + 12 * w by linarith)]

theorem abs_tailG_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |tailG v| ≤ 1 / 10 := by
  have hw0 : 0 ≤ v * (1 - v) := mul_nonneg h0 (by linarith)
  have hsq : tailG v ^ 2 = (v * (1 - v)) ^ 2 * (1 - 4 * (v * (1 - v))) := by
    unfold tailG
    ring
  have key : tailG v ^ 2 ≤ (1 / 10) ^ 2 := by
    rw [hsq]
    exact sq_mul_le_aux hw0
  exact abs_le_of_sq_le_sq key (by norm_num)

/-- (84): `|C(x)| < 22`. The proof uses `|G| ≤ 1/10` on `[0, 1]` in place of the paper's
`max |G| = 1/(6√3)`. -/
theorem abs_tailC_lt (x : ℝ) : |tailC x| < 22 := by
  have h1 := abs_tailG_le (Int.fract_nonneg x) (Int.fract_lt_one x).le
  have h2 := abs_tailG_le (Int.fract_nonneg ((alpha : ℝ) * x)) (Int.fract_lt_one _).le
  rw [abs_le] at h1 h2
  unfold tailC
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_tailP_sub_le (x : ℝ) : |tailP x - 11729 / 720| ≤ 17 := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hg0 := Int.fract_nonneg ((alpha : ℝ) * x)
  have hg1 := Int.fract_lt_one ((alpha : ℝ) * x)
  have a1 : 0 ≤ Int.fract x * (1 - Int.fract x) := mul_nonneg hf0 (by linarith)
  have a2 : Int.fract x * (1 - Int.fract x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  have b1 : 0 ≤ Int.fract ((alpha : ℝ) * x) * (1 - Int.fract ((alpha : ℝ) * x)) :=
    mul_nonneg hg0 (by linarith)
  have b2 : Int.fract ((alpha : ℝ) * x) * (1 - Int.fract ((alpha : ℝ) * x)) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (Int.fract ((alpha : ℝ) * x) - 1 / 2)]
  unfold tailP
  rw [lam_real, abs_le]
  constructor <;> linarith

/-- (85) at `T = 20`: `P(20) = 74/3`. -/
theorem tailP_twenty : tailP 20 = 74 / 3 := by
  have h1 : Int.fract (20 : ℝ) = 0 := Int.fract_eq_iff.mpr ⟨le_rfl, by norm_num, 20, by norm_num⟩
  have h2 : Int.fract ((alpha : ℝ) * 20) = 1 / 2 := by
    rw [alpha_real, Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, 1, by norm_num⟩
  simp only [tailP, h1, h2, lam_real]
  norm_num

/-- (85) at `T = 20`: `C(20) = 0`. -/
theorem tailC_twenty : tailC 20 = 0 := by
  have h1 : Int.fract (20 : ℝ) = 0 := Int.fract_eq_iff.mpr ⟨le_rfl, by norm_num, 20, by norm_num⟩
  have h2 : Int.fract ((alpha : ℝ) * 20) = 1 / 2 := by
    rw [alpha_real, Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, 1, by norm_num⟩
  simp only [tailC, h1, h2, tailG]
  norm_num

theorem fract_of_forty_dvd {M : ℕ} (h40 : 40 ∣ M) :
    Int.fract (M : ℝ) = 0 ∧ Int.fract ((alpha : ℝ) * M) = 0 := by
  obtain ⟨k, rfl⟩ := h40
  constructor
  · exact Int.fract_natCast _
  · rw [show (alpha : ℝ) * ((40 * k : ℕ) : ℝ) = ((3 * k : ℕ) : ℝ) by
      rw [alpha_real]; push_cast; ring]
    exact Int.fract_natCast _

/-- For `M ∈ 40ℤ_{>0}`, `{M} = {αM} = 0`, so `P(M) = 0`. -/
theorem tailP_of_forty_dvd {M : ℕ} (h40 : 40 ∣ M) : tailP M = 0 := by
  obtain ⟨h1, h2⟩ := fract_of_forty_dvd h40
  simp only [tailP, h1, h2]
  ring

/-- For `M ∈ 40ℤ_{>0}`, `C(M) = 0`. -/
theorem tailC_of_forty_dvd {M : ℕ} (h40 : 40 ∣ M) : tailC M = 0 := by
  obtain ⟨h1, h2⟩ := fract_of_forty_dvd h40
  simp only [tailC, h1, h2, tailG]
  ring

theorem fract_of_mod_forty_eq_twenty {M : ℕ} (h : M % 40 = 20) :
    Int.fract (M : ℝ) = 0 ∧ Int.fract ((alpha : ℝ) * M) = 1 / 2 := by
  constructor
  · exact Int.fract_natCast M
  · have hM : (M : ℝ) = 40 * ((M / 40 : ℕ) : ℝ) + 20 := by
      have h' := Nat.div_add_mod M 40
      rw [h] at h'
      exact_mod_cast h'.symm
    rw [Int.fract_eq_iff]
    refine ⟨by norm_num, by norm_num, 3 * ((M / 40 : ℕ) : ℤ) + 1, ?_⟩
    rw [hM, alpha_real]
    push_cast
    ring

/-- For `M ≡ 20 (mod 40)`, `P(M) = P(20) = 74/3`. -/
theorem tailP_of_mod_forty {M : ℕ} (h : M % 40 = 20) : tailP M = 74 / 3 := by
  obtain ⟨h1, h2⟩ := fract_of_mod_forty_eq_twenty h
  simp only [tailP, h1, h2, lam_real]
  norm_num

/-- For `M ≡ 20 (mod 40)`, `C(M) = 0`. -/
theorem tailC_of_mod_forty {M : ℕ} (h : M % 40 = 20) : tailC M = 0 := by
  obtain ⟨h1, h2⟩ := fract_of_mod_forty_eq_twenty h
  simp only [tailC, h1, h2, tailG]
  norm_num

end Primitives

/-! ## Measurability and integrability on `(T, ∞)` -/

section Integrability

theorem measurable_tailEps : Measurable tailEps := by
  unfold tailEps
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_tailD : Measurable tailD := by
  unfold tailD
  fun_prop

theorem measurable_tailF : Measurable tailF := by
  unfold tailF
  fun_prop

theorem measurable_tailQ : Measurable tailQ := by
  rw [funext tailQ_eq]
  have hE := measurable_tailEps
  have hD := measurable_tailD
  fun_prop

/-- `R` is measurable, by the closed form (80). -/
theorem measurable_innerR : Measurable innerR := by
  rw [funext innerR_eq_tail]
  have hF := measurable_tailF
  have hQ := measurable_tailQ
  fun_prop

theorem integrableOn_Ioi_inv_pow {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x : ℝ => (x ^ n)⁻¹) (Ioi T) := by
  have hn' : -(n : ℝ) < -1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine (integrableOn_Ioi_rpow_of_lt hn' hT).congr_fun (fun x hx => ?_) measurableSet_Ioi
  show x ^ (-(n : ℝ)) = (x ^ n)⁻¹
  rw [Real.rpow_neg (le_of_lt (lt_trans hT hx)), Real.rpow_natCast]

theorem integral_Ioi_inv_pow_three {T : ℝ} (hT : 0 < T) :
    ∫ x in Ioi T, (x ^ 3)⁻¹ = (T ^ 2)⁻¹ / 2 := by
  have h := integral_Ioi_rpow_of_lt (show (-3 : ℝ) < -1 by norm_num) hT
  have e : ∫ x in Ioi T, (x ^ 3)⁻¹ = ∫ x in Ioi T, x ^ (-3 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    show (x ^ 3)⁻¹ = x ^ (-3 : ℝ)
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt (lt_trans hT hx)),
      Real.rpow_natCast]
  rw [e, h, show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hT.le,
    Real.rpow_natCast, neg_div_neg_eq]
  norm_num

theorem integral_Ioi_inv_pow_four {T : ℝ} (hT : 0 < T) :
    ∫ x in Ioi T, (x ^ 4)⁻¹ = (T ^ 3)⁻¹ / 3 := by
  have h := integral_Ioi_rpow_of_lt (show (-4 : ℝ) < -1 by norm_num) hT
  have e : ∫ x in Ioi T, (x ^ 4)⁻¹ = ∫ x in Ioi T, x ^ (-4 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    show (x ^ 4)⁻¹ = x ^ (-4 : ℝ)
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt (lt_trans hT hx)),
      Real.rpow_natCast]
  rw [e, h, show (-4 : ℝ) + 1 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hT.le,
    Real.rpow_natCast, neg_div_neg_eq]
  norm_num

/-- A bounded measurable function divided by `x^n`, `n ≥ 2`, is integrable on `(T, ∞)`. -/
theorem integrableOn_div_pow {h : ℝ → ℝ} (hm : Measurable h) {K : ℝ} (hK : ∀ x, |h x| ≤ K)
    {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => h x / x ^ n) (Ioi T) := by
  refine Integrable.mono' (Integrable.const_mul (integrableOn_Ioi_inv_pow hn hT) K)
    (hm.div (measurable_id.pow_const n)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := lt_trans hT hx
  show ‖h x / x ^ n‖ ≤ K * (x ^ n)⁻¹
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx0 n), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hK x) (inv_nonneg.mpr (pow_pos hx0 n).le)

theorem abs_tailF_le (x : ℝ) : |tailF x| ≤ 24 := by
  have := Int.fract_nonneg x
  have := Int.fract_lt_one x
  have := Int.fract_nonneg ((alpha : ℝ) * x)
  have := Int.fract_lt_one ((alpha : ℝ) * x)
  unfold tailF
  rw [lam_real, abs_le]
  constructor <;> linarith

theorem abs_tailQ_le (x : ℝ) : |tailQ x| ≤ 27 / 8 := by
  obtain ⟨h1, h2⟩ := tailQ_bounds x
  rw [abs_le]
  constructor <;> linarith

/-- `C(x)/x⁴` is integrable on `(T, ∞)` for `T > 0`. -/
theorem integrableOn_tailC_div {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => tailC x / x ^ 4) (Ioi T) :=
  integrableOn_div_pow continuous_tailC.measurable (fun x => (abs_tailC_lt x).le) (by norm_num) hT

/-- `Q(x)/x³` is integrable on `(T, ∞)` for `T > 0`. -/
theorem integrableOn_tailQ_div {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => tailQ x / x ^ 3) (Ioi T) :=
  integrableOn_div_pow measurable_tailQ abs_tailQ_le (by norm_num) hT

theorem integrableOn_tailF_div {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => tailF x / x ^ 2) (Ioi T) :=
  integrableOn_div_pow measurable_tailF abs_tailF_le (by norm_num) hT

/-- `R(x)/x³` is integrable on `(T, ∞)` for `T > 0`, so the integrals in (85)-(86) are genuine
Lebesgue integrals. -/
theorem integrableOn_innerR_div_cube {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => innerR x / x ^ 3) (Ioi T) := by
  refine ((integrableOn_tailF_div hT).add (integrableOn_tailQ_div hT)).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  have hx0 : x ≠ 0 := (lt_trans hT hx).ne'
  show tailF x / x ^ 2 + tailQ x / x ^ 3 = innerR x / x ^ 3
  rw [innerR_eq_tail, div_add_div _ _ (pow_ne_zero 2 hx0) (pow_ne_zero 3 hx0),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 3 hx0)) (pow_ne_zero 3 hx0)]
  ring

theorem integrableOn_tailPhi_deriv {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => tailF x / x ^ 2 - 6 * tailC x / x ^ 4) (Ioi T) := by
  have h6 : IntegrableOn (fun x => 6 * tailC x / x ^ 4) (Ioi T) :=
    integrableOn_div_pow (K := 132) (continuous_tailC.measurable.const_mul 6)
      (fun x => by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        linarith [(abs_tailC_lt x).le]) (by norm_num) hT
  exact (integrableOn_tailF_div hT).sub h6

end Integrability

/-! ## The double integration by parts (85) and the tail bound (86) -/

section Tail

/-- The antiderivative `Φ(x) = λ/x + (P(x) - P̄)/x² + 2C(x)/x³` of `F/x² - 6C/x⁴`, with the
paper's constant `P̄ = 11729/720`. -/
noncomputable def tailPhi (x : ℝ) : ℝ :=
  (lam : ℝ) / x + (tailP x - 11729 / 720) / x ^ 2 + 2 * tailC x / x ^ 3

theorem hasDerivAt_tailPhi {x : ℝ} (hx : 0 < x) (hf : Int.fract x ≠ 0)
    (hg : Int.fract ((alpha : ℝ) * x) ≠ 0) :
    HasDerivAt tailPhi (tailF x / x ^ 2 - 6 * tailC x / x ^ 4) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h1 := (hasDerivAt_const x (lam : ℝ)).fun_div (hasDerivAt_id' x) hx0
  have h2 := ((hasDerivAt_tailP hf hg).sub_const (11729 / 720 : ℝ)).fun_div
    (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
  have h3 := ((hasDerivAt_tailC hf hg).const_mul (2 : ℝ)).fun_div (hasDerivAt_pow 3 x)
    (pow_ne_zero 3 hx0)
  refine ((h1.add h2).add h3).congr_deriv ?_
  simp only [Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
    pow_one]
  field_simp
  ring

theorem continuousOn_tailPhi {T : ℝ} (hT : 0 < T) : ContinuousOn tailPhi (Ici T) := by
  have hx : ∀ x ∈ Ici T, x ≠ 0 := fun x hx => (lt_of_lt_of_le hT hx).ne'
  unfold tailPhi
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact continuousOn_const.div continuousOn_id hx
  · exact (continuous_tailP.continuousOn.sub continuousOn_const).div (continuousOn_id.pow 2)
      (fun x hx' => pow_ne_zero 2 (hx x hx'))
  · exact (continuousOn_const.mul continuous_tailC.continuousOn).div (continuousOn_id.pow 3)
      (fun x hx' => pow_ne_zero 3 (hx x hx'))

theorem abs_tailPhi_le {x : ℝ} (hx : 1 ≤ x) : |tailPhi x| ≤ 62 / x := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hu1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hP := abs_tailP_sub_le x
  have hC := (abs_tailC_lt x).le
  rw [abs_le] at hP hC
  have e : tailPhi x = (lam : ℝ) * x⁻¹ + (tailP x - 11729 / 720) * x⁻¹ ^ 2
      + 2 * tailC x * x⁻¹ ^ 3 := by
    simp only [tailPhi, div_eq_mul_inv, inv_pow]
  rw [e, div_eq_mul_inv (62 : ℝ) x, abs_le, lam_real]
  have k1 := mul_nonneg (show (0 : ℝ) ≤ 17 - (tailP x - 11729 / 720) by linarith)
    (sq_nonneg x⁻¹)
  have k2 := mul_nonneg (show (0 : ℝ) ≤ 17 + (tailP x - 11729 / 720) by linarith)
    (sq_nonneg x⁻¹)
  have k3 := mul_nonneg (show (0 : ℝ) ≤ 22 - tailC x by linarith) (pow_nonneg hu0.le 3)
  have k4 := mul_nonneg (show (0 : ℝ) ≤ 22 + tailC x by linarith) (pow_nonneg hu0.le 3)
  have k5 := mul_nonneg hu0.le (show (0 : ℝ) ≤ 1 - x⁻¹ by linarith)
  have k6 := mul_nonneg (sq_nonneg x⁻¹) (show (0 : ℝ) ≤ 1 - x⁻¹ by linarith)
  constructor <;> nlinarith

theorem tendsto_tailPhi : Tendsto tailPhi atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 62 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs]
  exact abs_tailPhi_le hx

/-- The breakpoints of `P` and `C`: the countable set where `{x} = 0` or `{αx} = 0`. -/
theorem countable_tail_breaks :
    ({x : ℝ | Int.fract x = 0} ∪ {x : ℝ | Int.fract ((alpha : ℝ) * x) = 0}).Countable := by
  refine Set.Countable.union ?_ ?_
  · exact (Set.countable_range (fun n : ℤ => (n : ℝ))).mono
      (fun x hx => Int.fract_eq_zero_iff.mp hx)
  · refine (Set.countable_range (fun n : ℤ => (n : ℝ) * (40 / 3))).mono (fun x hx => ?_)
    obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hx
    refine ⟨n, ?_⟩
    rw [alpha_real] at hn
    show (n : ℝ) * (40 / 3) = x
    rw [hn]
    ring

theorem integral_tailPhi_deriv {T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    ∫ x in T..X, (tailF x / x ^ 2 - 6 * tailC x / x ^ 4) = tailPhi X - tailPhi T := by
  apply integral_eq_of_hasDerivAt_off_countable_of_le tailPhi _ hTX countable_tail_breaks
  · exact (continuousOn_tailPhi hT).mono Icc_subset_Ici_self
  · intro x hx
    obtain ⟨⟨hx1, _⟩, hxS⟩ := hx
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hxS
    exact hasDerivAt_tailPhi (lt_trans hT hx1) hxS.1 hxS.2
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTX]
    exact (integrableOn_tailPhi_deriv hT).mono_set Ioc_subset_Ioi_self

theorem integral_Ioi_tailPhi_deriv {T : ℝ} (hT : 0 < T) :
    ∫ x in Ioi T, (tailF x / x ^ 2 - 6 * tailC x / x ^ 4) = -tailPhi T := by
  have h1 := intervalIntegral_tendsto_integral_Ioi T (integrableOn_tailPhi_deriv hT) tendsto_id
  have h2 : Tendsto (fun X => ∫ x in T..X, (tailF x / x ^ 2 - 6 * tailC x / x ^ 4)) atTop
      (𝓝 (0 - tailPhi T)) := by
    refine (tendsto_tailPhi.sub_const (tailPhi T)).congr' ?_
    filter_upwards [eventually_ge_atTop T] with X hX
    exact (integral_tailPhi_deriv hT hX).symm
  exact (tendsto_nhds_unique h1 h2).trans (zero_sub _)

/-- (85): for `T > 0`, `∫_T^∞ R(x)/x³ dx = -λ/T - P(T)/T² + P̄/T² - 2C(T)/T³
+ 6∫_T^∞ C(x)/x⁴ dx + ∫_T^∞ Q(x)/x³ dx` with `P̄ = 11729/720`. -/
theorem integral_innerR_div_cube_eq {T : ℝ} (hT : 0 < T) :
    ∫ x in Ioi T, innerR x / x ^ 3 =
      -(lam : ℝ) / T - tailP T / T ^ 2 + 11729 / 720 / T ^ 2 - 2 * tailC T / T ^ 3
        + 6 * (∫ x in Ioi T, tailC x / x ^ 4) + ∫ x in Ioi T, tailQ x / x ^ 3 := by
  have e : ∫ x in Ioi T, innerR x / x ^ 3 = ∫ x in Ioi T,
      ((tailF x / x ^ 2 - 6 * tailC x / x ^ 4) + 6 * (tailC x / x ^ 4) + tailQ x / x ^ 3) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : x ≠ 0 := (lt_trans hT hx).ne'
    show innerR x / x ^ 3
      = (tailF x / x ^ 2 - 6 * tailC x / x ^ 4) + 6 * (tailC x / x ^ 4) + tailQ x / x ^ 3
    rw [innerR_eq_tail]
    field_simp
    ring
  have i1 := integrableOn_tailPhi_deriv hT
  have i2 : IntegrableOn (fun x => 6 * (tailC x / x ^ 4)) (Ioi T) :=
    Integrable.const_mul (integrableOn_tailC_div hT) 6
  have i3 := integrableOn_tailQ_div hT
  rw [e, integral_add, integral_add, integral_const_mul, integral_Ioi_tailPhi_deriv hT]
  · unfold tailPhi
    ring
  all_goals first | exact i1.add i2 | exact i1 | exact i2 | exact i3

/-- **(86)**: for `M ∈ 40ℤ_{>0}`,
`∫_M^∞ R(x)/x³ dx ≥ -λ/M + 11549/(720M²) - 44/M³`. The hypothesis `40 ∣ M` gives
`P(M) = C(M) = 0`; the estimate fails at every `M ≡ 20 (mod 40)`. -/
theorem tail_integral_bound {M : ℕ} (hM : 0 < M) (h40 : 40 ∣ M) :
    -(lam : ℝ) / M + 11549 / (720 * (M : ℝ) ^ 2) - 44 / (M : ℝ) ^ 3
      ≤ ∫ x in Ioi (M : ℝ), innerR x / x ^ 3 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [integral_innerR_div_cube_eq hM0, tailP_of_forty_dvd h40, tailC_of_forty_dvd h40]
  have hC : -22 * (((M : ℝ) ^ 3)⁻¹ / 3) ≤ ∫ x in Ioi (M : ℝ), tailC x / x ^ 4 := by
    have h := setIntegral_mono_on
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 4) (by norm_num) hM0) (-22))
      (integrableOn_tailC_div hM0) measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans hM0 hx
        have hc := (abs_lt.mp (abs_tailC_lt x)).1
        show -22 * (x ^ 4)⁻¹ ≤ tailC x / x ^ 4
        rw [div_eq_mul_inv (tailC x) (x ^ 4)]
        exact mul_le_mul_of_nonneg_right hc.le (inv_nonneg.mpr (pow_pos hx0 4).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_four hM0] at h
  have hQ : -1 / 2 * (((M : ℝ) ^ 2)⁻¹ / 2) ≤ ∫ x in Ioi (M : ℝ), tailQ x / x ^ 3 := by
    have h := setIntegral_mono_on
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 3) (by norm_num) hM0) (-1 / 2))
      (integrableOn_tailQ_div hM0) measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans hM0 hx
        have hq := (tailQ_bounds x).1
        show -1 / 2 * (x ^ 3)⁻¹ ≤ tailQ x / x ^ 3
        rw [div_eq_mul_inv (tailQ x) (x ^ 3)]
        exact mul_le_mul_of_nonneg_right hq (inv_nonneg.mpr (pow_pos hx0 3).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_three hM0] at h
  have key : (-(lam : ℝ) / M - 0 / (M : ℝ) ^ 2 + 11729 / 720 / (M : ℝ) ^ 2 - 2 * 0 / (M : ℝ) ^ 3
        + 6 * (∫ x in Ioi (M : ℝ), tailC x / x ^ 4) + ∫ x in Ioi (M : ℝ), tailQ x / x ^ 3)
      - (-(lam : ℝ) / M + 11549 / (720 * (M : ℝ) ^ 2) - 44 / (M : ℝ) ^ 3)
      = 6 * ((∫ x in Ioi (M : ℝ), tailC x / x ^ 4) - -22 * (((M : ℝ) ^ 3)⁻¹ / 3))
        + ((∫ x in Ioi (M : ℝ), tailQ x / x ^ 3) - -1 / 2 * (((M : ℝ) ^ 2)⁻¹ / 2)) := by
    ring
  linarith [key, hC, hQ]

/-- The hypothesis `M ∈ 40ℤ_{>0}` of (86) cannot be dropped: the estimate fails at every
`M ≡ 20 (mod 40)` (for example `M = 20`, `60`, `100`). By (85) with `P(M) = 74/3`, `C(M) = 0`,
`Q ≤ 27/8` and `C < 22`, the integral is at most `-λ/M + (11729/720 - 74/3 + 27/16)/M² + 44/M³`. -/
theorem tail_integral_bound_fails {M : ℕ} (h : M % 40 = 20) :
    ∫ x in Ioi (M : ℝ), innerR x / x ^ 3
      < -(lam : ℝ) / M + 11549 / (720 * (M : ℝ) ^ 2) - 44 / (M : ℝ) ^ 3 := by
  have hM20 : (20 : ℝ) ≤ M := by
    have : 20 ≤ M := by omega
    exact_mod_cast this
  have hM0 : (0 : ℝ) < M := by linarith
  rw [integral_innerR_div_cube_eq hM0, tailP_of_mod_forty h, tailC_of_mod_forty h]
  have hC : ∫ x in Ioi (M : ℝ), tailC x / x ^ 4 ≤ 22 * (((M : ℝ) ^ 3)⁻¹ / 3) := by
    have h' := setIntegral_mono_on (integrableOn_tailC_div hM0)
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 4) (by norm_num) hM0) 22)
      measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans hM0 hx
        have hc := (abs_lt.mp (abs_tailC_lt x)).2
        show tailC x / x ^ 4 ≤ 22 * (x ^ 4)⁻¹
        rw [div_eq_mul_inv (tailC x) (x ^ 4)]
        exact mul_le_mul_of_nonneg_right hc.le (inv_nonneg.mpr (pow_pos hx0 4).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_four hM0] at h'
  have hQ : ∫ x in Ioi (M : ℝ), tailQ x / x ^ 3 ≤ 27 / 8 * (((M : ℝ) ^ 2)⁻¹ / 2) := by
    have h' := setIntegral_mono_on (integrableOn_tailQ_div hM0)
      (Integrable.const_mul (integrableOn_Ioi_inv_pow (n := 3) (by norm_num) hM0) (27 / 8))
      measurableSet_Ioi (fun x hx => by
        have hx0 : 0 < x := lt_trans hM0 hx
        have hq := (tailQ_bounds x).2
        show tailQ x / x ^ 3 ≤ 27 / 8 * (x ^ 3)⁻¹
        rw [div_eq_mul_inv (tailQ x) (x ^ 3)]
        exact mul_le_mul_of_nonneg_right hq (inv_nonneg.mpr (pow_pos hx0 3).le))
    rwa [integral_const_mul, integral_Ioi_inv_pow_three hM0] at h'
  have hMi : (M : ℝ)⁻¹ ≤ 1 / 20 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hM20
  have hpos : 0 < ((M : ℝ) ^ 2)⁻¹ * (1091 / 48 - 88 * (M : ℝ)⁻¹) :=
    mul_pos (by positivity) (by linarith)
  have key : (-(lam : ℝ) / M + 11549 / (720 * (M : ℝ) ^ 2) - 44 / (M : ℝ) ^ 3)
      - (-(lam : ℝ) / M - 74 / 3 / (M : ℝ) ^ 2 + 11729 / 720 / (M : ℝ) ^ 2
        - 2 * 0 / (M : ℝ) ^ 3 + 6 * (∫ x in Ioi (M : ℝ), tailC x / x ^ 4)
        + ∫ x in Ioi (M : ℝ), tailQ x / x ^ 3)
      = 6 * (22 * (((M : ℝ) ^ 3)⁻¹ / 3) - ∫ x in Ioi (M : ℝ), tailC x / x ^ 4)
        + (27 / 8 * (((M : ℝ) ^ 2)⁻¹ / 2) - ∫ x in Ioi (M : ℝ), tailQ x / x ^ 3)
        + ((M : ℝ) ^ 2)⁻¹ * (1091 / 48 - 88 * (M : ℝ)⁻¹) := by
    ring
  linarith [key, hC, hQ, hpos]

end Tail

end ZetaSeven
