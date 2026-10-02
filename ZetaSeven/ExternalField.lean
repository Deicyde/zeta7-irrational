import Mathlib

/-!
# External field (paper Section 6.1, equations (91)-(93))

The external field `V(t)` on `[0,∞)`, its closed form through `J_a`,
and the logarithmic potential/energy notation `U_ρ`, `I(ρ)`.
-/

namespace ZetaSeven

open MeasureTheory

/-- Equation (91): `α = 3/40` (as a real; cf. the rational `alpha` in
`ZetaSeven.FunctionalMu`, kept separate so this node stays standalone). -/
noncomputable def eAlpha : ℝ := 3 / 40

/-- Equation (92): `J_a(t) = ∫_0^a log(t + u²) du`. -/
noncomputable def Jfield (a t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..a, Real.log (t + u ^ 2)

/-- Equation (91): `V(t) = 2π√t + J_1(t) - 8J_α(t)` on `[0,∞)`. -/
noncomputable def Vfield (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + Jfield 1 t - 8 * Jfield eAlpha t

/-- Equation (93): logarithmic potential `U_ρ(t) = ∫ log|t-u| dρ(u)`. -/
noncomputable def Ulog (ρ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ u, Real.log |t - u| ∂ρ

/-- Equation (93): logarithmic energy `I(ρ) = ∬ log|t-u| dρ(t)dρ(u)`,
via the product measure. -/
noncomputable def Ilog (ρ : Measure ℝ) : ℝ :=
  ∫ p, Real.log |p.1 - p.2| ∂(ρ.prod ρ)

end ZetaSeven
