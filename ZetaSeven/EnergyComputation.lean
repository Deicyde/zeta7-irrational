import ZetaSeven.ComparisonMeasure

/-!
# Energy and norm constant (paper Lemma 6.1, equations (95)-(96); Appendix A.1 (110), A.4)

The logarithmic energy `I(ρ) = ∬ log |t - u| dρ(t) dρ(u)` (`ZetaSeven.Ilog`) of the comparison
measure `ρ = Σ_j c_j ω_{[0,L_j]}` of Table 1, the constant
`C* = -2λ + 16αλ(1 - log α) + 3λ² - 2λ² log(2λ)` of (95), and the bound (96)
`λM_0 - I(ρ) + C* ≤ U = 44/25` with `λ = 37/40`, `α = 3/40`, `M_0 = -109/20`.

**The nesting formula.** For `0 < L ≤ L'` the potential of `ω_{[0,L']}` is the constant
`log (L'/4)` on `[0, L']` (equation (109), `Ulog_arcsineMeasure`), which carries `ω_{[0,L]}`; by
Fubini the mutual energy of the two components is `log (L'/4)`. The symmetry `|t - u| = |u - t|`
of the kernel gives the other order, so the mutual energy of `ω_{[0,L]}` and `ω_{[0,L']}` is
`log (max L L' / 4)` in both orders. The kernel is integrable against every product of two
components (`|log y| ≤ 2B - log y` for `0 ≤ y ≤ B`, and the potential is at least `log (L/4)`),
hence against `ρ ⊗ ρ`, and `I(ρ) = Σ_j Σ_k c_j c_k log (max (L_j, L_k) / 4)`. Since
`L_1 > ⋯ > L_16`, the larger of `L_j, L_k` is `L_{min(j,k)}`, and grouping the pairs by the
smaller index gives (110) in the form
`I(ρ) = Σ_j (T_j² - T_{j+1}²) log (L_j/4)` with tail sums `T_j = c_j + ⋯ + c_16`.
The paper writes (110) with the prefix sums `S_j = c_1 + ⋯ + c_j`, which is the same formula
for intervals listed in increasing order; with Table 1's decreasing order the prefix-sum
expression evaluates to `-3.1433…` (the value reported in A.4), while the energy is
`I(ρ) ≈ -1.9482`. The bound (96) holds with the true value, with more room.

**The bound (96).** Each mutual energy is at least `log (L_j/4)`, so
`I(ρ) ≥ λ Σ_j c_j log (L_j/4)`; the logarithms are bounded below by `log y ≥ 1 - y⁻¹` after
scaling by a power of two, and `C*` is evaluated with the Taylor bound
`Real.abs_log_sub_add_sum_range_le` and Mathlib's enclosure of `log 2`.
-/

namespace ZetaSeven

open MeasureTheory

/-! ### Supports, a lower bound for the potential, and integrability on products -/

/-- `ω_{[0,L]}`, a density against Lebesgue measure on `(0, L)`, is s-finite, so Fubini's theorem
applies to products of arcsine measures. -/
instance sFinite_arcsineMeasure (L : ℝ) : SFinite (arcsineMeasure L) := by
  unfold arcsineMeasure
  infer_instance

/-- `ω_{[0,L]}` is carried by `(0, L)`. -/
theorem ae_mem_Ioo_arcsineMeasure (L : ℝ) : ∀ᵐ t ∂(arcsineMeasure L), t ∈ Set.Ioo 0 L := by
  unfold arcsineMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- The closed form (109) is bounded below by its value `log (L/4)` on `[0, L]`. -/
theorem log_le_arcsinePotential {L t : ℝ} (hL : 0 < L) :
    Real.log (L / 4) ≤ arcsinePotential L t := by
  unfold arcsinePotential
  by_cases htL : t ≤ L
  · exact (ite_eq_left htL).symm.le
  · rw [ite_eq_right htL]
    have htL' := not_le.1 htL
    refine Real.log_le_log (by positivity) ?_
    have h := Real.sqrt_nonneg (t * (t - L))
    linarith

/-- `|log y| ≤ 2B - log y` for `0 ≤ y ≤ B`, since `log y ≤ y`. -/
theorem abs_log_le_two_mul_sub_log {y B : ℝ} (hy : 0 ≤ y) (hyB : y ≤ B) :
    |Real.log y| ≤ 2 * B - Real.log y := by
  have h := Real.log_le_self hy
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The kernel `log |t - u|` is integrable against `ω_{[0,L]} ⊗ ω_{[0,L']}`: for `t ∈ (0, L)`,
`∫ |log |t - u|| dω_{[0,L']}(u) ≤ 2(L + L') - U_{ω_{[0,L']}}(t) ≤ 2(L + L') - log (L'/4)`. -/
theorem integrable_log_abs_sub_prod_arcsineMeasure {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((arcsineMeasure L).prod (arcsineMeasure L')) := by
  have := isProbabilityMeasure_arcsineMeasure hL
  have := isProbabilityMeasure_arcsineMeasure hL'
  have hmeas : Measurable fun p : ℝ × ℝ => Real.log |p.1 - p.2| := by fun_prop
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun t => integrable_log_abs_sub_arcsineMeasure hL' t, ?_⟩
  refine Integrable.mono' (integrable_const (2 * (L + L') - Real.log (L' / 4)))
    hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
  filter_upwards [ae_mem_Ioo_arcsineMeasure L] with t ht
  show ‖∫ u, ‖Real.log |t - u|‖ ∂(arcsineMeasure L')‖ ≤ 2 * (L + L') - Real.log (L' / 4)
  have hint := integrable_log_abs_sub_arcsineMeasure hL' t
  have hle : ∀ᵐ u ∂(arcsineMeasure L'),
      ‖Real.log |t - u|‖ ≤ 2 * (L + L') - Real.log |t - u| := by
    filter_upwards [ae_mem_Ioo_arcsineMeasure L'] with u hu
    rw [Real.norm_eq_abs]
    exact abs_log_le_two_mul_sub_log (abs_nonneg _)
      (abs_le.2 ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩)
  have hU : Real.log (L' / 4) ≤ ∫ u, Real.log |t - u| ∂(arcsineMeasure L') := by
    have h := Ulog_arcsineMeasure hL' ht.1.le
    rw [Ulog] at h
    rw [h]
    exact log_le_arcsinePotential hL'
  have hmono : ∫ u, ‖Real.log |t - u|‖ ∂(arcsineMeasure L') ≤
      ∫ u, (2 * (L + L') - Real.log |t - u|) ∂(arcsineMeasure L') :=
    integral_mono_ae hint.norm ((integrable_const _).sub' hint) hle
  rw [integral_sub (integrable_const (2 * (L + L'))) hint, integral_const, probReal_univ,
    one_smul] at hmono
  have hnn : 0 ≤ ∫ u, ‖Real.log |t - u|‖ ∂(arcsineMeasure L') :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hnn]
  linarith

/-! ### Mutual energies of two components -/

/-- The mutual energy of nested arcsine measures: for `0 < L ≤ L'`,
`∫∫ log |t - u| dω_{[0,L]}(t) dω_{[0,L']}(u) = log (L'/4)`, because the potential of
`ω_{[0,L']}` is the constant `log (L'/4)` on `[0, L'] ⊇ (0, L)`. -/
theorem integral_log_abs_sub_prod_arcsineMeasure_of_le {L L' : ℝ} (hL : 0 < L)
    (hLL' : L ≤ L') :
    ∫ p, Real.log |p.1 - p.2| ∂((arcsineMeasure L).prod (arcsineMeasure L')) =
      Real.log (L' / 4) := by
  have hL' : 0 < L' := hL.trans_le hLL'
  have := isProbabilityMeasure_arcsineMeasure hL
  rw [integral_prod _ (integrable_log_abs_sub_prod_arcsineMeasure hL hL')]
  have h : ∀ᵐ t ∂(arcsineMeasure L),
      ∫ u, Real.log |t - u| ∂(arcsineMeasure L') = Real.log (L' / 4) := by
    filter_upwards [ae_mem_Ioo_arcsineMeasure L] with t ht
    have h := Ulog_arcsineMeasure hL' ht.1.le
    rw [Ulog, arcsinePotential, ite_eq_left (ht.2.le.trans hLL')] at h
    exact h
  refine (integral_congr_ae h).trans ?_
  rw [integral_const, probReal_univ, one_smul]

/-- The mutual energy of two arcsine measures on nested intervals:
`∫∫ log |t - u| dω_{[0,L]}(t) dω_{[0,L']}(u) = log (max L L' / 4)`. The case `L' < L` reduces
to the case `L ≤ L'` by the symmetry `|t - u| = |u - t|` of the kernel. -/
theorem integral_log_abs_sub_prod_arcsineMeasure {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') :
    ∫ p, Real.log |p.1 - p.2| ∂((arcsineMeasure L).prod (arcsineMeasure L')) =
      Real.log (max L L' / 4) := by
  rcases le_total L L' with h | h
  · rw [max_eq_right h]
    exact integral_log_abs_sub_prod_arcsineMeasure_of_le hL h
  · rw [max_eq_left h, ← integral_log_abs_sub_prod_arcsineMeasure_of_le hL' h,
      ← integral_prod_swap (μ := arcsineMeasure L) (ν := arcsineMeasure L')]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show Real.log |p.swap.1 - p.swap.2| = Real.log |p.1 - p.2|
    rw [Prod.fst_swap, Prod.snd_swap, abs_sub_comm]

/-! ### The energy of the comparison measure -/

/-- The product measure `ρ ⊗ ρ` splits over pairs of arcsine components. -/
theorem compMeasure_prod_compMeasure :
    compMeasure.prod compMeasure = ∑ j, ∑ k,
      (ENNReal.ofReal (compWeight j) * ENNReal.ofReal (compWeight k)) •
        (arcsineMeasure (compEndpoint j)).prod (arcsineMeasure (compEndpoint k)) := by
  have h : compMeasure =
      Measure.sum fun j => ENNReal.ofReal (compWeight j) • arcsineMeasure (compEndpoint j) := by
    rw [Measure.sum_fintype]
    rfl
  rw [h, Measure.prod_sum, Measure.sum_fintype, Fintype.sum_prod_type]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- Each pair of components, weighted by `c_j c_k`, integrates the kernel `log |t - u|`. -/
theorem integrable_log_abs_sub_smul_prod_arcsineMeasure (j k : Fin 16) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((ENNReal.ofReal (compWeight j) * ENNReal.ofReal (compWeight k)) •
        (arcsineMeasure (compEndpoint j)).prod (arcsineMeasure (compEndpoint k))) :=
  (integrable_log_abs_sub_prod_arcsineMeasure (compEndpoint_pos j)
    (compEndpoint_pos k)).smul_measure
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- The kernel `log |t - u|` is integrable against `ρ ⊗ ρ`, so the Bochner integral defining
`I(ρ)` is the genuine energy (a non-integrable integrand would integrate to `0`). -/
theorem integrable_log_abs_sub_prod_compMeasure :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) (compMeasure.prod compMeasure) := by
  rw [compMeasure_prod_compMeasure, integrable_finsetSum_measure]
  intro j _
  rw [integrable_finsetSum_measure]
  intro k _
  exact integrable_log_abs_sub_smul_prod_arcsineMeasure j k

/-- Lemma 6.1 and Appendix A.1: the energy of the comparison measure as a sum over pairs of
components, `I(ρ) = Σ_j Σ_k c_j c_k log (max (L_j, L_k) / 4)`. -/
theorem Ilog_compMeasure_eq_sum_sum :
    Ilog compMeasure = ∑ j, ∑ k, compWeight j * compWeight k *
      Real.log (max (compEndpoint j) (compEndpoint k) / 4) := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 16)),
      Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) (∑ k,
        (ENNReal.ofReal (compWeight j) * ENNReal.ofReal (compWeight k)) •
          (arcsineMeasure (compEndpoint j)).prod (arcsineMeasure (compEndpoint k))) :=
    fun j _ => integrable_finsetSum_measure.2 fun k _ =>
      integrable_log_abs_sub_smul_prod_arcsineMeasure j k
  rw [Ilog, compMeasure_prod_compMeasure, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hint' : ∀ k ∈ (Finset.univ : Finset (Fin 16)),
      Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
        ((ENNReal.ofReal (compWeight j) * ENNReal.ofReal (compWeight k)) •
          (arcsineMeasure (compEndpoint j)).prod (arcsineMeasure (compEndpoint k))) :=
    fun k _ => integrable_log_abs_sub_smul_prod_arcsineMeasure j k
  rw [integral_finsetSum_measure hint']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure,
    integral_log_abs_sub_prod_arcsineMeasure (compEndpoint_pos j) (compEndpoint_pos k),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (compWeight_pos j).le,
    ENNReal.toReal_ofReal (compWeight_pos k).le, smul_eq_mul]

/-- Grouping a double sum by the smaller index: for `c g : Fin n → ℝ`,
`Σ_j Σ_k c_j c_k g(min j k) = Σ_i (T_i² - T'_i²) g_i`, where `T_i = Σ_{k ≥ i} c_k` and
`T'_i = Σ_{k > i} c_k`. -/
theorem sum_sum_mul_min {n : ℕ} (c g : Fin n → ℝ) :
    ∑ j, ∑ k, c j * c k * g (min j k) =
      ∑ i, ((∑ k with i ≤ k, c k) ^ 2 - (∑ k with i < k, c k) ^ 2) * g i := by
  have key : ∀ i, (∑ k with i ≤ k, c k) ^ 2 - (∑ k with i < k, c k) ^ 2 =
      ∑ j, ∑ k, if min j k = i then c j * c k else 0 := by
    intro i
    rw [Finset.sum_filter, Finset.sum_filter, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ite_zero_mul_ite_zero, ite_zero_mul_ite_zero]
    rcases lt_trichotomy i (min j k) with h | h | h
    · rw [ite_eq_left (le_min_iff.1 h.le), ite_eq_left (lt_min_iff.1 h), ite_eq_right h.ne',
        sub_self]
    · have h2 : ¬(i < j ∧ i < k) := fun h' => ne_of_lt (lt_min_iff.2 h') h
      rw [ite_eq_left (le_min_iff.1 h.le), ite_eq_right h2, ite_eq_left h.symm, sub_zero]
    · have h1 : ¬(i ≤ j ∧ i ≤ k) := fun h' => not_lt_of_ge (le_min_iff.2 h') h
      have h2 : ¬(i < j ∧ i < k) := fun h' => lt_asymm (lt_min_iff.2 h') h
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h.ne, sub_zero]
  have hpt : ∀ j k : Fin n,
      c j * c k * g (min j k) = ∑ i, (if min j k = i then c j * c k else 0) * g i := by
    intro j k
    have h0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ≠ min j k →
        (if min j k = i then c j * c k else 0) * g i = 0 := fun i _ hi => by
      rw [ite_eq_right (Ne.symm hi), zero_mul]
    rw [Finset.sum_eq_single_of_mem (min j k) (Finset.mem_univ _) h0, ite_eq_left rfl]
  calc ∑ j, ∑ k, c j * c k * g (min j k)
      = ∑ j, ∑ k, ∑ i, (if min j k = i then c j * c k else 0) * g i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hpt j k
    _ = ∑ j, ∑ i, ∑ k, (if min j k = i then c j * c k else 0) * g i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, (if min j k = i then c j * c k else 0) * g i := Finset.sum_comm
    _ = ∑ i, (∑ j, ∑ k, if min j k = i then c j * c k else 0) * g i := by
        simp only [Finset.sum_mul]
    _ = ∑ i, ((∑ k with i ≤ k, c k) ^ 2 - (∑ k with i < k, c k) ^ 2) * g i :=
        Finset.sum_congr rfl fun i _ => by rw [key i]

/-- Equation (110) for the comparison measure, with Table 1's intervals in decreasing order
`L_1 > ⋯ > L_16`: `I(ρ) = Σ_j (T_j² - T_{j+1}²) log (L_j/4)`, where `T_j = Σ_{k ≥ j} c_k` is the
mass of the components supported in `[0, L_j]` and `T_{j+1} = Σ_{k > j} c_k`. -/
theorem Ilog_compMeasure : Ilog compMeasure = ∑ j, ((∑ k with j ≤ k, compWeight k) ^ 2 -
    (∑ k with j < k, compWeight k) ^ 2) * Real.log (compEndpoint j / 4) := by
  have hmax : ∀ j k, Real.log (max (compEndpoint j) (compEndpoint k) / 4) =
      Real.log (compEndpoint (min j k) / 4) := fun j k => by
    rw [compEndpoint_strictAnti.antitone.map_min]
  rw [Ilog_compMeasure_eq_sum_sum]
  simp only [hmax]
  exact sum_sum_mul_min compWeight fun i => Real.log (compEndpoint i / 4)

/-! ### The constant `C*` and the bound (96) -/

/-- Equation (95): `C* = -2λ + 16αλ(1 - log α) + 3λ² - 2λ² log(2λ)` with `λ = 37/40` and
`α = 3/40` (`eAlpha`). -/
noncomputable def cStar : ℝ :=
  -2 * (37 / 40) + 16 * eAlpha * (37 / 40) * (1 - Real.log eAlpha) + 3 * (37 / 40) ^ 2 -
    2 * (37 / 40) ^ 2 * Real.log (2 * (37 / 40))

/-- Appendix A.4: direct evaluation of `C* = 3.649335…` from (95), within `10⁻⁶`, by the
Taylor bound for `log (1 - x)` at `x = 1/6` and `x = 3/40`. -/
theorem cStar_bounds : 3649334 / 1000000 < cStar ∧ cStar < 3649336 / 1000000 := by
  have h6 := Real.abs_log_sub_add_sum_range_le (x := 1 / 6) (by norm_num) 10
  have h40 := Real.abs_log_sub_add_sum_range_le (x := 3 / 40) (by norm_num) 10
  have e6 : ∑ i ∈ Finset.range 10, (1 / 6 : ℝ) ^ (i + 1) / (i + 1) =
      1157550169 / 6348948480 := by
    norm_num [Finset.sum_range_succ]
  have b6 : |(1 / 6 : ℝ)| ^ (10 + 1) / (1 - |(1 / 6 : ℝ)|) = 1 / 302330880 := by norm_num
  have e40 : ∑ i ∈ Finset.range 10, (3 / 40 : ℝ) ^ (i + 1) / (i + 1) =
      57224020915670943 / 734003200000000000 := by
    norm_num [Finset.sum_range_succ]
  have b40 : |(3 / 40 : ℝ)| ^ (10 + 1) / (1 - |(3 / 40 : ℝ)|) =
      177147 / 387973120000000000 := by norm_num
  rw [e6, b6, abs_le] at h6
  rw [e40, b40, abs_le] at h40
  have halpha : Real.log eAlpha = -Real.log (1 - 1 / 6) - 4 * Real.log 2 := by
    rw [show eAlpha = (1 - 1 / 6)⁻¹ / 2 ^ 4 by norm_num [eAlpha],
      Real.log_div (by norm_num) (by norm_num), Real.log_inv, Real.log_pow]
    norm_num
  have hlam : Real.log (2 * (37 / 40)) = Real.log 2 + Real.log (1 - 3 / 40) := by
    rw [show (1 : ℝ) - 3 / 40 = 37 / 40 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  obtain ⟨h6a, h6b⟩ := h6
  obtain ⟨h40a, h40b⟩ := h40
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  rw [cStar, halpha, hlam, eAlpha]
  constructor <;> linarith

/-- Exponents `m_j` with `2^{m_j} L_j / 4` close to `1`, for the enclosure of `log (L_j/4)`. -/
def logScale : Fin 16 → ℕ := ![2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 7, 8]

/-- `log x ≥ 1 - (2^m x)⁻¹ - m log 2`, the bound `log y ≥ 1 - y⁻¹` at `y = 2^m x`. -/
theorem one_sub_inv_sub_mul_log_two_le_log {x : ℝ} (hx : 0 < x) (m : ℕ) :
    1 - (x * 2 ^ m)⁻¹ - m * Real.log 2 ≤ Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (mul_pos hx (pow_pos two_pos m))
  rw [Real.log_mul hx.ne' (pow_ne_zero m two_ne_zero), Real.log_pow] at h
  linarith

/-- A rational lower bound for `Σ_j c_j log (L_j/4)` (the sum is `-2.7522…`). -/
theorem neg_lt_sum_compWeight_mul_log :
    -2771 / 1000 < ∑ j, compWeight j * Real.log (compEndpoint j / 4) := by
  have hle : ∑ j, compWeight j *
        (1 - (compEndpoint j / 4 * 2 ^ logScale j)⁻¹ - logScale j * Real.log 2) ≤
      ∑ j, compWeight j * Real.log (compEndpoint j / 4) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (one_sub_inv_sub_mul_log_two_le_log (div_pos (compEndpoint_pos j) four_pos) _)
      (compWeight_pos j).le
  have hval : -2771 / 1000 < ∑ j, compWeight j *
      (1 - (compEndpoint j / 4 * 2 ^ logScale j)⁻¹ - logScale j * Real.log 2) := by
    have hl := Real.log_two_lt_d9
    norm_num [Fin.sum_univ_succ, compWeight, tableCNum, compEndpoint, tableLNum, logScale]
    linarith
  linarith

/-- Each mutual energy is at least `log (L_j/4)`, so `I(ρ) ≥ λ Σ_j c_j log (L_j/4)`. -/
theorem mul_sum_compWeight_mul_log_le_Ilog :
    (37 / 40 : ℝ) * ∑ j, compWeight j * Real.log (compEndpoint j / 4) ≤ Ilog compMeasure := by
  rw [Ilog_compMeasure_eq_sum_sum, ← sum_compWeight, mul_comm (∑ k, compWeight k),
    Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  have hlog : Real.log (compEndpoint j / 4) ≤
      Real.log (max (compEndpoint j) (compEndpoint k) / 4) :=
    Real.log_le_log (div_pos (compEndpoint_pos j) four_pos)
      (div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num))
  have hc : 0 ≤ compWeight j * compWeight k :=
    mul_nonneg (compWeight_pos j).le (compWeight_pos k).le
  calc compWeight j * Real.log (compEndpoint j / 4) * compWeight k
      = compWeight j * compWeight k * Real.log (compEndpoint j / 4) := by ring
    _ ≤ compWeight j * compWeight k * Real.log (max (compEndpoint j) (compEndpoint k) / 4) :=
      mul_le_mul_of_nonneg_left hlog hc

/-- Equation (96): `λM_0 - I(ρ) + C* ≤ U = 44/25`, with `λ = 37/40` and `M_0 = -109/20`. -/
theorem energy_norm_bound :
    (37 / 40 : ℝ) * (-109 / 20) - Ilog compMeasure + cStar ≤ 44 / 25 := by
  have hI := mul_sum_compWeight_mul_log_le_Ilog
  have hS := neg_lt_sum_compWeight_mul_log
  have hC := cStar_bounds.2
  linarith

end ZetaSeven
