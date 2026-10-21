# Zeta 7 preprint source map

Prince Anand, *Zeta 7 is Irrational*, preprint v1, 23 September 2026.
Stable public record: [Zenodo 22920911](https://zenodo.org/records/22920911)
(DOI `10.5281/zenodo.22920911`), file `Zeta7 (3).pdf`
(md5 `6b7fae049a3f5970a45f51483098b521`, 42 PDF pages).
Local vault copy: `Zeta7 (3).pdf` in this directory (md5 verified 2026-10-13).

This is the adopted source for the whole roadmap. Every formalizable
statement must trace to a locator below. Section, theorem, and equation
numbers are the stable locators; PDF page numbers refer to the v1 file
above and are given only to speed up lookup.

## Version note

The v1 record carries an author note: the proof of Theorem 1.2 at (118)
establishes `A200 + U < -11`, i.e. decay faster than `exp(-17600n^2)`
for `M = 200`, while the abstract claims `exp(-19000n^2)`. The author
states the `-19000` bound follows with `-11.99` in place of `-11`
(giving `-19184` after the `1600x` scaling) and will be fixed in v2.
The main polynomial estimates node keeps the abstract's `-19000` for
`M = 200` in its prose (open question 1, now superseded) but has no
Lean statement (`not_ready: true`). The final-margins node states, with
exact arithmetic, that `A_M + U > 0` at every cutoff, so neither `-11`
nor `-11.99` is reached (open question 5).

## Locator map

| Roadmap target | Source locator |
| --- | --- |
| Main theorem zeta(7) irrational | Theorem 1.1, Section 1.1 (p. 3); proved in Appendix B.2 (p. 34) |
| Polynomial estimates | Theorem 1.2, Section 1.1 (pp. 3-4); restated as Theorem 2.5, Section 2.6 (p. 9) |
| Approximation bound | Corollary 1.3, Section 1.1; proved in Appendix B.2 (pp. 40-41) |
| Construction overview | Section 1.3 (pp. 4-5) |
| Parameters and notation | Section 2.1, equations (3)-(4) (p. 5) |
| Functional mu_X | Definition 2.1, equations (5)-(6) (p. 5) |
| Matrix G_K, determinant Delta_K, Q_K,M | Definition 2.2, equations (7)-(9) (pp. 5-6) |
| Degree of Delta_K | Lemma 2.3, equations (10)-(15) (pp. 6-7) |
| Positive integral representation | Proposition 2.4, equations (16)-(19) (pp. 7-8) |
| Auxiliary functional tau_X, pullback | Section 3.1, equations (24)-(28); Lemma 3.1 (pp. 9-10) |
| Reflection and difference identities | Lemmas 3.2-3.3, equations (29)-(30) (pp. 11-12) |
| p-adic completion | Lemmas 3.4-3.5, equations (32)-(33) (pp. 12-13) |
| Distribution formula | Lemmas 3.6-3.7, equations (34)-(36) (pp. 14-15) |
| Small-prime estimate, integer-valued basis | Lemma 3.8, equations (37)-(41) (pp. 15-16) |
| Local range data: half-range, class counts | Section 4, opening paragraph, equations (42)-(43) (p. 17) |
| Inner-range estimate | Proposition 4.4, equations (44)-(51) (pp. 17-19), with (42)-(43) |
| Outer range data | Section 4.2, outer-range hypothesis (52), equations (54), (56), (58)-(59) (pp. 19-21); Section 5.1, first sentence, `γ^out_p = 0` for `p > K` (p. 22) |
| Outer moment integrality | Lemma 3.4 with (24) (pp. 9, 12); Section 4.2.1, first paragraph (pp. 19-20) |
| Outer modified functional | Section 4.2.1, second paragraph (`c_e`, `µ_0`) and (53) (p. 20) |
| Outer rank decomposition, rank lemma, Gauss-valuation form | Section 4.2.1, equations (53)-(54); Lemma 4.5, (55), and its last sentence (pp. 20-21) |
| Paired-pole congruence | Proof of Proposition 4.6, "the two remaining pole values at `a` and `p − a` are integral and congruent modulo `p`", and the case `p > K` (p. 21); erratum 7 |
| Large-prime integrality | Proposition 4.6 and its proof, case `p > K` (p. 21); erratum 7 |
| Outer class rows | Proof of Proposition 4.6, the rows `P_a q_{a,i}` with `q_{a,i}`, `E_a`, and the zero-class rows (p. 21); `P_a` and the zero-class rows reconstructed |
| Outer class basis | Proof of Proposition 4.6, "these form a `Z_p`-unimodular basis" (p. 21); reconstructed |
| Outer weight family | Equation (56) and the proof of Proposition 4.6 (p. 21); zero-class weights reconstructed |
| Outer entry valuations | Proof of Proposition 4.6, the residue bound `i + j + 8δ - ℓ - 6` (p. 21); reconstructed |
| Outer weight sum | Equations (56)-(59) and the proof of Proposition 4.6, "Applying Lemma 4.5 to the weights (56) and summing over classes yields `γ^out_p`" (p. 21); reconstructed |
| Outer-range estimate | Proposition 4.6, equations (52)-(59) (pp. 19-21); assembled from the rows above |
| Normalization factor, integrality | Section 5.1, first sentence; equations (60)-(62); Proposition 5.1 (p. 22) |
| Inner limiting function | Section 5.2, equations (64)-(70) (pp. 22-23) |
| Outer limiting function | Section 5.3, equations (71)-(73) and its last sentence (pp. 23-24); outer-range step of the proof of Proposition 5.4 (p. 26); erratum 8 |
| Tail integral | Section 5.4, equations (74)-(86) (pp. 24-25) |
| Prime-sum bound | Proposition 5.4, equations (87)-(90) (pp. 25-26) |
| External field | Section 6.1, equations (91)-(93) (p. 27) |
| Comparison measure | Lemma 6.1, equations (94)-(96) (p. 27); Appendix A.1-A.4 (pp. 30-33) |
| Zero-mass logarithmic energy | Lemma 6.2 (pp. 27-28) |
| General configuration bound | Section 6.4, equations (97)-(100) (pp. 28-29) |
| Andreief identity and scaling | Section 6.5, equations (101)-(104) (p. 29) |
| Real bound | Proposition 6.3, equations (105)-(108) (p. 30) |
| Comparison-measure tables | Appendix A.1, Table 1 (pp. 30-31) |
| Elementary enclosures | Appendix A.2, equations (111)-(112) (pp. 31-32) |
| Potential inequality | Appendix A.3, equations (113)-(116) (p. 32) |
| Assembly of Theorems 1.1-1.2 | Appendix B.1-B.2, equations (117)-(119) (pp. 33-34) |
| Exact inner integral, 192 affine pieces | Equations (120)-(121); Tables 2-4 (pp. 34-38) |
| Exact outer integral | Equation (122); Table 5 (pp. 35, 39); recomputed in erratum 9 |
| Final rational margins A200, A100000 | Appendix A.3 (p. 35) |
| Relative matrix norm | Proposition B.1, equations (123)-(127) (pp. 39-40) |
| Coefficient height, primitive normalization | Appendix B.3, equation (129) (p. 41) |

Labels locate the authoritative statements; chapter prose is a planning
aid and must not replace source inspection. Note the paper reuses the
appendix labels A.1-A.3 and B.1-B.2: one series for the
comparison-measure appendices (pp. 30-33) and a second series for the
exact-integral and matrix-norm appendices (pp. 34-41). The page
numbers above and the `comparison-measure` / `exact-integral` prefixes
in article citations disambiguate them.

## Open source questions

1. SUPERSEDED (2026-10-21; see the end of this item and open
   question 5): the earlier decision was to formalize `-19000` for
   `M = 200`. The v1 proof text
   derives only `1600(A200 + U) < -17600` (and states `-17000`),
   so `-19000` needs `A200 + U < -95/8`, which the exact values
   refute; see the `final-margins` node. The paper's printed values
   (`A200 ~ -13.7528`, `U = 44/25`) would leave a margin of about
   `0.118`, but they rest on the printed (122).
   NOTE (2026-10-18): the dispute of open question 5 is now
   verified. With the recomputed outer integral `A200 + U` is
   positive, so the `-19000` target cannot be met, nor can the
   paper's own (118), while open question 5 stands. DECIDED
   (2026-10-21): the `final-margins` node now states the failure;
   `main-estimates` keeps the `-19000` of Theorem 1.2 (1) in its prose
   statement but has no Lean statement (`not_ready: true`); see open
   question 5.
2. The Fauzan zeta(5) predecessor [5] is cited for the architecture but
   has not been inspected; confirm no hidden lemma is imported from it.
   PARTLY ANSWERED (2026-10-18): the proof of Proposition 4.6 defers
   the class rows, the zero-class weights, and the derivation of (59)
   to [5]; these are reconstructed as bridged nodes in the local
   arithmetic chapter. The residue bounds (50)-(51) of Proposition 4.4
   are also deferred to [5, Section 4.1], but Proposition 4.4 is proved
   in Lean (`ZetaSeven.inner_estimate` on main at `9487e76`, whose CI
   kernel-trust audit, run 39160466154, passed allowing only `propext`,
   `Classical.choice`, and `Quot.sound`), so no hidden lemma from [5]
   is needed for it. Proposition 4.6 is likewise proved in Lean
   (`ZetaSeven.outer_estimate`) through the reconstructed nodes, so no
   hidden lemma from [5] is needed for it either.
3. RESOLVED except Hermite/Hurwitz: von Staudt-Clausen is upstream
   (`Bernoulli.vonStaudt_clausen`), Bernoulli multiplication and Andreief
   were proved directly in Lean. Hermite/Hurwitz verdict (2026-10-17):
   no Hermite integral, Euler-Maclaurin, Abel-Plana, or periodic/Lerch
   zeta formula exists in the pinned Mathlib checkout (only special
   values in `HurwitzZetaValues`), so the `s = 7` instance is project
   work to prove directly (see the `hermite-hurwitz` node).
4. Decide whether the 192-piece exact integral tables are recomputed in
   Lean or verified as certificates.
5. VERIFIED (2026-10-18): an external reader report (gmDevi/zeta-7-21-lean
   issue #1, 2026-10-03) and an independent exact-arithmetic audit
   (Toledo cert-machine, record archived at Zenodo 23171167) recompute
   the outer integral from the paper's own formulas as
   `I_out = 453803/288000` (not (122)'s `-11002997/720000`) and
   `A200 + U ~ +4.86` (not `-11.99`), which breaks the v1 proof route at
   (117)-(118). The project has checked this, and no author v2 has
   appeared:
   - The outer integral recomputes exactly to `453803/288000`, matching
     the external audit, and no reading tried reproduces (122)
     (errata 8 and 9).
   - The inner side checks out: `R(x)` from Definition 5.2 matches
     Table 2 at spot checks, and `∫_3^20 R(x)/x^3 dx` recomputes
     numerically to `0.17035`, matching (121).
   - `A0 = 1.3175` is a valid but loose upper bound for the tail: the
     integral of `R(x)/x^3` over `[20, ∞)` is about `-0.064`, both
     numerically and from (85) at `T = 20`.
   - With the corrected `I_out`, `A200 + U ≈ +4.86`, or about `+3.5`
     with the true tail in place of `A0`. So (118), `A200 + U < -11`,
     fails, and the v1 route to Theorems 1.1-1.2 does not close.
     (119) fails in the same way: `A100000 + U ≈ +4.82`.

   DECIDED (2026-10-21): the `final-margins` node now states the
   failure with exact arithmetic: `B0` and `A200 + U` as exact
   rationals, and `A_M + U > 0` for every `M > 0`, so no choice of
   cutoff makes the right side of (117) negative. `main-estimates`
   and `main-theorem` get no Lean statement: they record
   `not_ready: true`, with notes that they have no known proof
   route.

## Errata found during formalization

Only items confirmed independently of the paper's own text are listed:
by exact or high-precision recomputation from the paper's definitions
and Tables 1-4, or by a Lean proof. Items 1-8 and 10-14 do not break the
main theorem as far as the formalization has checked; item 8 is resolved
in favor of the reading that the proof of Proposition 5.4 uses. Item 9
does: with the recomputed outer integral, (118) fails and the v1
route to Theorems 1.1-1.2 does not close (open question 5).

1. Section 4.2.1, (53): the claim that `A` is integral at every prime
   is false as written. In the monomial basis, pole values
   `j^6 H^(7)_j` with `p < j ≤ K`, `p ∤ j`, can have valuation `-7`,
   and by exact rational computation at `n = 1`, `p = 17`, the
   `X`-free coefficients of `A` reach valuation `-10`. Proposition
   4.6 itself is not contradicted: at `n = 1` the exact `Δ_K` meets
   `γ^out_p` at every prime satisfying (52). The
   [outer range estimate](../roadmap/local-arithmetic/outer-estimate.md)
   proves it in Lean (`ZetaSeven.outer_estimate`) through a class
   basis with weights instead of (53): the reconstructed class rows,
   their unimodularity, the weighted entry valuations, the
   Gauss-valuation rank lemma, and the weight sum, each its own
   proved node. Before the proof, the route was checked numerically:
   the exact `Δ_K` valuations at `n = 1`, the rank decomposition at
   `n = 1`, the class basis and the entry valuations at every
   `n ≤ 5`, and the weight sum for every `n ≤ 60`.
2. Section 6.4, (99): the coefficient `13/10` is false. Recomputing
   `2U_ρ(t) - V(t)` at 40 significant digits from Table 1, (109), and
   (113), the bound first fails near `t ≈ 3.535` and fails at every
   larger `t` checked (up to `3·10^7`); at `t = 4` the left side is
   about `-10.7226` and the right side about `-10.7633`. The correct
   bound past 2 is
   `2U_ρ(t) - V(t) ≤ (29/20) log t + 8α^3/t - 2π√t`, with
   `29/20 = 2λ - 1 + 8α`, proved in the
   [potential inequality](../roadmap/real-bound/potential-inequality.md)
   node. With it, (94) and the retained-factor inequality (98) still
   hold.
3. Appendix A.1 (110) and Appendix A.4: the energy formula uses the
   prefix sums `S_j = c_1 + ⋯ + c_j`, which is correct only for
   increasing `L_j`; Table 1 lists the `L_j` in decreasing order, so the
   tail sums `T_j = c_j + ⋯ + c_16` are needed. The true value is
   `I(ρ) ≈ -1.9482` (printed `-3.1433`) and
   `λM_0 - I(ρ) + C* ≈ 0.556` (printed `1.751`), so (96) still holds,
   with more margin. The
   [energy computation](../roadmap/real-bound/energy-computation.md)
   node records the tail-sum form.
4. Appendix A.3, below (113): `V(0) = -16α log α - 2 + 16α`, not
   `-8α log α - 2 + 16α`.
5. Section 6.2 and Appendix A.3: the reported numerical values do not
   match Table 1. Recomputed at 40 significant digits from Table 1,
   (109), and (113): the true maximum of `2U_ρ - V` on `[0, 2]` is
   about `-6.613`, near `t ≈ 0.214` (Section 6.2 prints `-5.4719` at
   `t ≈ 0.2648`, where the value is about `-6.620`); the worst
   interval bound (115) before `L_1` is about `-6.186` on
   `[0.3, 0.4]` (printed `-5.865`), and after subdividing `[L_1, 2]`
   into eight pieces about `-6.555`, on the first piece (printed
   `-5.689`). (94) holds with more margin than reported.
6. Section 3.3, proof of Lemma 3.5: the sentence "`τ(f) ∈ ℤ_p` when
   `‖f‖ ≤ 1`, by Lemma 3.4" is false. Lemma 3.4 gives only
   `|τ(f)|_p ≤ p‖f‖`, and `κ_41` at `p = 7` has `v_7(κ_41) = -1`
   (`7 - 1` divides `36`, and no factor of `41·40·39·38·37` is a
   multiple of `7`). Lemma 3.5 itself holds: the `j = 0` term has
   degree at most `p + 4`, where Lemma 3.4 gives integrality, and the
   `j ≥ 1` terms carry the factor `p^j`; the
   [p-adic completion](../roadmap/local-arithmetic/completion.md) node
   is proved.
7. Section 4.2, proof of Proposition 4.6, case `p > K`: the sentence
   "the residues are `p`-integral" is false as written. For poles
   `a` and `p - a` both in `(N, K]`, the factor
   `(p - a)^2 - a^2 = p(p - 2a)` of the derivative of `D_K/D_N` puts
   a `p` in the denominator of each of the two residues; only their
   sum is `p`-integral, and since the two pole values are congruent
   modulo `p`, so is the pair's contribution. By exact rational computation
   at `n = 1`, `p = 41`, for `a = 4, 10, 20` and `i + j = 0, 5`, each
   residue has `v_41 = -1`, while each pair sum of residues and each
   pair contribution to the entry has `v_41 = 0`. The conclusion
   `v^G_p(Δ_K) ≥ 0` is not contradicted; the
   [large-prime integrality](../roadmap/local-arithmetic/large-prime-integrality.md)
   node proves the entrywise integrality behind it with this
   pairing, which the
   [paired-pole congruence](../roadmap/local-arithmetic/paired-pole-congruence.md)
   node states, and the
   [outer range estimate](../roadmap/local-arithmetic/outer-estimate.md)
   derives the determinant bound from it.
8. Section 5.3, (71): the definition
   `R_0(y) = lim -γ^out_p/K` contradicts the last sentence of
   Section 5.3 ("Formula (59) gives
   `-γ^out_p = K(R_0(p/K) - d(p/K)) + O(1)` uniformly in the outer
   range") and the outer-range step of the proof of Proposition 5.4
   (`L_p = v_p(S_K) + γ^out_p = -K(R_0 - d - 2λ⌊1/y⌋ + ∑_j (2λ - jy)_+) + O(1)`),
   which both use `R_0 - d = lim -γ^out_p/K`. So the proof of
   Proposition 5.4 (its `L_p` identity) and the last sentence of
   Section 5.3 use the second reading. Under (71) that proof is off
   by the integral of `d`, which is `3/100`: the outer contribution
   to the prime sum exceeds the integral (73) by that amount, and
   (90) would then rest on the slack in `A_0` (the printed
   `A_0 = 1.3175` is about `1.38` above the true tail, about
   `-0.064`, which absorbs the `3/100`). The
   [outer limiting functions](../roadmap/normalization-prime-sum/outer-limiting.md)
   node adopts the second reading, `R_0 = g + d` with
   `g = lim -γ^out_p/K` and `γ^out_p = 0` for `p > K`. By exact
   rational computation from (54), (58), (59), (72), and (73),
   `I_out = 453803/288000` under the adopted reading and
   `445163/288000` under (71) read literally; neither is (122)'s
   value (see open question 5). Evidence that does not depend on how
   `R_0` and `d` are read: the outer contribution computed directly
   from (59) and (62), `-K^{-2} ∑_{K/3 < p ≤ 2h} L_p log p`, is
   `1.5717`, `1.5744`, and `1.5751` at `K = 10^5`, `10^6`, and `10^7`,
   approaching `453803/288000 ≈ 1.5757`, not `445163/288000 ≈ 1.5457`.
9. Appendix A.2, (122) and Table 5: the outer integral
   `I_out = -11002997/720000 ≈ -15.2819` and the nine affine pieces
   of Table 5 do not follow from the paper's definitions.
   Recomputed exactly from (54), (58), (59), (72), and (73), with
   `γ^out_p = 0` for `p > K` (Section 5.1) and `R_0` read as in
   erratum 8, the integrand is affine on 11 pieces and
   `I_out = 453803/288000 ≈ 1.5757`, which matches the external
   audit of open question 5. Of Table 5's pieces only `1 - 2y` on
   `[77/80, 1]` agrees; on `[1, 37/20]`, for example,
   `γ^out_p = 0` and the integrand is the scalar term `37/20 - y`,
   where Table 5 prints `-239/20 - 2y`. No reading tried reproduces
   (122), about `-15.28`. With `γ^out_p = 0` for `p > K`, changing
   the sign of, or dropping, the `γ^out_p` limit `g`, the correction
   `d` (taken up to twice), or the scalar term comes no closer than
   `-471083/288000 ≈ -1.64` (`-g - 2d` minus the scalar term). The
   values near `-2.5` (about `-2.47` and `-2.50`, for `g - d` and
   `g - 2d` minus the scalar term) also need (59) extended to
   `p > K`, an extension that by itself gives `-635917/288000`; (71)
   read literally gives `445163/288000`. The
   [exact outer integral](../roadmap/normalization-prime-sum/exact-outer-integral.md)
   node states the recomputed value and its 11 pieces.
10. Section 6.5, (102) and (104): both printed bounds are true, and
    the [Andreief scaling](../roadmap/real-bound/andreief-scaling.md)
    node proves them in Lean, but the paper's derivations do not reach
    the printed constants. For (102), the closed form of
    `∑ ℓ^6 q^ℓ` with `1 - e^{-u} ≥ u/(1+u)` gives only about
    `2^7 π^6 ≈ 1.2·10^5` in place of `8192` for large `y`; the Lean
    proof splits off the `ℓ = 1` term and bounds the rest with
    `x^6 e^{-x} ≤ 6!`. For (104), the chain from (102) and (103) as
    written gives `K^{2h(h+8N-K)+22h} (4096 e^{16})^h`; the printed
    `K^{2h(h+8N-K)+16h} (4096 e^{12})^h` needs the sharper bound
    `log N + 2` for the difference in (103) at `m = N`, which follows
    from Stirling's formula. (105) is unaffected.
11. Section 5.4, (82)-(83) and (86): in (82) the coefficient of
    `∫_0^{1/2} B(z)^2 dz` is `16`, not `25`, because `b = 4ℓ(αx, z)`
    contributes `-16B^2` to the integrand of (66); with `25` the
    decomposition (80) is off by `9∫B^2 = 9d({αx})(1 - 2d({αx}))`,
    which is nonzero whenever `2αx` is not an integer, and with `16`
    it holds exactly, consistently with Tables 2-4 and (121). The
    bounds (83), `-1/2 ≤ Q ≤ 27/8`, hold (the true range of `Q` is
    `[0, 9269/3698]`), but the printed termwise argument reaches
    only `-5/8` for the lower bound, and its upper-bound arithmetic
    `25/8 + 1/4` is not a valid termwise bound either; with `16` the
    termwise upper bound is `1/8 + 2 + 1/2 = 21/8`, and the lower
    bound follows from `|∫AB| ≤ ∫B^2` from (78)-(79). (86) holds for
    `M ∈ 40ℤ_{>0}`, as the paper assumes; the hypothesis cannot be
    dropped: (86) fails at every `M ≡ 20 (mod 40)`, for example at
    `M = 20`, `60`, and `100`. The
    [tail integral bound](../roadmap/normalization-prime-sum/tail-integral.md)
    node states the corrected forms.
12. Appendix A.1, Tables 2-4: `R(x) = a_i x + b_i` holds on the open
    intervals `(t_i, t_{i+1})` but not on the closed ones: `R` jumps
    at `x = 4, …, 19`, `40/3`, and `20`, so the closed-interval claim
    fails at 18 endpoints. The cut-point set also yields 61 redundant
    cuts: `R` has 131 distinct affine pieces on `[3, 20]`. Every row
    agrees with Definition 5.2 on its interior, and (121) recomputes
    exactly. The
    [exact inner integral](../roadmap/normalization-prime-sum/exact-inner-integral.md)
    node states the identities on open intervals.
13. Section 3.5, before (41): the pullback numerator `A_ij` in the
    `f`-basis has degree `16N + 4h + 4` (the paper says at most
    `16N + 4h + 5`), and the paper's inequality `max(2K, d+1) ≤ 5K`
    fails at `n = 1`, where `d + 1 = 201 > 200 = 5K`. The slip is
    harmless: `⌊log_p⌋` takes the same value at 200, 201 and 202 for
    every prime `p`, and the
    [small-prime estimate](../roadmap/local-arithmetic/small-prime-estimate.md)
    node applies the bound with the logarithm at `5K ≥ max(2K, d)`,
    so (41) holds as stated for every `n ≥ 1`.
14. Section 5.5, (87)-(88) and the proof of Proposition 5.4: the
    proof writes `B_0 = A_0 + I_out + ∫_3^20 R/x^3 dx` "with
    `A_0 = ∫_20^∞ R/x^3 dx` bounded in Appendix A", but the printed
    rational `A_0 ≈ 1.3175` is not that integral, which is about
    `-0.0642`, and Appendix A gives no bound. The proof only needs
    `∫_20^∞ R(x)/x^3 dx ≤ A_0`, which holds: (85) at `T = 20`, with
    `P(20) = 74/3`, `C(20) = 0`, `|C| < 22`, and `Q ≤ 27/8`, gives
    `∫_20^∞ R(x)/x^3 dx ≤ -2069/36000`. The
    [prime-sum bound](../roadmap/normalization-prime-sum/prime-sum-bound.md)
    node is to prove this inequality as a step of (90).
