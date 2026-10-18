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
The roadmap tracks the v1 statements as written and records the
discrepancy as an open source question below; do not silently upgrade
the `M = 200` constant.

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
| Inner-range estimate | Proposition 4.4, equations (42)-(51) (pp. 17-19) |
| Outer rank bound and rank lemma | Equations (53)-(55), Lemma 4.5 (pp. 20-21) |
| Outer-range estimate | Proposition 4.6, equations (56)-(59) (p. 21) |
| Normalization factor, integrality | Equations (60)-(62); Proposition 5.1 (p. 22) |
| Inner limiting function | Section 5.2, equations (65)-(70) (p. 23) |
| Outer limiting function | Section 5.3, equations (71)-(73) (pp. 23-24) |
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
| Exact outer integral | Equation (122); Table 5 (pp. 35, 39) |
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

1. DECIDED: formalize `-19000` for `M = 200`. The v1 proof text
   derives only `1600(A200 + U) < -17600` (and states `-17000`),
   so `-19000` needs `A200 + U < -95/8`, proved by exact rational
   arithmetic from the integral tables. The exact values
   (`A200 ~ -13.7528`, `U = 44/25`) leave margin `~0.118`, so the
   certificate is expected to close; see the `final-margins` node.
   NOTE (2026-10-13): an external exact-arithmetic audit disputes the
   Table 5 integral this target rests on (see open question 5). The
   `-19000` decision stands until the project adjudicates it.
2. The Fauzan zeta(5) predecessor [5] is cited for the architecture but
   has not been inspected; confirm no hidden lemma is imported from it.
   PARTLY ANSWERED (2026-10-18): the proof of Proposition 4.6 defers
   the class rows, the zero-class weights, and the derivation of (59)
   to [5]; these are reconstructed as bridged nodes in the local
   arithmetic chapter. The residue bounds (50)-(51) of Proposition 4.4
   are also deferred to [5, Section 4.1] and remain to be checked.
3. RESOLVED except Hermite/Hurwitz: von Staudt-Clausen is upstream
   (`Bernoulli.vonStaudt_clausen`), Bernoulli multiplication and Andreief
   were proved directly in Lean. Hermite/Hurwitz verdict (2026-10-17):
   no Hermite integral, Euler-Maclaurin, Abel-Plana, or periodic/Lerch
   zeta formula exists in the pinned Mathlib checkout (only special
   values in `HurwitzZetaValues`), so the `s = 7` instance is project
   work to prove directly (see the `hermite-hurwitz` node).
4. Decide whether the 192-piece exact integral tables are recomputed in
   Lean or verified as certificates.
5. UNADJUDICATED: an external reader report (gmDevi/zeta-7-21-lean issue
   #1, 2026-10-03) and an independent exact-arithmetic audit (Toledo
   cert-machine, record archived at Zenodo 23171167) recompute the outer
   integral from the paper's own formulas as `I_out = 453803/288000`
   (not (122)'s `-11002997/720000`) and `A200 + U ~ +4.86` (not `-11.99`),
   which would break the v1 proof route at (117)-(118). The project has
   not verified these recomputations, and no author v2 has appeared.
   Directly implicates the `exact-outer-integral`, `final-margins`, and
   `main-estimates` nodes.

## Errata found during formalization

Only items confirmed independently of the paper's own text are listed:
by exact or high-precision recomputation from the paper's definitions
and Table 1, or by a Lean proof. None of these items breaks the main
theorem as far as the formalization has checked; the unadjudicated
dispute in open question 5 is separate.

1. Section 4.2.1, (53): the claim that `A` is integral at every prime
   is false as written. In the monomial basis, pole values
   `j^6 H^(7)_j` with `p < j ≤ K`, `p ∤ j`, can have valuation `-7`,
   and by exact rational computation at `n = 1`, `p = 17`, the
   `X`-free coefficients of `A` reach valuation `-10`. Proposition
   4.6 itself is not contradicted: at `n = 1` the exact `Δ_K` meets
   `γ^out_p` at every prime satisfying (52). The
   [outer range estimate](../roadmap/local-arithmetic/outer-estimate.md)
   plans to prove it through a class basis with weights instead of
   (53). That route is a reconstruction checked numerically, not yet
   a proof: the exact `Δ_K` valuations at `n = 1`, the rank
   decomposition at `n = 1`, the class basis and the entry
   valuations at every `n ≤ 5`, and the weight sum for every
   `n ≤ 60`.
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
   node plans to prove it with this pairing.
