# Zeta 7 preprint source map

Prince Anand, *Zeta 7 is Irrational*, preprint v1, 23 September 2026.
Stable public record: [Zenodo 22920911](https://zenodo.org/records/22920911)
(DOI `10.5281/zenodo.22920911`), file `Zeta7 (3).pdf`
(md5 `6b7fae049a3f5970a45f51483098b521`, 42 PDF pages).

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
aid and must not replace source inspection.

## Open source questions

1. Which decay constant to formalize for `M = 200`: the proved v1
   `-17600` or the abstract's `-19000` pending the author's v2 fix.
2. The Fauzan zeta(5) predecessor [5] is cited for the architecture but
   has not been inspected; confirm no hidden lemma is imported from it.
3. Background identities (Hermite/Hurwitz integral, von Staudt-Clausen,
   Bernoulli multiplication, Andreief) still need a Mathlib audit before
   bridging lemmas are planned.
4. Decide whether the 192-piece exact integral tables are recomputed in
   Lean or verified as certificates.
