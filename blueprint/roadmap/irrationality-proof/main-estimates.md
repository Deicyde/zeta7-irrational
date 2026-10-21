---
article_id: af_b1c6c61b863767b94db5e919
declaration: theorem
origin: cited
not_ready: true
---

# Main polynomial estimates

For each admissible `M` and `K`, the polynomial `Q_{K,M}` is
integral of degree `h`, positive at `ζ(7)`, and for large `n`
satisfies `0 < Q_{40n,200}(ζ(7)) < exp(-19000n^2)` and the
same bound at cutoff `100000`. Here admissible means
`M, K ∈ 40ℤ_{>0}` with `K ≥ 200M^2`, as in Proposition 5.1.

The planned proof combines integrality, degree, and positivity
with the decay inequality from the prime-sum and real bounds,
substitutes `K = 40n`, and evaluates both cutoffs through the
final rational margins, which for the constant `-19000` at
`M = 200` would need `A_200 + U < -95/8`. That route does not
close: the final rational margins give `A_M + U > 0` at every
cutoff, so the prime-sum and real bounds yield no decay, and no
other proof route is known.

## Depends on

- [Degree lemma](../determinant-construction/degree-lemma.md)
- [Positive integral representation](../determinant-construction/positive-integral-representation.md)
- [Normalization and integrality](../normalization-prime-sum/normalization-integrality.md)
- [Prime-sum bound](../normalization-prime-sum/prime-sum-bound.md)
- [Real bound](../real-bound/real-bound.md)
- [Final rational margins](../normalization-prime-sum/final-margins.md)

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  Sections 1.1, 2.6, B.1, Theorems 1.2 and 2.5,
  equations (1)-(2), (20)-(21), (117)-(119).
- [Open question 5](../../sources/zeta7-preprint.md#open-source-questions):
  with the recomputed outer integral (erratum 9) the final rational
  margins fail at every cutoff, so this node has no known proof
  route.
