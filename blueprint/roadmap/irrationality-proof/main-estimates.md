---
article_id: af_b1c6c61b863767b94db5e919
declaration: theorem
origin: cited
---

# Main polynomial estimates

For each admissible `M` and `K`, the polynomial `Q_{K,M}` is
integral of degree `h`, positive at `ζ(7)`, and for large `n`
satisfies `0 < Q_{40n,200}(ζ(7)) < exp(-19000n^2)` and the
same bound at cutoff `100000`.

The proof combines integrality, degree, and positivity with
the decay inequality from the prime-sum and real bounds,
substitutes `K = 40n`, and evaluates both cutoffs through the
certified rational margins. The `-19000` constant at `M = 200`
is the approved target; source-map open question 5 records that
the final rational margins it rests on fail with the recomputed
outer integral, so this proof route does not close as stated.

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
  margins fail, so this node has no proof route as stated; what to
  do about its statement is the user's decision.
