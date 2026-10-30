# Zeta 7 is Irrational

This project formalizes Anand's preprint "Zeta 7 is Irrational"
([Zenodo 22920911](https://zenodo.org/records/22920911)), which claims ζ(7)
is irrational via integer Hankel-determinant polynomials with an explicit
irrationality measure.

**Status:** the formalization is finished as an audit. The paper's final step
fails: its printed outer integral (122) is wrong, and with the recomputed value
the quantity `A_M + U`, which the argument needs to be negative, is positive at
every integer cutoff `M ≥ 1`, as the
[final rational margins](roadmap/normalization-prime-sum/final-margins.md) node
proves in Lean. Theorems 1.1 and 1.2 therefore have no known proof route, and
nothing here shows that ζ(7) is irrational.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

The roadmap has five chapters, from the determinant
construction through the irrationality assembly, decomposed into
pull-request-sized formalization units.

<!-- Reference material goes in sources/. It is vault material rather than a
     chapter, so the site does not publish it: a statement's "## Sources" list
     links to the file in the repository instead. -->
