# Coverage contract

The rows below span the v1 preprint (Zenodo 22920911): the
construction, the arithmetic and analytic estimates, the assembly, the
background identities those estimates cite, the deferred approximation
bound, and the predecessor material excluded from scope.

| Area | Coverage | Evidence |
| --- | --- | --- |
| Determinant construction (Section 2) | `DECOMPOSED` | [Determinant construction chapter](../roadmap/determinant-construction/README.md) covers the functional, degree, and positivity |
| Local p-adic estimates (Sections 3-4) | `DECOMPOSED` | [Local arithmetic chapter](../roadmap/local-arithmetic/README.md) covers completion, distribution, and both range estimates |
| Normalization and prime sum (Section 5, exact integrals) | `DECOMPOSED` | [Normalization chapter](../roadmap/normalization-prime-sum/README.md) covers integrality, limiting integrals, and the prime-sum bound |
| Real determinant bound (Section 6, comparison measure) | `DECOMPOSED` | [Real bound chapter](../roadmap/real-bound/README.md) covers the energy comparison and the analytic bound |
| Main irrationality assembly (Theorems 1.1-1.2) | `DECOMPOSED` | [Irrationality proof chapter](../roadmap/irrationality-proof/README.md) covers the decay estimates and the contradiction |
| Background identities cited by the estimates | `DECOMPOSED` | Decomposed into [Hermite/Hurwitz](../roadmap/determinant-construction/hermite-hurwitz.md), [von Staudt-Clausen](../roadmap/local-arithmetic/von-staudt-clausen.md), [Bernoulli multiplication](../roadmap/local-arithmetic/bernoulli-multiplication.md), and [Andreief](../roadmap/real-bound/andreief-identity.md) nodes; the remaining Mathlib audit is node-level work |
| Approximation bound and coefficient height (Corollary 1.3) | `DEFERRED` | Later milestone after the main irrationality result; needs the relative matrix norm estimate of Proposition B.1 |
| Fauzan zeta(5) predecessor and survey material | `OUT` | Cited for architecture only; not a formalization target. The outer-range steps the paper defers to it are reconstructed as bridged nodes in the [local arithmetic chapter](../roadmap/local-arithmetic/README.md#outer-range) |

## Completion rule

The coarse milestone is complete when every chapter above is
fine-decomposed into pull-request-sized nodes and no row remains
`MAPPED`. Terminal disposition of every row means the contract is
closed, not that the source is exhaustively covered or any node is
proved.
