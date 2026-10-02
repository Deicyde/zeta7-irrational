---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZetaSeven.IntegerValued.intValued_lipschitz ZetaSeven.IntegerValued.bernoulli_functional_bound ZetaSeven.IntegerValued.deriv_loss ZetaSeven.IntegerValued.deriv_loss_five
---

# Integer-valued polynomial estimates

The two integer-valued-polynomial facts the small-prime proof
imports from the predecessor paper: the Lipschitz-type bound
`v_p(A(x) - A(y)) ≥ v_p(x-y) - ⌊log_p max(1,d)⌋` for
integer-valued `A` of degree `d`, and the bound on `v_p(L(P))`
for the Bernoulli functional applied to such polynomials. These
are project-authored bridging lemmas adapted from the cited
predecessor argument, not external provenance.

## Formalization

Proved over `ℕ`/`ℚ` shadows: polynomials are binomial-basis
coefficient functions evaluated by `evalBinom` at `ℕ` points.
`intValued_lipschitz` carries a nonzero-difference side
condition (`padicValRat p 0` is junk);
`bernoulli_functional_bound` is the factor-5-plus-`v_p(720)`
form; `deriv_loss`/`deriv_loss_five` bound the `r`th-derivative
coefficient loss. The full `τ`-bound with constant exactly 5
needs a cancellation lemma beyond these per-term bounds and is
out of scope here.

## Depends on

None. Background prerequisite.

## Sources

- [Zeta 7 preprint source map](../../sources/zeta7-preprint.md):
  used in the proof of Lemma 3.8 (via the predecessor's Section 3.3).
