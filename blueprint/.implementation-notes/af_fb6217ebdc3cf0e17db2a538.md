Outer class rows: not formalized. Split out of the outer class basis
node on 2026-10-18, so that the outer entry valuations state their
claim without waiting on the unimodularity proof.

## Evidence

The rows were reconstructed (the paper names only `q_{a,i}` and `E_a`)
and checked through the outer class basis (row count `h`, unimodular)
and the outer entry valuations, for `n = 1..5` and every prime
satisfying (52), 88 cases; those notes have the details.

## Lean hints

Index the rows by the index set of the outer weight family (its note
suggests a `Finset (ℕ × ℕ)` or a sigma type over `c ∈ Icc 0 m`), so the
outer estimate can pair rows with weights without a separate bijection;
the row count `h` is then the outer class basis's job. Build the rows in
`ℤ[X]`, like `DpolyZ` and `DtailZ` on branch `formalize/outer-estimate`
(commit `0f0a541`), and use `ZetaSeven.mHalf` and `ZetaSeven.ell` from
main for `m` and `ℓ_K(c)`.
