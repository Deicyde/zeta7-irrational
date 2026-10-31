# Exact inner integral generator

Regenerates everything after the hand-written head of `ZetaSeven/ExactInnerIntegral.lean`
(the 131 pieces, `innerRPieces`, the integral blocks, `innerIntegral_value` and the jump
lemmas), after checking each piece in exact rational arithmetic. The table rows in `tables.json` are only
used to label pieces and cross-check them; the Lean proof does not depend on them.

```
python3 -I scripts/exact_inner_integral/assemble.py .   # regenerate; git diff should be empty
python3 -I scripts/exact_inner_integral/gen.py check     # the checks only
python3 -I scripts/exact_inner_integral/recompute.py     # compare R with Tables 2-4 and (121)
```
