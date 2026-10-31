# Exact inner integral generator

Generates the 131 per-piece declarations of `ZetaSeven/ExactInnerIntegral.lean`, after
checking each piece in exact rational arithmetic. The table rows in `tables.json` are only
used to label pieces and cross-check them; the Lean proof does not depend on them.

```
python3 -I scripts/exact_inner_integral/assemble.py .   # regenerate; git diff should be empty
python3 -I scripts/exact_inner_integral/gen.py check     # the checks only
python3 -I scripts/exact_inner_integral/recompute.py     # compare R with Tables 2-4 and (121)
```
