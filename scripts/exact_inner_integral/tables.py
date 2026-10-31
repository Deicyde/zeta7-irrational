"""Tables 2-4 (pp. 36-38) of the zeta7 preprint, the 192 rows claimed for R(x) on [3, 20].

tables.json was transcribed once from a text extraction of the preprint.  load() returns a dict
i -> (l, u, a, b) of Fractions, where the table claims R(x) = a x + b on [l, u].
"""
import json
import os
import sys
from fractions import Fraction as F

TABLE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tables.json")


def load():
    with open(TABLE, encoding="utf-8") as f:
        rows = {i: tuple(F(t) for t in r) for i, r in enumerate(json.load(f))}
    assert sorted(rows) == list(range(192))
    return rows


if __name__ == "__main__":
    rows = load()
    for i in sorted(rows):
        print(i, *rows[i])
    sys.exit(0)
