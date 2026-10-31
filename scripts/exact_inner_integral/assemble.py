"""Rewrite the generated tail of ZetaSeven/ExactInnerIntegral.lean.

Keeps the hand-written head of the file (everything through the end of the doc comment that
starts with MARKER) and regenerates the rest from gen.py.

usage: python3 -I assemble.py WORKTREE [LO HI]   (pieces LO..HI-1 only; default all and the
assembly, the main theorems and the jump lemmas)
"""
import os
import subprocess
import sys

MARKER = "/-! ### `R` on the 131 pieces"
GEN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen.py")


def gen(*args):
    return subprocess.run([sys.executable, "-I", GEN, *args], check=True, capture_output=True,
                          text=True).stdout


def main():
    wt = sys.argv[1]
    path = f"{wt}/ZetaSeven/ExactInnerIntegral.lean"
    src = open(path, encoding="utf-8").read()
    i = src.index(MARKER)
    j = src.index("-/\n", i) + 3
    head = src[:j]
    full = len(sys.argv) == 2
    lo, hi = (0, 131) if full else (int(sys.argv[2]), int(sys.argv[3]))
    parts = [head, "\n", gen("pieces", str(lo), str(hi))]
    if full:
        parts += ["\n/-! ### The table of pieces -/\n\n", gen("table"),
                  "\n/-! ### The integral of `R(x)/x^3` over the pieces -/\n\n",
                  gen("ints", "0", "131"), "\n", gen("blocks"),
                  """
/-! ### The value of the inner integral -/

/-- `R(x)/x^3` is interval integrable on `[3, 20]`. -/
theorem intervalIntegrable_innerR_div_cube :
    IntervalIntegrable (fun x => innerR x / x ^ 3) volume 3 20 :=
  innerPiece_all.1

/-- **Exact inner integral** (Appendix A.1, (121)):
`∫_3^20 R(x)/x^3 dx = 120667538150827615739401/708353029541942104320000`. -/
theorem innerIntegral_value :
    ∫ x in (3 : ℝ)..20, innerR x / x ^ 3 =
      120667538150827615739401 / 708353029541942104320000 :=
  innerPiece_all.2

/-! ### The jumps of `R` (source-map erratum 12) -/

""", gen("jumps")]
    parts.append("\nend ZetaSeven\n")
    open(path, "w", encoding="utf-8").write("".join(parts))


if __name__ == "__main__":
    main()
