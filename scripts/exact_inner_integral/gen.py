"""Generate the per-piece Lean code of ZetaSeven/ExactInnerIntegral.lean (exact inner integral).

Independently re-derives the 131 cells of [3, 20] (cut where c x is an integer for
c in {1, 2, alpha, 2 alpha, 2H, 2 lambda, 1 - alpha, 1 + alpha, 9/20}), and for each cell checks,
in exact rational arithmetic, every side condition the Lean proof discharges with linarith
(floor bounds, branch of each min, order of d_f and d_g, branch of (s - n+)_+) at both
endpoints, and that the Lean closed form (innerR_eq_of_le / innerR_eq_of_ge, transcribed
verbatim below) reduces to the affine function a x + b fitted from R itself.

usage: python3 -I gen.py PART [ARGS]
  pieces LO HI     innerR_piece_LO .. innerR_piece_{HI-1}
  ints LO HI       private integral pieces innerPiece_LO .. innerPiece_{HI-1}
  blocks           blocks of ten pieces, the assembly, the main theorems
  jumps            jump lemmas and the x = 20 lemma
  check            run the checks only
"""
import os
import sys
from fractions import Fraction as F
from math import floor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recompute import R, points, COEFFS, affine_on, contrib, al, lam, H  # noqa: E402
from tables import load  # noqa: E402

TOTAL = F(120667538150827615739401, 708353029541942104320000)


class Aff:
    """p * x + r."""

    def __init__(self, p, r):
        self.p, self.r = F(p), F(r)

    def __add__(self, o):
        o = lift(o)
        return Aff(self.p + o.p, self.r + o.r)

    __radd__ = __add__

    def __neg__(self):
        return Aff(-self.p, -self.r)

    def __sub__(self, o):
        return self + (-lift(o))

    def __rsub__(self, o):
        return lift(o) - self

    def __mul__(self, o):
        o = lift(o)
        assert self.p == 0 or o.p == 0, "nonlinear"
        return Aff(self.p * o.r + self.r * o.p, self.r * o.r)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return Aff(self.p / F(o), self.r / F(o))

    def at(self, x):
        return self.p * x + self.r


def lift(o):
    return o if isinstance(o, Aff) else Aff(0, o)


X = Aff(1, 0)


def cell_data(l, u):
    mid = (l + u) / 2
    d = dict(n=floor(mid), q=floor(2 * mid), m=floor(al * mid), qq=floor(2 * al * mid),
             T=floor(2 * H * mid), k=floor(2 * lam * mid))
    n, q, m, qq, T, k = (d[s] for s in ("n", "q", "m", "qq", "T", "k"))
    # floor side conditions on the open cell
    for c, v in ((F(1), n), (F(2), q), (al, m), (2 * al, qq), (2 * H, T), (2 * lam, k)):
        assert v <= c * l and c * u <= v + 1, (l, u, c, v)
    # branch of d_f = min(x - n, n + 1 - x)
    lo_f, hi_f = X - n, n + 1 - X
    f_left = all(lo_f.at(t) <= hi_f.at(t) for t in (l, u))
    f_right = all(hi_f.at(t) <= lo_f.at(t) for t in (l, u))
    assert f_left != f_right
    df = lo_f if f_left else hi_f
    lo_g, hi_g = F(3, 40) * X - m, m + 1 - F(3, 40) * X
    g_left = all(lo_g.at(t) <= hi_g.at(t) for t in (l, u))
    g_right = all(hi_g.at(t) <= lo_g.at(t) for t in (l, u))
    assert g_left != g_right
    dg = lo_g if g_left else hi_g
    le = all(df.at(t) <= dg.at(t) for t in (l, u))
    ge = all(dg.at(t) <= df.at(t) for t in (l, u))
    assert le or ge
    le = le  # prefer the le lemma when both hold (never happens on a nondegenerate cell)
    E = F(49, 40) * X - F(T, 2) - (2 * X - q) / 2
    s_left = all(E.at(t) >= 0 for t in (l, u))
    s_right = all(E.at(t) <= 0 for t in (l, u))
    assert s_left or s_right
    S = E if s_left else Aff(0, 0)
    # the Lean closed form, verbatim
    W1 = (T - 8 * m - 4) * (T + 8 * m - 2 * n - 4)
    W2 = (T - 8 * m - 4) * (T + 8 * m + 2 * n - 2 * q - 3)
    W3 = (T + 8 * m - 8 * qq) * (T - 8 * m + 8 * qq + 2 * n - 2 * q - 7)
    W4 = (T + 8 * m - 8 * qq) * (T - 8 * m + 8 * qq - 2 * n - 8)
    if le:
        integ = df * W1 + (dg - df) * W2 + (F(1, 2) - dg) * W3
    else:
        integ = dg * W1 + (df - dg) * W4 + (F(1, 2) - df) * W3
    rhs = -(integ + (F(49, 40) * X - F(T, 2)) * (2 * T - q - 7) + S) \
        - (F(37, 20) * n * X - F(74, 5) * m * X - 2 * (F(37, 40) * k * X - F(k * (k + 1), 4)))
    a, b = affine_on(l, u)
    assert (rhs.p, rhs.r) == (a, b), (l, u, rhs.p, rhs.r, a, b)
    for t in (F(1, 3), F(1, 2), F(2, 3)):
        y = l + t * (u - l)
        assert R(y) == rhs.at(y)
    return dict(l=l, u=u, a=a, b=b, f_left=f_left, g_left=g_left, le=le, s_left=s_left,
                contrib=contrib(l, u, a, b), **d)


def cells():
    G = points(COEFFS)
    return [cell_data(l, u) for l, u in zip(G, G[1:])]


def lit(v):
    """A real literal for Lean, without outer parentheses."""
    v = F(v)
    s = f"{abs(v.numerator)}" if v.denominator == 1 else f"{abs(v.numerator)} / {v.denominator}"
    return ("-" + s) if v < 0 else s


def plit(v):
    s = lit(v)
    return f"({s})" if (" " in s or s.startswith("-")) else s


def txt(v):
    v = F(v)
    return str(v.numerator) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"


def affine_lean(a, b):
    if a == 0:
        return lit(b)
    head = "x" if a == 1 else f"{lit(a)} * x"
    if b == 0:
        return head
    return f"{head} + {lit(b)}" if b > 0 else f"{head} - {lit(-b)}"


def affine_txt(a, b):
    if a == 0:
        return txt(b)
    head = "x" if a == 1 else (f"{txt(a)}x" if F(a).denominator == 1 else f"({txt(a)})x")
    if b == 0:
        return head
    return f"{head} + {txt(b)}" if b > 0 else f"{head} - {txt(-b)}"


def row_groups(cs):
    rows = load()
    out = []
    for c in cs:
        ids = [i for i in range(192) if rows[i][0] >= c["l"] and rows[i][1] <= c["u"]]
        assert ids and rows[ids[0]][0] == c["l"] and rows[ids[-1]][1] == c["u"]
        assert all(rows[i][2:] == (c["a"], c["b"]) for i in ids)
        out.append(ids)
    assert sorted(i for g in out for i in g) == list(range(192))
    return out


FL = "(floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith))"


def piece(i, c, rows):
    rr = f"row {rows[0]}" if len(rows) == 1 else f"rows {rows[0]}-{rows[-1]}"
    lemma = "innerR_eq_of_le" if c["le"] else "innerR_eq_of_ge"
    mf = "min_eq_left" if c["f_left"] else "min_eq_right"
    mg = "min_eq_left" if c["g_left"] else "min_eq_right"
    ms = "max_eq_left" if c["s_left"] else "max_eq_right"
    return f"""/-- On `({txt(c['l'])}, {txt(c['u'])})`, `R(x) = {affine_txt(c['a'], c['b'])}` (Tables 2-4, {rr}). -/
private theorem innerR_piece_{i:03d} (x : ℝ) (h0 : {lit(c['l'])} < x) (h1 : x < {lit(c['u'])}) :
    innerR x = {lit(c['a'])} * x + {lit(c['b'])} := by
  rw [{lemma} (x := x) (n := {c['n']}) (q := {c['q']}) (m := {c['m']}) (q' := {c['qq']}) (T := {c['T']})
    (k := {c['k']}) {FL}
    {FL}
    {FL}
    {FL}
    {FL}
    {FL}
    ({mf} (by push_cast; linarith)) ({mg} (by push_cast; linarith))
    (by push_cast; linarith) ({ms} (by push_cast; linarith))]
  push_cast
  ring
"""


def intpiece(i, c):
    return f"""private theorem innerPiece_{i:03d} : InnerPiece {plit(c['l'])} {plit(c['u'])} {plit(c['contrib'])} :=
  innerPiece_of_affine (a := {lit(c['a'])}) (b := {lit(c['b'])}) (by norm_num) (by norm_num)
    innerR_piece_{i:03d} (by norm_num)
"""


def blocks(cs):
    out = []
    nb = (len(cs) + 9) // 10
    bsum = []
    for j in range(nb):
        idx = list(range(10 * j, min(10 * j + 10, len(cs))))
        s = cs[idx[0]]["contrib"]
        lines = [f"private theorem innerPiece_block_{j:02d} :",
                 f"    InnerPiece {plit(cs[idx[0]]['l'])} {plit(cs[idx[-1]]['u'])} SUM := by"]
        prev = f"innerPiece_{idx[0]:03d}"
        for t in idx[1:]:
            s += cs[t]["contrib"]
            lines.append(f"  have h := innerPiece_trans {prev} innerPiece_{t:03d} (C := {lit(s)})")
            lines.append("    (by norm_num)")
            prev = "h"
        lines.append(f"  exact {prev}")
        lines[1] = lines[1].replace("SUM", plit(s))
        bsum.append(s)
        out.append("\n".join(lines) + "\n")
    s = bsum[0]
    lines = ["private theorem innerPiece_all :",
             f"    InnerPiece 3 20 ({lit(TOTAL)}) := by"]
    prev = "innerPiece_block_00"
    for j in range(1, nb):
        s += bsum[j]
        lines.append(f"  have h := innerPiece_trans {prev} innerPiece_block_{j:02d}")
        lines.append(f"    (C := {lit(s)}) (by norm_num)")
        prev = "h"
    assert s == TOTAL
    lines.append(f"  exact {prev}")
    out.append("\n".join(lines) + "\n")
    return "\n".join(out)


def table(cs, groups):
    lines = ["""/-- The 131 pieces `(l, u, a, b)` of `[3, 20]`, in order: `R(x) = ax + b` for `l < x < u`
(`ZetaSeven.innerR_eq_of_mem_innerRPieces`). Consecutive pieces share an endpoint; the cut points
are the points of `[3, 20]` where `cx` is an integer for some
`c ∈ {1, 2, α, 2α, 2H, 2λ, 1 - α, 1 + α, 9/20}`. Each piece is the union of the rows of
Tables 2-4 noted beside it, which all have these coefficients. -/
def innerRPieces : List (ℚ × ℚ × ℚ × ℚ) :="""]
    # chunks of at most 25 entries, each type-ascribed: a long list literal elaborates its
    # entries without the expected type and times out
    CH = 25
    for i, c in enumerate(cs):
        g = groups[i]
        rr = f"row {g[0]}" if len(g) == 1 else f"rows {g[0]}-{g[-1]}"
        first, last = i % CH == 0, i % CH == CH - 1 or i == len(cs) - 1
        open_ = "  ([" if first else "    "
        if not last:
            close = ","
        elif i == len(cs) - 1:
            close = "] : List (ℚ × ℚ × ℚ × ℚ))"
        else:
            close = "] : List (ℚ × ℚ × ℚ × ℚ)) ++"
        lines.append(f"{open_}({lit(c['l'])}, {lit(c['u'])}, {lit(c['a'])}, {lit(c['b'])}){close} -- {rr}")
    # push_cast could simplify `1 * y` or `0 * y`; let ring absorb that for those pieces
    names = [f"innerR_piece_{i:03d}" if c["a"] not in (0, 1) and c["b"] != 0 else
             f"fun y h0 h1 => (innerR_piece_{i:03d} y h0 h1).trans (by ring)"
             for i, c in enumerate(cs)] + ["by simp"]
    body, cur = [], "    exact ⟨"
    for k, nm in enumerate(names):
        tok = nm + ("⟩" if k == len(names) - 1 else ",")
        if len(cur) + 1 + len(tok) > 100:
            body.append(cur)
            cur = "      " + tok
        else:
            cur = cur + ("" if cur.endswith("⟨") else " ") + tok
    body.append(cur)
    thm = """
/-- **`R` on the pieces** (Tables 2-4, on open intervals as in source-map erratum 12): for each
piece `(l, u, a, b)` of `ZetaSeven.innerRPieces`, `R(x) = ax + b` for `l < x < u`. -/
theorem innerR_eq_of_mem_innerRPieces {l u a b : ℚ} (hp : (l, u, a, b) ∈ innerRPieces) {x : ℝ}
    (h0 : (l : ℝ) < x) (h1 : x < u) : innerR x = a * x + b := by
  have key : ∀ p ∈ innerRPieces, ∀ y : ℝ, (p.1 : ℝ) < y → y < p.2.1 →
      innerR y = p.2.2.1 * y + p.2.2.2 := by
    simp only [innerRPieces, List.cons_append, List.nil_append, List.forall_mem_cons]
    push_cast
""" + "\n".join(body) + """
  exact key _ hp x h0 h1
"""
    return "\n".join(lines) + "\n" + thm


def jumps(cs):
    out = []
    for i in range(len(cs) - 1):
        c, d = cs[i], cs[i + 1]
        t = c["u"]
        left, right = c["a"] * t + c["b"], d["a"] * t + d["b"]
        if left == right:
            continue
        name = txt(t).replace("/", "_")
        out.append(f"""/-- `R` jumps at `x = {txt(t)}`: left limit `{txt(left)}`, right limit `{txt(right)}`. -/
theorem innerR_jump_{name} :
    Tendsto innerR (𝓝[<] ({lit(t)} : ℝ)) (𝓝 {plit(left)}) ∧
      Tendsto innerR (𝓝[>] ({lit(t)} : ℝ)) (𝓝 {plit(right)}) :=
  ⟨tendsto_nhdsLT_of_affine (l := {lit(c['l'])}) (a := {lit(c['a'])}) (b := {lit(c['b'])}) (by norm_num)
      (by norm_num) innerR_piece_{i:03d},
    tendsto_nhdsGT_of_affine (u := {lit(d['u'])}) (a := {lit(d['a'])}) (b := {lit(d['b'])}) (by norm_num)
      (by norm_num) innerR_piece_{i + 1:03d}⟩
""")
    c = cs[-1]
    assert c["u"] == 20 and c["a"] * 20 + c["b"] == 0 and R(F(20)) == -37
    fl20 = "(floor_eq_of_bounds (by norm_num) (by norm_num))"
    out.append(f"""/-- At the right endpoint `x = 20`, `R(x) → 0` as `x → 20` from the left, but `R(20) = -37`
(`⌊x⌋`, `⌊2x⌋`, `⌊2Hx⌋` and `⌊2λx⌋` all jump at `x = 20`). -/
theorem innerR_at_twenty : Tendsto innerR (𝓝[<] (20 : ℝ)) (𝓝 0) ∧ innerR 20 = -37 := by
  refine ⟨tendsto_nhdsLT_of_affine (l := {lit(c['l'])}) (a := {lit(c['a'])}) (b := {lit(c['b'])}) (by norm_num)
      (by norm_num) innerR_piece_130, ?_⟩
  rw [innerR_eq_of_le (x := 20) (n := 20) (q := 40) (m := 1) (q' := 3) (T := 49) (k := 37)
    {fl20}
    {fl20}
    {fl20}
    {fl20}
    {fl20}
    {fl20}
    (min_eq_left (by norm_num)) (min_eq_left (by norm_num)) (by norm_num)
    (max_eq_left (by norm_num))]
  norm_num
""")
    return out


def main():
    cs = cells()
    assert len(cs) == 131
    assert sum(c["contrib"] for c in cs) == TOTAL
    groups = row_groups(cs)
    part = sys.argv[1] if len(sys.argv) > 1 else "check"
    if part == "check":
        js = [(cs[i]["u"]) for i in range(130)
              if cs[i]["a"] * cs[i]["u"] + cs[i]["b"] != cs[i + 1]["a"] * cs[i]["u"] + cs[i + 1]["b"]]
        print("cells:", len(cs), " le:", sum(c["le"] for c in cs), " s_left:",
              sum(c["s_left"] for c in cs), " jumps at:", [txt(t) for t in js])
        print("last piece value at 20:", cs[-1]["a"] * 20 + cs[-1]["b"])
        print("max line length:", max(len(l) for i, c in enumerate(cs)
                                      for l in piece(i, c, groups[i]).splitlines()))
        return
    if part == "pieces":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        print("\n".join(piece(i, cs[i], groups[i]) for i in range(lo, hi)), end="")
    elif part == "ints":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        print("\n".join(intpiece(i, cs[i]) for i in range(lo, hi)), end="")
    elif part == "blocks":
        print(blocks(cs), end="")
    elif part == "table":
        print(table(cs, groups), end="")
    elif part == "jumps":
        print("\n".join(jumps(cs)), end="")


if __name__ == "__main__":
    main()
