"""Recompute the affine pieces of R(x) on [3, 20] and int_3^20 R(x)/x^3 dx exactly.

R is Definition 5.2, (64)-(69), of the zeta7 preprint, transcribed from the Lean definitions
ZetaSeven.innerGamma / innerN / innerR (ZetaSeven/InnerLimiting.lean).  All arithmetic is exact
(fractions.Fraction).

Structure.  On any open x-interval on which floor(c x) is constant for every
c in COEFFS = {1, 2, alpha, 2 alpha, 2H, 2 lambda, 1 - alpha, 1 + alpha, 2(H - 1)}:
  * T, q, floor(x), floor(alpha x), floor(2 lambda x) are constant;
  * the z-breakpoints {x}, 1-{x}, {alpha x}, 1-{alpha x} in (0, 1/2) keep their order
    (d({x}) = d({alpha x}) only when (1 -/+ alpha) x is an integer) and their positions are
    affine in x, while the integrand (T-b)(T+b-l-7) is constant on each z-cell;
  * (s - n+)_+ = ({2Hx} - {2x})_+ / 2 keeps its branch (switch at 2(H-1)x in Z).
Hence R is affine on each such cell.  We still verify affinity at 5 interior points per cell.
"""
import os
import sys
from fractions import Fraction as F
from math import floor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tables import load  # noqa: E402

al = F(3, 40)
lam = F(37, 40)
H = F(49, 40)
assert H == 1 + 3 * al and lam == 1 - al


def frac(x):
    return x - floor(x)


def ell(x, z):
    return floor(x - z) + floor(x + z) + 1


def gamma(x):
    T = floor(2 * H * x)
    s = H * x - F(T, 2)
    q = floor(2 * x)
    nplus = (2 * x - q) / 2
    zs = {F(0), F(1, 2)}
    for w in (x, al * x):
        for z in (frac(w), 1 - frac(w)):
            if 0 < z < F(1, 2):
                zs.add(z)
    zs = sorted(zs)
    integral = F(0)
    for z0, z1 in zip(zs, zs[1:]):
        zm = (z0 + z1) / 2
        l = ell(x, zm)
        b = 4 * ell(al * x, zm)
        integral += (T - b) * (T + b - l - 7) * (z1 - z0)
    return integral + s * (2 * T - q - 7) + max(s - nplus, F(0))


def J(u):
    m = floor(2 * u)
    return m * u - F(m * (m + 1), 4)


def N(x):
    return 2 * lam * x * floor(x) - 16 * lam * x * floor(al * x) - 2 * J(lam * x)


def R(x):
    return -gamma(x) - N(x)


def points(coeffs, lo=F(3), hi=F(20)):
    pts = {lo, hi}
    for c in coeffs:
        for k in range(floor(c * lo), floor(c * hi) + 1):
            x = F(k) / c
            if lo < x < hi:
                pts.add(x)
    return sorted(pts)


COEFFS = [F(1), F(2), al, 2 * al, 2 * H, 2 * lam, 1 - al, 1 + al, 2 * (H - 1)]
PAPER = [F(2), 2 * al, 2 * lam, 2 * H, 8 * al, 2 * (1 - al), 2 * (1 + al), 2 * (1 + 2 * al),
         F(9, 20)]


def affine_on(l, u):
    x1, x2 = (2 * l + u) / 3, (l + 2 * u) / 3
    a = (R(x2) - R(x1)) / (x2 - x1)
    b = R(x1) - a * x1
    for t in (F(1, 997), F(1, 2), F(996, 997)):
        x = l + t * (u - l)
        assert R(x) == a * x + b, (l, u, x)
    return a, b


def contrib(l, u, a, b):
    return a * (1 / l - 1 / u) + b / 2 * (1 / l ** 2 - 1 / u ** 2)


def main():
    G = points(COEFFS)
    P = points(PAPER)
    print("genuine cells:", len(G) - 1, " paper-set cells:", len(P) - 1)
    print("G subset of P:", set(G) <= set(P))
    print("P \\ G (spurious cut points in paper set):", len(set(P) - set(G)))
    cells = [(l, u) + affine_on(l, u) for l, u in zip(G, G[1:])]
    total = sum(contrib(*c) for c in cells)

    # merge adjacent cells with equal (a, b) into maximal pieces
    pieces = []
    for l, u, a, b in cells:
        if pieces and pieces[-1][2:] == (a, b):
            pieces[-1] = (pieces[-1][0], u, a, b)
        else:
            pieces.append((l, u, a, b))
    jumps = [(p[1], p[2] * p[1] + p[3], q[2] * p[1] + q[3])
             for p, q in zip(pieces, pieces[1:]) if p[2] * p[1] + p[3] != q[2] * p[1] + q[3]]
    print("maximal affine pieces:", len(pieces), " jump points:", len(jumps))
    for t, left, right in jumps:
        print("   jump at", t, ": left", left, " right", right, " size", right - left)

    rows = load()
    # chain check
    assert rows[0][0] == 3 and rows[191][1] == 20
    for i in range(191):
        if rows[i][1] != rows[i + 1][0]:
            print("CHAIN BREAK", i, rows[i], rows[i + 1])
    tset = sorted({r[0] for r in rows.values()} | {rows[191][1]})
    print("table cut points == paper set P:", tset == P,
          " table cut points == G:", tset == G)
    print("table pts not in P:", sorted(set(tset) - set(P)))
    print("P pts not in table:", sorted(set(P) - set(tset)))

    bad = []
    for i in range(192):
        l, u, a, b = rows[i]
        ra, rb = affine_on(l, u)  # asserts affinity on the row interval at 5 points
        if (ra, rb) != (a, b):
            bad.append((i, rows[i], (ra, rb)))
    print("table rows disagreeing with recomputed R:", len(bad))
    for x in bad:
        print("  ", x)
    # every genuine cut point that is a real change of (a, b) must be a table cut point
    real_cuts = [p[1] for p in pieces[:-1]]
    print("real (a,b) changes:", len(real_cuts), " all in table:", set(real_cuts) <= set(tset))
    print("table cuts where (a,b) does not change (spurious):",
          sum(1 for i in range(191) if rows[i][2:] == rows[i + 1][2:]))

    table_total = sum(contrib(*rows[i]) for i in range(192))
    printed = F(120667538150827615739401, 708353029541942104320000)
    print("recomputed integral  =", total, "~", float(total))
    print("table-sum integral   =", table_total, "~", float(table_total))
    print("printed (121)        =", printed, "~", float(printed))
    print("recomputed == printed:", total == printed, " table-sum == printed:", table_total == printed)
    print("printed fraction in lowest terms:",
          printed.numerator == 120667538150827615739401)
    print("denominator factorization of recomputed:", factor(total.denominator))
    return cells, pieces, rows, total


def factor(n):
    out, p = [], 2
    while p * p <= n:
        while n % p == 0:
            out.append(p)
            n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


if __name__ == "__main__":
    main()
