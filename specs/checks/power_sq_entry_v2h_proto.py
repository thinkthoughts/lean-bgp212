#!/usr/bin/env python3
"""Exploratory prototype of J_T[P₂, P₂] (V2h), independent of the certificate's coefficient form.

The piece value is computed as a direct placement sum over classes (Σ_c n_c ψ_c + Σ_{c,d}
(n_c n_d − [c = d] n_c) φ_{cd}), not through q2Coef; the emitter's q2J must agree with it.
Also runs the synthetic N = 3 grid comparison.

Usage: python3 -I specs/checks/power_sq_entry_v2h_proto.py [GRID]   (about 2–3 minutes)
"""
import itertools
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import marginal_entry_v2f_emit as E  # noqa
import power_sum_entry_v2g_emit as P  # noqa


def setdata(N, g, L, tau, Cf):
    E.N, E.G, E.L, E.TAU, E.C = N, g, L, tau, Cf
    P.N = N


def pieceM(r, k, a, b, m):
    N, G, TAU, C = P.N, E.G, E.TAU, E.C
    if C(r) - r * G < 0 or TAU - (r + k) * G < 0:
        return Fr(0)
    if r == 0:
        return Fr(1, fact(N + b - 1)) * E.seg0(k, TAU - k * G, N - 1 + b, m, 0)
    return Fr(1, fact(r + a - 1)) * Fr(1, fact(N - r + b - 1)) * E.cells(
        r, k, C(r) - r * G, TAU - (r + k) * G, r - 1 + a, N - r - 1 + b, m, 0)


def rp(c, a): return a if c == 0 else 0
def sp(c, a): return 0 if c == 0 else a
def sig(c): return Fr(0) if c == 2 else E.G
def cnt(r, k, c): return [r, k, P.N - r - k][c]


def phi(r, k, c, d, m, M):
    return sum(comb(2, a) * comb(2, b) * sig(c) ** (2 - a) * sig(d) ** (2 - b) * fact(a) * fact(b)
               * M(r, k, rp(c, a) + rp(d, b), sp(c, a) + sp(d, b), m) for a in range(3) for b in range(3))


def psi(r, k, c, m, M):
    return sum(comb(4, a) * sig(c) ** (4 - a) * fact(a) * M(r, k, rp(c, a), sp(c, a), m) for a in range(5))


def q2J(r, k, m=2, variant=None):
    cache = {}
    def M(r_, k_, a, b, mm):
        if (a, b, mm) not in cache:
            cache[(a, b, mm)] = pieceM(r_, k_, a, b, mm)
        return cache[(a, b, mm)]
    tot = sum(cnt(r, k, c) * psi(r, k, c, m, M) for c in range(3))
    for c in range(3):
        for d in range(3):
            mult = cnt(r, k, c) * cnt(r, k, d) - (cnt(r, k, c) if (c == d and variant != "nodiagfix") else 0)
            tot += mult * phi(r, k, c, d, m, M)
    return tot


def ssum(f):
    N = P.N
    return (N + 1) * sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * f(r, k) for k in range(N - r + 1))
                         for r in range(N + 1))


def entry(variant=None):
    a = ssum(lambda r, k: q2J(r, k, 2, variant))
    b = ssum(lambda r, k: P.p2J(r, k, 4))
    c = ssum(lambda r, k: E.pieceJ(r, k, 6, 0))
    return a + Fr(2, 3) * b + c / 9, (a, b, c)


if __name__ == "__main__":
    # synthetic N = 3
    gs, Ls, ts = Fr(3, 10), Fr(1), Fr(9, 10)
    CS = [Fr(0), Fr(1, 2), Fr(3, 5), Fr(7, 10)]
    Cs = lambda m: CS[min(m, 3)]
    setdata(3, gs, Ls, ts, Cs)
    v, parts = entry()
    vbad, _ = entry("nodiagfix")
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    h = float(ts) / n
    Cv = [float(Cs(m)) for m in range(6)]
    tot = 0.0
    for idx in itertools.product(range(n), repeat=3):
        x = [(i + 0.5) * h for i in idx]
        S = sum(x)
        if S > float(ts):
            continue
        R = [w for w in x if w > float(gs)]
        rho = sum(R)
        if rho > Cv[len(R)]:
            continue
        U = min(float(Ls) - S, max(float(gs), Cv[len(R) + 1] - rho))
        tot += (U * sum(w * w for w in x) + U ** 3 / 3) ** 2
    gv = 4 * tot * h ** 3
    print("N=3 closed", float(v), "grid", gv, "rel", abs(gv - float(v)) / float(v), "bad", float(vbad))
    # Table 3
    G, L, TAU = Fr(41, 625), Fr(53, 50), Fr(249, 250)
    C3 = lambda m: Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000)
    setdata(44, G, L, TAU, C3)
    t0 = time.time()
    v, (a, b, c) = entry()
    print("Table3 time", time.time() - t0)
    print("J_T[P2,P2] =", float(v), " parts", float(a), float(Fr(2, 3) * b), float(c / 9))
    print("NUM", v.numerator)
    print("DEN", v.denominator)
