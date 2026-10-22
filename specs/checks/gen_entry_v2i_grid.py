#!/usr/bin/env python3
"""Synthetic N = 3 check of V2i's general entry: midpoint grid on the τ-simplex, true rough-set
endpoint, untranslated power sums, inner integrals ∫₀^U G by Gauss–Legendre (exact for these
polynomial degrees). numpy; exploratory.

Usage: python3 -I specs/checks/gen_entry_v2i_grid.py GRID
"""
import sys
import numpy as np

g, L, tau = 0.3, 1.0, 0.9
C = np.array([0, .5, .6, .7, .7, .7])
CASES = [(0, [4], 0, []), (0, [2, 2], 0, []), (1, [], 0, []), (0, [2, 2], 0, [2]), (1, [2], 1, [2]),
         (2, [4], 0, [2])]
xg, wg = np.polynomial.legendre.leggauss(16)


def inner(a, lam, X, U):
    M = L - X.sum(0)
    tot = 0
    for t, w in zip(xg, wg):
        u = U * (t + 1) / 2
        v = (M - u) ** a
        for q in lam:
            v = v * ((X ** q).sum(0) + u ** q)
        tot = tot + w * v
    return tot * U / 2


def run(n):
    h = tau / n
    c = (np.arange(n) + .5) * h
    x1, x2 = np.meshgrid(c, c, indexing='ij')
    tot = np.zeros(len(CASES))
    for z in c:
        X = np.stack([x1, x2, np.full_like(x1, z)])
        S = X.sum(0)
        m = X > g
        cnt = m.sum(0)
        rho = (X * m).sum(0)
        ok = (S <= tau) & (rho <= C[cnt])
        U = np.minimum(L - S, np.maximum(g, C[cnt + 1] - rho))
        for i, (a1, l1, a2, l2) in enumerate(CASES):
            v = inner(a1, l1, X, U) * inner(a2, l2, X, U)
            tot[i] += v[ok].sum()
    return 4 * tot * h ** 3


for n in map(int, sys.argv[1:]):
    print(n, " ".join(f"{v:.9g}" for v in run(n)))
