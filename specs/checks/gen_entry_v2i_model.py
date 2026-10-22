#!/usr/bin/env python3
"""Exact mirror of V2i's general marginal Gram entry J_T[G_{a1,λ1}, G_{a2,λ2}] (BGP212/GenEntry.lean).

G_{a,λ} = (L − P₁)^a P_λ. The closed form `genEntryVal` is

  (N + 1) Σ_r C(N, r) Σ_k C(N − r, k) (−1)^k genPiece(r, k),
  genPiece(r, k) = Σ_{t₁ ∈ innerTerms(a₁, λ₁)} Σ_{t₂ ∈ innerTerms(a₂, λ₂)} c₁ c₂ ·
                   Φ(pieceMn(·, ·, p₁ + p₂, q₁ + q₂), n, [], parts(t₁) ++ parts(t₂)),

where innerTerms(a, λ) lists (parts kept, power of U, power of M = L − Ŝ, coefficient) of
∫₀^U (M − u)^a ∏_{q ∈ λ} (P̂_q + u^q) du, and Φ is the placement recursion (new coordinate of a
class, or merge into an open one). Standard library only; the cell formulas are V2f's emitter.
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import marginal_entry_v2f_emit as E  # noqa: E402

N = 44


def setdata(n, g, L, tau, Cf):
    global N
    N = n
    E.N, E.G, E.L, E.TAU, E.C = n, g, L, tau, Cf


def pieceMn(r, k, a, b, m, n):
    G, TAU, C = E.G, E.TAU, E.C
    if C(r) - r * G < 0 or TAU - (r + k) * G < 0:
        return Fr(0)
    if r == 0:
        return Fr(1, fact(N + b - 1)) * E.seg0(k, TAU - k * G, N - 1 + b, m, n)
    return Fr(1, fact(r + a - 1)) * Fr(1, fact(N - r + b - 1)) * E.cells(
        r, k, C(r) - r * G, TAU - (r + k) * G, r - 1 + a, N - r - 1 + b, m, n)


def rp(c, a):
    return a if c == 0 else 0


def sp(c, a):
    return 0 if c == 0 else a


def shiftPow(s, q):
    """(y + s)^q as a coefficient list."""
    return [comb(q, a) * s ** (q - a) for a in range(q + 1)]


def pmul(f, g):
    out = [Fr(0)] * (len(f) + len(g) - 1) if f and g else []
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i + j] += x * y
    return out


def V(M, S, A=0, B=0):
    if not S:
        return M(A, B)
    (c, f), rest = S[0], S[1:]
    return sum(x * fact(e) * V(M, rest, A + rp(c, e), B + sp(c, e)) for e, x in enumerate(f))


def Phi(M, n, S, factors):
    """factors: list of functions c ↦ coefficient list."""
    if not factors:
        return V(M, S)
    phi, rest = factors[0], factors[1:]
    tot = Fr(0)
    for j, (c, f) in enumerate(S):
        S2 = list(S)
        S2[j] = (c, pmul(f, phi(c)))
        tot += Phi(M, n, S2, rest)
    for c in range(3):
        mult = n[c] - sum(1 for (cc, _) in S if cc == c)
        tot += mult * Phi(M, n, [(c, phi(c))] + S, rest)
    return tot


def subsetTerms(lam):
    if not lam:
        return [([], 0)]
    q, rest = lam[0], lam[1:]
    st = subsetTerms(rest)
    return [([q] + K, s) for (K, s) in st] + [(K, s + q) for (K, s) in st]


def innerTerms(a, lam):
    return [(K, s + l + 1, a - l, Fr(comb(a, l) * (-1) ** l, s + l + 1))
            for (K, s) in subsetTerms(lam) for l in range(a + 1)]


def genPiece(r, k, a1, l1, a2, l2, Mo=None):
    G = E.G
    sig = [G, G, Fr(0)]
    n = [r, k, N - r - k]
    if Mo is None:
        Mo = lambda A, B, m, nn: pieceMn(r, k, A, B, m, nn)
    tot = Fr(0)
    for (K1, p1, q1, c1) in innerTerms(a1, l1):
        for (K2, p2, q2, c2) in innerTerms(a2, l2):
            fac = [(lambda c, q=q: shiftPow(sig[c], q)) for q in K1 + K2]
            tot += c1 * c2 * Phi(lambda A, B: Mo(A, B, p1 + p2, q1 + q2), n, [], fac)
    return tot


def genEntry(a1, l1, a2, l2):
    return (N + 1) * sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * genPiece(r, k, a1, l1, a2, l2)
                                         for k in range(N - r + 1)) for r in range(N + 1))


def keys(a1, l1, a2, l2):
    """The moment keys (A, B, m, n) queried by genPiece (any piece)."""
    seen = set()
    genPiece(1, 1, a1, l1, a2, l2, Mo=lambda A, B, m, n: (seen.add((A, B, m, n)), Fr(0))[1])
    return sorted(seen)
