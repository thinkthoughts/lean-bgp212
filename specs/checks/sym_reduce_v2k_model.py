#!/usr/bin/env python3
"""Exact mirror of V2k's symmetric-function evaluator (BGP212/SymReduce.lean).

A state is a canonical list of parts (c, e) — class, positive exponent — sorted by class ascending,
then exponent descending (one integer partition per class). It stands for the product of
augmented monomial symmetric functions ∏_c m̃_{ν_c}. A factor φ (class ↦ coefficient list)
multiplies by Σ_c n_c φ(c)_0 + Σ_c Σ_{a≥1} φ(c)_a p_{c,a}, using

    p_{c,a} · m̃_ν = Σ_j m̃_{ν + a e_j} + m̃_{ν ∪ (a)}          (new part weighted by n_c − ℓ(ν_c)).

After all factors a state contributes ∏ e! · M(rough degree, smooth degree).

Like the Lean definitions, every generated entry is kept (also with coefficient 0) and equal
states are merged after each factor; the output is sorted in the canonical order, so the lists
printed here are exactly the kernel's normal forms.

Usage: python3 -I specs/checks/sym_reduce_v2k_model.py   (self-checks against V2i's model)
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_entry_v2i_model as Q  # noqa: E402


def keyorder(k):
    """Lean's keyCmp: lexicographic in parts, part order (class asc, exponent desc)."""
    return [(c, -e) for (c, e) in k]


def ins(y, k):
    """Lean's sIns."""
    for i, x in enumerate(k):
        if y[0] < x[0] or (y[0] == x[0] and y[1] >= x[1]):
            return k[:i] + (y,) + k[i:]
    return k + (y,)


def const_term(f):
    return f[0] if f else Fr(0)


def pos_terms(f):
    return [(a, f[a]) for a in range(1, len(f)) if f[a] != 0]


def step(n, phi, k, kap, weighted=True):
    """Lean's symStep (weighted) / symStep1 (unweighted)."""
    out = []
    T = sum(n[c] * const_term(phi(c)) for c in range(3))
    if T != 0:
        out.append((k, kap * T))
    for i, x in enumerate(k):
        r = k[:i] + k[i + 1:]
        for a, co in pos_terms(phi(x[0])):
            out.append((ins((x[0], x[1] + a), r), kap * co))
    for c in range(3):
        cnt = sum(1 for y in k if y[0] == c)
        w = (n[c] - cnt) if weighted else 1
        for a, co in pos_terms(phi(c)):
            out.append((ins((c, a), k), kap * w * co))
    return out


def normalize(entries, order=keyorder):
    acc = {}
    for k, v in entries:
        acc[k] = acc.get(k, Fr(0)) + v
    return sorted(acc.items(), key=lambda kv: order(kv[0]))


def sym_run(n, factors, weighted=True, stats=None):
    L = [((), Fr(1))]
    for phi in factors:
        gen = [e for (k, kap) in L for e in step(n, phi, k, kap, weighted)]
        L = normalize(gen)
        if stats is not None:
            stats.append((len(gen), len(L)))
    return L


def key_AB(k):
    return (sum(e for c, e in k if c == 0), sum(e for c, e in k if c != 0))


def factW(k):
    w = 1
    for _, e in k:
        w *= fact(e)
    return w


def sym_place_val(M, n, factors):
    return sum(kap * factW(k) * M(*key_AB(k)) for k, kap in sym_run(n, factors))


def ps_factor(c, a):
    return lambda cc: ([Fr(0)] * a + [Fr(1)]) if cc == c else []


def ps_trans(alpha, n=(0, 0, 0)):
    """Lean's psTrans: p_α = Σ_ν R_{α,ν} m̃_ν (unweighted run)."""
    return sym_run(n, [ps_factor(c, a) for (c, a) in alpha], weighted=False)


def desc(m, l):
    out = 1
    for i in range(l):
        out *= (m - i)
    return out


def fallW(n, k):
    return desc(n[0], sum(1 for c, _ in k if c == 0)) * desc(n[1], sum(1 for c, _ in k if c == 1)) * \
        desc(n[2], sum(1 for c, _ in k if c == 2))


def gen_table(r, k, a1, l1, a2, l2):
    """Lean's genTable at the data loaded in Q / E (piece (r, k))."""
    G = Q.E.G
    sig = [G, G, Fr(0)]
    n = [r, k, Q.N - r - k]
    acc = {}
    for (K1, p1, q1, c1) in Q.innerTerms(a1, l1):
        for (K2, p2, q2, c2) in Q.innerTerms(a2, l2):
            fac = [(lambda c, q=q: Q.shiftPow(sig[c], q)) for q in K1 + K2]
            for st, kap in sym_run(n, fac):
                A, B = key_AB(st)
                s = (A, B, p1 + p2, q1 + q2)
                acc[s] = acc.get(s, Fr(0)) + c1 * c2 * kap * factW(st)
    return sorted(acc.items())


def agg_table(r, k, ws):
    acc = {}
    for (w, a1, l1, a2, l2) in ws:
        for s, v in gen_table(r, k, a1, l1, a2, l2):
            acc[s] = acc.get(s, Fr(0)) + w * v
    return sorted(acc.items())


# --- counting the placement recursion -------------------------------------------------------

def place_count(n, S, factors, M):
    """V2i's placement recursion (Q.Phi) with oracle calls counted through M."""
    return Q.Phi(M, n, S, factors)


def _selfcheck():
    g = Fr(3, 10)
    sig = [g, g, Fr(0)]
    n = [3, 2, 4]
    calls = [0]

    def M(A, B):
        calls[0] += 1
        return Fr(1, (A + 1) * (B + 2) + A * B + 3)

    print("| factor degrees | V2i oracle calls | V2i s | V2k states (generated → kept per factor, total kept) | V2k s | agree |")
    for qs in [[2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [3, 2, 2, 1, 1, 1]]:
        fac = [(lambda c, q=q: Q.shiftPow(sig[c], q)) for q in qs]
        calls[0] = 0
        t = time.time()
        a = Q.Phi(M, n, [], fac)
        t1 = time.time() - t
        c1 = calls[0]
        st = []
        t = time.time()
        L = sym_run(n, fac, stats=st)
        b = sum(kap * factW(k) * Fr(1, (key_AB(k)[0] + 1) * (key_AB(k)[1] + 2) + key_AB(k)[0] * key_AB(k)[1] + 3)
                for k, kap in L)
        t2 = time.time() - t
        print(f"| {qs} | {c1} | {t1:.2f} | {st} total {sum(x for _, x in st)} | {t2:.3f} | {a == b} |")
        assert a == b
    # weighted run = unweighted run scaled by the index counts (symRun_scale)
    fac = [(lambda c, q=q: Q.shiftPow(sig[c], q)) for q in [2, 3, 1]]
    W = sym_run(n, fac)
    U = sym_run(n, fac, weighted=False)
    assert [k for k, _ in W] == [k for k, _ in U]
    assert all(w == u * fallW(n, k) for (k, w), (_, u) in zip(W, U))
    # tables against V2i's piece value with an arbitrary oracle (Table 3, piece (6, 3))
    Mo = lambda A, B, m, nn: Fr(1, 1 + A + 2 * B + 3 * m + 5 * nn + A * B)
    for args in [(0, [2], 0, [2]), (0, [2, 2], 0, [2, 2]), (1, [2], 0, [3])]:
        T = gen_table(6, 3, *args)
        assert sum(v * Mo(*s) for s, v in T) == Q.genPiece(6, 3, *args, Mo=Mo)
        print("table", args, "keys", len(T), "agrees with V2i's genPiece")
    print("transition examples:", ps_trans([(0, 2), (0, 2)]), ps_trans([(0, 2), (1, 1), (0, 1)]))
    print("self-check passed")


if __name__ == "__main__":
    _selfcheck()
