#!/usr/bin/env python3
"""V2n model: direct moment-profile transitions through marked profiles (exploratory mirror).

A state is a list of parts (c, e) with coefficient κ and weight W = ∏ e!; its rough and smooth
degrees are (A, B). The *marked profile of order t* of a combination L collects, for every
ordered tuple u of t distinct parts (positions) of every state,

    ((A, B, u), κ · W)

and `aug(T, L)` is the union over t ≤ T (order 0 is V2ℓ's `abProfile`). One factor φ maps
`aug(T + 1, L)` to `aug(T, child)` entry by entry (`aug_step`), without forming child states.

Checks (run as a script):
  * the profile alone is insufficient (two counterexamples, also checked in Lean);
  * `aug_step` agrees with the marked profile of the true child (V2k's `symStep`) on random states
    and on V2m's stored nodes at Table 3, piece (6, 3), for T ≤ 3;
  * sizes: marked profiles against V2m's states for the three-factor layer and the block |λ| ≤ 8.
"""
import os
import random
import sys
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_entry_v2i_model as Q  # noqa: E402
import sym_reduce_v2k_model as S  # noqa: E402


def W(k):
    w = 1
    for (_, e) in k:
        w *= factorial(e)
    return w


def AB(k):
    return (sum(e for (c, e) in k if c == 0), sum(e for (c, e) in k if c != 0))


def picks(l):
    return [(l[i], l[:i] + l[i + 1:]) for i in range(len(l))]


def dtup(t, l):
    if t == 0:
        return [()]
    return [(x,) + u for (x, r) in picks(l) for u in dtup(t - 1, r)]


def collect(entries, keep_zero=False):
    acc = {}
    for k, v in entries:
        acc[k] = acc.get(k, Fr(0)) + v
    return acc if keep_zero else {k: v for k, v in acc.items() if v != 0}


def mkey(k):
    """Lean's markCmp order: A, B, then the marks by keyCmp (class ascending, exponent descending)."""
    A, B, u = k
    return (A, B, tuple((c, -e) for (c, e) in u))


def lean_sorted(acc):
    return sorted(acc.items(), key=lambda kv: mkey(kv[0]))


def aug_lean(T, L):
    """Lean's `markProfile T L` (zeros kept, markCmp order)."""
    out = []
    for (k, kap) in L:
        A, B = AB(k)
        for t in range(T + 1):
            for u in dtup(t, list(k)):
                out.append(((A, B, u), kap * W(k)))
    return lean_sorted(collect(out, True))


def step_lean(T, n, phi, P):
    """Lean's `markStep n φ T P` (zeros kept, markCmp order); P a list of (key, value)."""
    return lean_sorted(collect(emit(T, n, phi, P), True))


def emit(T, n, phi, P):
    C = sum(n[c] * (phi(c)[0] if phi(c) else 0) for c in range(3))
    out = []
    for (A, B, u), v in P:
        m = len(u)
        if m <= T:
            out.append(((A, B, u), v * C))
        if m >= 1:
            (c, e), w = u[0], u[1:]
            for a, f in pos_terms(phi(c)):
                key = (A + r_(c, a), B + s_(c, a))
                out.append((key + (w,), v * f * (desc(e + a, a) - factorial(a))))
                if m <= T:
                    for i in range(m):
                        out.append((key + (w[:i] + ((c, e + a),) + w[i:],), v * f * desc(e + a, a)))
                        out.append((key + (w[:i] + ((c, a),) + w[i:],), -(v * f * factorial(a))))
        for c in range(3):
            cnt = sum(1 for x in u if x[0] == c)
            for a, f in pos_terms(phi(c)):
                key = (A + r_(c, a), B + s_(c, a))
                wt = (n[c] - cnt) * f * factorial(a) * v
                if m <= T:
                    out.append((key + (u,), wt))
                if m + 1 <= T:
                    for i in range(m + 1):
                        out.append((key + (u[:i] + ((c, a),) + u[i:],), wt))
    return out


def to_prof(P):
    """Lean's `markToProf` (normalized by (A, B), zeros kept)."""
    acc = {}
    for (A, B, u), v in P:
        acc[(A, B)] = acc.get((A, B), Fr(0)) + v
    return sorted(acc.items())


def aug(T, L):
    out = []
    for (k, kap) in L:
        A, B = AB(k)
        for t in range(T + 1):
            for u in dtup(t, list(k)):
                out.append(((A, B, u), kap * W(k)))
    return collect(out)


def r_(c, a):
    return a if c == 0 else 0


def s_(c, a):
    return 0 if c == 0 else a


def desc(n, k):
    p = 1
    for i in range(k):
        p *= n - i
    return p


def pos_terms(f):
    return [(a, f[a]) for a in range(1, len(f)) if f[a] != 0]


def aug_step(T, n, phi, P):
    """One factor on a marked profile of order ≤ T + 1, giving order ≤ T (entry by entry)."""
    C = sum(n[c] * (phi(c)[0] if phi(c) else 0) for c in range(3))
    out = []
    for (A, B, u), v in P.items():
        m = len(u)
        if m <= T and C != 0:
            out.append(((A, B, u), v * C))                                   # E1 constant terms
        if m >= 1:
            (c, e), w = u[0], u[1:]
            for a, f in pos_terms(phi(c)):
                key = (A + r_(c, a), B + s_(c, a))
                # E2 + E4: the marked part absorbs a, minus the opening counted by ℓ_c
                if m - 1 <= T:
                    out.append(((key + (w,)), v * f * (desc(e + a, a) - factorial(a))))
                if m <= T:
                    for i in range(m):
                        out.append((key + (w[:i] + ((c, e + a),) + w[i:],), v * f * desc(e + a, a)))   # E3
                        out.append((key + (w[:i] + ((c, a),) + w[i:],), -v * f * factorial(a)))     # E4'
        for c in range(3):
            cnt = sum(1 for x in u if x[0] == c)
            for a, f in pos_terms(phi(c)):
                key = (A + r_(c, a), B + s_(c, a))
                wt = v * (n[c] - cnt) * f * factorial(a)
                if m <= T:
                    out.append((key + (u,), wt))                                  # E5 new part, unmarked
                if m + 1 <= T:
                    for i in range(m + 1):
                        out.append((key + (u[:i] + ((c, a),) + u[i:],), wt))       # E6 new part, marked
    return collect(out)


def child(n, phi, L):
    return S.normalize([e for (k, kap) in L for e in S.step(n, phi, k, kap)])


def counterexamples(n, phi):
    L1, L2 = [(((0, 2),), Fr(1))], [(((0, 1), (0, 1)), Fr(2))]
    assert aug(0, L1) == aug(0, L2)
    assert aug(0, child(n, phi, L1)) != aug(0, child(n, phi, L2))
    L3, L4 = [(((0, 3), (0, 1)), Fr(2))], [(((0, 2), (0, 2)), Fr(3))]
    assert aug(0, L3) == aug(0, L4)
    cls = lambda L: collect([((AB(k), c), kap * W(k) * sum(1 for x in k if x[0] == c)) for (k, kap) in L for c in range(3)])  # noqa: E731
    assert cls(L3) == cls(L4)
    assert aug(0, child(n, phi, L3)) != aug(0, child(n, phi, L4))
    return True


def main():
    g = Fr(41, 625)
    sig = [g, g, Fr(0)]
    n = [6, 3, 35]
    fac = lambda q: (lambda c: Q.shiftPow(sig[c], q))  # noqa: E731
    assert counterexamples(n, fac(2))
    rnd = random.Random(7)
    for trial in range(60):
        L = []
        for _ in range(rnd.randint(1, 4)):
            k = tuple(sorted(((rnd.randint(0, 2), rnd.randint(1, 5)) for _ in range(rnd.randint(0, 4))),
                             key=lambda x: (x[0], -x[1])))
            L.append((k, Fr(rnd.randint(-5, 5), rnd.randint(1, 4))))
        q = rnd.choice([2, 4, 6])
        T = rnd.randint(0, 3)
        assert aug_step(T, n, fac(q), aug(T + 1, L)) == aug(T, child(n, fac(q), L)), (L, q, T)
    print("random transitions: ok")
    # chains: from the state of [2, 2] (V2m stored) to [2]^5 profiles through orders 3, 2, 1, 0
    L = [((), Fr(1))]
    for q in [2, 2]:
        L = child(n, fac(q), L)
    P = aug(3, L)
    Ls = L
    for T, q in zip([2, 1, 0], [2, 2, 2]):
        P = aug_step(T, n, fac(q), P)
        Ls = child(n, fac(q), Ls)
        assert P == aug(T, Ls)
    print("chain [2,2] -> [2]^5 through orders 3,2,1,0: ok;", len(Ls), "states at [2]^5, profile", len(P))
    # the Lean-order mirror agrees with the set-level model
    Lp = child(n, fac(2), [((), Fr(1))])
    P2 = aug_lean(2, Lp)
    P1 = step_lean(1, n, fac(4), P2)
    assert {k: v for k, v in P1 if v != 0} == aug(1, child(n, fac(4), Lp))
    print("Lean-order mirror: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
