#!/usr/bin/env python3
"""Positive and negative controls for V2f (all endpoint branches; the marginal entry J_T[1, 1]).

Writes Lean files into the given directory (default /tmp/v2f_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected. Independent checks run here first:

  (a) small synthetic data (N = 3, g = 3/10, L = 1, τ = 9/10, C = 0, 1/2, 3/5, 7/10, 7/10, …;
      the hypotheses of jT_one_eq hold): the closed form jtSum 3 … 2 0 against a direct midpoint
      grid integration of 4 ∫_{T̂} U(x)² with the true rough-set endpoint (no stratification,
      no translation, no aggregates);
  (b) Table 3, piece (r, k) = (1, 0) in dimension 44: pieceJ against exact polygon clipping of
      the four branch cells in the (u₁, u₂) plane (no boxVal, no signed cells);
  (c) Table 3, N = 44: J_T[1, 1] against a Monte Carlo estimate (uniform samples of the τ-simplex,
      true rough-set endpoint), |z| < 4.

  ok_small / nc_small_*     jtSum on the synthetic data; nc_small_gcell assigns the L − S value
                            on the g cell, nc_small_U the first power U instead of U².
  ok_piece / nc_piece       pieceJ 44 1 0 at Table 3 equals the clipping value; the cap-only
                            value (all of the piece on the cap branch) is rejected.
  ok_entry / nc_entry_*     J_T[1, 1] at Table 3 (jT_one_table3); nc_entry_capindex uses C(r) for
                            C(r+1) in the endpoint, nc_entry_U the first power.

Usage: python3 -I specs/checks/marginal_entry_v2f_controls.py [dir] [--mc SAMPLES]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import itertools
import math
import os
import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import marginal_entry_v2f_emit as E  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else "/tmp/v2f_ctl"
MC = int(sys.argv[sys.argv.index("--mc") + 1]) if "--mc" in sys.argv else 100000
os.makedirs(OUT, exist_ok=True)


# ---- the closed form with arbitrary data (mirror of BGP212/MarginalEntry.lean) ------------------
def jt_closed(N, g, L, tau, Cf, m=2, n=0, variant=None):
    E.G, E.L, E.TAU, E.N = g, L, tau, N
    E.C = Cf
    if variant == "gcell":           # the g cell evaluated with the L − S value
        orig = E.cells

        def cells(r, k, c, M, al, be, m_, n_):
            Lp = L - (r + k) * g
            c1 = Cf(r + 1) - (r + 1) * g
            A1 = min(c, c1)
            M3 = min(M, Lp - g)
            v = orig(r, k, c, M, al, be, m_, n_)
            tp = E.twopow
            v -= g ** m_ * (tp(c, M, M3, 0, Lp, al, be, 0, n_) - tp(A1, M, M3, 0, Lp, al, be, 0, n_))
            v += tp(c, M, M3, 0, Lp, al, be, 0, m_ + n_) - tp(A1, M, M3, 0, Lp, al, be, 0, m_ + n_)
            return v
        E.cells = cells
    try:
        tot = (N + 1) * sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * E.pieceJ(r, k, m, n)
                                             for k in range(N - r + 1)) for r in range(N + 1))
    finally:
        if variant == "gcell":
            E.cells = orig
    return tot


def restore_table3():
    E.G, E.L, E.TAU, E.N = Fr(41, 625), Fr(53, 50), Fr(249, 250), 44
    E.C = lambda m: Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000)


# ---- (a) synthetic data, N = 3 -----------------------------------------------------------------
gs, Ls, ts = Fr(3, 10), Fr(1), Fr(9, 10)
CS = [Fr(0), Fr(1, 2), Fr(3, 5), Fr(7, 10)]
Cs = lambda m: CS[min(m, 3)]
assert Cs(3) - 3 * gs < 0 and gs <= Cs(1)
v_small = jt_closed(3, gs, Ls, ts, Cs)
v_small_g = jt_closed(3, gs, Ls, ts, Cs, variant="gcell")
v_small_U = jt_closed(3, gs, Ls, ts, Cs, m=1)


def grid(N, n, g, L, tau, Cf):
    h = float(tau) / n
    gf, Lf, tf = float(g), float(L), float(tau)
    Cv = [float(Cf(m)) for m in range(N + 2)]
    tot = 0.0
    for idx in itertools.product(range(n), repeat=N):
        x = [(i + 0.5) * h for i in idx]
        S = sum(x)
        if S > tf:
            continue
        R = [v for v in x if v > gf]
        s = len(R)
        rho = sum(R)
        if rho > Cv[s]:
            continue
        U = min(Lf - S, max(gf, Cv[s + 1] - rho))
        tot += U * U
    return (N + 1) * tot * h ** N


g_small = grid(3, 200, gs, Ls, ts, Cs)
assert abs(g_small - float(v_small)) / float(v_small) < 1e-2, (g_small, float(v_small))
assert abs(g_small - float(v_small_g)) / float(v_small) > 5e-2

# ---- (b) Table 3, piece (1, 0) in dimension 44, by polygon clipping ------------------------------
restore_table3()
G, L, TAU, C = E.G, E.L, E.TAU, E.C


def clip(poly, a, b, c):
    out = []
    for i in range(len(poly)):
        P, Q = poly[i], poly[(i + 1) % len(poly)]
        fP = a * P[0] + b * P[1] - c
        fQ = a * Q[0] + b * Q[1] - c
        if fP <= 0:
            out.append(P)
        if (fP < 0 < fQ) or (fQ < 0 < fP):
            t = fP / (fP - fQ)
            out.append((P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])))
    return out


def pmul(p, q):
    o = {}
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            o[(a + d, b + e)] = o.get((a + d, b + e), 0) + c * f
    return o


def ppow(p, n):
    o = {(0, 0): Fr(1)}
    for _ in range(n):
        o = pmul(o, p)
    return o


def tri_int(f, A, B, Cc):
    xs = {(0, 0): A[0], (1, 0): B[0] - A[0], (0, 1): Cc[0] - A[0]}
    ys = {(0, 0): A[1], (1, 0): B[1] - A[1], (0, 1): Cc[1] - A[1]}
    jac = abs((B[0] - A[0]) * (Cc[1] - A[1]) - (Cc[0] - A[0]) * (B[1] - A[1]))
    tot = Fr(0)
    for (i, j), c in f.items():
        for (u, v), w in pmul(ppow(xs, i), ppow(ys, j)).items():
            tot += c * w * Fr(fact(u) * fact(v), fact(u + v + 2))
    return jac * tot


def poly_on(cons, f):
    big = Fr(10)
    P = [(Fr(0), Fr(0)), (big, Fr(0)), (big, big), (Fr(0), big)]
    for (a, b, c) in cons:
        P = clip(P, a, b, c)
    if len(P) < 3:
        return Fr(0)
    return sum(tri_int(f, P[0], P[i], P[i + 1]) for i in range(1, len(P) - 1))


r, k, Nn = 1, 0, 44
c = C(r) - r * G
M = TAU - (r + k) * G
Lp = L - (r + k) * G
c1, c2, c3 = C(r + 1) - (r + 1) * G, L - k * G - C(r + 1), Lp - G
al, be = r - 1, Nn - r - 1
wt = {(al, be): Fr(1)}
base = [(-1, 0, 0), (0, -1, 0), (1, 0, c), (1, 1, M)]
capP = pmul(wt, ppow({(0, 0): C(r + 1) - r * G, (1, 0): Fr(-1)}, 2))
LsP = pmul(wt, ppow({(0, 0): Lp, (1, 0): Fr(-1), (0, 1): Fr(-1)}, 2))
gP = {(al, be): G ** 2}
v_clip = (poly_on(base + [(1, 0, c1), (0, 1, c2)], capP)
          + poly_on(base + [(1, 0, c1), (0, -1, -c2)], LsP)
          + poly_on(base + [(-1, 0, -c1), (1, 1, c3)], gP)
          + poly_on(base + [(-1, 0, -c1), (-1, -1, -c3)], LsP)) / (fact(al) * fact(be))
v_piece = E.pieceJ(1, 0)
assert v_clip == v_piece, (float(v_clip), float(v_piece))
v_piece_caponly = poly_on(base, capP) / (fact(al) * fact(be))
assert v_piece_caponly != v_piece

# ---- (c) Table 3, N = 44: the entry, its variants, Monte Carlo ----------------------------------
v_entry = jt_closed(44, G, L, TAU, C)
restore_table3()
assert v_entry == (45 * sum(comb(44, r) * E.row(r) for r in range(45)))
Cshift = lambda m: C(m - 1) if m >= 1 else Fr(0)      # C(r) in place of C(r+1) inside U
v_entry_capindex = None
# the cap index enters only through C(r+1); shifting the function by one realizes C(r)
v_entry_U = jt_closed(44, G, L, TAU, C, m=1)
restore_table3()


def jt_capindex():
    # U with C(s) in place of C(s+1): same pieces, endpoint built from C(r)
    E.G, E.L, E.TAU, E.N = G, L, TAU, 44
    orig_cells, orig_seg0 = E.cells, E.seg0
    E.C = lambda m: (Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000))
    Cpiece = E.C

    def cells(r, k, c_, M_, al_, be_, m_, n_):
        saved = E.C
        E.C = lambda mm: Cpiece(mm - 1) if mm >= 1 else Fr(0)
        try:
            return orig_cells(r, k, c_, M_, al_, be_, m_, n_)
        finally:
            E.C = saved

    def seg0(k_, M_, be_, m_, n_):
        saved = E.C
        E.C = lambda mm: Cpiece(mm - 1) if mm >= 1 else Fr(0)
        try:
            return orig_seg0(k_, M_, be_, m_, n_)
        finally:
            E.C = saved
    E.cells, E.seg0 = cells, seg0
    try:
        return 45 * sum(comb(44, r) * sum(comb(44 - r, k) * (-1) ** k * E.pieceJ(r, k)
                                          for k in range(45 - r)) for r in range(45))
    finally:
        E.cells, E.seg0 = orig_cells, orig_seg0
        restore_table3()


v_entry_capindex = jt_capindex()
assert len({v_entry, v_entry_capindex, v_entry_U}) == 3

random.seed(11)
gf, Lf, tf = float(G), float(L), float(TAU)
Cv = [float(C(m)) for m in range(47)]
s1 = s2 = 0.0
for _ in range(MC):
    e = [random.expovariate(1.0) for _ in range(45)]
    T = sum(e)
    x = [tf * v / T for v in e[:44]]
    S = sum(x)
    R = [v for v in x if v > gf]
    rho = sum(R)
    val = 0.0
    if rho <= Cv[len(R)]:
        U = min(Lf - S, max(gf, Cv[len(R) + 1] - rho))
        val = U * U
    s1 += val
    s2 += val * val
vol = tf ** 44 / math.factorial(44)
mean = s1 / MC
est = 45 * vol * mean
err = 45 * vol * math.sqrt(max(s2 / MC - mean * mean, 0) / MC)
z = (est - float(v_entry)) / err
assert abs(z) < 4, z


def q(v, field="ℚ"):
    v = Fr(v)
    return f"({v.numerator} / {v.denominator} : {field})"


HEAD = """import Solution.MarginalEntry

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
SMALL = """def Csm : ℕ → ℚ := fun m => if m = 0 then 0 else if m = 1 then 1 / 2 else if m = 2 then 3 / 5 else 7 / 10

theorem ctl : jtSum 3 (3 / 10 : ℚ) 1 (9 / 10) Csm {M} 0 = {V} := by decide +kernel
"""
PIECE = """theorem ctl : pieceJ 44 1 0 BGP212.Params.g BGP212.Params.L BGP212.Params.τ BGP212.Params.C 2 0 =
    {V} := by
  rw [pj_1_0]
  all_goals norm_num
"""
ENTRY = """theorem ctl : jT 44 g3 L3 τ3 C3 (fun _ => 1) = (({V} : ℚ) : ℝ) := by
  rw [jT_one_table3]
  all_goals norm_num
"""
files = {
    "ok_small": SMALL.replace("{M}", "2").replace("{V}", q(v_small)),
    "nc_small_gcell": SMALL.replace("{M}", "2").replace("{V}", q(v_small_g)),
    "nc_small_U": SMALL.replace("{M}", "2").replace("{V}", q(v_small_U)),
    "ok_small_U": SMALL.replace("{M}", "1").replace("{V}", q(v_small_U)),
    "ok_piece": PIECE.replace("{V}", q(v_clip)),
    "nc_piece": PIECE.replace("{V}", q(v_piece_caponly)),
    "ok_entry": ENTRY.replace("{V}", q(v_entry)),
    "nc_entry_capindex": ENTRY.replace("{V}", q(v_entry_capindex)),
    "nc_entry_U": ENTRY.replace("{V}", q(v_entry_U)),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("(a) N = 3 synthetic: closed form", float(v_small), " grid", g_small,
      " g-cell variant", float(v_small_g))
print("(b) piece (1, 0): clipping = pieceJ =", float(v_piece), " cap-only", float(v_piece_caponly))
print("(c) J_T[1,1] =", float(v_entry), " MC", est, "±", err, " z =", round(z, 2))
print("    variants: cap index C(r)", float(v_entry_capindex), " first power U", float(v_entry_U))
