#!/usr/bin/env python3
"""Positive and negative controls for V2g (the power-sum marginal Gram entry J_T[P₂, 1]).

Writes Lean files into the given directory (default /tmp/v2g_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected. Independent checks run here first:

  (a) synthetic data (N = 3, g = 3/10, L = 1, τ = 9/10, C = 0, 1/2, 3/5, 7/10, …; the hypotheses
      of p2Entry_eq hold): the closed form p2EntryVal 3 … against a direct midpoint grid
      integration of 4 ∫_{T̂} (U² P̂₂ + U⁴/3) with the true rough-set endpoint and the untranslated
      power sum (no stratification, no translation, no placements);
  (b) Table 3, N = 44: J_T[P₂, 1] against a Monte Carlo estimate (uniform samples of the
      τ-simplex), |z| < 4.

  ok_small / nc_small_*   p2EntryVal on the synthetic data; nc_small_noshift drops the shift
                          (P̂₂(y) in place of P̂₂(y + g·1_{R∪K})), nc_small_Kplain treats the K
                          coordinates as unshifted.
  ok_entry / nc_entry_*   J_T[P₂, 1] at Table 3 (jT_P2_one_table3); nc_entry_noshift and
                          nc_entry_U4only (the U⁴/3 term alone, i.e. P₂ ↦ u²).

Usage: python3 -I specs/checks/power_sum_entry_v2g_controls.py [dir] [--mc SAMPLES]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import itertools
import math
import os
import random
import sys
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import marginal_entry_v2f_emit as E  # noqa: E402
import power_sum_entry_v2g_emit as P  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else "/tmp/v2g_ctl"
MC = int(sys.argv[sys.argv.index("--mc") + 1]) if "--mc" in sys.argv else 100000
os.makedirs(OUT, exist_ok=True)


def setdata(N, g, L, tau, Cf):
    E.N, E.G, E.L, E.TAU, E.C = N, g, L, tau, Cf
    P.N = N


def p2_variant(r, k, variant):
    G, N = E.G, P.N
    pe = P.pieceE
    if variant == "noshift":
        return (N - r) * pe(r, k, 0, 2, 2) + (r * pe(r, k, 2, 0, 2) if r > 0 else 0)
    if variant == "Kplain":
        v = (N - r) * pe(r, k, 0, 2, 2)
        if r > 0:
            v += r * (pe(r, k, 2, 0, 2) + 2 * G * pe(r, k, 1, 0, 2) + G ** 2 * pe(r, k, 0, 0, 2))
        return v
    return P.p2J(r, k)


def entry(variant=None, with_p2=True):
    N = P.N
    s2 = sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * p2_variant(r, k, variant)
                              for k in range(N - r + 1)) for r in range(N + 1)) if with_p2 else 0
    s4 = sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * E.pieceJ(r, k, 4, 0)
                              for k in range(N - r + 1)) for r in range(N + 1))
    return (N + 1) * (s2 + s4 / 3)


# ---- (a) synthetic N = 3 -------------------------------------------------------------------------
gs, Ls, ts = Fr(3, 10), Fr(1), Fr(9, 10)
CS = [Fr(0), Fr(1, 2), Fr(3, 5), Fr(7, 10)]
Cs = lambda m: CS[min(m, 3)]
setdata(3, gs, Ls, ts, Cs)
v_small = entry()
v_small_noshift = entry("noshift")
v_small_K = entry("Kplain")


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
        R = [w for w in x if w > gf]
        rho = sum(R)
        if rho > Cv[len(R)]:
            continue
        U = min(Lf - S, max(gf, Cv[len(R) + 1] - rho))
        tot += U * U * sum(w * w for w in x) + U ** 4 / 3
    return (N + 1) * tot * h ** N


g_small = grid(3, 200, gs, Ls, ts, Cs)
assert abs(g_small - float(v_small)) / float(v_small) < 1.5e-2, (g_small, float(v_small))
assert abs(g_small - float(v_small_noshift)) / float(v_small) > 5e-2

# ---- (b) Table 3, N = 44 -------------------------------------------------------------------------
G, L, TAU = Fr(41, 625), Fr(53, 50), Fr(249, 250)
C3 = lambda m: Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000)
setdata(44, G, L, TAU, C3)
v_entry = entry()
v_entry_noshift = entry("noshift")
v_entry_U4 = entry(with_p2=False)
assert len({v_entry, v_entry_noshift, v_entry_U4}) == 3

random.seed(13)
gf, Lf, tf = float(G), float(L), float(TAU)
Cv = [float(C3(m)) for m in range(47)]
s1 = s2 = 0.0
for _ in range(MC):
    e = [random.expovariate(1.0) for _ in range(45)]
    T = sum(e)
    x = [tf * w / T for w in e[:44]]
    S = sum(x)
    R = [w for w in x if w > gf]
    rho = sum(R)
    val = 0.0
    if rho <= Cv[len(R)]:
        U = min(Lf - S, max(gf, Cv[len(R) + 1] - rho))
        val = U * U * sum(w * w for w in x) + U ** 4 / 3
    s1 += val
    s2 += val * val
vol = tf ** 44 / math.factorial(44)
mean = s1 / MC
est = 45 * vol * mean
err = 45 * vol * math.sqrt(max(s2 / MC - mean * mean, 0) / MC)
z = (est - float(v_entry)) / err
assert abs(z) < 4, z


def q(v):
    v = Fr(v)
    return f"({v.numerator} / {v.denominator} : ℚ)"


HEAD = """import Solution.PowerSumEntry

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
SMALL = """def Csm : ℕ → ℚ := fun m => if m = 0 then 0 else if m = 1 then 1 / 2 else if m = 2 then 3 / 5 else 7 / 10

theorem ctl : p2EntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) Csm = {V} := by decide +kernel
"""
ENTRY = """theorem ctl : jTbil 44 g3 L3 τ3 C3
    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) = (({V}) : ℝ) := by
  rw [jT_P2_one_table3]
  all_goals norm_num
"""
files = {
    "ok_small": SMALL.replace("{V}", q(v_small)),
    "nc_small_noshift": SMALL.replace("{V}", q(v_small_noshift)),
    "nc_small_Kplain": SMALL.replace("{V}", q(v_small_K)),
    "ok_entry": ENTRY.replace("{V}", q(v_entry)),
    "nc_entry_noshift": ENTRY.replace("{V}", q(v_entry_noshift)),
    "nc_entry_U4only": ENTRY.replace("{V}", q(v_entry_U4)),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("(a) N = 3 synthetic: closed form", float(v_small), " grid", g_small,
      " no-shift", float(v_small_noshift), " K unshifted", float(v_small_K))
print("(b) J_T[P2,1] =", float(v_entry), " MC", est, "±", err, " z =", round(z, 2))
print("    variants: no shift", float(v_entry_noshift), " U⁴/3 only", float(v_entry_U4))
