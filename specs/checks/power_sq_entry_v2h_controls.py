#!/usr/bin/env python3
"""Positive and negative controls for V2h (the marginal Gram entry J_T[P₂, P₂]).

Writes Lean files into the given directory (default /tmp/v2h_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected. Independent checks run here first:

  (a) synthetic data (N = 3, g = 3/10, L = 1, τ = 9/10, C = 0, 1/2, 3/5, 7/10, …; the hypotheses
      of p2p2Entry_eq hold): the closed form p2p2EntryVal 3 … against a direct midpoint grid
      integration of 4 ∫_{T̂} (U P̂₂ + U³/3)² with the true rough-set endpoint and the untranslated
      power sum (no stratification, no translation, no placements, no moments);
  (b) Table 3, N = 44: J_T[P₂, P₂] against a Monte Carlo estimate (uniform samples of the
      τ-simplex), |z| < 4;
  (c) Cauchy–Schwarz for the 2 × 2 block {1, P₂}: J[P₂,1]² ≤ J[1,1] J[P₂,P₂] (exact rationals).

  ok_small / nc_small_*   p2p2EntryVal on the synthetic data; nc_small_nodiag counts the ordered
                          pairs of classes n_c n_d without removing the diagonal i = j (the
                          diagonal counted twice), nc_small_noshift drops the shift
                          (P̂₂(y)² in place of P̂₂(y + g·1_{R∪K})²).
  ok_entry / nc_entry_*   J_T[P₂, P₂] at Table 3 (jT_P2_P2_table3); nc_entry_nodiag as above and
                          nc_entry_noU6 (the U⁶/9 term dropped).

Usage: python3 -I specs/checks/power_sq_entry_v2h_controls.py [dir] [--mc SAMPLES]
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
import power_sum_entry_v2g_emit as P  # noqa: E402
import power_sq_entry_v2h_emit as Q  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else "/tmp/v2h_ctl"
MC = int(sys.argv[sys.argv.index("--mc") + 1]) if "--mc" in sys.argv else 100000
os.makedirs(OUT, exist_ok=True)


def setdata(N, g, L, tau, Cf):
    E.N, E.G, E.L, E.TAU, E.C = N, g, L, tau, Cf
    P.N = N


def coef(r, k, A, B, variant):
    """q2Coef with an optional defect."""
    sig = (lambda c: Fr(0)) if variant == "noshift" else Q.sig
    v = Fr(0)
    for c in range(3):
        v += Q.cnt(r, k, c) * sum(comb(4, a) * sig(c) ** (4 - a) * fact(a)
                                  for a in range(5) if (Q.rp(c, a), Q.sp(c, a)) == (A, B))
    for c in range(3):
        for d in range(3):
            pc = Q.cnt(r, k, c) * Q.cnt(r, k, d)
            if c == d and variant != "nodiag":
                pc -= Q.cnt(r, k, c)
            v += pc * sum(comb(2, a) * comb(2, b) * sig(c) ** (2 - a) * sig(d) ** (2 - b) * fact(a) * fact(b)
                          for a in range(3) for b in range(3)
                          if (Q.rp(c, a) + Q.rp(d, b), Q.sp(c, a) + Q.sp(d, b)) == (A, B))
    return v


def entries():
    """Exact J_T[P₂,P₂] and its variants for the current data (moments computed once)."""
    N = P.N
    pieces = [(r, k) for r in range(N + 1) for k in range(N - r + 1)]
    moms = {rk: {ab: Q.pieceM(*rk, *ab, 2) for ab in Q.MOMS} for rk in pieces}

    def tot(f):
        return (N + 1) * sum(comb(N, r) * comb(N - r, k) * (-1) ** k * f(r, k) for (r, k) in pieces)
    q2 = {v: tot(lambda r, k: sum(coef(r, k, A, B, v) * moms[(r, k)][(A, B)] for (A, B) in Q.MOMS))
          for v in (None, "nodiag", "noshift")}
    p4 = tot(lambda r, k: P.p2J(r, k, 4))
    p4plain = tot(lambda r, k: (N - r) * P.pieceE(r, k, 0, 2, 4) + (r * P.pieceE(r, k, 2, 0, 4) if r else 0))
    u6 = tot(lambda r, k: E.pieceJ(r, k, 6, 0))
    return {"ok": q2[None] + Fr(2, 3) * p4 + u6 / 9,
            "nodiag": q2["nodiag"] + Fr(2, 3) * p4 + u6 / 9,
            "noshift": q2["noshift"] + Fr(2, 3) * p4plain + u6 / 9,
            "noU6": q2[None] + Fr(2, 3) * p4}


# ---- (a) synthetic N = 3 -------------------------------------------------------------------------
gs, Ls, ts = Fr(3, 10), Fr(1), Fr(9, 10)
CS = [Fr(0), Fr(1, 2), Fr(3, 5), Fr(7, 10)]
Cs = lambda m: CS[min(m, 3)]
setdata(3, gs, Ls, ts, Cs)
small = entries()


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
        tot += (U * sum(w * w for w in x) + U ** 3 / 3) ** 2
    return (N + 1) * tot * h ** N


g_small = grid(3, 200, gs, Ls, ts, Cs)
assert abs(g_small - float(small["ok"])) / float(small["ok"]) < 1.5e-2, (g_small, float(small["ok"]))
for v in ("nodiag", "noshift"):
    assert abs(g_small - float(small[v])) / float(small["ok"]) > 5e-2, v

# ---- (b) Table 3, N = 44 -------------------------------------------------------------------------
G, L, TAU = Fr(41, 625), Fr(53, 50), Fr(249, 250)
C3 = lambda m: Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000)
setdata(44, G, L, TAU, C3)
big = entries()
assert len(set(big.values())) == 4

random.seed(17)
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
        val = (U * sum(w * w for w in x) + U ** 3 / 3) ** 2
    s1 += val
    s2 += val * val
vol = tf ** 44 / math.factorial(44)
mean = s1 / MC
est = 45 * vol * mean
err = 45 * vol * math.sqrt(max(s2 / MC - mean * mean, 0) / MC)
z = (est - float(big["ok"])) / err
assert abs(z) < 4, z

# ---- (c) Cauchy–Schwarz with V2f's J_T[1,1] and V2g's J_T[P₂,1] -----------------------------------
j11 = 45 * sum(comb(44, r) * sum(comb(44 - r, k) * (-1) ** k * E.pieceJ(r, k, 2, 0) for k in range(45 - r))
               for r in range(45))
jp1 = (45 * sum(comb(44, r) * sum(comb(44 - r, k) * (-1) ** k * (P.p2J(r, k, 2) + E.pieceJ(r, k, 4, 0) / 3)
                                  for k in range(45 - r)) for r in range(45)))
cs = jp1 ** 2 / (j11 * big["ok"])
assert 0 < cs < 1, cs


def q(v):
    v = Fr(v)
    return f"({v.numerator} / {v.denominator} : ℚ)"


HEAD = """import Solution.PowerSumSquare

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
SMALL = """def Csm : ℕ → ℚ := fun m => if m = 0 then 0 else if m = 1 then 1 / 2 else if m = 2 then 3 / 5 else 7 / 10

theorem ctl : p2p2EntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) Csm = {V} := by decide +kernel
"""
ENTRY = """theorem ctl : jTbil 44 g3 L3 τ3 C3
    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) = (({V}) : ℝ) := by
  rw [jT_P2_P2_table3]
  all_goals norm_num
"""
files = {
    "ok_small": SMALL.replace("{V}", q(small["ok"])),
    "nc_small_nodiag": SMALL.replace("{V}", q(small["nodiag"])),
    "nc_small_noshift": SMALL.replace("{V}", q(small["noshift"])),
    "ok_entry": ENTRY.replace("{V}", q(big["ok"])),
    "nc_entry_nodiag": ENTRY.replace("{V}", q(big["nodiag"])),
    "nc_entry_noU6": ENTRY.replace("{V}", q(big["noU6"])),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("(a) N = 3 synthetic: closed form", float(small["ok"]), " grid", g_small,
      " no diagonal correction", float(small["nodiag"]), " no shift", float(small["noshift"]))
print("(b) J_T[P2,P2] =", float(big["ok"]), " MC", est, "±", err, " z =", round(z, 2))
print("    variants: no diagonal correction", float(big["nodiag"]), " no shift", float(big["noshift"]),
      " U⁶ dropped", float(big["noU6"]))
print("(c) J[P2,1]^2 / (J[1,1] J[P2,P2]) =", float(cs), " det/(J11 JPP) =", float(1 - cs))
