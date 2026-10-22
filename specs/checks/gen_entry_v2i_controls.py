#!/usr/bin/env python3
"""Positive and negative controls for V2i (general marginal Gram entries J_T[G_{a,λ}, G_{b,μ}]).

Writes Lean files into the given directory (default /tmp/v2i_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected. Independent checks run here first:

  (a) synthetic data (N = 3, g = 3/10, L = 1, τ = 9/10, C = 0, 1/2, 3/5, 7/10, …): the closed form
      against V2f/V2g/V2h (J[1,1], J[P₂,1], J[P₂,P₂], equal as rationals), and the values of
      J[P₄,1], J[P_{(2,2)},1], J[L−P₁,1] printed for comparison with
      specs/checks/gen_entry_v2i_grid.py (direct midpoint grids, numpy);
  (b) Table 3, N = 44: the worked entries against a Monte Carlo estimate (uniform samples of the
      τ-simplex, true rough-set endpoint, untranslated generators; numpy), |z| < 4;
  (c) exact identities: J[P_{(2,2)},1] − J[P₂,P₂] = (1/5 − 1/9) · 45 ∫ U⁶ (both from the same
      moments), and Cauchy–Schwarz for {1, L − P₁}.

  ok_small_LP / nc_small_LP_sign   J[L−P₁,1] at N = 3; the variant with the sign-flipped factor P₁ − L.
  ok_entry_* / nc_entry_*          the Table 3 theorems; nc_entry_P22_nomerge drops the merge
                                   branch of the placement (the diagonal i = j), nc_entry_P4_noshift
                                   drops the shift, nc_entry_LP_noM drops the factor (L − S).

Usage: python3 -I specs/checks/gen_entry_v2i_controls.py [dir] [--mc SAMPLES]
"""
import math
import os
import sys
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import marginal_entry_v2f_emit as E  # noqa: E402
import gen_entry_v2i_model as Q  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else "/tmp/v2i_ctl"
MC = int(sys.argv[sys.argv.index("--mc") + 1]) if "--mc" in sys.argv else 2000000
os.makedirs(OUT, exist_ok=True)

ORIG_PHI = Q.Phi


def Phi_nomerge(M, n, S, factors):
    if not factors:
        return Q.V(M, S)
    phi, rest = factors[0], factors[1:]
    tot = Fr(0)
    for c in range(3):
        mult = n[c] - sum(1 for (cc, _) in S if cc == c)
        tot += mult * Phi_nomerge(M, n, [(c, phi(c))] + S, rest)
    return tot


def entry(args, variant=None, cache=None):
    N = Q.N
    a1, l1, a2, l2 = args

    def piece(r, k):
        Mo = (lambda A, B, m, n: cache[(r, k)][(A, B, m, n)]) if cache else None
        if variant == "nomerge":
            Q.Phi = Phi_nomerge
        try:
            if variant == "noshift":
                g0 = E.G
                v = piece_shift0(r, k, args, Mo)
            elif variant == "noM":
                v = sum(c1 * c2 * Q.Phi(lambda A, B: (Mo or (lambda A_, B_, m, n: Q.pieceMn(r, k, A_, B_, m, n)))(
                        A, B, p1 + p2, 0), [r, k, N - r - k], [], [])
                        for (K1, p1, q1, c1) in Q.innerTerms(a1, l1) for (K2, p2, q2, c2) in Q.innerTerms(a2, l2))
            elif variant == "sign":
                v = sum(c1 * c2 * (-1) ** (q1 + q2) * Q.Phi(
                        lambda A, B: (Mo or (lambda A_, B_, m, n: Q.pieceMn(r, k, A_, B_, m, n)))(A, B, p1 + p2, q1 + q2),
                        [r, k, N - r - k], [], [])
                        for (K1, p1, q1, c1) in Q.innerTerms(a1, l1) for (K2, p2, q2, c2) in Q.innerTerms(a2, l2))
            else:
                v = Q.genPiece(r, k, a1, l1, a2, l2, Mo=Mo)
        finally:
            Q.Phi = ORIG_PHI
        return v
    return (N + 1) * sum(comb(N, r) * sum(comb(N - r, k) * (-1) ** k * piece(r, k)
                                         for k in range(N - r + 1)) for r in range(N + 1))


def piece_shift0(r, k, args, Mo):
    a1, l1, a2, l2 = args
    N = Q.N
    Mo = Mo or (lambda A, B, m, n: Q.pieceMn(r, k, A, B, m, n))
    tot = Fr(0)
    for (K1, p1, q1, c1) in Q.innerTerms(a1, l1):
        for (K2, p2, q2, c2) in Q.innerTerms(a2, l2):
            fac = [(lambda c, q=q: Q.shiftPow(Fr(0), q)) for q in K1 + K2]
            tot += c1 * c2 * Q.Phi(lambda A, B: Mo(A, B, p1 + p2, q1 + q2), [r, k, N - r - k], [], fac)
    return tot


# ---- (a) synthetic N = 3 -------------------------------------------------------------------------
CS = [Fr(0), Fr(1, 2), Fr(3, 5), Fr(7, 10)]
Q.setdata(3, Fr(3, 10), Fr(1), Fr(9, 10), lambda m: CS[min(m, 3)])
small = {name: entry(args) for name, args in
         [("11", (0, [], 0, [])), ("P2_1", (0, [2], 0, [])), ("PP", (0, [2], 0, [2])), ("P4", (0, [4], 0, [])),
          ("P22", (0, [2, 2], 0, [])), ("LP", (1, [], 0, []))]}
assert small["11"] == Fr(3768, 100000), small["11"]
small_LP_sign = entry((1, [], 0, []), "sign")
assert small_LP_sign != small["LP"]

# ---- (b) Table 3 -------------------------------------------------------------------------------
G, L, TAU = Fr(41, 625), Fr(53, 50), Fr(249, 250)
C3 = lambda m: Fr(0) if m == 0 else 4 * Fr(E.BNUM[min(m, 10) - 1], 5000)
Q.setdata(44, G, L, TAU, C3)
keys = sorted({kk for args in [(0, [4], 0, []), (0, [2, 2], 0, []), (1, [], 0, []), (0, [2], 0, [2]),
                                (1, [], 1, [])]
               for kk in Q.keys(*args)} | {(A, B, m, 0) for m in (2, 4, 6) for A in range(5) for B in range(5)
                                            if A + B <= 4})
pieces = [(r, k) for r in range(45) for k in range(45 - r)]
cache = {rk: {kk: Q.pieceMn(*rk, *kk) for kk in keys} for rk in pieces}
big = {name: entry(args, cache=cache) for name, args in
       [("PP", (0, [2], 0, [2])), ("P4", (0, [4], 0, [])), ("P22", (0, [2, 2], 0, [])), ("LP", (1, [], 0, [])),
        ("11", (0, [], 0, [])), ("LPLP", (1, [], 1, []))]}
var = {"P22_nomerge": entry((0, [2, 2], 0, []), "nomerge", cache),
       "P4_noshift": entry((0, [4], 0, []), "noshift", cache),
       "LP_noM": entry((1, [], 0, []), "noM", cache)}
u6 = 45 * sum(comb(44, r) * comb(44 - r, k) * (-1) ** k * cache[(r, k)][(0, 0, 6, 0)] for (r, k) in pieces)
assert big["P22"] - big["PP"] == (Fr(1, 5) - Fr(1, 9)) * u6
for k_, v in var.items():
    assert v != big[k_.split("_")[0]], k_

try:
    import numpy as np
    rng = np.random.default_rng(7)
    BN = [777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081]
    gf, Lf, tf = float(G), float(L), float(TAU)
    Cv = np.array([0.0] + [4 * BN[min(m, 10) - 1] / 5000 for m in range(1, 47)])
    acc = {k: [0.0, 0.0] for k in ("P4", "P22", "LP")}
    B = 200000
    for _ in range(MC // B):
        e = rng.exponential(size=(B, 45))
        x = tf * e[:, :44] / e.sum(1, keepdims=True)
        S = x.sum(1); msk = x > gf; cnt = msk.sum(1); rho = (x * msk).sum(1)
        ok = rho <= Cv[cnt]
        U = np.minimum(Lf - S, np.maximum(gf, Cv[np.minimum(cnt + 1, 46)] - rho))
        M = Lf - S
        p2 = (x ** 2).sum(1); p4 = (x ** 4).sum(1)
        vals = {"P4": (U * p4 + U ** 5 / 5) * U,
                "P22": (U * p2 ** 2 + 2 * U ** 3 * p2 / 3 + U ** 5 / 5) * U,
                "LP": (M * U - U ** 2 / 2) * U}
        for k_, v in vals.items():
            v = v * ok
            acc[k_][0] += v.sum(); acc[k_][1] += (v * v).sum()
    vol = tf ** 44 / math.factorial(44)
    mc = {}
    for k_, (s1, s2) in acc.items():
        m = s1 / MC; sd = math.sqrt(max(s2 / MC - m * m, 0) / MC)
        mc[k_] = (45 * vol * m, 45 * vol * sd, (45 * vol * m - float(big[k_])) / (45 * vol * sd))
        assert abs(mc[k_][2]) < 4, (k_, mc[k_])
except ImportError:
    mc = None


def q(v):
    v = Fr(v)
    return f"({v.numerator} / {v.denominator} : ℚ)"


HEAD = """import Solution.GenEntry

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
SMALL = """def Csm : ℕ → ℚ := fun m => if m = 0 then 0 else if m = 1 then 1 / 2 else if m = 2 then 3 / 5 else 7 / 10

theorem ctl : genEntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) Csm 1 [] 0 [] = {V} := by decide +kernel
"""
ENTRY = {"P4": ("gen 0 {4}", "gen 0 0", "jT_P4_one_table3"), "P22": ("gen 0 {2, 2}", "gen 0 0", "jT_P22_one_table3"),
         "LP": ("gen 1 0", "gen 0 0", "jT_LP1_one_table3")}


def entry_file(k_, v):
    a, b, thm = ENTRY[k_]
    return (f"theorem ctl : jTbil 44 g3 L3 τ3 C3\n"
            f"    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.{a}))\n"
            f"    (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.{b})) = (({q(v)}) : ℝ) := by\n"
            f"  rw [{thm}]\n  all_goals norm_num\n")


files = {"ok_small_LP": SMALL.replace("{V}", q(small["LP"])),
         "nc_small_LP_sign": SMALL.replace("{V}", q(small_LP_sign))}
for k_ in ("P4", "P22", "LP"):
    files[f"ok_entry_{k_}"] = entry_file(k_, big[k_])
files["nc_entry_P22_nomerge"] = entry_file("P22", var["P22_nomerge"])
files["nc_entry_P4_noshift"] = entry_file("P4", var["P4_noshift"])
files["nc_entry_LP_noM"] = entry_file("LP", var["LP_noM"])
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("(a) N = 3:", {k_: float(v) for k_, v in small.items()})
print("(b) Table 3:", {k_: float(v) for k_, v in big.items()})
print("    variants:", {k_: float(v) for k_, v in var.items()})
if mc:
    print("    Monte Carlo:", {k_: (f"{v[0]:.6g} ± {v[1]:.2g}", round(v[2], 2)) for k_, v in mc.items()})
cs = big["LP"] ** 2 / (big["11"] * big["LPLP"])
print("(c) J[P22,1] − J[P2,P2] = (4/45)·45∫U⁶ exactly; J[L−P1,1]² / (J[1,1] J[L−P1,L−P1]) =", float(cs))
