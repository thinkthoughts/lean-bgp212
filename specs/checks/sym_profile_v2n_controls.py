#!/usr/bin/env python3
"""Emit V2n's controls (each file is checked with `lake env lean`; build the project first).

Negative controls (must be rejected):
  neg_profile_only.lean  — the child [6, 2]'s profile claimed from the parent's order-0 marked profile
                           alone (the moment profile, marks dropped) by the direct transition;
  neg_coef.lean          — the direct transition from [6] (marks of order ≤ 1) claimed to give V2m's
                           profile of [6, 2] with one coefficient changed;
  neg_marks_equal.lean   — the two states of `profile_insufficient` claimed to have equal marked
                           profiles of order ≤ 1;
  neg_outside.lean       — the multiset [2]^9 (block |λ| ≤ 10) claimed to have a certified profile;
  neg_table.lean         — the table of J_T[P_(2,2,2,2), P_(2,2,2,2)] on piece (6, 3) with one power of
                           U changed.
Positive controls (must be accepted):
  pos_direct_agrees.lean — the direct transition from V2n's marked profile of [6] (order ≤ 1) gives
                           exactly V2m's staged profile of [6, 2];
  pos_marks_separate.lean — the marked profiles of order ≤ 1 of the two states of
                           `profile_insufficient` differ, while their moment profiles agree;
  pos_inside.lean        — [2]^8 has a certified profile (V2n), [6, 4, 2] too (V2m).

Usage: python3 -I specs/checks/sym_profile_v2n_controls.py outdir
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_staged_v2l_demo as V  # noqa: E402
import sym_trie_v2m_demo as D  # noqa: E402
import sym_profile_v2n_demo as N  # noqa: E402
import sym_profile_v2n_model as M  # noqa: E402

HEAD = "import Solution.SymProfileNodes\n\nopen BGP212.V2e BGP212.Params\n\nset_option maxRecDepth 20000\n\n"
N3 = "(clsCount 44 6 3)"
STEP = f"markStep {N3} (stepFactor g 2) 0 (Tn_P_6.filter fun e => decide (e.1.2.2.length ≤ {{k}}))"
L1 = "([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ))"
L2 = "([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ))"


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    T = D.Trie()
    P62 = V.prof(T.L[(6, 2)])
    # mirror checks: the direct transition with marks reproduces V2m's profile; without marks it differs
    P6 = M.aug_lean(3, T.L[(6,)])
    direct = lambda k: M.to_prof(M.step_lean(0, N.NCLS, N.fac(2), [e for e in P6 if len(e[0][2]) <= k]))  # noqa: E731
    assert direct(1) == P62 and direct(0) != P62
    bad = [(ab, v + 1 if i == 0 else v) for i, (ab, v) in enumerate(P62)]
    pl = N.Plan()
    Tb = D.prof_table(pl.T, [(1, 0, (2, 2, 2, 2), 0, (2, 2, 2, 2))])
    (a, b, m, n), c = Tb[0]
    Tbad = [((a, b, m + 2, n), c)] + Tb[1:]
    files = {
        "neg_profile_only.lean": HEAD + f"theorem t : markToProf ({STEP.format(k=0)}) = Tt_P_6_2 := by\n  decide +kernel\n",
        "neg_coef.lean": HEAD + f"theorem t : markToProf ({STEP.format(k=1)}) =\n    ({V.penc(bad)}) := by\n  decide +kernel\n",
        "neg_marks_equal.lean": HEAD + f"theorem t : markProfile 1 {L1} = markProfile 1 {L2} := by\n  decide +kernel\n",
        "neg_outside.lean": HEAD + "theorem t : natListMem [2, 2, 2, 2, 2, 2, 2, 2, 2] (Tn_all.map Prod.fst) = true := by\n"
                                   "  decide +kernel\n",
        "neg_table.lean": HEAD + "theorem t : profTable 44 6 3 g Tn_all [((1 : ℚ), 0, [2, 2, 2, 2], 0, [2, 2, 2, 2])] =\n    (" +
                                 V.tenc(Tbad) + ") := by\n  decide +kernel\n",
        "pos_direct_agrees.lean": HEAD + f"theorem t : markToProf ({STEP.format(k=1)}) = Tt_P_6_2 := by\n  decide +kernel\n",
        "pos_marks_separate.lean": HEAD + f"theorem t : abProfile {L1} = abProfile {L2} ∧\n"
                                          f"    markProfile 1 {L1} ≠ markProfile 1 {L2} := by\n  decide +kernel\n",
        "pos_inside.lean": HEAD + "theorem t : natListMem [2, 2, 2, 2, 2, 2, 2, 2] (Tn_all.map Prod.fst) = true ∧\n"
                                  "    natListMem [6, 4, 2] (Tn_all.map Prod.fst) = true := by\n  decide +kernel\n",
    }
    for name, body in files.items():
        open(os.path.join(out, name), "w").write(body)
    print("wrote", len(files), "controls to", out)


if __name__ == "__main__":
    main()
