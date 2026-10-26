#!/usr/bin/env python3
"""Emit V2o's controls (each file is checked with `lake env lean`; build the project first).

Negative controls (must be rejected):
  neg_summary_deg2.lean  — the two states of `summary_degree_gap` claimed to have equal summaries of degree 2;
  neg_bridge.lean        — the literal coefficients of P̂₂ claimed to be those of P̂₄;
  neg_wrong_factor.lean  — the profile of the leaf [4, 2, 2] claimed from its parent [4, 2] by P̂₄;
  neg_profile_only.lean  — the profile of [4, 2, 2] claimed from the parent's order-0 entries alone;
  neg_leaf_coef.lean     — the direct step to [2, 2, 2] claimed with one coefficient changed;
  neg_outside.lean       — [10, 10, 10] (degree 30) claimed to have a one-level profile.
Positive controls (must be accepted):
  pos_summary_deg1.lean  — the same two states have equal summaries of degree 1 and equal profiles;
  pos_bridge.lean        — the bridge for P̂₂;
  pos_direct.lean        — the profile of [4, 2, 2] from the parent's order-≤ 1 marks by P̂₂ (the twin
                           of neg_wrong_factor and neg_profile_only);
  pos_inside.lean        — [10, 8, 8] has a one-level profile.

Usage: python3 -I specs/checks/sym_read_v2o_controls.py outdir
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_profile_v2n_demo as N  # noqa: E402
import sym_profile_v2n_model as M  # noqa: E402
import sym_read_v2o_demo as O  # noqa: E402

HEAD = "import Solution.SymReadNodes\n\nopen BGP212.V2e BGP212.Params\n\nset_option maxRecDepth 20000\n\n"
N3 = "(clsCount 44 6 3)"
L1 = "([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ))"
L2 = "([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ))"


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    pl = O.Plan()
    P42 = pl.P1[(4, 2)]
    # mirror: with marks and P̂₂ the profile of [4, 2, 2]; by P̂₄ or without marks it differs
    good = M.to_prof(M.step_lean(0, N.NCLS, N.fac(2), P42))
    assert good == pl.prof[(4, 2, 2)]
    assert M.to_prof(M.step_lean(0, N.NCLS, N.fac(4), P42)) != good
    assert M.to_prof(M.step_lean(0, N.NCLS, N.fac(2), [e for e in P42 if not e[0][2]])) != good
    D222 = M.step_lean(0, N.NCLS, N.fac(2), pl.P1[(2, 2)])
    bad = [(k, v + 1 if i == 0 else v) for i, (k, v) in enumerate(D222)]
    step = lambda q, p, k: (f"markStep {N3} To_f_{q} 0 (To_P_{p}.filter fun e => decide (e.1.2.2.length ≤ {k}))")  # noqa: E731
    files = {
        "neg_summary_deg2.lean": HEAD + f"theorem t : readSummary 2 (markProfile 1 {L1}) = readSummary 2 (markProfile 1 {L2}) := by\n"
                                        "  decide +kernel\n",
        "neg_bridge.lean": HEAD + "theorem t : stepFactor g 4 = To_f_2 := by\n  funext c; fin_cases c <;> decide +kernel\n",
        "neg_wrong_factor.lean": HEAD + f"theorem t : markToProf ({step(4, '4_2', 1)}) = To_R_4_2_2 := by\n  decide +kernel\n",
        "neg_profile_only.lean": HEAD + f"theorem t : markToProf ({step(2, '4_2', 0)}) = To_R_4_2_2 := by\n  decide +kernel\n",
        "neg_leaf_coef.lean": HEAD + f"theorem t : {step(2, '2_2', 1)} =\n    ({N.menc(bad)}) := by\n  decide +kernel\n",
        "neg_outside.lean": HEAD + "theorem t : natListMem [10, 10, 10] (To_prof.map Prod.fst) = true := by\n  decide +kernel\n",
        "pos_summary_deg1.lean": HEAD + f"theorem t : abProfile {L1} = abProfile {L2} ∧\n"
                                        f"    readSummary 1 (markProfile 1 {L1}) = readSummary 1 (markProfile 1 {L2}) := by\n"
                                        "  decide +kernel\n",
        "pos_bridge.lean": HEAD + "theorem t : stepFactor g 2 = To_f_2 := by\n  funext c; fin_cases c <;> decide +kernel\n",
        "pos_direct.lean": HEAD + f"theorem t : markToProf ({step(2, '4_2', 1)}) = To_R_4_2_2 := by\n  decide +kernel\n",
        "pos_inside.lean": HEAD + "theorem t : natListMem [10, 8, 8] (To_prof.map Prod.fst) = true := by\n  decide +kernel\n",
    }
    for name, body in files.items():
        open(os.path.join(out, name), "w").write(body)
    print("wrote", len(files), "controls to", out)


if __name__ == "__main__":
    main()
