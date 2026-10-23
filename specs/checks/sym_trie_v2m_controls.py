#!/usr/bin/env python3
"""Emit V2m's controls (each file is checked with `lake env lean`; build the project first).

Negative controls (must be rejected):
  neg_wrong_factor.lean   — the profile of the node [2, 2] claimed for the step by P̂₄ from [2];
  neg_profile.lean        — the profile of the leaf [20, 20] with one coefficient changed;
  neg_outside.lean        — the multiset [8, 2, 2, 2] (block |λ| ≤ 8) claimed to have a certified profile;
  neg_shape.lean          — the set {[], [4, 2]} claimed prefix-closed;
  neg_table.lean          — the table of J_T[P_20, P_20] on piece (6, 3) with one power of U changed.
Positive controls (must be accepted):
  pos_perm.lean           — the profile of [4, 2] reused for the order [2, 4] (`profCert_perm`);
  pos_step.lean           — the profile of [2, 2] from the stored node [2] by the correct factor P̂₂
                            (the twin of neg_wrong_factor);
  pos_inside.lean         — the multiset [6, 4, 2] has a certified profile, and {[], [4], [4, 2]} is a trie.

Usage: python3 -I specs/checks/sym_trie_v2m_controls.py outdir
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_reduce_v2k_model as S  # noqa: E402
import sym_staged_v2l_demo as V  # noqa: E402
import sym_trie_v2m_demo as D  # noqa: E402

HEAD = "import Solution.SymTrieNodes\n\nopen BGP212.V2e BGP212.Params\n\nset_option maxRecDepth 20000\n\n"


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    T = D.Trie()
    P20 = V.prof(T.L[(20, 20)])
    bad = [(ab, v + 1 if i == 0 else v) for i, (ab, v) in enumerate(P20)]
    Tb = D.prof_table(T, [(Fr(1), 0, (20,), 0, (20,))])
    (a, b, m, n), c = Tb[0]
    Tbad = [((a, b, m + 2, n), c)] + Tb[1:]
    files = {
        "neg_wrong_factor.lean": HEAD + "theorem t : abProfile (symStepAll (clsCount 44 6 3) (stepFactor g 4) Tt_L_2) = Tt_P_2_2 := by\n"
                                        "  decide +kernel\n",
        "neg_profile.lean": HEAD + "theorem t : ProfCert (clsCount 44 6 3) g [20, 20] (" + V.penc(bad) + ") :=\n"
                                   "  profCert_of_step_chunks (clsCount 44 6 3) g [20] [" +
                                   ", ".join(T.lname((20,), j) for j in range(len(T.chunks[(20,)]))) + "] 20\n"
                                   "    [" + ", ".join(f"Tt_P_20_20_c{j}" for j in range(len(T.chunks[(20,)]))) + "] _ Tt_c_20\n    " +
                                   "".join(f"(List.Forall₂.cons Tt_pq_20_20_c{j} " for j in range(len(T.chunks[(20,)]))) +
                                   "List.Forall₂.nil" + ")" * len(T.chunks[(20,)]) + "\n    (by decide +kernel)\n",
        "neg_outside.lean": HEAD + "theorem t : natListMem [8, 2, 2, 2] (Tt_prof.map Prod.fst) = true := by\n  decide +kernel\n",
        "neg_shape.lean": HEAD + "theorem t : trieShapeOK [[], [4, 2]] = true := by\n  decide +kernel\n",
        "neg_table.lean": HEAD + "theorem t : profTable 44 6 3 g Tt_prof [((1 : ℚ), 0, [20], 0, [20])] =\n    (" +
                                 V.tenc(Tbad) + ") := by\n  decide +kernel\n",
        "pos_perm.lean": HEAD + "theorem t : ProfCert (clsCount 44 6 3) g [2, 4] Tt_P_4_2 :=\n"
                                "  profCert_perm _ g [4, 2] [2, 4] _ Tt_pc_4_2 (List.Perm.swap 4 2 [])\n",
        "pos_step.lean": HEAD + "theorem t : abProfile (symStepAll (clsCount 44 6 3) (stepFactor g 2) Tt_L_2) = Tt_P_2_2 := by\n"
                                "  decide +kernel\n",
        "pos_inside.lean": HEAD + "theorem t : natListMem [6, 4, 2] (Tt_prof.map Prod.fst) = true ∧\n"
                                  "    trieShapeOK [[], [4], [4, 2]] = true := by\n  decide +kernel\n",
    }
    for name, body in files.items():
        open(os.path.join(out, name), "w").write(body)
    print("wrote", len(files), "controls to", out)


if __name__ == "__main__":
    main()
