#!/usr/bin/env python3
"""Emit V2k's kernel controls (each file is checked with `lake env lean`).

Negative controls (must be rejected):
  neg_trans_m_basis.lean   — the transition p₂² written with the m-basis coefficient 2 on (2,2)
                             (the augmented basis m̃ has coefficient 1);
  neg_value_shift.lean     — symPlaceVal on P̂₂² off by 1/1000;
  neg_zero_part.lean       — psTrans with a part of exponent 0 does depend on the class sizes
                             (p_{c,0} = n_c), so psTrans_indep needs positive parts;
  neg_table_key.lean       — the J_T[P₂, P₂] table of piece (6, 3) with one key's power of U changed.
Positive control (must be accepted):
  pos_trans_m_tilde.lean   — the correct transition and value.

Usage: python3 -I specs/checks/sym_reduce_v2k_controls.py outdir
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_reduce_v2k_demo as D  # noqa: E402
import sym_reduce_v2k_model as S  # noqa: E402

HEAD = "import Solution.SymReduce\n\nopen BGP212.V2e BGP212.Params\n\n"


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    v = S.sym_place_val(D.demo_m, [3, 2, 4], D.sig_factors([2, 2]))
    files = {
        "neg_trans_m_basis.lean": "theorem t : psTrans (K := ℚ) demoN [(0, 2), (0, 2)] =\n"
                                  "    ([([(0, 4)], 1), ([(0, 2), (0, 2)], 2)] : List (SKey × ℚ)) := by\n  decide +kernel\n",
        "neg_value_shift.lean": f"theorem t : symPlaceVal demoM demoN (demoF [2, 2]) = {D.lit(v + Fr(1, 1000))} := by\n"
                                "  decide +kernel\n",
        "neg_zero_part.lean": "theorem t : psTrans (K := ℚ) demoN [(0, 0)] = psTrans (K := ℚ) (fun _ => 0) [(0, 0)] := by\n"
                              "  decide +kernel\n",
        "pos_trans_m_tilde.lean": "theorem t : psTrans (K := ℚ) demoN [(0, 2), (0, 2)] =\n"
                                  "    ([([(0, 4)], 1), ([(0, 2), (0, 2)], 1)] : List (SKey × ℚ)) := by\n  decide +kernel\n\n"
                                  f"theorem t' : symPlaceVal demoM demoN (demoF [2, 2]) = {D.lit(v)} := by\n  decide +kernel\n",
    }
    T = S.gen_table(6, 3, 0, [2], 0, [2])
    (a, b, m, n), c = T[-1]
    T_bad = T[:-1] + [((a, b, m + 2, n), c)]
    files["neg_table_key.lean"] = (f"theorem t : genTable 44 6 3 g 0 [2] 0 [2] =\n    ({D.table_lit(T_bad)} : "
                                   "List (MKey × ℚ)) := by\n  decide +kernel\n")
    for name, body in files.items():
        open(os.path.join(out, name), "w").write(HEAD + body)
    print("wrote", len(files), "controls to", out)


if __name__ == "__main__":
    main()
