#!/usr/bin/env python3
"""Emit V2ℓ's kernel controls (each file is checked with `lake env lean`; build the project first).

Negative controls (must be rejected):
  neg_step_value.lean     — a list-level step `symStepAll` of P̂₂ on the example data with one
                            coefficient changed;
  neg_chunk_state.lean    — a chunk certificate of the run `T3` (factor 5, chunk 0) with one exponent
                            of one state changed;
  neg_merge_drop.lean     — the merge of the chunks of factor 5 of `T3` claimed equal to the states
                            with the last state removed;
  neg_profile.lean        — the moment profile of `T3` after four factors with one coefficient doubled;
  neg_multiset.lean       — equal values claimed for the different multisets of degrees [4, 2] and [3, 3].
Positive controls (must be accepted):
  pos_step_value.lean     — the same step with the correct coefficients, and the two orders' values;
  pos_order_free.lean     — the canonical runs of [4, 2] and [2, 4] end in the same list (the final
                            combination in the augmented monomial basis is unique).

Usage: python3 -I specs/checks/sym_staged_v2l_controls.py outdir
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_reduce_v2k_model as S  # noqa: E402
import sym_staged_v2l_demo as D  # noqa: E402
import gen_entry_v2i_model as Q  # noqa: E402


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    sig = [Fr(3, 10), Fr(3, 10), Fr(0)]
    fac = lambda c: Q.shiftPow(sig[c], 2)  # noqa: E731
    L1 = S.normalize(S.step([3, 2, 4], fac, (), Fr(1)))
    L2 = S.normalize([e for (k, kap) in L1 for e in S.step([3, 2, 4], fac, k, kap)])
    bad = list(L2)
    k0, v0 = bad[-1]
    bad[-1] = (k0, v0 + 1)
    phi = "(fun c => lpShiftPow (clsShift (3 / 10 : ℚ) c) 2)"
    head = "import Solution.SymStaged\n\nopen BGP212.V2e\n\n"
    files = {
        "neg_step_value.lean": head + f"theorem t : symStepAll demoN {phi} ({D.enc(L1)}) = {D.enc(bad)} := by\n"
                                      "  decide +kernel\n",
        "pos_step_value.lean": head + f"theorem t : symStepAll demoN {phi} ({D.enc(L1)}) = {D.enc(L2)} := by\n"
                                      "  decide +kernel\n\n"
                                      "theorem t' : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [4, 2]) =\n"
                                      "    placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 4]) := by\n"
                                      "  decide +kernel\n",
        "neg_multiset.lean": head + "theorem t : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [4, 2]) =\n"
                                    "    placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [3, 3]) := by\n  decide +kernel\n",
        "pos_order_free.lean": head + "theorem t : symRun demoN (demoF [4, 2]) [([], 1)] =\n"
                                      "    symRun demoN (demoF [2, 4]) [([], 1)] := by\n  decide +kernel\n",
    }
    t3 = D.Run("T3", [6, 3, 35], Fr(41, 625), "(clsCount 44 6 3)", "g", "", "")
    c0 = D.split(t3.L[4], t3.chunk_size(4))[0]
    D0, _ = D.step(t3.n, t3.fac, c0)
    badD = list(D0)
    k1, v1 = badD[0]
    k1 = ((k1[0][0], k1[0][1] + 1),) + k1[1:] if k1 else ((0, 1),)
    badD[0] = (k1, v1)
    files["neg_chunk_state.lean"] = ("import Solution.SymStagedCert.T3Run5C0\n\nopen BGP212.V2e BGP212.Params\n\n"
                                     f"theorem t : StepCert (clsCount 44 6 3) (fun c => lpShiftPow (clsShift g c) 2) T3_L4_0\n"
                                     f"    ({D.enc(badD)}) :=\n  stepCert_of_beq _ _ _ _ (by decide +kernel)\n")
    n5 = len(D.split(t3.L[4], t3.chunk_size(4)))
    ds = ", ".join(f"T3_D5_{j}" for j in range(n5))
    files["neg_merge_drop.lean"] = ("import Solution.SymStagedCert.T3Run5\n\nopen BGP212.V2e\n\n"
                                    f"theorem t : combBEq (mergeAll keyCmp 64 [{ds}]) T3_L5.dropLast = true := by\n"
                                    "  decide +kernel\n")
    P4 = D.prof(t3.L[4])
    P4b = [(ab, 2 * v if i == 0 else v) for i, (ab, v) in enumerate(P4)]
    files["neg_profile.lean"] = ("import Solution.SymStagedCert.T3Run1\n\nopen BGP212.V2e\n\n"
                                 f"theorem t : abProfile T3_L4 = {D.penc(P4b)} := by\n  decide +kernel\n")
    for name, body in files.items():
        open(os.path.join(out, name), "w").write(body)
    print("wrote", len(files), "controls to", out)


if __name__ == "__main__":
    main()
