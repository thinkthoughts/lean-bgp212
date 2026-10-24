/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import Solution.SymProfile

/-! # V2n: regrouping certified marked profiles

A marked profile is certified by its value against every test function (`MarkOK`), so it can be
replaced by any list of the same value (`markOK_congr`). The certificates use this to merge the chunk
results of a node by ranges of keys: each chunk result is certified as the concatenation of its
slices on the ranges, the slices of each range are merged in a separate kernel check, and the value
of the concatenated range merges equals the value of the chunk results by commutativity of the sum
(`linear_combination` in each assembly). No merge of all results is evaluated. -/

namespace BGP212.V2e

section Regroup

variable {K : Type*} [Field K] [LinearOrder K]

omit [LinearOrder K] in
/-- **Regrouping.** A certified marked profile can be replaced by any list with the same value
against every test function. -/
theorem markOK_congr (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T : ℕ) (P P' : List (MarkKey × K))
    (h : MarkOK n g Q T P)
    (hv : ∀ F : MarkKey → K, (P.map fun e => e.2 * F e.1).sum = (P'.map fun e => e.2 * F e.1).sum) :
    MarkOK n g Q T P' := by
  obtain ⟨L, hc, hL⟩ := h
  exact ⟨L, hc, fun F => (hv F).symm.trans (hL F)⟩

omit [LinearOrder K] in
/-- The value of a merge of slices, as the sum of the slices' values. -/
theorem merge_slices_val (Ss : List (List (MarkKey × K))) (C : List (MarkKey × K))
    (h : mergeAll markCmp 64 Ss = C) (F : MarkKey → K) :
    (Ss.map fun S => (S.map fun e => e.2 * F e.1).sum).sum = (C.map fun e => e.2 * F e.1).sum := by
  rw [← h, mergeAll_markVal]

end Regroup

end BGP212.V2e

#print axioms BGP212.V2e.markOK_congr
