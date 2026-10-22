/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, Lemma 9.2 and the display of `J_T` (p. 41).
-/
import BGP212.GenEntry

/-! # V2i: the integrand block of a piece (definition)

Kept apart from `BGP212/GenEntry.lean` (which the computational certificate imports). -/

namespace BGP212.V2e

/-- **Definition.** The block `U^m (L − S)^n` of a piece in the aggregates. -/
noncomputable def blk {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R : Finset (Fin N)) (k m n : ℕ)
    (y : Fin N → ℝ) : ℝ :=
  (endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m *
    (L - ((R.card + k) * g + aggR R y + aggS R y)) ^ n

end BGP212.V2e
