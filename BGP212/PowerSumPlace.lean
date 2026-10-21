/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, Lemma 9.2 and the display of `J_T` (p. 41).
-/
import BGP212.PowerSumSquare

/-! # V2h: classes of coordinates and the placement values (definitions)

Track B. Kept apart from `BGP212/PowerSumSquare.lean` (which the computational certificate
imports): the class `cls R K i` of a coordinate of a piece `(R, K)`, and the real-valued
diagonal and pair values `diagT`, `pairT` through which `Solution/PowerSumSquare.lean` collects
the placements (`sum_place2`) into the moment form `q2J` (`q2J_expand`). -/

namespace BGP212.V2e

/-- **Definition.** The class of a coordinate of a piece `(R, K)`: `0` rough, `1` in `K`,
`2` neither. -/
def cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) : Fin 3 :=
  if i ∈ R then 0 else if i ∈ K then 1 else 2

/-- **Definition.** The diagonal class value `Σ_a C(4, a) σ_c^{4−a} a! M(…)`. -/
noncomputable def diagT (N r k : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (m : ℕ) (c : Fin 3) : ℝ :=
  ∑ a ∈ Finset.range 5, ((Nat.choose 4 a : ℕ) : ℝ) * clsShift g c ^ (4 - a) * (a.factorial : ℝ) *
    pieceM N r k (roughPart c a) (smoothPart c a) g L τ C m

/-- **Definition.** The off-diagonal pair value
`Σ_{a,b} C(2,a) C(2,b) σ_c^{2−a} σ_d^{2−b} a! b! M(…)`. -/
noncomputable def pairT (N r k : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (m : ℕ) (c d : Fin 3) : ℝ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ((Nat.choose 2 a : ℕ) : ℝ) *
    ((Nat.choose 2 b : ℕ) : ℝ) * clsShift g c ^ (2 - a) * clsShift g d ^ (2 - b) *
      ((a.factorial : ℝ) * (b.factorial : ℝ)) *
      pieceM N r k (roughPart c a + roughPart d b) (smoothPart c a + smoothPart d b) g L τ C m

end BGP212.V2e
