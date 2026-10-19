/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 and the display of
`J_T` (p. 41), Proposition 10.2 (pp. 41–42), §11 (B₂₁, p. 42).
-/
import BGP212.MarginalEntry
import BGP212.Fibre

/-! # V2g: a marginal Gram entry with a power sum, `J_T[P₂, 1]` (definitions)

Track B. The proofs are in `Solution/PowerSumEntry.lean`.

`jTbil` is the bilinear form of §9.4's `J_T`: `J_T[F, G] = (n + 1) ∫_{T̂} (∫₀^U F)(∫₀^U G)`, with
`jT F = jTbil F F`. For the generator `P₂ = gen 0 {2} = Σᵢ xᵢ²` and `1 = gen 0 ∅`,
`∫₀^U P₂(x̂, u) du = U P̂₂(x̂) + U³/3`, so `J_T[P₂, 1] = 45 ∫_{T̂} (U² P̂₂ + U⁴/3)`.

After the stratum translation `x = y + g·1_{R ∪ K}` of a piece `(R, K)`,
`P̂₂(x) = Σᵢ yᵢ² + 2 g Σ_{i ∈ R ∪ K} yᵢ + g² |R ∪ K|`: a sum of **single-coordinate weights**
`yᵢ^e` (`e ≤ 2`). By symmetry within the rough and the smooth group, `∫_{piece} yᵢ^e U^m`
depends only on whether `i ∈ R` (`pieceE … e 0`) or `i ∉ R` (`pieceE … 0 e`): the Dirichlet
exponent of that group rises by `e` and its constant gains `e!`. Summing over `i` places the
distinguished coordinate in `R`, in `K` or in neither, with multiplicities `r`, `k`, `N − r − k`
(`p2J`). All values are defined over an ordered field, so over `ℚ` they are computable. -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-- **Definition.** The bilinear form of `J_T` (§9.4): `(n + 1) ∫_{T̂} (∫₀^U F)(∫₀^U G)`. -/
noncomputable def jTbil (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F G : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  (n + 1 : ℝ) * ∫ x in hatSupport n g τ C,
    (∫ u in (0 : ℝ)..(endpoint g L C x), F (Fin.snoc x u)) *
      (∫ u in (0 : ℝ)..(endpoint g L C x), G (Fin.snoc x u))

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** `∫_{piece} yᵢ^{e} U^m` for one coordinate `i` with exponent `eR` if `i ∈ R`
(and `eS = 0`) or `eS` if `i ∉ R` (and `eR = 0`); zero for an empty piece. -/
def pieceE (N r k eR eS : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  if C r - r * g < 0 ∨ τ - (r + k) * g < 0 then 0
  else if r = 0 then (eS.factorial : K) / ((N + eS - 1).factorial : K) *
    seg0Val g L C k (τ - k * g) (N - 1 + eS) m 0
  else (eR.factorial : K) / ((r + eR - 1).factorial : K) *
    ((eS.factorial : K) / ((N - r + eS - 1).factorial : K)) *
    cellsVal g L C r k (C r - r * g) (τ - (r + k) * g) (r - 1 + eR) (N - r - 1 + eS) m 0

/-- **Definition.** The piece value of `∫ U^m P̂₂(y + g·1_{R∪K})`, the distinguished coordinate
placed in `K`, in neither, or in `R`. -/
def p2J (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  (k : K) * (pieceE N r k 0 2 g L τ C m + 2 * g * pieceE N r k 0 1 g L τ C m +
      g ^ 2 * pieceE N r k 0 0 g L τ C m) +
    ((N - r - k : ℕ) : K) * pieceE N r k 0 2 g L τ C m +
    (r : K) * (pieceE N r k 2 0 g L τ C m + 2 * g * pieceE N r k 1 0 g L τ C m +
      g ^ 2 * pieceE N r k 0 0 g L τ C m)

/-- **Definition.** One row of the signed count of `p2J`. -/
def p2Row (N r : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k * p2J N r k g L τ C m

/-- **Definition.** `(N + 1) ∫_{T̂} U^m P̂₂` in closed form. -/
def p2Sum (N : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) * p2Row N r g L τ C m

/-- **Definition.** The closed form of `J_T[P₂, 1] = (N+1) ∫_{T̂} (U² P̂₂ + U⁴/3)`. -/
def p2EntryVal (N : ℕ) (g L τ : K) (C : ℕ → K) : K :=
  p2Sum N g L τ C 2 + jtSum N g L τ C 4 0 / 3

end Formula

end BGP212.V2e
