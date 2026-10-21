/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 and the display of
`J_T` (p. 41), Proposition 10.2 (pp. 41–42), §11 (B₂₁, p. 42).
-/
import BGP212.PowerSumEntry

/-! # V2h: the marginal Gram entry `J_T[P₂, P₂]` (definitions)

Track B. The proofs are in `Solution/PowerSumSquare.lean`.

`∫₀^U P₂ = U P̂₂ + U³/3`, so `J_T[P₂, P₂] = (N + 1) ∫_{T̂} (U² P̂₂² + (2/3) U⁴ P̂₂ + U⁶/9)`.
The last two terms are V2g's `p2Sum … 4` and V2f's `jtSum … 6 0`. The new term carries
`P̂₂(y + s)² = Σᵢ Σⱼ (yᵢ + sᵢ)² (yⱼ + sⱼ)²` with **two distinguished coordinates**.

**Moments.** On a piece `(R, K)` with `r = |R|`, `k = |K|`, every monomial weight `yᵗ` integrates
to `(∏ tᵢ!) · pieceM N r k a b … m`, where `a = Σ_{i ∈ R} tᵢ` and `b = Σ_{i ∉ R} tᵢ` are the
degrees landing in the rough and the smooth group (`Solution/PowerSumSquare.lean`, `piece_mono`).

**Placements.** Each coordinate has a class: `0` (in `R`, shifted by `g`), `1` (in `K`, shifted
by `g`, smooth) or `2` (neither, unshifted), with counts `r`, `k`, `N − r − k`. A distinct ordered
pair of classes `(c, d)` occurs `n_c n_d − [c = d] n_c` times; the diagonal `i = j` occurs `n_c`
times with weight `(yᵢ + sᵢ)⁴`. Collecting the binomial expansion by `(a, b)` gives the
coefficient `q2Coef` of each moment; only `a + b ≤ 4` occurs. All values are defined over an
ordered field, so over `ℚ` they are computable. -/

namespace BGP212.V2e

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The weighted piece moment with the factorials of the weight removed: the
rough group carries total degree `a`, the smooth group total degree `b`; zero for an empty piece.
(For `r = 0` the rough degree is necessarily `0` and `a` is ignored.) -/
def pieceM (N r k a b : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  if C r - r * g < 0 ∨ τ - (r + k) * g < 0 then 0
  else if r = 0 then 1 / ((N + b - 1).factorial : K) * seg0Val g L C k (τ - k * g) (N - 1 + b) m 0
  else 1 / ((r + a - 1).factorial : K) * (1 / ((N - r + b - 1).factorial : K)) *
    cellsVal g L C r k (C r - r * g) (τ - (r + k) * g) (r - 1 + a) (N - r - 1 + b) m 0

/-- **Definition.** Class counts: `r` rough, `k` in `K`, `N − r − k` neither. -/
def clsCount (N r k : ℕ) (c : Fin 3) : ℕ := if c = 0 then r else if c = 1 then k else N - r - k

/-- **Definition.** Class shift: `g` for classes `0`, `1`; `0` for class `2`. -/
def clsShift (g : K) (c : Fin 3) : K := if c = 2 then 0 else g

/-- **Definition.** The degree `a` of a class-`c` coordinate lands in the rough group iff `c = 0`. -/
def roughPart (c : Fin 3) (a : ℕ) : ℕ := if c = 0 then a else 0

/-- **Definition.** The smooth part of the degree `a` of a class-`c` coordinate. -/
def smoothPart (c : Fin 3) (a : ℕ) : ℕ := if c = 0 then 0 else a

/-- **Definition.** Multiplicity of the ordered pair of classes `(c, d)` among distinct
coordinates. -/
def pairCount (N r k : ℕ) (c d : Fin 3) : K :=
  (clsCount N r k c : K) * clsCount N r k d - if c = d then (clsCount N r k c : K) else 0

/-- **Definition.** The coefficient of the moment `(A, B)` in `∫_{piece} U^m P̂₂(y + s)²`: the
diagonal `(yᵢ + sᵢ)⁴` and the distinct pairs `(yᵢ + sᵢ)² (yⱼ + sⱼ)²`, expanded binomially,
with the factorials of the weight. -/
def q2Coef (N r k : ℕ) (g : K) (A B : ℕ) : K :=
  (∑ c : Fin 3, (clsCount N r k c : K) * ∑ a ∈ Finset.range 5,
      if roughPart c a = A ∧ smoothPart c a = B then
        ((Nat.choose 4 a : ℕ) : K) * clsShift g c ^ (4 - a) * (a.factorial : K) else 0) +
    ∑ c : Fin 3, ∑ d : Fin 3, pairCount N r k c d * ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
      if roughPart c a + roughPart d b = A ∧ smoothPart c a + smoothPart d b = B then
        ((Nat.choose 2 a : ℕ) : K) * ((Nat.choose 2 b : ℕ) : K) * clsShift g c ^ (2 - a) *
          clsShift g d ^ (2 - b) * ((a.factorial : K) * (b.factorial : K)) else 0

/-- **Definition.** The piece value of `∫ U^m P̂₂(y + g·1_{R∪K})²`: a combination of the 15
moments with `A + B ≤ 4`. -/
def q2J (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  ∑ A ∈ Finset.range 5, ∑ B ∈ Finset.range (5 - A),
    q2Coef N r k g A B * pieceM N r k A B g L τ C m

/-- **Definition.** One row of the signed count of `q2J`. -/
def q2Row (N r : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k * q2J N r k g L τ C m

/-- **Definition.** `(N + 1) ∫_{T̂} U^m P̂₂²` in closed form. -/
def q2Sum (N : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) : K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) * q2Row N r g L τ C m

/-- **Definition.** The closed form of
`J_T[P₂, P₂] = (N + 1) ∫_{T̂} (U² P̂₂² + (2/3) U⁴ P̂₂ + U⁶/9)`. -/
def p2p2EntryVal (N : ℕ) (g L τ : K) (C : ℕ → K) : K :=
  q2Sum N g L τ C 2 + 2 / 3 * p2Sum N g L τ C 4 + jtSum N g L τ C 6 0 / 9

end Formula

end BGP212.V2e
