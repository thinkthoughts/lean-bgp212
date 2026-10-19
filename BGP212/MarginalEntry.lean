/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 and the display of
`J_T` (p. 41), Proposition 10.2 (pp. 41–42), §11 (B₂₁, p. 42).
-/
import BGP212.CapCell

/-! # V2f: all three endpoint branches and the marginal Gram entry `J_T[1, 1]` (definitions)

Track B. The proofs are in `Solution/MarginalEntry.lean`.

On a piece `(R, K)` (`r = |R|`, `k = |K|`, piece cap `c`, piece total `M`, `L' = L − (r+k) g`)
the piece region in the aggregates is `P = boxTri c M M` and the endpoint `U` has four cells:

| cell | definition | `U` |
|---|---|---|
| `Z₁` | `boxTri A₁ c₂ M` | `C(r+1) − r g − u₁` (cap) |
| `Z₂` | `boxTri A₁ M M \ Z₁` | `L' − u₁ − u₂` |
| `Z₃` | `boxTri c M M₃ \ boxTri A₁ M M₃` | `g` |
| `Z₄` | `(P \ boxTri A₁ M M) \ Z₃` | `L' − u₁ − u₂` |

with `c₁ = C(r+1) − (r+1) g`, `c₂ = L − k g − C(r+1)`, `A₁ = min c c₁`, `M₃ = min M (L' − g)`.
Every cell integral of `u₁^α u₂^β (p − u₁)^{m₁} (L' − u₁ − u₂)^{m₂}` is `twoPowVal`, a finite
combination of V2e-B's `boxVal`; `cellsVal` assembles the four cells for the block `U^m (L − S)^n`.

`pieceJ` is the closed form of one piece integral of `U^m (L − S)^n` (two aggregates for `r ≥ 1`,
one aggregate for `r = 0`, zero for an empty piece), and `jtSum` the signed count over pieces.
All are defined over an ordered field, so over `ℚ` they are computable. -/

namespace BGP212.V2e

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- `∫_{boxTri A B D} u₁^α u₂^β (p − u₁)^{m₁} (L' − u₁ − u₂)^{m₂}`, expanded into `boxVal`s. -/
def twoPowVal (A B D p L' : K) (α β m₁ m₂ : ℕ) : K :=
  ∑ i ∈ Finset.range (m₁ + 1), ∑ j ∈ Finset.range (m₂ + 1), ∑ l ∈ Finset.range (j + 1),
    (m₁.choose i : K) * p ^ (m₁ - i) * (-1) ^ i * ((m₂.choose j : K) * L' ^ (m₂ - j) * (-1) ^ j) *
      (j.choose l : K) * boxVal A B D (α + i + l) (β + (j - l))

/-- **Definition.** The four-cell value of `∫_{boxTri c M M} u₁^α u₂^β U^m (L − S)^n` on a piece
(`r` rough, `k` inclusion–exclusion coordinates). -/
def cellsVal (g L : K) (C : ℕ → K) (r k : ℕ) (c M : K) (α β m n : ℕ) : K :=
  let Lp := L - (r + k) * g
  let c₁ := C (r + 1) - (r + 1) * g
  let c₂ := L - k * g - C (r + 1)
  let a := C (r + 1) - r * g
  let A₁ := min c c₁
  let M₃ := min M (Lp - g)
  twoPowVal A₁ c₂ M a Lp α β m n +
    (twoPowVal A₁ M M 0 Lp α β 0 (m + n) - twoPowVal A₁ c₂ M 0 Lp α β 0 (m + n)) +
    g ^ m * (twoPowVal c M M₃ 0 Lp α β 0 n - twoPowVal A₁ M M₃ 0 Lp α β 0 n) +
    ((twoPowVal c M M 0 Lp α β 0 (m + n) - twoPowVal A₁ M M 0 Lp α β 0 (m + n)) -
      (twoPowVal c M M₃ 0 Lp α β 0 (m + n) - twoPowVal A₁ M M₃ 0 Lp α β 0 (m + n)))

/-- **Definition.** The one-aggregate value for the stratum with no rough coordinates
(`u₁ = 0`, `U = C(1)` up to `u₂ = c₂`, then `U = L' − u₂`). -/
def seg0Val (g L : K) (C : ℕ → K) (k : ℕ) (M : K) (β m n : ℕ) : K :=
  let Lp := L - k * g
  let X := max 0 (min (L - k * g - C 1) M)
  C 1 ^ m * innerVal X Lp n β + (innerVal M Lp (m + n) β - innerVal X Lp (m + n) β)

/-- **Definition.** The closed form of one piece integral of `U^m (L − S)^n` in dimension `N`
(`r` rough, `k` inclusion–exclusion coordinates, weight `yᵗ = 1`). -/
def pieceJ (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) : K :=
  if C r - r * g < 0 ∨ τ - (r + k) * g < 0 then 0
  else if r = 0 then 1 / ((N - 1).factorial : K) * seg0Val g L C k (τ - k * g) (N - 1) m n
  else 1 / ((r - 1).factorial : K) * (1 / ((N - r - 1).factorial : K)) *
    cellsVal g L C r k (C r - r * g) (τ - (r + k) * g) (r - 1) (N - r - 1) m n

/-- **Definition.** One row of the signed count: `Σ_k C(N − r, k) (−1)^k pieceJ N r k`. -/
def jtRow (N r : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) : K :=
  ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k * pieceJ N r k g L τ C m n

/-- **Definition.** The signed count over pieces: `(N + 1) Σ_r C(N, r) Σ_k C(N − r, k) (−1)^k
pieceJ N r k`. -/
def jtSum (N : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) : K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
    ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k * pieceJ N r k g L τ C m n

end Formula

end BGP212.V2e
