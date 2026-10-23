/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.GenEntry

/-! # V2j: shared-moment aggregation of marginal Gram entries (definitions)

Track B. The proofs are in `Solution/MomentAgg.lean`. V2i's specification (`genPieceWith`,
`genEntryVal`) is unchanged; this module adds an evaluation strategy and its data.

**Moment keys.** A key `(A, B, m, n) : MKey` names the moment `pieceMn … A B … m n` of a piece.
V2i's piece value `genPieceWith … Mo …` reads the moment oracle `Mo` only at the leaves of
`stateVal`, multiplied by rational coefficients: it is linear in `Mo` and depends on `Mo` only at
the keys it queries. `stateKeys`, `placeKeys` and `genKeys` list those keys, mirroring the
recursion of `stateVal`, `placeVal` and `genPieceWith`; `genKeys` removes duplicates.

**Coefficient collapse.** The coefficient of a key `s` is the value against the unit oracle
`delta s`. For a weighted list of generator pairs `ws` (the shape of `J_T(P⋆) = Σ cᵢ cⱼ J_T[Gᵢ, Gⱼ]`),
`aggCoeff` sums the coefficients of each key across all pairs before any moment is evaluated, and
`aggPiece` evaluates each distinct key once: `Σ_{s ∈ aggKeys} aggCoeff s · Mo s`. `aggEntryVal` is
the signed sum over pieces, as for `genEntryVal`. -/

namespace BGP212.V2e

/-- A moment key `(A, B, m, n)`: rough degree, smooth degree, power of `U`, power of `L − S`. -/
abbrev MKey := ℕ × ℕ × ℕ × ℕ

/-- A weighted generator pair `(w, a₁, l₁, a₂, l₂)`. -/
abbrev WPair (K : Type*) := K × ℕ × List ℕ × ℕ × List ℕ

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The unit moment oracle at the key `s`. -/
def delta (s : MKey) : ℕ → ℕ → ℕ → ℕ → K := fun A B m n => if (A, B, m, n) = s then 1 else 0

/-- **Definition.** The pairs `(A, B)` at which `stateVal` reads its oracle. -/
def stateKeys : (d : ℕ) → (Fin d → Fin 3) → (Fin d → List K) → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _, A, B => [(A, B)]
  | d + 1, c, fs, A, B => ((List.range (fs 0).length).flatMap fun e =>
      stateKeys d (fun j => c j.succ) (fun j => fs j.succ) (A + roughPart (c 0) e)
        (B + smoothPart (c 0) e)).dedup

/-- **Definition.** The pairs `(A, B)` at which `placeVal` reads its oracle (every branch,
whatever its multiplicity), duplicates removed at every level. -/
def placeKeys : (d : ℕ) → (Fin d → Fin 3) → (Fin d → List K) → List (Fin 3 → List K) →
    List (ℕ × ℕ)
  | d, c, fs, [] => stateKeys d c fs 0 0
  | d, c, fs, φ :: rest =>
      (((List.finRange d).flatMap fun j =>
        placeKeys d c (Function.update fs j (lpMul (fs j) (φ (c j)))) rest) ++
      ((List.finRange 3).flatMap fun c' =>
        placeKeys (d + 1) (Fin.cons c' c) (Fin.cons (φ c') fs) rest)).dedup

/-- **Definition.** The distinct moment keys queried by `genPieceWith`. -/
def genKeys (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) : List MKey :=
  ((innerTerms (K := K) a₁ l₁).flatMap fun t₁ => (innerTerms (K := K) a₂ l₂).flatMap fun t₂ =>
    (placeKeys (K := K) 0 Fin.elim0 Fin.elim0
      ((t₁.1 ++ t₂.1).map fun q c => lpShiftPow (clsShift g c) q)).map fun p =>
        (p.1, p.2, t₁.2.1 + t₂.2.1, t₁.2.2.1 + t₂.2.2.1)).dedup

/-- **Definition.** The keys and coefficients of one generator pair on a piece. -/
def genCoeffs (N r k : ℕ) (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    List (MKey × K) :=
  (genKeys g a₁ l₁ a₂ l₂).map fun s => (s, genPieceWith N r k g (delta s) a₁ l₁ a₂ l₂)

/-- **Definition.** The distinct keys of a weighted list of generator pairs. -/
def aggKeys (g : K) (ws : List (WPair K)) : List MKey :=
  (ws.flatMap fun w => genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).dedup

/-- **Definition.** The coefficient of a key, summed over the weighted pairs. -/
def aggCoeff (N r k : ℕ) (g : K) (ws : List (WPair K)) (s : MKey) : K :=
  (ws.map fun w => w.1 * genPieceWith N r k g (delta s) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum

/-- **Definition.** The aggregated piece value: each distinct key evaluated once. -/
def aggPiece (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) : K :=
  ((aggKeys g ws).map fun s => aggCoeff N r k g ws s * Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum

/-- **Definition.** The aggregated piece value over a given key list `S` (a certificate supplies
`S` as a literal; `aggPieceOn_eq` needs only that `S` is duplicate-free and covers the keys). -/
def aggPieceOn (S : List MKey) (N r k : ℕ) (g : K) (ws : List (WPair K))
    (Mo : ℕ → ℕ → ℕ → ℕ → K) : K :=
  (S.map fun s => aggCoeff N r k g ws s * Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum

/-- **Definition.** The aggregated entry over a given key list `S`. -/
def aggEntryValOn (S : List MKey) (N : ℕ) (g L τ : K) (C : ℕ → K) (ws : List (WPair K)) : K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
    ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
      aggPieceOn S N r k g ws (fun A B m n => pieceMn N r k A B g L τ C m n)

/-- **Definition.** The aggregated value of `Σ_{(w, …) ∈ ws} w · J_T[G_{a₁,l₁}, G_{a₂,l₂}]`. -/
def aggEntryVal (N : ℕ) (g L τ : K) (C : ℕ → K) (ws : List (WPair K)) : K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
    ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
      aggPiece N r k g ws (fun A B m n => pieceMn N r k A B g L τ C m n)

end Formula

/-- **Definition.** The synthetic cap function of the controls and demonstrations (`N = 3`,
`g = 3/10`, `L = 1`, `τ = 9/10`): `C = 0, 1/2, 3/5, 7/10, 7/10, …`. -/
def synthC : ℕ → ℚ := fun m => if m = 0 then 0 else if m = 1 then 1 / 2 else if m = 2 then 3 / 5 else 7 / 10

end BGP212.V2e
