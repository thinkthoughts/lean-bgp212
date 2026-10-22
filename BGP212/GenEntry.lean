/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 and the display of
`J_T` (p. 41), Proposition 10.2 (pp. 41–42), §11 (B₂₁, p. 42).
-/
import BGP212.PowerSumPlace

/-! # V2i: general polynomial marginal Gram entries `J_T[G_{a,λ}, G_{b,μ}]` (definitions)

Track B. The proofs are in `Solution/GenEntry.lean`.

**Generators.** `genFun L a l x = (L − Σ x)^a ∏_{q ∈ l} Σᵢ xᵢ^q` is V0's `gen a l` (`(L − P₁)^a P_λ`)
as a function (`eval_gen`), with the parts of `λ` as a list.

**Inner integral.** With `M = L − Σ x̂`, `∫₀^U G_{a,λ}(x̂, u) du = Σ_{T ⊆ λ} P̂_{λ∖T} ·
Σ_{j ≤ a} C(a, j) (−1)^j M^{a−j} U^{s_T + j + 1} / (s_T + j + 1)` (`innerTerms`: parts kept, power
of `U`, power of `M`, coefficient). After the translation of a piece, `M` is the `L − S` of V2f's
`cellsVal`, so every term is a power-sum product against `U^m (L − S)^n`.

**Placement.** On a piece, `P̂_q(y + s) = Σᵢ φ_q(yᵢ, cls i)` with `φ_q(y, c) = (y + σ_c)^q`, a
univariate polynomial (a coefficient list, `lpShiftPow`). A product of such sums is integrated by
`placeVal`: each factor either merges into an open distinguished coordinate (its polynomial is
multiplied, `lpMul`) or opens a new coordinate of class `c`, with multiplicity `n_c − #(open in c)`.
Unrolled this is the sum over set partitions with falling-factorial class counts. `stateVal`
integrates the open coordinates: a coordinate of class `c` with polynomial `f` contributes
`Σ_e f_e e!`, its degree `e` landing in the rough (`c = 0`) or the smooth group.

**Moments.** Everything is linear in a moment oracle `Mo A B m n`; for the integral it is
`pieceMn N r k A B … m n`, V2h's `pieceM` with the `(L − S)^n` factor. All values are defined over
an ordered field, so over `ℚ` they are computable. -/

namespace BGP212.V2e

/-- **Definition.** The generator `(L − Σ x)^a ∏_{q ∈ l} Σᵢ xᵢ^q` (`l` the parts of `λ`). -/
def genFun {n : ℕ} (L : ℝ) (a : ℕ) (l : List ℕ) (x : Fin n → ℝ) : ℝ :=
  (L - ∑ i, x i) ^ a * (l.map fun q => ∑ i, x i ^ q).prod

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The weighted piece moment `∫_{piece} yᵗ U^m (L − S)^n` with the factorials of
the weight removed (rough degree `a`, smooth degree `b`); zero for an empty piece. For `n = 0` it
is V2h's `pieceM`. -/
def pieceMn (N r k a b : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) : K :=
  if C r - r * g < 0 ∨ τ - (r + k) * g < 0 then 0
  else if r = 0 then 1 / ((N + b - 1).factorial : K) * seg0Val g L C k (τ - k * g) (N - 1 + b) m n
  else 1 / ((r + a - 1).factorial : K) * (1 / ((N - r + b - 1).factorial : K)) *
    cellsVal g L C r k (C r - r * g) (τ - (r + k) * g) (r - 1 + a) (N - r - 1 + b) m n

/-! ### Univariate polynomials as coefficient lists -/

/-- **Definition.** Horner evaluation `f₀ + y (f₁ + y (f₂ + ⋯))`. -/
def lpEval (f : List K) (y : K) : K := f.foldr (fun c acc => c + y * acc) 0

/-- **Definition.** Sum of coefficient lists. -/
def lpAdd : List K → List K → List K
  | [], g => g
  | a :: f, [] => a :: f
  | a :: f, b :: g => (a + b) :: lpAdd f g

/-- **Definition.** Product of coefficient lists. -/
def lpMul : List K → List K → List K
  | [], _ => []
  | a :: f, g => lpAdd (g.map (a * ·)) (0 :: lpMul f g)

/-- **Definition.** `(y + s)^q` as a coefficient list. -/
def lpShiftPow (s : K) (q : ℕ) : List K :=
  (List.range (q + 1)).map fun a => ((q.choose a : ℕ) : K) * s ^ (q - a)

/-! ### Open coordinates and placements -/

/-- **Definition.** `Σ_j f_j · body(e + j)`. -/
def coordSum (body : ℕ → K) : List K → ℕ → K
  | [], _ => 0
  | c :: f, e => c * body e + coordSum body f (e + 1)

/-- **Definition.** The value of `d` open coordinates of classes `c` with polynomials `fs`
(degrees accumulated in the rough part `A` and the smooth part `B`), against the moment
oracle `M`. -/
def stateVal (M : ℕ → ℕ → K) : (d : ℕ) → (Fin d → Fin 3) → (Fin d → List K) → ℕ → ℕ → K
  | 0, _, _, A, B => M A B
  | d + 1, c, fs, A, B => coordSum (fun e => (e.factorial : K) *
      stateVal M d (fun j => c j.succ) (fun j => fs j.succ) (A + roughPart (c 0) e)
        (B + smoothPart (c 0) e)) (fs 0) 0

/-- **Definition.** The placement recursion: each factor (a class-dependent polynomial) merges
into an open coordinate or opens a new one of class `c'`, multiplicity `n c' − #(open in c')`. -/
def placeVal (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    (d : ℕ) → (Fin d → Fin 3) → (Fin d → List K) → List (Fin 3 → List K) → K
  | d, c, fs, [] => stateVal M d c fs 0 0
  | d, c, fs, φ :: rest =>
      (∑ j : Fin d, placeVal M n d c (Function.update fs j (lpMul (fs j) (φ (c j)))) rest) +
        ∑ c' : Fin 3, (((n c' : ℕ) : K) - (((Finset.univ.filter fun j => c j = c').card : ℕ) : K)) *
          placeVal M n (d + 1) (Fin.cons c' c) (Fin.cons (φ c') fs) rest

/-! ### Inner integrals of generators -/

/-- **Definition.** The terms of `∏_{q ∈ l} (X_q + u^q)`: parts kept and power of `u`. -/
def subsetTerms : List ℕ → List (List ℕ × ℕ)
  | [] => [([], 0)]
  | q :: l => (subsetTerms l).map (fun t => (q :: t.1, t.2)) ++
      (subsetTerms l).map (fun t => (t.1, t.2 + q))

/-- **Definition.** The terms of `∫₀^U (M − u)^a ∏_{q ∈ l} (P̂_q + u^q) du`: parts kept, power of
`U`, power of `M`, coefficient. -/
def innerTerms (a : ℕ) (l : List ℕ) : List (List ℕ × ℕ × ℕ × K) :=
  (subsetTerms l).flatMap fun t => (List.range (a + 1)).map fun j =>
    (t.1, t.2 + j + 1, a - j, ((a.choose j : ℕ) : K) * (-1) ^ j / ((t.2 + j + 1 : ℕ) : K))

/-! ### The entry -/

/-- **Definition.** The piece value of `J_T[G_{a₁,l₁}, G_{a₂,l₂}]` against a moment oracle
`Mo A B m n`. -/
def genPieceWith (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) : K :=
  ((innerTerms (K := K) a₁ l₁).map fun t₁ => ((innerTerms (K := K) a₂ l₂).map fun t₂ =>
    t₁.2.2.2 * t₂.2.2.2 *
      placeVal (fun A B => Mo A B (t₁.2.1 + t₂.2.1) (t₁.2.2.1 + t₂.2.2.1)) (clsCount N r k) 0
        Fin.elim0 Fin.elim0 ((t₁.1 ++ t₂.1).map fun q c => lpShiftPow (clsShift g c) q)).sum).sum

/-- **Definition.** The piece value with the integral moments `pieceMn`. -/
def genPiece (N r k : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    K :=
  genPieceWith N r k g (fun A B m n => pieceMn N r k A B g L τ C m n) a₁ l₁ a₂ l₂

/-- **Definition.** One row of the signed count of `genPiece`. -/
def genRow (N r : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) : K :=
  ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
    genPiece N r k g L τ C a₁ l₁ a₂ l₂

/-- **Definition.** The closed form of `J_T[G_{a₁,l₁}, G_{a₂,l₂}]`. -/
def genEntryVal (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) * genRow N r g L τ C a₁ l₁ a₂ l₂

/-- **Definition.** A moment oracle given by a finite table of values, falling back to `dflt`
off the table (used by the certificate: the table holds certified moments). -/
def tableFn (keys : List ((ℕ × ℕ × ℕ × ℕ) × K)) (dflt : ℕ → ℕ → ℕ → ℕ → K) (A B m n : ℕ) : K :=
  match keys.find? (fun p => p.1 == (A, B, m, n)) with
  | some p => p.2
  | none => dflt A B m n

end Formula

end BGP212.V2e
