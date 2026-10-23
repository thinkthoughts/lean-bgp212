/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymReduce

/-! # V2ℓ: staged symmetric-function evaluation and reusable coefficient tables (definitions)

Track B. The proofs are in `Solution/SymStaged.lean`. V2i's, V2j's and V2k's definitions and
theorems are unchanged; this module adds certificate predicates for evaluating V2k's canonical
symmetric states one factor (or one chunk of states) at a time, and a table built from
separately certified runs, each shared by every inner-term pair with the same factors.

**Steps.** `symStepAll n φ L = normalize (L.flatMap (symStep n φ))` is one step of V2k's `symRun`.
`StepCert n φ L L'` says that `L'` carries the value of `L` with the factor `φ` applied, for
every moment oracle and every continuation; it follows from the list equality
`symStepAll n φ L = L'` (one kernel evaluation per factor), from certified chunks of `L` together
with one merge `normalize (D₁ ++ D₂) = L'`, and from Boolean checks (`combBEq`).

**Chains.** `ChainCert n φs L L'` composes step certificates along the factor list `φs`; a chain
for a prefix is reused by every continuation (`chainCert_append`). `StepsOK` is the list-level
form `symStepAll n φᵢ Lᵢ = Lᵢ₊₁`.

**Tables.** `pairGroups ws` collects the inner-term pairs of a weighted list of generator pairs
by `(factor degrees Q, power of U, power of L − S)`, adding coefficients, so each distinct triple
appears once; `stagedTable N r k g R ws` evaluates each group from the certified run of `Q` in
`R` (or V2k's `symRun` when `Q` is absent) and collects moment keys as V2k's `aggTable`. -/

namespace BGP212.V2e

section Staged

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** One step of `symRun`: apply `φ` to every state and normalize. -/
def symStepAll (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L : List (SKey × K)) : List (SKey × K) :=
  normalize (L.flatMap (symStep n φ))

/-- **Definition.** `L'` carries the value of `L` continued by `φ`, for every moment oracle `M`
and every continuation `rest`. -/
def StepCert (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' : List (SKey × K)) : Prop :=
  ∀ (M : ℕ → ℕ → K) (rest : List (Fin 3 → List K)), symVal M n rest L' = symVal M n (φ :: rest) L

/-- **Definition.** `L` and `L'` have the same value for every oracle and continuation. -/
def ValEq (n : Fin 3 → ℕ) (L L' : List (SKey × K)) : Prop :=
  ∀ (M : ℕ → ℕ → K) (rest : List (Fin 3 → List K)), symVal M n rest L' = symVal M n rest L

/-- **Definition.** A chain of step certificates along the factor list. -/
def ChainCert (n : Fin 3 → ℕ) : List (Fin 3 → List K) → List (SKey × K) → List (SKey × K) → Prop
  | [], L, L' => ValEq n L L'
  | φ :: φs, L, L' => ∃ L₁, StepCert n φ L L₁ ∧ ChainCert n φs L₁ L'

/-- **Definition.** List-level staged steps: `symStepAll n φᵢ Lᵢ = Lᵢ₊₁` along the factors. -/
def StepsOK (n : Fin 3 → ℕ) : List (Fin 3 → List K) → List (List (SKey × K)) → Prop
  | [], [_] => True
  | φ :: φs, L :: L' :: Ls => symStepAll n φ L = L' ∧ StepsOK n φs (L' :: Ls)
  | _, _ => False

/-- **Definition.** Boolean equality of combinations (natural-number key comparison, for kernel
certificates). -/
def combBEq : List (SKey × K) → List (SKey × K) → Bool
  | [], [] => true
  | p :: L, q :: L' => (keyCmp p.1 q.1 == .eq) && decide (p.2 = q.2) && combBEq L L'
  | _, _ => false

/-- **Definition.** The factor list of the shifted power sums `P̂_q`, `q ∈ Q`, on a piece. -/
def psFactors (g : K) (Q : List ℕ) : List (Fin 3 → List K) :=
  Q.map fun q c => lpShiftPow (clsShift g c) q

/-- **Definition.** The run of `Q` from a table of certified runs, or V2k's `symRun` if absent. -/
def runLookup (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List (SKey × K))) (Q : List ℕ) :
    List (SKey × K) :=
  match R.find? (fun p => p.1 == Q) with
  | some p => p.2
  | none => symRun n (psFactors g Q) [([], 1)]

end Staged

/-- **Definition.** Lexicographic comparison of lists of natural numbers. -/
def natListCmp : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: l, b :: m => if a < b then .lt else if b < a then .gt else natListCmp l m

/-- **Definition.** Comparison of group keys `(Q, m, n)`. -/
def qmnCmp (s t : List ℕ × ℕ × ℕ) : Ordering :=
  match natListCmp s.1 t.1 with
  | .eq => if s.2.1 < t.2.1 then .lt else if t.2.1 < s.2.1 then .gt else
      if s.2.2 < t.2.2 then .lt else if t.2.2 < s.2.2 then .gt else .eq
  | o => o

/-- **Definition.** Lexicographic comparison of `(A, B)` pairs. -/
def abCmp (s t : ℕ × ℕ) : Ordering :=
  if s.1 < t.1 then .lt else if t.1 < s.1 then .gt else
  if s.2 < t.2 then .lt else if t.2 < s.2 then .gt else .eq

section Tables

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The inner-term pairs of a weighted list of generator pairs, grouped by
`(Q, power of U, power of L − S)` with summed coefficients; `Q` is the multiset of power-sum
degrees, sorted in decreasing order (the order of the factors is immaterial, `placeVal_perm`). -/
def pairGroups (ws : List (WPair K)) : List ((List ℕ × ℕ × ℕ) × K) :=
  normalizeBy qmnCmp (ws.flatMap fun w => (innerTerms (K := K) w.2.1 w.2.2.1).flatMap fun t₁ =>
    (innerTerms (K := K) w.2.2.2.1 w.2.2.2.2).map fun t₂ =>
      (((t₁.1 ++ t₂.1).insertionSort (fun a b => b ≤ a), t₁.2.1 + t₂.2.1, t₁.2.2.1 + t₂.2.2.1),
        w.1 * (t₁.2.2.2 * t₂.2.2.2)))

/-- **Definition.** The moment-coefficient table of a piece from certified runs: each group
`(Q, m, n)` contributes its coefficient times `κ ∏ e!` of every final state of the run of `Q`. -/
def stagedTable (N r k : ℕ) (g : K) (R : List (List ℕ × List (SKey × K))) (ws : List (WPair K)) :
    List (MKey × K) :=
  normalizeBy mkeyCmp ((pairGroups ws).flatMap fun G =>
    (runLookup (clsCount N r k) g R G.1.1).map fun q =>
      ((keyA q.1, keyB q.1, G.1.2.1, G.1.2.2), G.2 * q.2 * factW q.1))

/-- **Definition.** The moment profile of a combination: `Σ κ ∏ e!` collected by
`(rough degree, smooth degree)`, so that `symFinal M L = Σ c · M(A, B)` over the profile. -/
def abProfile (L : List (SKey × K)) : List ((ℕ × ℕ) × K) :=
  normalizeBy abCmp (L.map fun q => ((keyA q.1, keyB q.1), q.2 * factW q.1))

/-- **Definition.** A certified profile: V2i's placement value of the power sums `P̂_q`, `q ∈ Q`,
is `Σ c · M(A, B)` over `P`, for every oracle `M`. -/
def ProfCert (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (P : List ((ℕ × ℕ) × K)) : Prop :=
  ∀ M : ℕ → ℕ → K, placeVal M n 0 Fin.elim0 Fin.elim0 (psFactors g Q) =
    (P.map fun e => e.2 * M e.1.1 e.1.2).sum

/-- **Definition.** The profile of `Q` from a table of certified profiles, or from V2k's run. -/
def profLookup (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K))) (Q : List ℕ) :
    List ((ℕ × ℕ) × K) :=
  match R.find? (fun p => p.1 == Q) with
  | some p => p.2
  | none => abProfile (symRun n (psFactors g Q) [([], 1)])

/-- **Definition.** The moment-coefficient table of a piece from certified profiles: each group
`(Q, m, n)` with coefficient `c` contributes `c · c'` at `(A, B, m, n)` for each profile entry
`((A, B), c')` of `Q`. -/
def profTable (N r k : ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K))) (ws : List (WPair K)) :
    List (MKey × K) :=
  normalizeBy mkeyCmp ((pairGroups ws).flatMap fun G =>
    (profLookup (clsCount N r k) g R G.1.1).map fun e =>
      ((e.1.1, e.1.2, G.1.2.1, G.1.2.2), G.2 * e.2))

end Tables

/-! ### Compact encoding of certificate data -/

/-- **Definition.** Parts from `[c₁, e₁, c₂, e₂, …]` (classes reduced mod 3). -/
def decParts : List ℕ → SKey
  | c :: e :: rest => (⟨c % 3, Nat.mod_lt _ (by decide)⟩, e) :: decParts rest
  | _ => []

/-- **Definition.** A state with coefficient from `[sign, numerator, denominator, c₁, e₁, …]`. -/
def decEntry : List ℕ → SKey × ℚ
  | s :: a :: b :: rest => (decParts rest, (if s = 0 then (a : ℚ) else -(a : ℚ)) / (b : ℚ))
  | _ => ([], 0)

/-- **Definition.** A combination from its compact encoding (one list of naturals per state; the
elaborator reads natural-number literals far faster than rational and `Fin` literals). -/
def decComb (raw : List (List ℕ)) : List (SKey × ℚ) := raw.map decEntry

/-- **Definition.** A table entry from `[A, B, m, n, sign, numerator, denominator]`. -/
def decTEntry : List ℕ → MKey × ℚ
  | A :: B :: m :: n :: s :: a :: b :: _ => ((A, B, m, n), (if s = 0 then (a : ℚ) else -(a : ℚ)) / (b : ℚ))
  | _ => ((0, 0, 0, 0), 0)

/-- **Definition.** A profile entry from `[A, B, sign, numerator, denominator]`. -/
def decPEntry : List ℕ → (ℕ × ℕ) × ℚ
  | A :: B :: s :: a :: b :: _ => ((A, B), (if s = 0 then (a : ℚ) else -(a : ℚ)) / (b : ℚ))
  | _ => ((0, 0), 0)

/-- **Definition.** A moment profile from its compact encoding. -/
def decProf (raw : List (List ℕ)) : List ((ℕ × ℕ) × ℚ) := raw.map decPEntry

/-- **Definition.** A moment-coefficient table from its compact encoding. -/
def decTable (raw : List (List ℕ)) : List (MKey × ℚ) := raw.map decTEntry

end BGP212.V2e
