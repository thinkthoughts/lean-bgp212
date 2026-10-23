/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymStaged

/-! # V2m: certified prefix-trie evaluation (definitions)

Track B. The proofs are in `Solution/SymTrie.lean`. V2i–V2ℓ are unchanged.

**Tries.** The factor multisets of `B₂₁`, each stored as its degrees in decreasing order, form a
prefix-closed set: dropping the last (smallest) degree gives another multiset of the set, so one
certified step per multiset reaches all of them from the empty state. `TrieOK n g T` says that every
node `(Q, L)` of `T` carries a chain certificate from the empty state for the factors `P̂_q`,
`q ∈ Q`; `ProfOK n g R` says that every entry `(Q, P)` of `R` is a certified moment profile.
Profiles are indexed by `(A, B)` (rough and smooth degree) and are what the tables of V2ℓ
(`profTable`) consume; they are coefficient representations, not values of the moments.

**Shape and enumeration.** `evenPartsList`, `b21Kept` and `b21Multisets` enumerate, from the
definition of `B₂₁` (even parts, `|λ| ≤ 21`) and V2i's `subsetTerms`, the sorted factor multisets
of all inner-term pairs; `trieShapeOK` checks sortedness and prefix closure. -/

namespace BGP212.V2e

section Trie

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The factor `P̂_q` on a piece with class shift `g`. -/
def stepFactor (g : K) (q : ℕ) : Fin 3 → List K := fun c => lpShiftPow (clsShift g c) q

/-- **Definition.** Every node of the trie carries a chain certificate from the empty state. -/
def TrieOK (n : Fin 3 → ℕ) (g : K) (T : List (List ℕ × List (SKey × K))) : Prop :=
  ∀ p ∈ T, ChainCert n (psFactors g p.1) [([], 1)] p.2

/-- **Definition.** Every entry is a certified moment profile. -/
def ProfOK (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K))) : Prop :=
  ∀ p ∈ R, ProfCert n g p.1 p.2

end Trie

/-- **Definition.** Degrees in decreasing order (the canonical form of a factor multiset). -/
def sortDesc (Q : List ℕ) : List ℕ := Q.insertionSort (fun a b => b ≤ a)

/-- **Definition.** Decreasing order test. -/
def isSortedDesc : List ℕ → Bool
  | a :: b :: l => decide (b ≤ a) && isSortedDesc (b :: l)
  | _ => true

/-- **Definition.** Membership of a list of naturals in a list of such lists. -/
def natListMem (Q : List ℕ) : List (List ℕ) → Bool
  | [] => false
  | R :: S => (natListCmp Q R == .eq) || natListMem Q S

/-- **Definition.** Every nonempty element's prefix without its last entry is in the set. -/
def prefixClosed (S : List (List ℕ)) : Bool :=
  S.all fun Q => Q.isEmpty || natListMem Q.dropLast S

/-- **Definition.** Sorted (decreasing) and prefix-closed. -/
def trieShapeOK (S : List (List ℕ)) : Bool := S.all isSortedDesc && prefixClosed S

/-- **Definition.** Partitions of `j` into parts at most `k`, as decreasing lists. -/
def partsList : ℕ → ℕ → List (List ℕ)
  | j, 0 => if j = 0 then [[]] else []
  | j, k + 1 => (List.range (j / (k + 1) + 1)).flatMap fun c =>
      (partsList (j - c * (k + 1)) k).map fun s => List.replicate c (k + 1) ++ s

/-- **Definition.** The partitions `λ` of the generators of `B₂₁` (even parts, `|λ| ≤ 21`), parts
doubled, as decreasing lists. -/
def b21Lambdas : List (List ℕ) :=
  (List.range 11).flatMap fun j => (partsList j j).map fun s => s.map (2 * ·)

/-- **Definition.** The distinct kept-part lists of the inner integrals of `B₂₁` (V2i's
`subsetTerms`), sorted and merged. -/
def b21Kept : List (List ℕ) :=
  ((normalizeBy natListCmp ((b21Lambdas.flatMap fun l => (subsetTerms l).map fun t => t.1).map
    fun Q => (Q, ()))).map Prod.fst : List (List ℕ))

/-- **Definition.** The kept-part lists of the generators with `|λ| ≤ s`. -/
def keptUpTo (s : ℕ) : List (List ℕ) :=
  ((normalizeBy natListCmp (((b21Lambdas.filter fun l => l.sum ≤ s).flatMap fun l =>
    (subsetTerms l).map fun t => t.1).map fun Q => (Q, ()))).map Prod.fst : List (List ℕ))

/-- **Definition.** The factor multisets of the inner-term pairs of the generators with `|λ| ≤ s`
(the block `|λ| ≤ s` of `B₂₁`), in decreasing order. -/
def blockMultisets (s : ℕ) : List (List ℕ) :=
  (normalizeBy natListCmp (((keptUpTo s).flatMap fun x => (keptUpTo s).map fun y =>
    sortDesc (x ++ y)).map fun Q => (Q, ()))).map Prod.fst

/-- **Definition.** The factor multisets with at most `k` factors of the pairs from a list of
kept-part lists. -/
def shortMultisetsOf (kept : List (List ℕ)) (k : ℕ) : List (List ℕ) :=
  (normalizeBy natListCmp (((kept.filter fun x => x.length ≤ k).flatMap fun x =>
    ((kept.filter fun y => x.length + y.length ≤ k).map fun y => sortDesc (x ++ y))).map
      fun Q => (Q, ()))).map Prod.fst

/-- **Definition.** The factor multisets of `B₂₁` with at most `k` factors. -/
def shortMultisets (k : ℕ) : List (List ℕ) := shortMultisetsOf b21Kept k

/-- **Definition.** The distinct factor multisets of all inner-term pairs of `B₂₁`, each in
decreasing order (2 361 of them by the exploratory enumeration). -/
def b21Multisets : List (List ℕ) :=
  (normalizeBy natListCmp ((b21Kept.flatMap fun x => b21Kept.map fun y => sortDesc (x ++ y)).map
    fun Q => (Q, ()))).map Prod.fst

end BGP212.V2e
