/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymProfile

/-! # V2o: what one factor reads (definitions)

Track B. The proofs are in `Solution/SymRead.lean`. V2i–V2n are unchanged.

**The question.** V2n's direct transition reads, for a leaf, the parent's marked profile of order
`≤ 1`: the moment profile `P(A, B)` and, for every part `(c, e)` of every state, the entry
`((A, B, [(c, e)]), κ ∏ e!)`. One factor `φ` uses a marked part only through the weight
`(e + a)!/e! − a! = a! (C(e + a, a) − 1)` for the degrees `a` of `φ(c)`. So the factor reads, besides
`P`, only the **binomial read summary**

  `δ_a(A, B, c) = Σ_{(A, B, [(c, e)])} v · (C(e + a, a) − 1)`,   `1 ≤ a ≤ d`,

for factors of degree `≤ d` (`readSummary d`); the class counts enter only through these
differences. `readStep` computes the child's moment profile from `P` and the summary
(`readStep_sufficient`); conversely, the monomial factor `x^a` in class `c` reads exactly
`a! (n_c P(A, B) + δ_a(A, B, c))` at the key `(A, B)` shifted by `a` (`monomial_reads`), so no
coordinate of the summary can be dropped for factors of degree `≤ d`, and V2n's two states agree on
`δ₁` but not `δ₂` (`summary_degree_gap`).

* `ReadKey`, `readCmp`, `readTerms`, `readSummary` — the binomial read summary of an order-`≤ 1`
  marked profile;
* `pull0`, `pull1`, `readStep` — the child's moment profile from the profile and the summary;
* `degLe`, `monoF`, `profAt`, `readAt` — degree bound, monomial factors, values at one key. -/

namespace BGP212.V2e

/-- A read key: rough degree, smooth degree, class, degree read. -/
abbrev ReadKey := ℕ × ℕ × Fin 3 × ℕ

/-- **Definition.** Lexicographic comparison of read keys. -/
def readCmp (s t : ReadKey) : Ordering :=
  if s.1 < t.1 then .lt else if t.1 < s.1 then .gt else
  if s.2.1 < t.2.1 then .lt else if t.2.1 < s.2.1 then .gt else
  if s.2.2.1 < t.2.2.1 then .lt else if t.2.2.1 < s.2.2.1 then .gt else
  if s.2.2.2 < t.2.2.2 then .lt else if t.2.2.2 < s.2.2.2 then .gt else .eq

section Read

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The read terms of one marked key (per unit coefficient): for a key with one mark
`(c, e)`, the entries `((A, B, c, a), C(e + a, a) − 1)`, `1 ≤ a ≤ d`; nothing otherwise. -/
def readTerms (d : ℕ) (key : MarkKey) : List (ReadKey × K) :=
  match key.2.2 with
  | [x] => (List.range d).map fun i =>
      ((key.1, key.2.1, x.1, i + 1), ((((x.2 + (i + 1)).choose (i + 1) : ℕ) : K) - 1))
  | _ => []

/-- **Definition (binomial read summary).** `δ_a(A, B, c)` for `1 ≤ a ≤ d`, from a marked profile,
merged by key. -/
def readSummary (d : ℕ) (P : List (MarkKey × K)) : List (ReadKey × K) :=
  normalizeBy readCmp (P.flatMap fun e => (readTerms d e.1).map fun t => (t.1, e.2 * t.2))

/-- **Definition.** The child keys and coefficients of a profile entry `(A, B)`: the constant terms,
and a new part `(c, a)` with weight `n_c φ(c)_a a!`. -/
def pull0 (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (ab : ℕ × ℕ) : List ((ℕ × ℕ) × K) :=
  (ab, constSum n φ) :: ([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
    ((ab.1 + roughPart c ac.1, ab.2 + smoothPart c ac.1), (n c : K) * ac.2 * (ac.1.factorial : K))

/-- **Definition.** The child key and coefficient of a summary entry `(A, B, c, a)`: weight
`φ(c)_a a!` at `(A, B)` shifted by `a` in class `c`. -/
def pull1 (φ : Fin 3 → List K) (key : ReadKey) : (ℕ × ℕ) × K :=
  ((key.1 + roughPart key.2.2.1 key.2.2.2, key.2.1 + smoothPart key.2.2.1 key.2.2.2),
    (φ key.2.2.1).getD key.2.2.2 0 * (key.2.2.2.factorial : K))

/-- **Definition (the step read from the summary).** The child's moment profile from the parent's
profile `R0` and read summary `Rd`. -/
def readStep (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (R0 : List ((ℕ × ℕ) × K)) (Rd : List (ReadKey × K)) :
    List ((ℕ × ℕ) × K) :=
  normalizeBy abCmp ((R0.flatMap fun e => (pull0 n φ e.1).map fun t => (t.1, e.2 * t.2)) ++
    Rd.map fun e => ((pull1 φ e.1).1, e.2 * (pull1 φ e.1).2))

/-- **Definition.** `φ` has degree at most `d` in every class. -/
def degLe (d : ℕ) (φ : Fin 3 → List K) : Prop := ∀ c, (φ c).length ≤ d + 1

/-- **Definition.** The monomial factor `x^a` in class `c` (zero in the other classes). -/
def monoF (c : Fin 3) (a : ℕ) : Fin 3 → List K :=
  fun c' => if c' = c then List.replicate a 0 ++ [1] else []

/-- **Definition.** The value of a profile at one key. -/
def profAt (R : List ((ℕ × ℕ) × K)) (ab : ℕ × ℕ) : K :=
  (R.map fun e => if e.1 = ab then e.2 else 0).sum

/-- **Definition.** The value of a read summary at one key. -/
def readAt (R : List (ReadKey × K)) (key : ReadKey) : K :=
  (R.map fun e => if e.1 = key then e.2 else 0).sum

end Read

end BGP212.V2e
