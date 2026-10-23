/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.MomentAgg

/-! # V2k: symmetric-function reduction of the placement recursion (definitions)

Track B. The proofs are in `Solution/SymReduce.lean`. V2i's specification (`placeVal`,
`genPieceWith`, `genEntryVal`) and V2j's aggregation layer are unchanged; this module adds a
second evaluator for the same values and the specification it is proved against.

**Class power sums.** On a piece each factor of a product of shifted power sums is
`Σᵢ φ(cls i)(yᵢ)` with `φ(c) = Σ_a φ(c)_a y^a` (V2i's coefficient lists), i.e.

  `Σ_c n_c · φ(c)₀ + Σ_c Σ_{a ≥ 1} φ(c)_a · p_{c,a}`,   `p_{c,a} = Σ_{cls i = c} yᵢ^a`.

**Augmented monomial symmetric functions.** A state is a multiset `S` of parts `(c, e)` (class,
positive exponent), standing for `∏_c m̃_{ν_c}` where `ν_c` collects the exponents of class `c` and
`m̃_ν = Σ_{distinct i₁, …, i_ℓ in class c} ∏_j y_{i_j}^{ν_j}` (`= ∏_v mult_v(ν)! · m_ν`). The
classical transition rule `p_a · m̃_ν = Σ_j m̃_{ν + a e_j} + m̃_{ν ∪ (a)}` is applied factor by factor;
a new part of class `c` is weighted by `n_c − ℓ(ν_c)`, the number of free coordinates of that
class, so the falling factorial `(n_c)_{ℓ(ν_c)}` (the number of index choices of `m̃_{ν_c}`)
accumulates in the coefficient.

**Dirichlet moment.** After all factors, a state contributes `∏_{(c,e) ∈ S} e! · M(A, B)`, with
`A` the rough degree (class `0`) and `B` the smooth degree (classes `1`, `2`). With the
accumulated weight `∏_c (n_c)_{ℓ(ν_c)}` this is the integral of `∏_c m̃_{ν_c}` (`monoMoment`; for
`m_ν` divide by `∏_v mult_v(ν)!`, i.e. `#monomials(m_ν) · ∏ νᵢ! · M(A, B)`).

**Canonical representation.** A state is stored as a list of parts sorted by class, then by
decreasing exponent (`sIns`), i.e. one integer partition per class; equal states are merged after
every factor (`normalize`, a balanced merge sort by structural recursion, which keeps the kernel's
evaluation shallow), with exact coefficients in `K` (`ℚ` in certificates).

* `msOf`, `msum`, `msVal M n rest S` — the specification side: the multiset of parts of open
  coordinates, iterated coefficient sums, and the value of the state `S` continued by the factors
  `rest` (on multisets, so the order of parts is immaterial by construction);
* `symStep`, `normalize`, `symRun`, `symFinal`, `symPlaceVal`, `symVal` — the canonical evaluator;
* `genPieceSym`, `genEntrySym` — V2i's piece and entry values with `symPlaceVal` in place of
  `placeVal`;
* `psFactor`, `symStep1`, `symRun1`, `psTrans`, `fallW`, `scaleQ`, `monoMoment` — the transition
  `p_α = Σ_ν R_{α,ν} m̃_ν` and the Dirichlet-weighted moment;
* `genTable`, `aggTable`, `tableVal` — all moment coefficients of a piece from one evaluation;
* `demoN`, `demoM`, `demoF` — data of the small certified examples. -/

namespace BGP212.V2e

/-- A part `(c, e)`: class and exponent of one distinguished coordinate. -/
abbrev SPart := Fin 3 × ℕ

/-- A canonical state: parts sorted by class, then by decreasing exponent. -/
abbrev SKey := List SPart

/-- **Definition.** The order of the canonical form: class ascending, exponent descending. -/
def partLe (x y : SPart) : Bool := x.1.val < y.1.val || (x.1.val == y.1.val && y.2 ≤ x.2)

/-- **Definition.** Sorted insertion of a part. -/
def sIns (y : SPart) : SKey → SKey
  | [] => [y]
  | x :: l => if partLe y x then y :: x :: l else x :: sIns y l

/-- **Definition.** Each element of a list together with the remaining elements. -/
def picks {α : Type*} : List α → List (α × List α)
  | [] => []
  | x :: l => (x, l) :: (picks l).map fun p => (p.1, x :: p.2)

/-- **Definition.** The number of parts of class `c`, `ℓ(ν_c)`. -/
def clsCnt (k : SKey) (c : Fin 3) : ℕ := k.countP fun x => x.1.val == c.val

/-- **Definition.** Comparison of parts in the canonical order (on natural numbers, for kernel
evaluation). -/
def partCmp (x y : SPart) : Ordering :=
  if x.1.val < y.1.val then .lt else if y.1.val < x.1.val then .gt
  else if y.2 < x.2 then .lt else if x.2 < y.2 then .gt else .eq

/-- **Definition.** Lexicographic comparison of canonical states. -/
def keyCmp : SKey → SKey → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: l, y :: m => match partCmp x y with
    | .eq => keyCmp l m
    | o => o

/-! ### Sorted merging of combinations (generic in the key) -/

section Merge

variable {α K : Type*} [Add K] (cmp : α → α → Ordering)

/-- **Definition.** Merge step of two sorted combinations (`rec` merges the tail of the first). -/
def mergeGo (a : α × K) (l₁ : List (α × K)) (rec : List (α × K) → List (α × K)) :
    List (α × K) → List (α × K)
  | [] => a :: l₁
  | b :: l₂ => match cmp a.1 b.1 with
    | .lt => a :: rec (b :: l₂)
    | .eq => (a.1, a.2 + b.2) :: rec l₂
    | .gt => b :: mergeGo a l₁ rec l₂

/-- **Definition.** Merge two sorted combinations, adding the coefficients of equal keys. -/
def mergeT : List (α × K) → List (α × K) → List (α × K)
  | [], l₂ => l₂
  | a :: l₁, l₂ => mergeGo cmp a l₁ (mergeT l₁) l₂

/-- **Definition.** Merge adjacent pairs of sorted runs. -/
def mergePairs : List (List (α × K)) → List (List (α × K))
  | a :: b :: rest => mergeT cmp a b :: mergePairs rest
  | rs => rs

/-- **Definition.** Merge all runs by rounds of `mergePairs` (balanced, so the kernel's evaluation
stays shallow; `fuel` rounds, then a plain fold). -/
def mergeAll : ℕ → List (List (α × K)) → List (α × K)
  | 0, rs => rs.foldr (mergeT cmp) []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => mergeAll fuel (mergePairs cmp (a :: b :: rest))

/-- **Definition.** Sort a combination by key and merge equal keys (`O(n log n)` comparisons,
balanced merge sort by structural recursion). -/
def normalizeBy (L : List (α × K)) : List (α × K) :=
  mergeAll cmp 64 (L.map fun t => [t])

end Merge

/-- **Definition.** Lexicographic comparison of moment keys. -/
def mkeyCmp (s t : MKey) : Ordering :=
  if s.1 < t.1 then .lt else if t.1 < s.1 then .gt else
  if s.2.1 < t.2.1 then .lt else if t.2.1 < s.2.1 then .gt else
  if s.2.2.1 < t.2.2.1 then .lt else if t.2.2.1 < s.2.2.1 then .gt else
  if s.2.2.2 < t.2.2.2 then .lt else if t.2.2.2 < s.2.2.2 then .gt else .eq

/-! ### Open coordinates (the specification side) -/

/-- **Definition.** The multiset of parts of open coordinates with classes `c`, exponents `e`. -/
def msOf {d : ℕ} (c : Fin d → Fin 3) (e : Fin d → ℕ) : Multiset SPart :=
  (Finset.univ : Finset (Fin d)).val.map fun j => (c j, e j)

section Iter

variable {K : Type*} [Field K]

/-- **Definition.** `Σ_{e} ∏_j (fs j)_{e_j} · F e`: the iterated coefficient sum over `d` open
coordinates with coefficient lists `fs`. -/
def msum : (d : ℕ) → (Fin d → List K) → ((Fin d → ℕ) → K) → K
  | 0, _, F => F Fin.elim0
  | d + 1, fs, F => coordSum (fun e₀ => msum d (fun j => fs j.succ) (fun e => F (Fin.cons e₀ e)))
      (fs 0) 0

end Iter

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition.** The exponent-coefficient pairs `(e + j, f_j)` of a coefficient list. -/
def cterms : List K → ℕ → List (ℕ × K)
  | [], _ => []
  | c :: f, e => (e, c) :: cterms f (e + 1)

/-- **Definition.** The constant coefficient `f₀`. -/
def constTerm : List K → K
  | [] => 0
  | c :: _ => c

/-- **Definition.** The nonzero coefficients of positive degree, `(a, f_a)` with `a ≥ 1`. -/
def posTerms : List K → List (ℕ × K)
  | [] => []
  | _ :: f => (cterms f 1).filter fun p => p.2 ≠ 0

/-- **Definition (specification).** The value of the state `S` (a multiset of parts, standing for
`∏_c m̃_{ν_c}`) continued by the factors `rest`. A factor multiplies `Σᵢ φ(cls i)(yᵢ)`: every
part `x` absorbs it (`x.2 ↦ x.2 + a` with coefficient `φ(x.1)_a`), or a new part `(c, a)` opens,
`n_c − #(parts of class c)` times. With no factor left, `∏ e! · M(rough degree, smooth degree)`. -/
def msVal (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) : List (Fin 3 → List K) → Multiset SPart → K
  | [], S => (S.map fun x => (x.2.factorial : K)).prod *
      M (S.map fun x => roughPart x.1 x.2).sum (S.map fun x => smoothPart x.1 x.2).sum
  | φ :: rest, S =>
      (S.map fun x => coordSum (fun a => msVal M n rest ((x.1, x.2 + a) ::ₘ S.erase x)) (φ x.1) 0).sum +
        ∑ c : Fin 3, ((n c : K) - (S.countP fun x => x.1 = c : ℕ)) *
          coordSum (fun a => msVal M n rest ((c, a) ::ₘ S)) (φ c) 0

/-- **Definition.** The value of a combination of canonical states continued by `rest`. -/
def symVal (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K)) (L : List (SKey × K)) : K :=
  (L.map fun q => q.2 * msVal M n rest (q.1 : Multiset SPart)).sum

/-- **Definition.** One factor applied to one canonical state with coefficient `κ`: the constant
terms `Σ_c n_c φ(c)₀` keep the state (omitted when they vanish); each positive term `φ(c)_a` merges into a part of class `c`
or opens a new part `(c, a)` with weight `n_c − ℓ(ν_c)`. -/
def symStep (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (p : SKey × K) : List (SKey × K) :=
  (if (n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) + (n 2 : K) * constTerm (φ 2) = 0
    then [] else [(p.1, p.2 * ((n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) +
      (n 2 : K) * constTerm (φ 2)))]) ++
    (((picks p.1).flatMap fun xr => (posTerms (φ xr.1.1)).map fun ac =>
        (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, p.2 * ac.2)) ++
      ([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
        (sIns (c, ac.1) p.1, p.2 * ((n c : K) - (clsCnt p.1 c : K)) * ac.2))

/-- **Definition.** Sort a combination by state and merge equal states. -/
def normalize (L : List (SKey × K)) : List (SKey × K) := normalizeBy keyCmp L

/-- **Definition.** Apply the factors in order, normalizing after each. -/
def symRun (n : Fin 3 → ℕ) : List (Fin 3 → List K) → List (SKey × K) → List (SKey × K)
  | [], L => L
  | φ :: rest, L => symRun n rest (normalize (L.flatMap (symStep n φ)))

/-- **Definition.** The Dirichlet moment of a canonical state: `∏ e! · M(A, B)`. -/
def keyW (M : ℕ → ℕ → K) (k : SKey) : K :=
  (k.map fun x => (x.2.factorial : K)).prod *
    M (k.map fun x => roughPart x.1 x.2).sum (k.map fun x => smoothPart x.1 x.2).sum

/-- **Definition.** `∏ e!` over the parts of a state. -/
def factW (k : SKey) : K := (k.map fun x => (x.2.factorial : K)).prod

/-- **Definition.** Sums of adjacent pairs. -/
def pairSums : List K → List K
  | a :: b :: rest => (a + b) :: pairSums rest
  | l => l

/-- **Definition.** Balanced summation (`fuel` rounds of `pairSums`, then a plain sum). -/
def bsumAux : ℕ → List K → K
  | 0, l => l.sum
  | _ + 1, [] => 0
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => bsumAux fuel (pairSums (a :: b :: rest))

/-- **Definition.** Balanced summation of a list (equal to `List.sum`, `bsum_eq`). -/
def bsum (l : List K) : K := bsumAux 64 l

/-- **Definition.** The value of a combination of canonical states. -/
def symFinal (M : ℕ → ℕ → K) (L : List (SKey × K)) : K := bsum (L.map fun p => p.2 * keyW M p.1)

/-- **Definition.** The symmetric-function evaluation of a product of class-dependent power sums
(the same value as `placeVal M n 0 Fin.elim0 Fin.elim0`, `symPlaceVal_eq`). -/
def symPlaceVal (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) : K :=
  symFinal M (symRun n φs [([], 1)])

/-! ### The transition to monomial symmetric functions and the Dirichlet moment -/

/-- **Definition.** The class power sum `p_{c,a}` as a factor: `y^a` on class `c`, zero elsewhere. -/
def psFactor (c : Fin 3) (a : ℕ) : Fin 3 → List K :=
  fun c' => if c' = c then List.replicate a 0 ++ [1] else []

/-- **Definition.** One factor in the augmented monomial basis without the index-count weight:
`p_{c,a} · m̃_ν = Σ_j m̃_{ν + a e_j} + m̃_{ν ∪ (a)}` (and the constant terms `Σ_c n_c φ(c)₀`). -/
def symStep1 (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (p : SKey × K) : List (SKey × K) :=
  (if (n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) + (n 2 : K) * constTerm (φ 2) = 0
    then [] else [(p.1, p.2 * ((n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) +
      (n 2 : K) * constTerm (φ 2)))]) ++
    (((picks p.1).flatMap fun xr => (posTerms (φ xr.1.1)).map fun ac =>
        (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, p.2 * ac.2)) ++
      ([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
        (sIns (c, ac.1) p.1, p.2 * ac.2))

/-- **Definition.** The factors applied in the augmented monomial basis (`symStep1`). -/
def symRun1 (n : Fin 3 → ℕ) : List (Fin 3 → List K) → List (SKey × K) → List (SKey × K)
  | [], L => L
  | φ :: rest, L => symRun1 n rest (normalize (L.flatMap (symStep1 n φ)))

/-- **Definition (transition).** `p_α = Σ_ν R_{α,ν} m̃_ν` for a product of class power sums
`α = [(c₁, a₁), …]`, as the list of canonical `ν` with coefficients `R_{α,ν}` (independent of
`n` when every `aⱼ ≥ 1`, `symRun1_indep`). -/
def psTrans (n : Fin 3 → ℕ) (α : List SPart) : List (SKey × K) :=
  symRun1 n (α.map fun x => psFactor x.1 x.2) [([], 1)]

/-- **Definition.** The number of index choices of `∏_c m̃_{ν_c}`: `∏_c (n_c)_{ℓ(ν_c)}`. -/
def fallW (n : Fin 3 → ℕ) (k : SKey) : K :=
  ((n 0).descFactorial (clsCnt k 0) : K) * ((n 1).descFactorial (clsCnt k 1) : K) *
    ((n 2).descFactorial (clsCnt k 2) : K)

/-- **Definition.** Scale a coefficient by the number of index choices of its state. -/
def scaleQ (n : Fin 3 → ℕ) (q : SKey × K) : SKey × K := (q.1, q.2 * fallW n q.1)

/-- **Definition (Dirichlet moment of `m̃_ν`).** `∏_c (n_c)_{ℓ(ν_c)} · ∏ νᵢ! · M(A, B)`; for `m_ν`
divide by `∏_v mult_v(ν)!`, i.e. `#monomials(m_ν) · ∏ νᵢ! · M(A, B)`. -/
def monoMoment (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (k : SKey) : K := fallW n k * keyW M k

/-- **Definition.** V2i's piece value with the symmetric-function evaluator. -/
def genPieceSym (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) : K :=
  ((innerTerms (K := K) a₁ l₁).map fun t₁ => ((innerTerms (K := K) a₂ l₂).map fun t₂ =>
    t₁.2.2.2 * t₂.2.2.2 *
      symPlaceVal (fun A B => Mo A B (t₁.2.1 + t₂.2.1) (t₁.2.2.1 + t₂.2.2.1)) (clsCount N r k)
        ((t₁.1 ++ t₂.1).map fun q c => lpShiftPow (clsShift g c) q)).sum).sum

/-- **Definition.** V2i's entry value with the symmetric-function evaluator. -/
def genEntrySym (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    K :=
  (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
    ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
      genPieceSym N r k g (fun A B m n => pieceMn N r k A B g L τ C m n) a₁ l₁ a₂ l₂

/-! ### Moment-coefficient tables -/

/-- **Definition.** The rough degree of a state. -/
def keyA (k : SKey) : ℕ := (k.map fun x => roughPart x.1 x.2).sum

/-- **Definition.** The smooth degree of a state. -/
def keyB (k : SKey) : ℕ := (k.map fun x => smoothPart x.1 x.2).sum

/-- **Definition.** The moment-coefficient table of one generator pair on a piece: every final
state of every inner-term pair contributes `c₁ c₂ κ ∏ e!` to the key
`(rough degree, smooth degree, power of U, power of L − S)`; equal keys are merged. All
coefficients of a piece come from one evaluation (`genPieceWith_eq_table`). -/
def genTable (N r k : ℕ) (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) : List (MKey × K) :=
  normalizeBy mkeyCmp ((innerTerms (K := K) a₁ l₁).flatMap fun t₁ =>
    (innerTerms (K := K) a₂ l₂).flatMap fun t₂ =>
      (symRun (clsCount N r k) ((t₁.1 ++ t₂.1).map fun q c => lpShiftPow (clsShift g c) q)
        [([], 1)]).map fun q =>
          ((keyA q.1, keyB q.1, t₁.2.1 + t₂.2.1, t₁.2.2.1 + t₂.2.2.1),
            t₁.2.2.2 * t₂.2.2.2 * q.2 * factW q.1))

/-- **Definition.** The table of a weighted list of generator pairs (the shape of
`J_T(P⋆) = Σ cᵢ cⱼ J_T[Gᵢ, Gⱼ]`). -/
def aggTable (N r k : ℕ) (g : K) (ws : List (WPair K)) : List (MKey × K) :=
  normalizeBy mkeyCmp (ws.flatMap fun w =>
    (genTable N r k g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).map fun p => (p.1, w.1 * p.2))

/-- **Definition.** A table evaluated against a moment oracle. -/
def tableVal (T : List (MKey × K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) : K :=
  (T.map fun p => p.2 * Mo p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2).sum

end Formula

/-! ### Data of the small certified examples -/

/-- **Definition (example data).** Class sizes `n = (3, 2, 4)`. -/
def demoN : Fin 3 → ℕ := fun c => if c = 0 then 3 else if c = 1 then 2 else 4

/-- **Definition (example data).** A rational moment oracle `M(A, B) = 1 / ((A+1)(B+2) + AB + 3)`. -/
def demoM : ℕ → ℕ → ℚ := fun A B => 1 / (((A : ℚ) + 1) * ((B : ℚ) + 2) + (A : ℚ) * (B : ℚ) + 3)

/-- **Definition (example data).** Shifted power sums `P̂_q(y + s)` with class shifts
`(3/10, 3/10, 0)`, one factor per entry of `qs`. -/
def demoF (qs : List ℕ) : List (Fin 3 → List ℚ) :=
  qs.map fun q c => lpShiftPow (clsShift (3 / 10 : ℚ) c) q

end BGP212.V2e
