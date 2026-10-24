/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymTrie

/-! # V2n: direct moment-profile transitions (definitions)

Track B. The proofs are in `Solution/SymProfile.lean`. V2i–V2m are unchanged.

**The question.** V2ℓ's moment profile `abProfile L` keeps, for each pair `(A, B)` of rough and
smooth degrees, only `Σ κ ∏ e!` over the states of `L`. Multiplying by a factor `φ` sends a part
`(c, e)` to `(c, e + a)`, which multiplies `∏ e!` by `(e + a)! / e!`, a weight that depends on the
individual exponent `e`; a new part `(c, a)` is weighted by `n_c − ℓ_c`, which depends on the number
of parts of class `c`. The profile forgets both, and the profile of the child is not a function of
the profile of the parent (`profile_insufficient`, `classProfile_insufficient`, Lean-checked
counterexamples).

**Marked profiles.** For a state `k` (a list of parts) let `dtup t k` be the ordered `t`-tuples of
distinct parts (positions) of `k`. The marked profile of order `≤ T` of a combination `L` is

  `markProfile T L = Σ_{(k, κ) ∈ L} Σ_{t ≤ T} Σ_{u ∈ dtup t k} ((A k, B k, u), κ ∏ e!)`,

merged by key; order `0` is the moment profile. One factor `φ` maps the marked profile of order
`≤ T + 1` of `L` to the marked profile of order `≤ T` of its child (`markProfile_step`), entry by
entry (`markTerms`), without forming the child's states: a marked part absorbs `a` (weight
`(e + a)! / e!`, the mark moves to `(c, e + a)` or is released), a new part opens unmarked or marked
(weight `n_c − #marks of class c`), and the unmarked parts of class `c` that `n_c − ℓ_c` subtracts
are exactly the marks of the next order (`− a!` terms). Each order consumes one order of marks, so a
node with marked profile of order `T` serves every descendant up to `T` levels below it.

* `dtup`, `tupsLe`, `insAt` — tuples of distinct parts, of length at most `T`, insertion of a mark;
* `markCmp`, `markProfile`, `constSum`, `markTerms`, `markStep` — the marked profile and one
  direct transition;
* `MarkOK n g Q T P` — `P` is the marked profile of order `≤ T` of some combination reached from the
  empty state by certified steps for the factors `P̂_q`, `q ∈ Q` (value equality for every test
  function on keys);
* `markToProf` — the moment profile of an order-0 marked profile;
* `decMEntry`, `decMark` — compact certificate data;
* `classProfile` — the moment profile refined by the number of parts of each class (also
  insufficient). -/

namespace BGP212.V2e

/-- A marked key: rough degree, smooth degree, marked parts. -/
abbrev MarkKey := ℕ × ℕ × List SPart

/-- **Definition.** The ordered `t`-tuples of distinct entries (positions) of a list. -/
def dtup {α : Type*} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | t + 1, l => (picks l).flatMap fun xr => (dtup t xr.2).map (xr.1 :: ·)

/-- **Definition.** The tuples of distinct entries of length at most `T`. -/
def tupsLe {α : Type*} (T : ℕ) (l : List α) : List (List α) :=
  (List.range (T + 1)).flatMap fun t => dtup t l

/-- **Definition.** Insert `y` at position `i` (at the end if `i` exceeds the length). -/
def insAt {α : Type*} : ℕ → α → List α → List α
  | 0, y, l => y :: l
  | _ + 1, y, [] => [y]
  | i + 1, y, x :: l => x :: insAt i y l

/-- **Definition.** Comparison of marked keys: degrees, then the marks (`keyCmp`). -/
def markCmp (s t : MarkKey) : Ordering :=
  if s.1 < t.1 then .lt else if t.1 < s.1 then .gt else
  if s.2.1 < t.2.1 then .lt else if t.2.1 < s.2.1 then .gt else keyCmp s.2.2 t.2.2

/-- **Definition.** Lexicographic comparison of triples of natural numbers. -/
def nat3Cmp (s t : ℕ × ℕ × ℕ) : Ordering :=
  if s.1 < t.1 then .lt else if t.1 < s.1 then .gt else
  if s.2.1 < t.2.1 then .lt else if t.2.1 < s.2.1 then .gt else
  if s.2.2 < t.2.2 then .lt else if t.2.2 < s.2.2 then .gt else .eq

section Marked

variable {K : Type*} [Field K] [LinearOrder K]

/-- **Definition (marked profile).** For every state `(k, κ)` of `L`, every `t ≤ T` and every
ordered `t`-tuple `u` of distinct parts of `k`, the entry `((keyA k, keyB k, u), κ ∏ e!)`; merged by
key. Order `0` (`u = []`) is the moment profile `abProfile L`. -/
def markProfile (T : ℕ) (L : List (SKey × K)) : List (MarkKey × K) :=
  normalizeBy markCmp (L.flatMap fun q => (tupsLe T q.1).map fun u =>
    ((keyA q.1, keyB q.1, u), q.2 * factW q.1))

/-- **Definition.** The constant term `Σ_c n_c φ(c)₀` of a factor. -/
def constSum (n : Fin 3 → ℕ) (φ : Fin 3 → List K) : K :=
  (n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) + (n 2 : K) * constTerm (φ 2)

/-- **Definition (one direct transition, per marked key).** The child keys and coefficients
(per unit of the parent coefficient) of a marked key `(A, B, u)` of order `m = |u|` under the
factor `φ`, keeping child orders `≤ T`:
* the constant terms keep the key (order `m`);
* if `u = x :: w` with `x = (c, e)`, for each `φ(c)_a ≠ 0`, `a ≥ 1`: the marked part absorbs `a`
  and is released, with weight `(e + a)!/e! − a!` (order `m − 1`), or stays marked at any of `m`
  positions of `w`, as `(c, e + a)` with weight `(e + a)!/e!` or, for the subtracted opening, as
  `(c, a)` with weight `− a!` (order `m`);
* for each class `c` and `φ(c)_a ≠ 0`, `a ≥ 1`: a new part `(c, a)` opens with weight
  `(n_c − #marks of class c in u) · a!`, unmarked (order `m`) or marked at any of `m + 1`
  positions (order `m + 1`). -/
def markTerms (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (key : MarkKey) : List (MarkKey × K) :=
  (if key.2.2.length ≤ T then [(key, constSum n φ)] else []) ++
  ((match key.2.2 with
    | [] => []
    | x :: w => (posTerms (φ x.1)).flatMap fun ac =>
        ((key.1 + roughPart x.1 ac.1, key.2.1 + smoothPart x.1 ac.1, w),
          ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) - (ac.1.factorial : ℕ) : K)) ::
        (if w.length + 1 ≤ T then (List.range (w.length + 1)).flatMap fun i =>
          [((key.1 + roughPart x.1 ac.1, key.2.1 + smoothPart x.1 ac.1, insAt i (x.1, x.2 + ac.1) w),
              ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K)),
            ((key.1 + roughPart x.1 ac.1, key.2.1 + smoothPart x.1 ac.1, insAt i (x.1, ac.1) w),
              -(ac.2 * (ac.1.factorial : K)))]
        else [])) ++
  ([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).flatMap fun ac =>
    (if key.2.2.length ≤ T then
      [((key.1 + roughPart c ac.1, key.2.1 + smoothPart c ac.1, key.2.2),
        ((n c : K) - (clsCnt key.2.2 c : K)) * ac.2 * (ac.1.factorial : K))] else []) ++
    (if key.2.2.length + 1 ≤ T then (List.range (key.2.2.length + 1)).map fun i =>
      ((key.1 + roughPart c ac.1, key.2.1 + smoothPart c ac.1, insAt i (c, ac.1) key.2.2),
        ((n c : K) - (clsCnt key.2.2 c : K)) * ac.2 * (ac.1.factorial : K)) else []))

/-- **Definition (direct transition).** Apply `markTerms` to every entry of a marked profile and
merge by key. No state of the child is formed. -/
def markStep (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (P : List (MarkKey × K)) :
    List (MarkKey × K) :=
  normalizeBy markCmp (P.flatMap fun p => (markTerms n φ T p.1).map fun kc => (kc.1, p.2 * kc.2))

/-- **Definition.** `P` is a marked profile of order `≤ T` for the factors `P̂_q`, `q ∈ Q`: some
combination `L` reached from the empty state by certified steps has, for every test function `F`
on marked keys, `Σ_P c · F = Σ_{markProfile T L} c · F`. -/
def MarkOK (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T : ℕ) (P : List (MarkKey × K)) : Prop :=
  ∃ L : List (SKey × K), ChainCert n (psFactors g Q) [([], 1)] L ∧
    ∀ F : MarkKey → K, (P.map fun e => e.2 * F e.1).sum =
      ((markProfile T L).map fun e => e.2 * F e.1).sum

/-- **Definition.** The class-count profile: `Σ κ ∏ e! · ℓ_c` collected by `(A, B, c)` (the moment
profile refined by the number of parts of each class). -/
def classProfile (L : List (SKey × K)) : List ((ℕ × ℕ × ℕ) × K) :=
  normalizeBy nat3Cmp (L.flatMap fun q => ([0, 1, 2] : List (Fin 3)).map fun c =>
      ((keyA q.1, keyB q.1, c.val), q.2 * factW q.1 * (clsCnt q.1 c : K)))

/-- **Definition.** The moment profile of a marked profile (marks dropped, merged by `(A, B)`). -/
def markToProf (P : List (MarkKey × K)) : List ((ℕ × ℕ) × K) :=
  normalizeBy abCmp (P.map fun e => ((e.1.1, e.1.2.1), e.2))

end Marked

/-- **Definition.** A marked entry from `[A, B, sign, numerator, denominator, c₁, e₁, …]` (compact
certificate data, as V2ℓ's `decComb`). -/
def decMEntry : List ℕ → MarkKey × ℚ
  | A :: B :: s :: a :: b :: rest => ((A, B, decParts rest), (if s = 0 then (a : ℚ) else -(a : ℚ)) / (b : ℚ))
  | _ => ((0, 0, []), 0)

/-- **Definition.** A marked profile from its compact encoding. -/
def decMark (raw : List (List ℕ)) : List (MarkKey × ℚ) := raw.map decMEntry

end BGP212.V2e
