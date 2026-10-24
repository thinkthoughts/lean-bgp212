/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymProfile
import Solution.SymTrie

/-! # V2n: direct moment-profile transitions (proofs)

* §1 tuples of distinct parts on multisets: the list form agrees with the multiset form
  (`dtup_sum`), a new part splits the tuples (`dtupM_cons_sum`), and the parts outside a tuple are
  counted by the next order (`dtupM_compl`);
* §2 the marked profile of a child is the direct transition of the marked profile of the parent
  (`markProfile_step`), for arbitrary class sizes, factors, orders and test functions;
* §3 certificates: `MarkOK` from stored states (with chunks), along direct transitions (with
  chunks and merges), to V2m's `ProfCert`;
* §4 the profile alone is insufficient (`profile_insufficient`, `classProfile_insufficient`). -/

namespace BGP212.V2e

/-! ## §1 Tuples of distinct parts -/

section Tuples

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- The ordered `t`-tuples of distinct elements (positions) of a multiset. -/
def dtupM : ℕ → Multiset α → Multiset (List α)
  | 0, _ => {[]}
  | t + 1, S => S.bind fun x => (dtupM t (S.erase x)).map (x :: ·)

theorem dtupM_succ_sum (t : ℕ) (S : Multiset α) (G : List α → K) :
    ((dtupM (t + 1) S).map G).sum = (S.map fun x => ((dtupM t (S.erase x)).map fun w => G (x :: w)).sum).sum := by
  rw [dtupM, Multiset.map_bind, Multiset.sum_bind]
  simp only [Multiset.map_map, Function.comp_def]

theorem dtupM_length : ∀ (t : ℕ) (S : Multiset α), ∀ u ∈ dtupM t S, u.length = t := by
  intro t
  induction t with
  | zero => intro S u hu; simp [dtupM] at hu; simp [hu]
  | succ t ih =>
    intro S u hu
    simp only [dtupM, Multiset.mem_bind, Multiset.mem_map] at hu
    obtain ⟨x, _, w, hw, rfl⟩ := hu
    simp [ih _ w hw]

theorem dtup_sum : ∀ (t : ℕ) (l : List α) (G : List α → K),
    ((dtup t l).map G).sum = ((dtupM t (l : Multiset α)).map G).sum := by
  intro t
  induction t with
  | zero => intro l G; simp [dtup, dtupM]
  | succ t ih =>
    intro l G
    rw [dtup, flatMap_map_sum, dtupM_succ_sum]
    have h := picks_sum l (fun x (m : Multiset α) => ((dtupM t m).map fun w => G (x :: w)).sum)
    rw [h]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    rw [List.map_map]
    exact ih p.2 _

theorem msum_finset {β ι : Type*} (S : Multiset β) (s : Finset ι) (f : ι → β → K) :
    (S.map fun u => ∑ i ∈ s, f i u).sum = ∑ i ∈ s, (S.map (f i)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons y S ih => simp [ih, Finset.sum_add_distrib]

theorem msum_list {β γ : Type*} (S : Multiset β) (l : List γ) (f : γ → β → K) :
    (S.map fun u => (l.map fun a => f a u).sum).sum = (l.map fun a => (S.map (f a)).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Multiset.sum_map_add, ih]

/-- **A new element splits the tuples**: tuples avoiding it, or containing it at one of `t`
positions. -/
theorem dtupM_cons_sum (y : α) : ∀ (t : ℕ) (S : Multiset α) (G : List α → K),
    ((dtupM t (y ::ₘ S)).map G).sum = ((dtupM t S).map G).sum +
      ∑ i ∈ Finset.range t, ((dtupM (t - 1) S).map fun w => G (insAt i y w)).sum := by
  intro t
  induction t with
  | zero => intro S G; simp [dtupM]
  | succ t ih =>
    intro S G
    rw [dtupM_succ_sum, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    have h1 : (S.map fun x => ((dtupM t ((y ::ₘ S).erase x)).map fun w => G (x :: w)).sum) =
        (S.map fun x => ((dtupM t (y ::ₘ S.erase x)).map fun w => G (x :: w)).sum) :=
      Multiset.map_congr rfl fun x hx => by rw [Multiset.erase_cons_tail_of_mem hx]
    rw [h1]
    simp only [ih, Multiset.sum_map_add, msum_finset]
    rw [← dtupM_succ_sum, Finset.sum_range_succ', Nat.add_sub_cancel]
    simp only [insAt]
    cases t with
    | zero => simp [add_comm]
    | succ t =>
      have h2 : ∀ i ∈ Finset.range (t + 1), (S.map fun x => ((dtupM (t + 1 - 1) (S.erase x)).map fun w =>
          G (x :: insAt i y w)).sum).sum = ((dtupM (t + 1) S).map fun w => G (insAt (i + 1) y w)).sum := by
        intro i _
        rw [dtupM_succ_sum, Nat.add_sub_cancel]
        rfl
      rw [Finset.sum_congr rfl h2]
      ring

/-- Ordered pairs of distinct positions, in either order. -/
theorem erase_swap_sum (g : α → α → K) : ∀ S : Multiset α,
    (S.map fun y => ((S.erase y).map fun x => g y x).sum).sum =
      (S.map fun x => ((S.erase x).map fun y => g y x).sum).sum := by
  intro S
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, Multiset.map_cons,
      Multiset.sum_cons, Multiset.erase_cons_head]
    have h1 : (S.map fun y => (((z ::ₘ S).erase y).map fun x => g y x).sum) =
        (S.map fun y => g y z + ((S.erase y).map fun x => g y x).sum) :=
      Multiset.map_congr rfl fun y hy => by
        rw [Multiset.erase_cons_tail_of_mem hy, Multiset.map_cons, Multiset.sum_cons]
    have h2 : (S.map fun x => (((z ::ₘ S).erase x).map fun y => g y x).sum) =
        (S.map fun x => g z x + ((S.erase x).map fun y => g y x).sum) :=
      Multiset.map_congr rfl fun x hx => by
        rw [Multiset.erase_cons_tail_of_mem hx, Multiset.map_cons, Multiset.sum_cons]
    rw [h1, h2, Multiset.sum_map_add, Multiset.sum_map_add, ih]
    ring

/-- **Parts outside a tuple** are counted by the tuples of the next order:
`Σ_{y} h(y) · #(tuples of S ∖ y) = Σ_{tuples u of S} (Σ_S h − Σ_u h)`. -/
theorem dtupM_compl (h : α → K) : ∀ (t : ℕ) (S : Multiset α) (G : List α → K),
    (S.map fun y => h y * ((dtupM t (S.erase y)).map G).sum).sum =
      ((dtupM t S).map fun u => ((S.map h).sum - (u.map h).sum) * G u).sum := by
  intro t
  induction t with
  | zero => intro S G; simp [dtupM, Multiset.sum_map_mul_right]
  | succ t ih =>
    intro S G
    have e1 : (S.map fun y => h y * ((dtupM (t + 1) (S.erase y)).map G).sum) =
        (S.map fun y => ((S.erase y).map fun x =>
          h y * ((dtupM t ((S.erase x).erase y)).map fun w => G (x :: w)).sum).sum) :=
      Multiset.map_congr rfl fun y _ => by
        rw [dtupM_succ_sum, Multiset.sum_map_mul_left]
        exact congrArg (fun s => h y * s) (congrArg Multiset.sum
          (Multiset.map_congr rfl fun x _ => by rw [Multiset.erase_comm]))
    rw [e1, erase_swap_sum (fun y x => h y * ((dtupM t ((S.erase x).erase y)).map fun w => G (x :: w)).sum)]
    rw [dtupM_succ_sum]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [ih (S.erase x) (fun w => G (x :: w))]
    have hS : (S.map h).sum = h x + ((S.erase x).map h).sum := by
      conv_lhs => rw [← Multiset.cons_erase hx]
      rw [Multiset.map_cons, Multiset.sum_cons]
    refine congrArg _ (Multiset.map_congr rfl fun w _ => ?_)
    rw [hS, List.map_cons, List.sum_cons]
    ring

end Tuples

/-! ## §2 The direct transition -/

section Step

variable {K : Type*} [Field K] [LinearOrder K]

/-- The sum of `G` over the `t`-tuples of distinct parts of `S`. -/
def dsum (t : ℕ) (S : Multiset SPart) (G : List SPart → K) : K := ((dtupM t S).map G).sum

omit [LinearOrder K] in
theorem dsum_add (t : ℕ) (S : Multiset SPart) (G H : List SPart → K) :
    dsum t S (fun u => G u + H u) = dsum t S G + dsum t S H := by
  simp [dsum, Multiset.sum_map_add]

omit [LinearOrder K] in
theorem dsum_sub (t : ℕ) (S : Multiset SPart) (G H : List SPart → K) :
    dsum t S (fun u => G u - H u) = dsum t S G - dsum t S H := by
  simp [dsum, Multiset.sum_map_sub]

omit [LinearOrder K] in
theorem dsum_mul (t : ℕ) (S : Multiset SPart) (c : K) (G : List SPart → K) :
    dsum t S (fun u => c * G u) = c * dsum t S G := by
  simp [dsum, Multiset.sum_map_mul_left]

omit [LinearOrder K] in
theorem dsum_finset {ι : Type*} (t : ℕ) (S : Multiset SPart) (s : Finset ι) (f : ι → List SPart → K) :
    dsum t S (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, dsum t S (f i) := msum_finset _ _ _

omit [LinearOrder K] in
theorem dsum_list {γ : Type*} (t : ℕ) (S : Multiset SPart) (l : List γ) (f : γ → List SPart → K) :
    dsum t S (fun u => (l.map fun a => f a u).sum) = (l.map fun a => dsum t S (f a)).sum := msum_list _ _ _

omit [LinearOrder K] in
theorem dsum_congr (t : ℕ) (S : Multiset SPart) (G H : List SPart → K)
    (h : ∀ u, u.length = t → G u = H u) : dsum t S G = dsum t S H := by
  unfold dsum
  exact congrArg _ (Multiset.map_congr rfl fun u hu => h u (dtupM_length t S u hu))

omit [LinearOrder K] in
theorem dsum_succ (t : ℕ) (S : Multiset SPart) (G : List SPart → K) :
    dsum (t + 1) S G = (S.map fun x => dsum t (S.erase x) fun w => G (x :: w)).sum :=
  dtupM_succ_sum t S G

omit [LinearOrder K] in
theorem dsum_zero (S : Multiset SPart) (G : List SPart → K) : dsum 0 S G = G [] := by
  simp [dsum, dtupM]

omit [LinearOrder K] in
theorem dsum_cons (y : SPart) (t : ℕ) (S : Multiset SPart) (G : List SPart → K) :
    dsum t (y ::ₘ S) G = dsum t S G + ∑ i ∈ Finset.range t, dsum (t - 1) S fun w => G (insAt i y w) :=
  dtupM_cons_sum y t S G

/-- The indicator of class `c`. -/
def clsInd (c : Fin 3) (x : SPart) : K := if x.1 = c then 1 else 0

omit [LinearOrder K] in
theorem clsInd_sum (u : List SPart) (c : Fin 3) : (u.map (clsInd (K := K) c)).sum = (clsCnt u c : K) := by
  induction u with
  | nil => simp [clsCnt]
  | cons x u ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [clsCnt, List.countP_cons]
    by_cases hx : x.1 = c
    · simp [clsInd, hx]
      ring
    · have : (x.1.val == c.val) = false := by simp [Fin.val_inj, hx]
      simp [clsInd, hx, this]

omit [LinearOrder K] in
theorem clsInd_sel (x : SPart) (H : Fin 3 → K) : ∑ c : Fin 3, clsInd c x * H c = H x.1 := by
  simp [clsInd]

omit [LinearOrder K] in
/-- **Complement counting** for one class. -/
theorem dsum_compl (c : Fin 3) (t : ℕ) (S : Multiset SPart) (G : List SPart → K) :
    (S.map fun y => clsInd c y * dsum t (S.erase y) G).sum =
      dsum t S fun u => ((S.map (clsInd c)).sum - (u.map (clsInd c)).sum) * G u :=
  dtupM_compl (clsInd c) t S G

/-- Rough degree, smooth degree and `∏ e!` of a multiset of parts. -/
def aM (S : Multiset SPart) : ℕ := (S.map fun x => roughPart x.1 x.2).sum
def bM (S : Multiset SPart) : ℕ := (S.map fun x => smoothPart x.1 x.2).sum
def wM (S : Multiset SPart) : K := (S.map fun x => (x.2.factorial : K)).prod

theorem keyA_m (k : SKey) : keyA k = aM (k : Multiset SPart) := by
  simp [keyA, aM]

theorem keyB_m (k : SKey) : keyB k = bM (k : Multiset SPart) := by
  simp [keyB, bM]

omit [LinearOrder K] in
theorem factW_m (k : SKey) : factW (K := K) k = wM (k : Multiset SPart) := by
  simp [factW, wM]

theorem roughPart_add (c : Fin 3) (e a : ℕ) : roughPart c (e + a) = roughPart c e + roughPart c a := by
  unfold roughPart; split_ifs <;> simp

theorem smoothPart_add (c : Fin 3) (e a : ℕ) : smoothPart c (e + a) = smoothPart c e + smoothPart c a := by
  unfold smoothPart; split_ifs <;> simp

/-- The value of one state against a test function on marked keys, orders `≤ T`. -/
def markVal (T : ℕ) (F : MarkKey → K) (S : Multiset SPart) (κ : K) : K :=
  κ * wM S * ∑ t ∈ Finset.range (T + 1), dsum t S fun u => F (aM S, bM S, u)

theorem markCmp_eq (s t : MarkKey) (h : markCmp s t = .eq) : s = t := by
  unfold markCmp at h
  split_ifs at h with h1 h2 h3 h4
  obtain ⟨a, b, u⟩ := s
  obtain ⟨a', b', u'⟩ := t
  simp only at h1 h2 h3 h4 h
  obtain rfl : u = u' := keyCmp_eq u u' h
  obtain rfl : a = a' := by omega
  obtain rfl : b = b' := by omega
  rfl

omit [LinearOrder K] in
theorem tupsLe_sum (T : ℕ) (l : List SPart) (G : List SPart → K) :
    ((tupsLe T l).map G).sum = ∑ t ∈ Finset.range (T + 1), dsum t (l : Multiset SPart) G := by
  rw [tupsLe, flatMap_map_sum, list_range_sum]
  exact Finset.sum_congr rfl fun t _ => dtup_sum t l G

omit [LinearOrder K] in
/-- The value of a marked profile is the sum of the values of the states. -/
theorem markProfile_val (T : ℕ) (L : List (SKey × K)) (F : MarkKey → K) :
    ((markProfile T L).map fun e => e.2 * F e.1).sum =
      (L.map fun q => markVal T F (q.1 : Multiset SPart) q.2).sum := by
  have h := normalizeBy_val markCmp markCmp_eq (fun s : MarkKey => F s)
    (L.flatMap fun q => (tupsLe T q.1).map fun u => ((keyA q.1, keyB q.1, u), q.2 * factW q.1))
  unfold valBy at h
  rw [markProfile, h, flatMap_map_sum]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  rw [List.map_map]
  have : ((tupsLe T q.1).map ((fun e : MarkKey × K => e.2 * F e.1) ∘ fun u =>
      ((keyA q.1, keyB q.1, u), q.2 * factW q.1))) =
      (tupsLe T q.1).map fun u => q.2 * factW q.1 * F (keyA q.1, keyB q.1, u) := rfl
  rw [this, List.sum_map_mul_left, tupsLe_sum, markVal, keyA_m, keyB_m, factW_m]

omit [LinearOrder K] in
theorem lsum_finset {γ ι : Type*} (l : List γ) (s : Finset ι) (f : γ → ι → K) :
    (l.map fun a => ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

omit [LinearOrder K] in
theorem lsum_ite {γ : Type*} (l : List γ) (p : Prop) [Decidable p] (f : γ → K) :
    (l.map fun a => if p then f a else 0).sum = if p then (l.map f).sum else 0 := by
  split_ifs <;> simp

omit [LinearOrder K] in
theorem lsum_sub {γ : Type*} (l : List γ) (f g : γ → K) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-- The test function at a key shifted by `a` in class `c`. -/
def fca (F : MarkKey → K) (A B : ℕ) (c : Fin 3) (a : ℕ) (u : List SPart) : K :=
  F (A + roughPart c a, B + smoothPart c a, u)

/-- New part `(c, a)` opened, unmarked: `Σ_a φ(c)_a a! F(shifted, u)`. -/
def hc (φ : Fin 3 → List K) (F : MarkKey → K) (A B : ℕ) (c : Fin 3) (u : List SPart) : K :=
  ((posTerms (φ c)).map fun ac => ac.2 * (ac.1.factorial : K) * fca F A B c ac.1 u).sum

/-- New part `(c, a)` opened, marked at position `i`. -/
def jc (φ : Fin 3 → List K) (F : MarkKey → K) (A B : ℕ) (c : Fin 3) (i : ℕ) (u : List SPart) : K :=
  ((posTerms (φ c)).map fun ac => ac.2 * (ac.1.factorial : K) * fca F A B c ac.1 (insAt i (c, ac.1) u)).sum

/-- The part `x` absorbs `a`, released. -/
def axT (φ : Fin 3 → List K) (F : MarkKey → K) (A B : ℕ) (x : SPart) (u : List SPart) : K :=
  ((posTerms (φ x.1)).map fun ac =>
    ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) * fca F A B x.1 ac.1 u).sum

/-- The part `x` absorbs `a`, kept marked at position `i`. -/
def bxT (φ : Fin 3 → List K) (F : MarkKey → K) (A B : ℕ) (x : SPart) (i : ℕ) (u : List SPart) : K :=
  ((posTerms (φ x.1)).map fun ac =>
    ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) * fca F A B x.1 ac.1 (insAt i (x.1, x.2 + ac.1) u)).sum

/-- The terms of a marked key whose first mark absorbs. -/
def absT (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (A B : ℕ) : List SPart → K
  | [] => 0
  | x :: w => axT φ F A B x w - hc φ F A B x.1 w +
      if w.length + 1 ≤ T then ∑ i ∈ Finset.range (w.length + 1), (bxT φ F A B x i w - jc φ F A B x.1 i w)
      else 0

/-- The terms of a marked key that open a new part of class `c`. -/
def newT (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (A B : ℕ) (c : Fin 3)
    (u : List SPart) : K :=
  ((n c : K) - (clsCnt u c : K)) * ((if u.length ≤ T then hc φ F A B c u else 0) +
    if u.length + 1 ≤ T then ∑ i ∈ Finset.range (u.length + 1), jc φ F A B c i u else 0)

/-- `markTerms` as explicit sums. -/
theorem markTerms_val (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (A B : ℕ)
    (u : List SPart) :
    ((markTerms n φ T (A, B, u)).map fun kc => kc.2 * F kc.1).sum =
      (if u.length ≤ T then constSum n φ * F (A, B, u) else 0) + absT φ T F A B u +
        ∑ c : Fin 3, newT n φ T F A B c u := by
  rw [markTerms, List.map_append, List.sum_append, List.map_append, List.sum_append, add_assoc]
  dsimp only
  congr 1
  · split_ifs <;> simp
  congr 1
  · cases u with
    | nil => simp [absT]
    | cons x w =>
      simp only [absT, flatMap_map_sum, List.map_cons, List.sum_cons]
      rw [List.sum_map_add]
      have e1 : ∀ ac : ℕ × K, (List.map (fun kc : MarkKey × K => kc.2 * F kc.1) (if w.length + 1 ≤ T then
          (List.range (w.length + 1)).flatMap fun i =>
            [((A + roughPart x.1 ac.1, B + smoothPart x.1 ac.1, insAt i (x.1, x.2 + ac.1) w),
                ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K)),
              ((A + roughPart x.1 ac.1, B + smoothPart x.1 ac.1, insAt i (x.1, ac.1) w),
                -(ac.2 * (ac.1.factorial : K)))] else [])).sum =
          if w.length + 1 ≤ T then ∑ i ∈ Finset.range (w.length + 1),
            (ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) *
                fca F A B x.1 ac.1 (insAt i (x.1, x.2 + ac.1) w) -
              ac.2 * (ac.1.factorial : K) * fca F A B x.1 ac.1 (insAt i (x.1, ac.1) w)) else 0 := by
        intro ac
        split_ifs
        · rw [flatMap_map_sum, list_range_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [fca]
          ring
        · simp
      simp only [e1, lsum_ite, lsum_finset, lsum_sub]
      simp only [axT, hc, bxT, jc]
      have e2 : ∀ ac : ℕ × K, ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) - (ac.1.factorial : ℕ) : K) *
          F (A + roughPart x.1 ac.1, B + smoothPart x.1 ac.1, w) =
          ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) * fca F A B x.1 ac.1 w -
            ac.2 * (ac.1.factorial : K) * fca F A B x.1 ac.1 w := by
        intro ac; simp only [fca]; ring
      simp only [e2, lsum_sub]
  · rw [flatMap_map_sum, Fin.sum_univ_three]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have e3 : ∀ c : Fin 3, (((posTerms (φ c)).flatMap fun ac =>
        (if u.length ≤ T then
          [((A + roughPart c ac.1, B + smoothPart c ac.1, u),
            ((n c : K) - (clsCnt u c : K)) * ac.2 * (ac.1.factorial : K))] else []) ++
        (if u.length + 1 ≤ T then (List.range (u.length + 1)).map fun i =>
          ((A + roughPart c ac.1, B + smoothPart c ac.1, insAt i (c, ac.1) u),
            ((n c : K) - (clsCnt u c : K)) * ac.2 * (ac.1.factorial : K)) else [])).map
        fun kc => kc.2 * F kc.1).sum = newT n φ T F A B c u := by
      intro c
      rw [flatMap_map_sum, newT]
      simp only [hc, jc]
      simp only [List.map_append, List.sum_append]
      rw [List.sum_map_add]
      have e4 : ∀ ac : ℕ × K, ((if u.length ≤ T then
          [((A + roughPart c ac.1, B + smoothPart c ac.1, u),
            ((n c : K) - (clsCnt u c : K)) * ac.2 * (ac.1.factorial : K))] else []).map
          fun kc : MarkKey × K => kc.2 * F kc.1).sum =
          ((n c : K) - (clsCnt u c : K)) * if u.length ≤ T then ac.2 * (ac.1.factorial : K) * fca F A B c ac.1 u else 0 := by
        intro ac; split_ifs <;> simp [fca]; ring
      have e5 : ∀ ac : ℕ × K, ((if u.length + 1 ≤ T then (List.range (u.length + 1)).map fun i =>
          ((A + roughPart c ac.1, B + smoothPart c ac.1, insAt i (c, ac.1) u),
            ((n c : K) - (clsCnt u c : K)) * ac.2 * (ac.1.factorial : K)) else []).map
          fun kc : MarkKey × K => kc.2 * F kc.1).sum =
          ((n c : K) - (clsCnt u c : K)) * if u.length + 1 ≤ T then
            ∑ i ∈ Finset.range (u.length + 1), ac.2 * (ac.1.factorial : K) * fca F A B c ac.1 (insAt i (c, ac.1) u)
          else 0 := by
        intro ac
        split_ifs
        · rw [List.map_map, list_range_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [fca]; ring
        · simp
      simp only [e4, e5, List.sum_map_mul_left, lsum_ite, lsum_finset]
      ring
    rw [e3 0, e3 1, e3 2, add_assoc]

omit [LinearOrder K] in
/-- Reindexing the marked openings: `Σ_{t ≤ T} Σ_{i < t} g (t − 1) i = Σ_{s ≤ T, s + 1 ≤ T} Σ_{i ≤ s} g s i`. -/
theorem range_reindex (T : ℕ) (g : ℕ → ℕ → K) :
    ∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t, g (t - 1) i =
      ∑ s ∈ Finset.range (T + 1), if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), g s i else 0 := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.add_sub_cancel,
    ite_eq_right_iff, show ¬ T + 1 ≤ T by omega, if_false]
  exact Finset.sum_congr rfl fun s hs => by
    rw [if_pos (by simp at hs; omega)]

omit [LinearOrder K] in
theorem aM_cons (y : SPart) (S : Multiset SPart) : aM (y ::ₘ S) = roughPart y.1 y.2 + aM S := by
  simp [aM]

omit [LinearOrder K] in
theorem bM_cons (y : SPart) (S : Multiset SPart) : bM (y ::ₘ S) = smoothPart y.1 y.2 + bM S := by
  simp [bM]

omit [LinearOrder K] in
theorem wM_cons (y : SPart) (S : Multiset SPart) : wM (K := K) (y ::ₘ S) = (y.2.factorial : K) * wM S := by
  simp [wM]

omit [LinearOrder K] in
theorem desc_fact (e a : ℕ) : (((e + a).factorial : ℕ) : K) = (((e + a).descFactorial a : ℕ) : K) * (e.factorial : K) := by
  rw [← Nat.cast_mul, mul_comm]
  have h := Nat.factorial_mul_descFactorial (show a ≤ e + a by omega)
  rw [Nat.add_sub_cancel] at h
  rw [h]

omit [LinearOrder K] in
/-- The child of an absorption, against a test function. -/
theorem markVal_absorb (T : ℕ) (F : MarkKey → K) (S : Multiset SPart) (x : SPart) (hx : x ∈ S)
    (a : ℕ) (c₀ : K) :
    markVal T F ((x.1, x.2 + a) ::ₘ S.erase x) c₀ =
      c₀ * wM S * (((x.2 + a).descFactorial a : ℕ) : K) *
        ∑ t ∈ Finset.range (T + 1), (dsum t (S.erase x) (fca F (aM S) (bM S) x.1 a) +
          ∑ i ∈ Finset.range t, dsum (t - 1) (S.erase x)
            fun w => fca F (aM S) (bM S) x.1 a (insAt i (x.1, x.2 + a) w)) := by
  have hS : S = x ::ₘ S.erase x := (Multiset.cons_erase hx).symm
  have hA : aM ((x.1, x.2 + a) ::ₘ S.erase x) = aM S + roughPart x.1 a := by
    conv_rhs => rw [hS]
    rw [aM_cons, aM_cons, roughPart_add]; ring
  have hB : bM ((x.1, x.2 + a) ::ₘ S.erase x) = bM S + smoothPart x.1 a := by
    conv_rhs => rw [hS]
    rw [bM_cons, bM_cons, smoothPart_add]; ring
  have hW : wM (K := K) ((x.1, x.2 + a) ::ₘ S.erase x) = (((x.2 + a).descFactorial a : ℕ) : K) * wM S := by
    conv_rhs => rw [hS]
    rw [wM_cons, wM_cons, desc_fact]; ring
  rw [markVal, hA, hB, hW]
  have : ∀ t, dsum t ((x.1, x.2 + a) ::ₘ S.erase x) (fun u => F (aM S + roughPart x.1 a, bM S + smoothPart x.1 a, u)) =
      dsum t (S.erase x) (fca F (aM S) (bM S) x.1 a) +
        ∑ i ∈ Finset.range t, dsum (t - 1) (S.erase x) fun w => fca F (aM S) (bM S) x.1 a (insAt i (x.1, x.2 + a) w) :=
    fun t => dsum_cons _ t _ _
  simp only [this]
  ring

omit [LinearOrder K] in
/-- The child of a new part, against a test function. -/
theorem markVal_open (T : ℕ) (F : MarkKey → K) (S : Multiset SPart) (c : Fin 3) (a : ℕ) (c₀ : K) :
    markVal T F ((c, a) ::ₘ S) c₀ =
      c₀ * wM S * (a.factorial : K) *
        ∑ t ∈ Finset.range (T + 1), (dsum t S (fca F (aM S) (bM S) c a) +
          ∑ i ∈ Finset.range t, dsum (t - 1) S fun w => fca F (aM S) (bM S) c a (insAt i (c, a) w)) := by
  rw [markVal, aM_cons, bM_cons, wM_cons]
  have : ∀ t, dsum t ((c, a) ::ₘ S) (fun u => F (roughPart c a + aM S, smoothPart c a + bM S, u)) =
      dsum t S (fca F (aM S) (bM S) c a) +
        ∑ i ∈ Finset.range t, dsum (t - 1) S fun w => fca F (aM S) (bM S) c a (insAt i (c, a) w) := by
    intro t
    rw [dsum_cons]
    simp only [add_comm (roughPart c a), add_comm (smoothPart c a)]
    rfl
  simp only [this]
  ring


omit [LinearOrder K] in
theorem par_const (T : ℕ) (S : Multiset SPart) (G : List SPart → K) :
    ∑ t ∈ Finset.range (T + 2), dsum t S (fun u => if u.length ≤ T then G u else 0) =
      ∑ t ∈ Finset.range (T + 1), dsum t S G := by
  rw [Finset.sum_range_succ, dsum_congr (T + 1) S _ (fun _ => 0) fun u hu => by simp [hu]]
  simp only [dsum, Multiset.map_const', Multiset.sum_replicate, smul_zero, add_zero]
  exact Finset.sum_congr rfl fun t ht => congrArg _ (Multiset.map_congr rfl fun u hu => by
    rw [dtupM_length t S u hu, if_pos (by simp at ht; omega)])

theorem par_abs (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (A B : ℕ) (S : Multiset SPart) :
    ∑ t ∈ Finset.range (T + 2), dsum t S (absT φ T F A B) =
      ∑ s ∈ Finset.range (T + 1), (S.map fun x => dsum s (S.erase x) fun w =>
        axT φ F A B x w - hc φ F A B x.1 w +
          if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), (bxT φ F A B x i w - jc φ F A B x.1 i w)
          else 0).sum := by
  rw [Finset.sum_range_succ', dsum_zero]
  simp only [absT, add_zero]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dsum_succ]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => dsum_congr _ _ _ _ fun w hw => ?_)
  simp only [absT, hw]

theorem par_new (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (A B : ℕ)
    (S : Multiset SPart) (c : Fin 3) :
    ∑ t ∈ Finset.range (T + 2), dsum t S (newT n φ T F A B c) =
      ∑ t ∈ Finset.range (T + 1), dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * hc φ F A B c u) +
        ∑ t ∈ Finset.range (T + 1), if t + 1 ≤ T then ∑ i ∈ Finset.range (t + 1),
          dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * jc φ F A B c i u) else 0 := by
  rw [Finset.sum_range_succ]
  have h0 : dsum (T + 1) S (newT n φ T F A B c) = 0 := by
    rw [dsum_congr (T + 1) S _ (fun _ => 0) fun u hu => by simp [newT, hu]]
    simp [dsum]
  rw [h0, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ T := by simp at ht; omega
  rw [dsum_congr t S (newT n φ T F A B c) (fun u => ((n c : K) - (clsCnt u c : K)) * hc φ F A B c u +
      if t + 1 ≤ T then ∑ i ∈ Finset.range (t + 1), ((n c : K) - (clsCnt u c : K)) * jc φ F A B c i u
      else 0) fun u hu => by
        simp only [newT, hu, if_pos ht', mul_add]
        split_ifs <;> simp [Finset.mul_sum]]
  rw [dsum_add]
  split_ifs
  · rw [dsum_finset]
  · simp [dsum]

/-- The parent side: the marked profile of order `≤ T + 1` against the transition of `F`. -/
theorem par_val (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K)
    (S : Multiset SPart) (κ : K) :
    markVal (T + 1) (fun key => ((markTerms n φ T key).map fun kc => kc.2 * F kc.1).sum) S κ =
      κ * wM S * (constSum n φ * ∑ t ∈ Finset.range (T + 1), dsum t S (fun u => F (aM S, bM S, u)) +
        ∑ s ∈ Finset.range (T + 1), (S.map fun x => dsum s (S.erase x) fun w =>
          axT φ F (aM S) (bM S) x w - hc φ F (aM S) (bM S) x.1 w +
            if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1),
              (bxT φ F (aM S) (bM S) x i w - jc φ F (aM S) (bM S) x.1 i w) else 0).sum +
        ∑ c : Fin 3, (∑ t ∈ Finset.range (T + 1),
            dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * hc φ F (aM S) (bM S) c u) +
          ∑ t ∈ Finset.range (T + 1), if t + 1 ≤ T then ∑ i ∈ Finset.range (t + 1),
            dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * jc φ F (aM S) (bM S) c i u) else 0)) := by
  rw [markVal]
  congr 1
  have e : ∀ t, dsum t S (fun u => ((markTerms n φ T (aM S, bM S, u)).map fun kc => kc.2 * F kc.1).sum) =
      dsum t S (fun u => if u.length ≤ T then constSum n φ * F (aM S, bM S, u) else 0) +
        dsum t S (absT φ T F (aM S) (bM S)) + ∑ c : Fin 3, dsum t S (newT n φ T F (aM S) (bM S) c) := by
    intro t
    rw [dsum_congr t S _ _ fun u _ => markTerms_val n φ T F (aM S) (bM S) u, dsum_add, dsum_add, dsum_finset]
  rw [show T + 1 + 1 = T + 2 from rfl]
  simp only [e, Finset.sum_add_distrib]
  rw [par_const, par_abs, Finset.sum_comm]
  simp only [par_new]
  rw [Finset.mul_sum]
  simp only [dsum_mul]
  rw [Finset.sum_add_distrib]

/-- The child side, constant terms. -/
theorem child_const (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (k : SKey) (κ : K) :
    (((if (n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) + (n 2 : K) * constTerm (φ 2) = 0
      then [] else [(k, κ * ((n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) +
        (n 2 : K) * constTerm (φ 2)))]) : List (SKey × K)).map
        fun q => markVal T F (q.1 : Multiset SPart) q.2).sum =
      κ * wM (k : Multiset SPart) * (constSum n φ *
        ∑ t ∈ Finset.range (T + 1), dsum t (k : Multiset SPart) (fun u => F (aM (k : Multiset SPart), bM (k : Multiset SPart), u))) := by
  change ((if constSum n φ = 0 then [] else [(k, κ * constSum n φ)] : List (SKey × K)).map
    fun q => markVal T F (q.1 : Multiset SPart) q.2).sum = _
  split_ifs with h
  · simp [h]
  · simp [markVal]; ring

/-- The child side, absorptions. -/
theorem child_abs (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (k : SKey) (κ : K) :
    (((picks k).flatMap fun xr => (posTerms (φ xr.1.1)).map fun ac =>
      (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, κ * ac.2)).map fun q => markVal T F (q.1 : Multiset SPart) q.2).sum =
      κ * wM (k : Multiset SPart) * ∑ t ∈ Finset.range (T + 1), ((k : Multiset SPart).map fun x =>
        dsum t ((k : Multiset SPart).erase x) (axT φ F (aM (k : Multiset SPart)) (bM (k : Multiset SPart)) x) +
        ∑ i ∈ Finset.range t, dsum (t - 1) ((k : Multiset SPart).erase x)
          (bxT φ F (aM (k : Multiset SPart)) (bM (k : Multiset SPart)) x i)).sum := by
  rw [flatMap_map_sum]
  have e1 := picks_sum k (fun x (m : Multiset SPart) => ((posTerms (φ x.1)).map fun ac =>
    markVal T F ((x.1, x.2 + ac.1) ::ₘ m) (κ * ac.2)).sum)
  have e2 : ((picks k).map fun xr => (((posTerms (φ xr.1.1)).map fun ac =>
      (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, κ * ac.2)).map fun q => markVal T F (q.1 : Multiset SPart) q.2).sum) =
      (picks k).map fun p => ((posTerms (φ p.1.1)).map fun ac =>
        markVal T F ((p.1.1, p.1.2 + ac.1) ::ₘ (p.2 : Multiset SPart)) (κ * ac.2)).sum :=
    List.map_congr_left fun p _ => by rw [List.map_map]; simp only [Function.comp_def, sIns_coe]
  rw [e2, ← e1]
  conv_rhs => rw [← msum_finset, ← Multiset.sum_map_mul_left]
  refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
  set S := (k : Multiset SPart)
  have e3 : ((posTerms (φ x.1)).map fun ac => markVal T F ((x.1, x.2 + ac.1) ::ₘ S.erase x) (κ * ac.2)) =
      (posTerms (φ x.1)).map fun ac => κ * wM S * ∑ t ∈ Finset.range (T + 1),
        (dsum t (S.erase x) (fun w => ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) *
            fca F (aM S) (bM S) x.1 ac.1 w) +
          ∑ i ∈ Finset.range t, dsum (t - 1) (S.erase x)
            fun w => ac.2 * (((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) *
              fca F (aM S) (bM S) x.1 ac.1 (insAt i (x.1, x.2 + ac.1) w)) :=
    List.map_congr_left fun ac _ => by
      rw [markVal_absorb T F S x hx]
      simp only [dsum_mul, ← Finset.mul_sum, ← mul_add]
      ring
  rw [e3, List.sum_map_mul_left, lsum_finset]
  refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
  rw [List.sum_map_add, lsum_finset]
  congr 1
  · rw [← dsum_list]; rfl
  · exact Finset.sum_congr rfl fun i _ => by rw [← dsum_list]; rfl

/-- The child side, new parts. -/
theorem child_new (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (k : SKey) (κ : K) :
    ((([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
      (sIns (c, ac.1) k, κ * ((n c : K) - (clsCnt k c : K)) * ac.2)).map
        fun q => markVal T F (q.1 : Multiset SPart) q.2).sum =
      κ * wM (k : Multiset SPart) * ∑ c : Fin 3, (((n c : K) - ((k : Multiset SPart).map (clsInd c)).sum) *
        ∑ t ∈ Finset.range (T + 1), (dsum t (k : Multiset SPart) (hc φ F (aM (k : Multiset SPart)) (bM (k : Multiset SPart)) c) +
          ∑ i ∈ Finset.range t, dsum (t - 1) (k : Multiset SPart)
            (jc φ F (aM (k : Multiset SPart)) (bM (k : Multiset SPart)) c i))) := by
  set S := (k : Multiset SPart) with hSdef
  have hℓ : ∀ c : Fin 3, (clsCnt k c : K) = (S.map (clsInd c)).sum := fun c => by
    rw [hSdef, Multiset.map_coe, Multiset.sum_coe, clsInd_sum]
  rw [flatMap_map_sum, Fin.sum_univ_three, mul_add, mul_add]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have e4 : ∀ c : Fin 3, (((posTerms (φ c)).map fun ac =>
      (sIns (c, ac.1) k, κ * ((n c : K) - (clsCnt k c : K)) * ac.2)).map
        fun q => markVal T F (q.1 : Multiset SPart) q.2).sum =
      κ * wM S * (((n c : K) - (S.map (clsInd c)).sum) *
        ∑ t ∈ Finset.range (T + 1), (dsum t S (hc φ F (aM S) (bM S) c) +
          ∑ i ∈ Finset.range t, dsum (t - 1) S (jc φ F (aM S) (bM S) c i))) := by
    intro c
    rw [List.map_map]
    have e5 : ((posTerms (φ c)).map ((fun q : SKey × K => markVal T F (q.1 : Multiset SPart) q.2) ∘
        fun ac => (sIns (c, ac.1) k, κ * ((n c : K) - (clsCnt k c : K)) * ac.2))) =
        (posTerms (φ c)).map fun ac => κ * wM S * (((n c : K) - (S.map (clsInd c)).sum) *
          ∑ t ∈ Finset.range (T + 1), (dsum t S (fun w => ac.2 * (ac.1.factorial : K) * fca F (aM S) (bM S) c ac.1 w) +
            ∑ i ∈ Finset.range t, dsum (t - 1) S fun w =>
              ac.2 * (ac.1.factorial : K) * fca F (aM S) (bM S) c ac.1 (insAt i (c, ac.1) w))) :=
      List.map_congr_left fun ac _ => by
        simp only [Function.comp_apply, sIns_coe, markVal_open, hℓ, dsum_mul, ← Finset.mul_sum, ← mul_add]
        ring
    rw [e5, List.sum_map_mul_left, List.sum_map_mul_left, lsum_finset]
    congr 2
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [List.sum_map_add, lsum_finset]
    congr 1
    · rw [← dsum_list]; rfl
    · exact Finset.sum_congr rfl fun i _ => by rw [← dsum_list]; rfl
  rw [e4 0, e4 1, e4 2]
  ring

omit [LinearOrder K] in
/-- Complement counting for a class-dependent function of the released mark. -/
theorem compl_class (t : ℕ) (S : Multiset SPart) (H : Fin 3 → List SPart → K) :
    (S.map fun x => dsum t (S.erase x) (H x.1)).sum =
      ∑ c : Fin 3, dsum t S fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * H c u := by
  have e1 : (S.map fun x => dsum t (S.erase x) (H x.1)) =
      S.map fun x => ∑ c : Fin 3, clsInd c x * dsum t (S.erase x) (H c) :=
    Multiset.map_congr rfl fun x _ => (clsInd_sel x (fun c => dsum t (S.erase x) (H c))).symm
  rw [e1, msum_finset]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dsum_compl]
  exact dsum_congr _ _ _ _ fun u _ => by rw [clsInd_sum]

/-- **One factor, one state.** The marked profile of order `≤ T` of the child of a state `(k, κ)`
under `φ` (V2k's `symStep`), against a test function `F`, equals the marked profile of order
`≤ T + 1` of the state against the direct transition `markTerms` of `F`. -/
theorem markVal_step (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (k : SKey) (κ : K) :
    ((symStep n φ (k, κ)).map fun q => markVal T F (q.1 : Multiset SPart) q.2).sum =
      markVal (T + 1) (fun key => ((markTerms n φ T key).map fun kc => kc.2 * F kc.1).sum)
        (k : Multiset SPart) κ := by
  rw [par_val, symStep, List.map_append, List.sum_append, List.map_append, List.sum_append, child_const,
    child_abs, child_new]
  generalize (k : Multiset SPart) = S
  generalize aM S = A
  generalize bM S = B
  -- abbreviations for the atoms
  have hD : ∀ (c : Fin 3) (t : ℕ) (H : List SPart → K),
      dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * H u) -
        dsum t S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * H u) =
      ((n c : K) - (S.map (clsInd c)).sum) * dsum t S H := by
    intro c t H
    rw [← dsum_sub, ← dsum_mul]
    exact dsum_congr _ _ _ _ fun u _ => by ring
  have hite : ∀ (s : ℕ) (X Y : ℕ → K), (if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), (X i - Y i) else 0) =
      (if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), X i else 0) -
        (if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), Y i else 0) := by
    intro s X Y; split_ifs <;> simp [Finset.sum_sub_distrib]
  -- parent absorption terms
  have eqAbsPar : ∑ s ∈ Finset.range (T + 1), (S.map fun x => dsum s (S.erase x) fun w =>
      axT φ F A B x w - hc φ F A B x.1 w +
        if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), (bxT φ F A B x i w - jc φ F A B x.1 i w) else 0).sum =
      (∑ s ∈ Finset.range (T + 1), (S.map fun x => dsum s (S.erase x) (axT φ F A B x)).sum) -
        ∑ c : Fin 3, (∑ s ∈ Finset.range (T + 1),
          dsum s S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * hc φ F A B c u)) +
      (∑ s ∈ Finset.range (T + 1), if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1),
          (S.map fun x => dsum s (S.erase x) (bxT φ F A B x i)).sum else 0) -
        ∑ c : Fin 3, (∑ s ∈ Finset.range (T + 1), if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1),
          dsum s S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * jc φ F A B c i u) else 0) := by
    rw [Finset.sum_comm (s := Finset.univ), Finset.sum_comm (s := Finset.univ)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : (S.map fun x => dsum s (S.erase x) fun w =>
        axT φ F A B x w - hc φ F A B x.1 w +
          if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1), (bxT φ F A B x i w - jc φ F A B x.1 i w) else 0) =
        S.map fun x => dsum s (S.erase x) (axT φ F A B x) - dsum s (S.erase x) (hc φ F A B x.1) +
          if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1),
            (dsum s (S.erase x) (bxT φ F A B x i) - dsum s (S.erase x) (jc φ F A B x.1 i)) else 0 :=
      Multiset.map_congr rfl fun x _ => by
        split_ifs
        · rw [dsum_add, dsum_sub, dsum_finset]
          simp only [dsum_sub]
        · rw [dsum_add, dsum_sub]; simp [dsum]
    rw [e, Multiset.sum_map_add, Multiset.sum_map_sub, compl_class s S (fun c => hc φ F A B c)]
    split_ifs
    · have : ∀ i ∈ Finset.range (s + 1), (S.map fun x => dsum s (S.erase x) (bxT φ F A B x i) -
            dsum s (S.erase x) (jc φ F A B x.1 i)).sum =
          (S.map fun x => dsum s (S.erase x) (bxT φ F A B x i)).sum -
            ∑ c : Fin 3, dsum s S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * jc φ F A B c i u) := by
        intro i _; rw [Multiset.sum_map_sub, compl_class s S (fun c => jc φ F A B c i)]
      rw [msum_finset, Finset.sum_congr rfl this, Finset.sum_sub_distrib,
        Finset.sum_comm (s := Finset.range (s + 1)) (t := Finset.univ)]
      ring
    · simp
  -- child absorption terms
  have eqAbsChild : ∑ t ∈ Finset.range (T + 1), (S.map fun x => dsum t (S.erase x) (axT φ F A B x) +
      ∑ i ∈ Finset.range t, dsum (t - 1) (S.erase x) (bxT φ F A B x i)).sum =
      (∑ s ∈ Finset.range (T + 1), (S.map fun x => dsum s (S.erase x) (axT φ F A B x)).sum) +
        ∑ s ∈ Finset.range (T + 1), if s + 1 ≤ T then ∑ i ∈ Finset.range (s + 1),
          (S.map fun x => dsum s (S.erase x) (bxT φ F A B x i)).sum else 0 := by
    rw [← range_reindex T (fun s i => (S.map fun x => dsum s (S.erase x) (bxT φ F A B x i)).sum),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Multiset.sum_map_add, msum_finset]
  -- new parts
  have eqNew : ∀ c : Fin 3, ((n c : K) - (S.map (clsInd c)).sum) *
      ∑ t ∈ Finset.range (T + 1), (dsum t S (hc φ F A B c) + ∑ i ∈ Finset.range t, dsum (t - 1) S (jc φ F A B c i)) =
      ((∑ t ∈ Finset.range (T + 1), dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * hc φ F A B c u)) -
        ∑ t ∈ Finset.range (T + 1), dsum t S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * hc φ F A B c u)) +
      ((∑ t ∈ Finset.range (T + 1), if t + 1 ≤ T then ∑ i ∈ Finset.range (t + 1),
          dsum t S (fun u => ((n c : K) - (clsCnt u c : K)) * jc φ F A B c i u) else 0) -
        ∑ t ∈ Finset.range (T + 1), if t + 1 ≤ T then ∑ i ∈ Finset.range (t + 1),
          dsum t S (fun u => ((S.map (clsInd c)).sum - (clsCnt u c : K)) * jc φ F A B c i u) else 0) := by
    intro c
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_add,
      range_reindex T (fun s i => dsum s S (jc φ F A B c i)), Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun t _ => (hD c t _).symm
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [← hite]
      split_ifs
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (hD c t _).symm
      · simp
  rw [eqAbsChild, Finset.sum_congr rfl (fun c _ => eqNew c), eqAbsPar]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

omit [LinearOrder K] in
theorem markVal_lin (T : ℕ) (F : MarkKey → K) (S : Multiset SPart) (κ : K) :
    markVal T F S κ = κ * markVal T F S 1 := by
  simp only [markVal]; ring

/-- **The direct transition (general theorem).** For every combination `L` of states, every
factor `φ`, all class sizes `n`, every order `T` and every test function `F` on marked keys, the
marked profile of order `≤ T` of the child `symStepAll n φ L` equals the direct transition of the
marked profile of order `≤ T + 1` of `L`. No state of the child enters `markStep`. -/
theorem markProfile_step (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (L : List (SKey × K))
    (F : MarkKey → K) :
    ((markProfile T (symStepAll n φ L)).map fun e => e.2 * F e.1).sum =
      ((markStep n φ T (markProfile (T + 1) L)).map fun e => e.2 * F e.1).sum := by
  set G : MarkKey → K := fun key => ((markTerms n φ T key).map fun kc => kc.2 * F kc.1).sum
  have hS : ∀ P : List (MarkKey × K), ((markStep n φ T P).map fun e => e.2 * F e.1).sum =
      (P.map fun e => e.2 * G e.1).sum := by
    intro P
    have h := normalizeBy_val markCmp markCmp_eq F
      (P.flatMap fun p => (markTerms n φ T p.1).map fun kc => (kc.1, p.2 * kc.2))
    unfold valBy at h
    rw [markStep, h, flatMap_map_sum]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    rw [List.map_map]
    simp only [Function.comp_def, G, ← List.sum_map_mul_left]
    exact congrArg _ (List.map_congr_left fun kc _ => by ring)
  rw [hS, markProfile_val, markProfile_val, symStepAll]
  have h1 := normalizeBy_val keyCmp keyCmp_eq (fun k : SKey => markVal T F (k : Multiset SPart) 1)
    (L.flatMap (symStep n φ))
  unfold valBy at h1
  beta_reduce at h1
  have e1 : ∀ L' : List (SKey × K), (L'.map fun q => markVal T F (q.1 : Multiset SPart) q.2) =
      L'.map fun q => q.2 * markVal T F (q.1 : Multiset SPart) 1 :=
    fun L' => List.map_congr_left fun q _ => markVal_lin T F _ q.2
  rw [e1, normalize, h1, ← e1, flatMap_map_sum]
  exact congrArg _ (List.map_congr_left fun q _ => markVal_step n φ T F q.1 q.2)

/-! ## §3 Certificates -/

omit [LinearOrder K] in
theorem sum_flatten_val (Ps : List (List (MarkKey × K))) (F : MarkKey → K) :
    ((Ps.flatten).map fun e => e.2 * F e.1).sum = (Ps.map fun P => (P.map fun e => e.2 * F e.1).sum).sum := by
  induction Ps with
  | nil => simp
  | cons P Ps ih => rw [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

omit [LinearOrder K] in
theorem mergeAll_markVal (Ps : List (List (MarkKey × K))) (F : MarkKey → K) :
    ((mergeAll markCmp 64 Ps).map fun e => e.2 * F e.1).sum =
      (Ps.map fun P => (P.map fun e => e.2 * F e.1).sum).sum := by
  have h := mergeAll_val markCmp markCmp_eq F 64 Ps
  unfold valBy at h
  exact h

/-- The transition of a test function (`markTerms` against `F`). -/
def markPull (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (F : MarkKey → K) (key : MarkKey) : K :=
  ((markTerms n φ T key).map fun kc => kc.2 * F kc.1).sum

theorem markStep_val (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (T : ℕ) (P : List (MarkKey × K))
    (F : MarkKey → K) :
    ((markStep n φ T P).map fun e => e.2 * F e.1).sum =
      (P.map fun e => e.2 * markPull n φ T F e.1).sum := by
  have h := normalizeBy_val markCmp markCmp_eq F
    (P.flatMap fun p => (markTerms n φ T p.1).map fun kc => (kc.1, p.2 * kc.2))
  unfold valBy at h
  rw [markStep, h, flatMap_map_sum]
  refine congrArg _ (List.map_congr_left fun p _ => ?_)
  rw [List.map_map]
  simp only [Function.comp_def, markPull, ← List.sum_map_mul_left]
  exact congrArg _ (List.map_congr_left fun kc _ => by ring)

omit [LinearOrder K] in
/-- **Start.** A certified state gives a marked profile of every order. -/
theorem markOK_of_chain (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T : ℕ) (L : List (SKey × K))
    (P : List (MarkKey × K)) (h : ChainCert n (psFactors g Q) [([], 1)] L) (hP : markProfile T L = P) :
    MarkOK n g Q T P :=
  ⟨L, h, fun F => by rw [hP]⟩

omit [LinearOrder K] in
/-- **Start, in chunks.** The marked profiles of chunks of a certified state, merged once. -/
theorem markOK_of_chunks (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T : ℕ) (Ls : List (List (SKey × K)))
    (Ps : List (List (MarkKey × K))) (P : List (MarkKey × K))
    (h : ChainCert n (psFactors g Q) [([], 1)] Ls.flatten)
    (hc : List.Forall₂ (fun C P => markProfile T C = P) Ls Ps) (hm : mergeAll markCmp 64 Ps = P) :
    MarkOK n g Q T P := by
  refine ⟨Ls.flatten, h, fun F => ?_⟩
  rw [← hm, mergeAll_markVal, markProfile_val]
  clear hm h
  induction hc with
  | nil => simp
  | cons hd _ ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih, ← hd,
      markProfile_val]

/-- **Direct step.** The direct transition of a marked profile of order `≤ T + 1` of `Q` is a
marked profile of order `≤ T` of `Q ++ [q]`. -/
theorem markOK_step (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q T : ℕ) (P P' : List (MarkKey × K))
    (h : MarkOK n g Q (T + 1) P) (hs : markStep n (stepFactor g q) T P = P') :
    MarkOK n g (Q ++ [q]) T P' := by
  obtain ⟨L, hc, hv⟩ := h
  refine ⟨symStepAll n (stepFactor g q) L,
    chainCert_snoc n g Q q _ L _ hc (stepCert_of_eq n _ L _ rfl), fun F => ?_⟩
  rw [← hs, markStep_val, hv, ← markStep_val]
  exact (markProfile_step n _ T L F).symm

/-- **Direct step, in chunks.** The parent's marked profile in chunks, each chunk's transition
certified separately, the results merged once. -/
theorem markOK_step_chunks (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q T : ℕ) (P : List (MarkKey × K))
    (Cs Ds : List (List (MarkKey × K))) (P' : List (MarkKey × K))
    (h : MarkOK n g Q (T + 1) P) (hP : Cs.flatten = P)
    (hc : List.Forall₂ (fun C D => markStep n (stepFactor g q) T C = D) Cs Ds)
    (hm : mergeAll markCmp 64 Ds = P') : MarkOK n g (Q ++ [q]) T P' := by
  obtain ⟨L, hch, hv⟩ := h
  refine ⟨symStepAll n (stepFactor g q) L,
    chainCert_snoc n g Q q _ L _ hch (stepCert_of_eq n _ L _ rfl), fun F => ?_⟩
  rw [markProfile_step, markStep_val, ← hv, ← hP, ← hm, mergeAll_markVal, sum_flatten_val]
  clear hm hP hv hch
  induction hc with
  | nil => simp
  | cons hd _ ih => rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, ← hd, markStep_val]

/-- **Lower order.** A marked profile of order `≤ T` keeps its entries of order `≤ T'`. -/
theorem markOK_mono (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T T' : ℕ) (hT : T' ≤ T) (P : List (MarkKey × K))
    (h : MarkOK n g Q T P) : MarkOK n g Q T' (P.filter fun e => decide (e.1.2.2.length ≤ T')) := by
  obtain ⟨L, hc, hv⟩ := h
  refine ⟨L, hc, fun F => ?_⟩
  have e : ∀ P : List (MarkKey × K), ((P.filter fun e => decide (e.1.2.2.length ≤ T')).map fun e => e.2 * F e.1).sum =
      (P.map fun e => e.2 * (if e.1.2.2.length ≤ T' then F e.1 else 0)).sum := by
    intro P
    induction P with
    | nil => simp
    | cons e P ih =>
      by_cases he : e.1.2.2.length ≤ T'
      · simp [List.filter_cons, he, ih]
      · simp [List.filter_cons, he, ih]
  rw [e, hv (fun key => if key.2.2.length ≤ T' then F key else 0),
    markProfile_val T L (fun key => if key.2.2.length ≤ T' then F key else 0), markProfile_val]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  simp only [markVal]
  congr 1
  rw [show T + 1 = T' + 1 + (T - T') by omega, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range (T - T'), dsum (T' + 1 + x) (q.1 : Multiset SPart)
      (fun u => if u.length ≤ T' then F (aM (q.1 : Multiset SPart), bM (q.1 : Multiset SPart), u) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      rw [dsum_congr _ _ _ (fun _ => 0) fun u hu => by rw [if_neg (by omega)]]
      simp [dsum]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun t ht => dsum_congr _ _ _ _ fun u hu => by
    rw [if_pos (by simp at ht; omega)]

/-- **To V2m's profiles.** A marked profile of order `0` gives a certified moment profile. -/
theorem profCert_of_markOK (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (P : List (MarkKey × K))
    (h : MarkOK n g Q 0 P) : ProfCert n g Q (markToProf P) := by
  obtain ⟨L, hc, hv⟩ := h
  intro M
  rw [chainCert_placeVal n _ L hc M, symFinal_abProfile]
  have hA : ((abProfile L).map fun e => e.2 * M e.1.1 e.1.2).sum =
      (L.map fun q => q.2 * factW q.1 * M (keyA q.1) (keyB q.1)).sum := by
    have h3 := normalizeBy_val abCmp abCmp_eq (fun ab : ℕ × ℕ => M ab.1 ab.2)
      (L.map fun q => ((keyA q.1, keyB q.1), q.2 * factW q.1))
    unfold valBy at h3
    rw [abProfile, h3, List.map_map]
    rfl
  have hB : ((markToProf P).map fun e => e.2 * M e.1.1 e.1.2).sum =
      (P.map fun e => e.2 * M e.1.1 e.1.2.1).sum := by
    have h1 := normalizeBy_val abCmp abCmp_eq (fun ab : ℕ × ℕ => M ab.1 ab.2)
      (P.map fun e => ((e.1.1, e.1.2.1), e.2))
    unfold valBy at h1
    rw [markToProf, h1, List.map_map]
    rfl
  have hC : (P.map fun e => e.2 * M e.1.1 e.1.2.1).sum =
      (L.map fun q => markVal 0 (fun key : MarkKey => M key.1 key.2.1) (q.1 : Multiset SPart) q.2).sum :=
    (hv (fun key => M key.1 key.2.1)).trans (markProfile_val 0 L (fun key : MarkKey => M key.1 key.2.1))
  rw [hA, hB, hC]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  simp [markVal, dsum_zero, keyA_m, keyB_m, factW_m]

/-- **Direct profile of a child** (the analogue of V2m's `profCert_of_step`): the order-`0`
transition of a parent's marked profile of order `≤ 1` certifies the child's moment profile. -/
theorem profCert_of_markStep (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q : ℕ) (P P' : List (MarkKey × K))
    (R : List ((ℕ × ℕ) × K)) (h : MarkOK n g Q 1 P) (hs : markStep n (stepFactor g q) 0 P = P')
    (hR : markToProf P' = R) : ProfCert n g (Q ++ [q]) R :=
  hR ▸ profCert_of_markOK n g (Q ++ [q]) P' (markOK_step n g Q q 0 P P' h hs)

omit [LinearOrder K] in
/-- **From a V2m trie node.** Every node of a certified trie has marked profiles of every order. -/
theorem markOK_of_trie (n : Fin 3 → ℕ) (g : K) (Tr : List (List ℕ × List (SKey × K))) (hT : TrieOK n g Tr)
    (Q : List ℕ) (L : List (SKey × K)) (hp : (Q, L) ∈ Tr) (T : ℕ) :
    MarkOK n g Q T (markProfile T L) :=
  markOK_of_chain n g Q T L _ (hT (Q, L) hp) rfl

omit [LinearOrder K] in
/-- Merging in two levels has the value of all the parts. -/
theorem merge_tree_val (Gs : List (List (List (MarkKey × K)))) (Rs : List (List (MarkKey × K)))
    (hg : List.Forall₂ (fun G R => mergeAll markCmp 64 G = R) Gs Rs) (F : MarkKey → K) :
    ((mergeAll markCmp 64 Rs).map fun e => e.2 * F e.1).sum =
      ((Gs.flatten).map fun P => (P.map fun e => e.2 * F e.1).sum).sum := by
  rw [mergeAll_markVal]
  induction hg with
  | nil => simp
  | cons hd _ ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatten_cons, List.map_append, List.sum_append, ← hd,
      mergeAll_markVal]

/-- **Start, chunked, merged in a tree.** Marked profiles of chunks `Ls` of a certified state,
merged in groups `Gs` and then once more. -/
theorem markOK_of_tree (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (T : ℕ) (L : List (SKey × K))
    (Ls : List (List (SKey × K))) (Qs : List (List (MarkKey × K))) (Gs : List (List (List (MarkKey × K))))
    (Rs : List (List (MarkKey × K))) (P : List (MarkKey × K))
    (h : ChainCert n (psFactors g Q) [([], 1)] L) (hL : Ls.flatten = L)
    (hc : List.Forall₂ (fun C Qc => markProfile T C = Qc) Ls Qs) (hQ : Gs.flatten = Qs)
    (hg : List.Forall₂ (fun G R => mergeAll markCmp 64 G = R) Gs Rs) (hm : mergeAll markCmp 64 Rs = P) :
    MarkOK n g Q T P := by
  refine ⟨L, h, fun F => ?_⟩
  rw [← hm, merge_tree_val Gs Rs hg, hQ, ← hL, markProfile_val]
  clear hm hg hQ hL h
  induction hc with
  | nil => simp
  | cons hd _ ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih, ← hd,
      markProfile_val]

/-- **Direct step, chunked, merged in a tree, from a higher order.** The parent's marked profile
of order `≤ T'` (`T + 1 ≤ T'`) in chunks `Cs`; each chunk restricted to order `≤ T + 1` and
stepped; the results merged in groups `Gs` and once more. -/
theorem markOK_step_tree (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q T T' : ℕ) (hT : T + 1 ≤ T')
    (P : List (MarkKey × K)) (Cs Ds : List (List (MarkKey × K))) (Gs : List (List (List (MarkKey × K))))
    (Rs : List (List (MarkKey × K))) (P' : List (MarkKey × K))
    (h : MarkOK n g Q T' P) (hP : Cs.flatten = P)
    (hc : List.Forall₂ (fun C D => markStep n (stepFactor g q) T
      (C.filter fun e => decide (e.1.2.2.length ≤ T + 1)) = D) Cs Ds)
    (hD : Gs.flatten = Ds) (hg : List.Forall₂ (fun G R => mergeAll markCmp 64 G = R) Gs Rs)
    (hm : mergeAll markCmp 64 Rs = P') : MarkOK n g (Q ++ [q]) T P' := by
  have h1 := markOK_mono n g Q T' (T + 1) hT P h
  obtain ⟨L, hch, hv⟩ := h1
  refine ⟨symStepAll n (stepFactor g q) L,
    chainCert_snoc n g Q q _ L _ hch (stepCert_of_eq n _ L _ rfl), fun F => ?_⟩
  rw [markProfile_step, markStep_val, ← hv, ← hm, merge_tree_val Gs Rs hg, hD, ← hP, List.filter_flatten,
    sum_flatten_val]
  clear hm hg hD hP hv hch
  induction hc with
  | nil => simp
  | cons hd _ ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← hd, markStep_val]

omit [LinearOrder K] in
/-- Certified profile lists can be concatenated. -/
theorem profOK_append (n : Fin 3 → ℕ) (g : K) (R R' : List (List ℕ × List ((ℕ × ℕ) × K)))
    (h : ProfOK n g R) (h' : ProfOK n g R') : ProfOK n g (R ++ R') := fun p hp => by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

end Step

/-! ## §4 The moment profile alone is insufficient -/

section Obstruction

open BGP212.Params

/-- **Obstruction.** No map from a parent's moment profile to the child's value exists, for the
factor `P̂₂` at Table 3, piece `(6, 3)`: the states `{(0, 2)}` (coefficient `1`) and
`{(0, 1), (0, 1)}` (coefficient `2`) have the same profile (so the same value for every moment
oracle), but their children have different values at the oracle `M(A, B) = [A = 4 ∧ B = 0]` (`44` against `40`).
The absorption weight `(e + a)!/e!` depends on the individual exponents. -/
theorem profile_insufficient :
    ¬ ∃ f : List ((ℕ × ℕ) × ℚ) → List ((ℕ × ℕ) × ℚ), ∀ (L : List (SKey × ℚ)) (M : ℕ → ℕ → ℚ),
      symFinal M (symStepAll (clsCount 44 6 3) (stepFactor g 2) L) =
        ((f (abProfile L)).map fun e => e.2 * M e.1.1 e.1.2).sum := by
  rintro ⟨f, hf⟩
  have hp : abProfile ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ)) =
      abProfile ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ)) := by decide +kernel
  have hv : symFinal (fun A B => if A = 4 ∧ B = 0 then (1 : ℚ) else 0)
      (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 2)], 1)]) ≠
      symFinal (fun A B => if A = 4 ∧ B = 0 then (1 : ℚ) else 0)
        (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)]) := by
    decide +kernel
  exact hv (by rw [hf, hf, hp])

/-- **Obstruction with class counts.** The moment profile together with the class-count profile
(`Σ κ ∏ e! ℓ_c` by `(A, B, c)`) is still insufficient: `{(0, 3), (0, 1)}` (coefficient `2`) and
`{(0, 2), (0, 2)}` (coefficient `3`) agree on both, but their children under `P̂₂` differ at the
oracle `M(A, B) = [A = 6 ∧ B = 0]`; the marks must carry the exponents. -/
theorem classProfile_insufficient :
    ¬ ∃ f : List ((ℕ × ℕ) × ℚ) → List ((ℕ × ℕ × ℕ) × ℚ) → List ((ℕ × ℕ) × ℚ),
      ∀ (L : List (SKey × ℚ)) (M : ℕ → ℕ → ℚ),
        symFinal M (symStepAll (clsCount 44 6 3) (stepFactor g 2) L) =
          ((f (abProfile L) (classProfile L)).map fun e => e.2 * M e.1.1 e.1.2).sum := by
  rintro ⟨f, hf⟩
  have hp : abProfile ([([((0 : Fin 3), 3), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ)) =
      abProfile ([([((0 : Fin 3), 2), ((0 : Fin 3), 2)], 3)] : List (SKey × ℚ)) := by decide +kernel
  have hc : classProfile ([([((0 : Fin 3), 3), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ)) =
      classProfile ([([((0 : Fin 3), 2), ((0 : Fin 3), 2)], 3)] : List (SKey × ℚ)) := by decide +kernel
  have hv : symFinal (fun A B => if A = 6 ∧ B = 0 then (1 : ℚ) else 0)
      (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 3), ((0 : Fin 3), 1)], 2)]) ≠
      symFinal (fun A B => if A = 6 ∧ B = 0 then (1 : ℚ) else 0)
        (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 2), ((0 : Fin 3), 2)], 3)]) := by
    decide +kernel
  exact hv (by rw [hf, hf, hp, hc])

end Obstruction

end BGP212.V2e
#print axioms BGP212.V2e.markProfile_step
#print axioms BGP212.V2e.profile_insufficient
#print axioms BGP212.V2e.classProfile_insufficient
