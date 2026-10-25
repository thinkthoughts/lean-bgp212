/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymRead
import Solution.SymProfile

/-! # V2o: what one factor reads (proofs)

* §1 values of the read summary and of `readStep`; the positive-degree terms of a factor of degree
  `≤ d` as a sum over `1 ≤ a ≤ d`;
* §2 **sufficiency** (`readStep_sufficient`): for every factor of degree `≤ d`, the child's moment
  profile is `readStep` of the parent's profile and binomial read summary, for arbitrary class sizes
  and moment oracles;
* §3 **the monomial factors read every coordinate** (`monomial_reads`, `monomial_reads_at`);
* §4 **the degree gap** (`summary_degree_gap`): V2n's two states agree on every factor of degree
  `≤ 1` and differ under `P̂₂`. -/

namespace BGP212.V2e

section Read

variable {K : Type*} [Field K] [LinearOrder K]

/-! ## §1 Values -/

theorem readCmp_eq (s t : ReadKey) (h : readCmp s t = .eq) : s = t := by
  obtain ⟨a, b, c, d⟩ := s
  obtain ⟨a', b', c', d'⟩ := t
  unfold readCmp at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  have e3 : c = c' := le_antisymm (not_lt.mp h6) (not_lt.mp h5)
  have e4 : d = d' := by omega
  subst e1 e2 e3 e4
  rfl

theorem readSummary_val (d : ℕ) (P : List (MarkKey × K)) (G : ReadKey → K) :
    ((readSummary d P).map fun e => e.2 * G e.1).sum =
      (P.map fun e => e.2 * ((readTerms d e.1).map fun t => t.2 * G t.1).sum).sum := by
  have h := normalizeBy_val readCmp readCmp_eq G
    (P.flatMap fun e => (readTerms (K := K) d e.1).map fun t => (t.1, e.2 * t.2))
  unfold valBy at h
  rw [readSummary, h, flatMap_map_sum]
  refine congrArg _ (List.map_congr_left fun p _ => ?_)
  rw [List.map_map]
  simp only [Function.comp_def, ← List.sum_map_mul_left]
  exact congrArg _ (List.map_congr_left fun kc _ => by ring)

theorem readStep_val (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (R0 : List ((ℕ × ℕ) × K))
    (Rd : List (ReadKey × K)) (M : ℕ → ℕ → K) :
    ((readStep n φ R0 Rd).map fun e => e.2 * M e.1.1 e.1.2).sum =
      (R0.map fun e => e.2 * ((pull0 n φ e.1).map fun t => t.2 * M t.1.1 t.1.2).sum).sum +
        (Rd.map fun e => e.2 * ((pull1 φ e.1).2 * M (pull1 φ e.1).1.1 (pull1 φ e.1).1.2)).sum := by
  have h := normalizeBy_val abCmp abCmp_eq (fun ab : ℕ × ℕ => M ab.1 ab.2)
    ((R0.flatMap fun e => (pull0 n φ e.1).map fun t => (t.1, e.2 * t.2)) ++
      Rd.map fun e => ((pull1 φ e.1).1, e.2 * (pull1 φ e.1).2))
  unfold valBy at h
  rw [readStep, h, List.map_append, List.sum_append, flatMap_map_sum, List.map_map]
  congr 1
  · refine congrArg _ (List.map_congr_left fun p _ => ?_)
    rw [List.map_map]
    simp only [Function.comp_def, ← List.sum_map_mul_left]
    exact congrArg _ (List.map_congr_left fun kc _ => by ring)
  · refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    ring

theorem filter_ne_sum (l : List (ℕ × K)) (H : ℕ → K) :
    ((l.filter fun p => p.2 ≠ 0).map fun ac => ac.2 * H ac.1).sum = (l.map fun ac => ac.2 * H ac.1).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [ne_eq, decide_not] at ih ⊢
    by_cases hp : p.2 = 0
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih]

omit [LinearOrder K] in
theorem cterms_sumD (H : ℕ → K) : ∀ (f : List K) (k d : ℕ), f.length ≤ d →
    ((cterms f k).map fun ac => ac.2 * H ac.1).sum = ∑ i ∈ Finset.range d, f.getD i 0 * H (k + i)
  | [], k, d, _ => by simp [cterms]
  | c :: f, k, d, h => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at h; omega⟩
    have ih := cterms_sumD H f (k + 1) d' (by simp at h; omega)
    rw [cterms, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg₂ _ (Finset.sum_congr rfl fun i _ => by rw [show k + 1 + i = k + (i + 1) by omega]) rfl

/-- The positive-degree terms of a factor of degree `≤ d`, as a sum over `1 ≤ a ≤ d`. -/
theorem posTerms_sum (f : List K) (d : ℕ) (hf : f.length ≤ d + 1) (H : ℕ → K) :
    ((posTerms f).map fun ac => ac.2 * H ac.1).sum =
      ∑ i ∈ Finset.range d, f.getD (i + 1) 0 * H (i + 1) := by
  cases f with
  | nil => simp [posTerms]
  | cons c f =>
    rw [posTerms, filter_ne_sum, cterms_sumD H f 1 d (by simp at hf; omega)]
    exact Finset.sum_congr rfl fun i _ => by rw [List.getD_cons_succ, add_comm 1 i]

omit [LinearOrder K] in
/-- `markVal` of order `≤ 1`: the unmarked key and one mark per part. -/
theorem markVal_one (H : MarkKey → K) (S : Multiset SPart) (κ : K) :
    markVal 1 H S κ = κ * wM S * (H (aM S, bM S, []) + (S.map fun x => H (aM S, bM S, [x])).sum) := by
  rw [markVal, Finset.sum_range_succ, Finset.sum_range_one, dsum_zero, dsum_succ]
  congr 2
  exact congrArg _ (Multiset.map_congr rfl fun x _ => dsum_zero _ _)

omit [LinearOrder K] in
theorem markVal_zero (H : MarkKey → K) (S : Multiset SPart) (κ : K) :
    markVal 0 H S κ = κ * wM S * H (aM S, bM S, []) := by
  rw [markVal, Finset.sum_range_one, dsum_zero]

/-! ## §2 Sufficiency -/

/-- The unmarked key at order `0`: constant terms and new parts. -/
theorem markPull_nil (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (M : ℕ → ℕ → K) (A B : ℕ) :
    markPull n φ 0 (fun k => M k.1 k.2.1) (A, B, []) =
      ((pull0 n φ (A, B)).map fun t => t.2 * M t.1.1 t.1.2).sum := by
  have key : ∀ c : Fin 3, (((posTerms (φ c)).map fun ac =>
      ((A + roughPart c ac.1, B + smoothPart c ac.1), (n c : K) * ac.2 * (ac.1.factorial : K))).map
        fun t => t.2 * M t.1.1 t.1.2).sum =
      (n c : K) * hc φ (fun k => M k.1 k.2.1) A B c [] := by
    intro c
    rw [hc, List.map_map, ← List.sum_map_mul_left]
    exact congrArg _ (List.map_congr_left fun ac _ => by simp only [Function.comp_apply, fca]; ring)
  have hm := markTerms_val n φ 0 (fun k : MarkKey => M k.1 k.2.1) A B []
  rw [markPull]
  rw [hm, pull0, List.map_cons, List.sum_cons, flatMap_map_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, key, Fin.sum_univ_three,
    newT, absT, List.length_nil, le_refl, if_true, zero_add, Nat.one_le_iff_ne_zero, ne_eq,
    not_true, if_false, add_zero, clsCnt, List.countP_nil, Nat.cast_zero, sub_zero]
  ring

/-- A marked key with one mark at order `0`: the mark absorbs `a`, minus the opening counted by
`ℓ_c`; as a sum over `1 ≤ a ≤ d` of the binomial weight times the shifted oracle. -/
theorem markPull_one (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (d : ℕ) (hd : degLe d φ) (M : ℕ → ℕ → K)
    (A B : ℕ) (x : SPart) :
    markPull n φ 0 (fun k => M k.1 k.2.1) (A, B, [x]) =
      ∑ i ∈ Finset.range d, ((((x.2 + (i + 1)).choose (i + 1) : ℕ) : K) - 1) *
        ((φ x.1).getD (i + 1) 0 * ((i + 1).factorial : K) *
          M (A + roughPart x.1 (i + 1)) (B + smoothPart x.1 (i + 1))) := by
  have hm := markTerms_val n φ 0 (fun k : MarkKey => M k.1 k.2.1) A B [x]
  rw [markPull]
  rw [hm]
  have hz : ∀ c : Fin 3, newT n φ 0 (fun k => M k.1 k.2.1) A B c [x] = 0 := by
    intro c; simp [newT]
  simp only [hz, Finset.sum_const_zero, add_zero, absT, List.length_nil, List.length_singleton]
  norm_num
  rw [axT, hc, ← lsum_sub]
  have hp := posTerms_sum (φ x.1) d (hd x.1) fun a =>
    ((((x.2 + a).descFactorial a : ℕ) : K) - (a.factorial : K)) * M (A + roughPart x.1 a) (B + smoothPart x.1 a)
  calc _ = ((posTerms (φ x.1)).map fun ac => ac.2 * (((((x.2 + ac.1).descFactorial ac.1 : ℕ) : K) -
          (ac.1.factorial : K)) * M (A + roughPart x.1 ac.1) (B + smoothPart x.1 ac.1))).sum :=
        congrArg _ (List.map_congr_left fun ac _ => by simp only [fca]; ring)
    _ = _ := hp
    _ = _ := Finset.sum_congr rfl fun i _ => by
        rw [Nat.descFactorial_eq_factorial_mul_choose, List.getD_eq_getElem?_getD]
        push_cast
        ring

omit [LinearOrder K] in
theorem symFinal_markZero (M : ℕ → ℕ → K) (L : List (SKey × K)) :
    symFinal M L = ((markProfile 0 L).map fun e => e.2 * M e.1.1 e.1.2.1).sum := by
  have hm := markProfile_val 0 L (fun k : MarkKey => M k.1 k.2.1)
  rw [hm, symFinal, bsum_eq]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  rw [markVal_zero, keyW, ← keyA_m, ← keyB_m]
  simp only [keyA, keyB, wM, Multiset.map_coe, Multiset.prod_coe]
  ring

theorem abProfile_valG (L : List (SKey × K)) (G : ℕ × ℕ → K) :
    ((abProfile L).map fun e => e.2 * G e.1).sum =
      (L.map fun q => q.2 * factW q.1 * G (keyA q.1, keyB q.1)).sum := by
  have h := normalizeBy_val abCmp abCmp_eq G (L.map fun q => ((keyA q.1, keyB q.1), q.2 * factW q.1))
  unfold valBy at h
  rw [abProfile, h, List.map_map]
  rfl

/-- **Sufficiency (general theorem).** For every factor `φ` of degree `≤ d`, all class sizes `n`,
every combination `L` and every moment oracle `M`, the value of the child `symStepAll n φ L` is the
value of `readStep` of the parent's moment profile and binomial read summary of degree `d`. -/
theorem readStep_sufficient (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (d : ℕ) (hd : degLe d φ)
    (L : List (SKey × K)) (M : ℕ → ℕ → K) :
    symFinal M (symStepAll n φ L) =
      ((readStep n φ (abProfile L) (readSummary d (markProfile 1 L))).map
        fun e => e.2 * M e.1.1 e.1.2).sum := by
  set F : MarkKey → K := fun k => M k.1 k.2.1 with hF
  have e1 : symFinal M (symStepAll n φ L) = ((markProfile 0 (symStepAll n φ L)).map fun e => e.2 * F e.1).sum :=
    symFinal_markZero M _
  have e2 := readSummary_val d (markProfile 1 L) (fun k => (pull1 φ k).2 * M (pull1 φ k).1.1 (pull1 φ k).1.2)
  have e3 := abProfile_valG L fun ab => ((pull0 n φ ab).map fun t => t.2 * M t.1.1 t.1.2).sum
  simp only at e2 e3
  have e4 := markProfile_val 1 L (fun k => ((readTerms (K := K) d k).map fun e =>
    e.2 * ((pull1 φ e.1).2 * M (pull1 φ e.1).1.1 (pull1 φ e.1).1.2)).sum)
  rw [e1, markProfile_step n φ 0 L F, markStep_val, markProfile_val, readStep_val, e2, e4, e3,
    ← List.sum_map_add, zero_add]
  refine congrArg _ (List.map_congr_left fun q _ => ?_)
  rw [markVal_one, markVal_one, hF, markPull_nil, ← keyA_m, ← keyB_m, ← factW_m]
  have h1 : ∀ x : SPart, markPull n φ 0 (fun k => M k.1 k.2.1) (keyA q.1, keyB q.1, [x]) =
      ((readTerms d (keyA q.1, keyB q.1, [x])).map fun t =>
        t.2 * ((pull1 φ t.1).2 * M (pull1 φ t.1).1.1 (pull1 φ t.1).1.2)).sum := by
    intro x
    rw [markPull_one n φ d hd, readTerms, List.map_map, list_range_sum]
    rfl
  simp only [h1, readTerms, List.map_nil, List.sum_nil, zero_add]
  ring


/-! ## §3 The monomial factors read every coordinate -/

omit [LinearOrder K] in
theorem monoF_degLe (c : Fin 3) (a d : ℕ) (had : a ≤ d) : degLe d (monoF (K := K) c a) := by
  intro c'
  unfold monoF
  split_ifs <;> simp <;> omega

theorem cterms_mono_filter : ∀ (m k : ℕ),
    (cterms (List.replicate m (0 : K) ++ [1]) k).filter (fun p => p.2 ≠ 0) = [(k + m, 1)]
  | 0, k => by simp [cterms]
  | m + 1, k => by
    rw [List.replicate_succ, List.cons_append, cterms, List.filter_cons]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    rw [cterms_mono_filter m (k + 1)]
    congr 2
    omega

theorem posTerms_monoF (c c' : Fin 3) (a : ℕ) (ha : 1 ≤ a) :
    posTerms (monoF (K := K) c a c') = if c' = c then [(a, 1)] else [] := by
  unfold monoF
  split_ifs
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [List.replicate_succ, List.cons_append, posTerms, cterms_mono_filter, add_comm]
  · rfl

omit [LinearOrder K] in
theorem constSum_monoF (n : Fin 3 → ℕ) (c : Fin 3) (a : ℕ) (ha : 1 ≤ a) :
    constSum n (monoF (K := K) c a) = 0 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold constSum monoF
  fin_cases c <;> simp [constTerm, List.replicate_succ]

omit [LinearOrder K] in
theorem getD_monoF (c c' : Fin 3) (a i : ℕ) :
    (monoF (K := K) c a c').getD i 0 = if c' = c ∧ i = a then 1 else 0 := by
  unfold monoF
  by_cases hc : c' = c
  · simp only [hc, if_true, true_and]
    rw [List.getD_eq_getElem?_getD]
    rcases lt_trichotomy i a with h | h | h
    · rw [List.getElem?_append_left (by simpa using h), List.getElem?_replicate]
      simp [h, h.ne]
    · subst h
      rw [List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp [h.ne']
  · simp [hc]

/-- **The monomial factor `x^a` in class `c` reads exactly** `a! (n_c P(A, B) + δ_a(A, B, c))`:
for every moment oracle, the child's value is the profile weighted by `n_c a!` and the summary
coordinates `(·, ·, c, a)` weighted by `a!`, at the keys shifted by `a` in class `c`; no other
coordinate of the summary enters. -/
theorem monomial_reads (n : Fin 3 → ℕ) (c : Fin 3) (a : ℕ) (ha : 1 ≤ a) (d : ℕ) (had : a ≤ d)
    (L : List (SKey × K)) (M : ℕ → ℕ → K) :
    symFinal M (symStepAll n (monoF c a) L) =
      ((abProfile L).map fun e => e.2 * ((n c : K) * (a.factorial : K) *
        M (e.1.1 + roughPart c a) (e.1.2 + smoothPart c a))).sum +
      ((readSummary d (markProfile 1 L)).map fun e => if e.1.2.2 = (c, a) then
        e.2 * ((a.factorial : K) * M (e.1.1 + roughPart c a) (e.1.2.1 + smoothPart c a)) else 0).sum := by
  rw [readStep_sufficient n (monoF c a) d (monoF_degLe c a d had) L M, readStep_val]
  congr 1
  · refine congrArg _ (List.map_congr_left fun e _ => ?_)
    congr 1
    rw [pull0, List.map_cons, List.sum_cons, flatMap_map_sum, constSum_monoF n c a ha]
    simp only [posTerms_monoF c _ a ha]
    fin_cases c <;> simp
  · refine congrArg _ (List.map_congr_left fun e _ => ?_)
    obtain ⟨A, B, c', a'⟩ := e.1
    simp only [pull1, getD_monoF]
    by_cases h : c' = c ∧ a' = a
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have h' : ¬ ((c', a') = (c, a)) := fun h'' => h (Prod.mk.inj h'')
      simp [h, h']

omit [LinearOrder K] in
theorem shift_inj (c : Fin 3) (a A B A' B' : ℕ) :
    (A' + roughPart c a = A + roughPart c a ∧ B' + smoothPart c a = B + smoothPart c a) ↔
      (A', B') = (A, B) := by
  constructor
  · rintro ⟨h1, h2⟩; simp only [Prod.mk.injEq]; omega
  · intro h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp

/-- **Recovering one coordinate.** At the indicator oracle of the key `(A, B)` shifted by `a` in
class `c`, the child under `x^a` has the value `a! (n_c P(A, B) + δ_a(A, B, c))`. -/
theorem monomial_reads_at (n : Fin 3 → ℕ) (c : Fin 3) (a : ℕ) (ha : 1 ≤ a) (d : ℕ) (had : a ≤ d)
    (L : List (SKey × K)) (A B : ℕ) :
    symFinal (fun A' B' => if A' = A + roughPart c a ∧ B' = B + smoothPart c a then (1 : K) else 0)
        (symStepAll n (monoF c a) L) =
      (a.factorial : K) * ((n c : K) * profAt (abProfile L) (A, B) +
        readAt (readSummary d (markProfile 1 L)) (A, B, c, a)) := by
  rw [monomial_reads n c a ha d had L, mul_add, profAt, readAt]
  simp only [← List.sum_map_mul_left]
  congr 1
  · refine congrArg _ (List.map_congr_left fun e _ => ?_)
    by_cases h : e.1 = (A, B)
    · have h2 : e.1.1 + roughPart c a = A + roughPart c a ∧ e.1.2 + smoothPart c a = B + smoothPart c a :=
        (shift_inj c a A B e.1.1 e.1.2).mpr h
      simp only [h2, h, and_self, if_true]
      ring
    · have h2 : ¬ (e.1.1 + roughPart c a = A + roughPart c a ∧ e.1.2 + smoothPart c a = B + smoothPart c a) :=
        fun h3 => h ((shift_inj c a A B e.1.1 e.1.2).mp h3)
      simp only [h2, h, if_false]
      ring
  · refine congrArg _ (List.map_congr_left fun e _ => ?_)
    obtain ⟨⟨A', B', c', a'⟩, v⟩ := e
    simp only
    by_cases h4 : (c', a') = (c, a)
    · simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      by_cases hAB : A' = A ∧ B' = B
      · obtain ⟨rfl, rfl⟩ := hAB
        simp only [and_self, if_true]
        ring
      · have h5 : ¬ (A' + roughPart c' a' = A + roughPart c' a' ∧ B' + smoothPart c' a' = B + smoothPart c' a') := by
          intro h3; apply hAB; omega
        have h6 : ¬ ((A', B', c', a') = (A, B, c', a')) := by
          intro h7; apply hAB; simp only [Prod.mk.injEq] at h7; exact ⟨h7.1, h7.2.1⟩
        simp only [h5, h6, if_true, if_false]
        ring
    · have h6 : ¬ ((A', B', c', a') = (A, B, c, a)) := by
        intro h7; apply h4; simp only [Prod.mk.injEq] at h7 ⊢; exact ⟨h7.2.2.1, h7.2.2.2⟩
      simp only [h4, h6, if_false]
      ring

/-- **Minimality.** For combinations with the same moment profile, the binomial read summary of
degree `d` is determined by the children under the monomial factors of degree `≤ d`: if those
children agree for every moment oracle, every summary coordinate agrees. With `readStep_sufficient`,
`(P, δ₁, …, δ_d)` is exactly the information that factors of degree `≤ d` read. -/
theorem summary_determined [CharZero K] (n : Fin 3 → ℕ) (d : ℕ) (L₁ L₂ : List (SKey × K))
    (hP : ∀ ab, profAt (abProfile L₁) ab = profAt (abProfile L₂) ab)
    (hM : ∀ (c : Fin 3) (a : ℕ), 1 ≤ a → a ≤ d → ∀ M : ℕ → ℕ → K,
      symFinal M (symStepAll n (monoF c a) L₁) = symFinal M (symStepAll n (monoF c a) L₂))
    (A B : ℕ) (c : Fin 3) (a : ℕ) (ha : 1 ≤ a) (had : a ≤ d) :
    readAt (readSummary d (markProfile 1 L₁)) (A, B, c, a) =
      readAt (readSummary d (markProfile 1 L₂)) (A, B, c, a) := by
  have h := hM c a ha had fun A' B' => if A' = A + roughPart c a ∧ B' = B + smoothPart c a then (1 : K) else 0
  rw [monomial_reads_at n c a ha d had L₁, monomial_reads_at n c a ha d had L₂, hP] at h
  have hf : (a.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  exact add_left_cancel (mul_left_cancel₀ hf h)

end Read

/-! ## §4 The degree gap -/

section Gap

open BGP212.Params

/-- **The information grows with the degree.** V2n's two states `{(0, 2)}` (coefficient 1) and
`{(0, 1), (0, 1)}` (coefficient 2) have the same moment profile and the same summary of degree 1,
so their children agree under every factor of degree `≤ 1` for all class sizes and moment oracles;
their summaries of degree 2 differ, and their children under `P̂₂` at Table 3, piece `(6, 3)` differ. -/
theorem summary_degree_gap :
    abProfile ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ)) =
        abProfile ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ)) ∧
    readSummary 1 (markProfile 1 ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ))) =
        readSummary 1 (markProfile 1 ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ))) ∧
    readSummary 2 (markProfile 1 ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ))) ≠
        readSummary 2 (markProfile 1 ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ))) ∧
    (∀ (n : Fin 3 → ℕ) (φ : Fin 3 → List ℚ), degLe 1 φ → ∀ M : ℕ → ℕ → ℚ,
      symFinal M (symStepAll n φ [([((0 : Fin 3), 2)], 1)]) =
        symFinal M (symStepAll n φ [([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)])) ∧
    symFinal (fun A B => if A = 4 ∧ B = 0 then (1 : ℚ) else 0)
        (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 2)], 1)]) ≠
      symFinal (fun A B => if A = 4 ∧ B = 0 then (1 : ℚ) else 0)
        (symStepAll (clsCount 44 6 3) (stepFactor g 2) [([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)]) := by
  have hp : abProfile ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ)) =
      abProfile ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ)) := by decide +kernel
  have h1 : readSummary 1 (markProfile 1 ([([((0 : Fin 3), 2)], 1)] : List (SKey × ℚ))) =
      readSummary 1 (markProfile 1 ([([((0 : Fin 3), 1), ((0 : Fin 3), 1)], 2)] : List (SKey × ℚ))) := by
    decide +kernel
  refine ⟨hp, h1, by decide +kernel, fun n φ hφ M => ?_, by decide +kernel⟩
  rw [readStep_sufficient n φ 1 hφ _ M, readStep_sufficient n φ 1 hφ _ M, hp, h1]

end Gap

end BGP212.V2e

#print axioms BGP212.V2e.readStep_sufficient
#print axioms BGP212.V2e.monomial_reads
#print axioms BGP212.V2e.summary_determined
#print axioms BGP212.V2e.summary_degree_gap
