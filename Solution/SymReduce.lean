/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymReduce
import Solution.MomentAgg

/-! # V2k: the symmetric-function evaluator equals V2i's placement recursion (proofs)

* §1 coefficient-list algebra: `coordSum` of `lpAdd`, `lpMul` (composition), shifts, exchange;
* §2 `msum`, the iterated coefficient sum over open coordinates, and its linearity;
* §3 `placeVal_eq_msum`: V2i's placement value is the iterated coefficient sum of the
  multiset-state value `msVal`, hence `placeVal_eq_msVal` (no open coordinate);
* §4 `msVal_zero_part`: a part of exponent `0` can be removed (`m̃_{ν ∪ 0} = (n − ℓ) m̃_ν`);
* §5 the canonical evaluator: insertion, picks, one step, normalization, the run;
* §6 `symPlaceVal_eq`, `genPieceSym_eq`, `genEntrySym_eq`, `jT_eq_genEntrySym`. -/

namespace BGP212.V2e

open BigOperators

section Algebra

variable {K : Type*} [Field K]

/-! ## §1 Coefficient lists -/

theorem coordSum_zero_body (f : List K) (e : ℕ) : coordSum (fun _ => (0 : K)) f e = 0 := by
  induction f generalizing e with
  | nil => rfl
  | cons c f ih => simp [coordSum, ih]

theorem coordSum_lpAdd (b : ℕ → K) (f g : List K) (e : ℕ) :
    coordSum b (lpAdd f g) e = coordSum b f e + coordSum b g e := by
  induction f generalizing g e with
  | nil => simp [lpAdd, coordSum]
  | cons a f ih =>
    cases g with
    | nil => simp [lpAdd, coordSum]
    | cons c g => simp only [lpAdd, coordSum, ih]; ring

theorem coordSum_map_mul (b : ℕ → K) (a : K) (g : List K) (e : ℕ) :
    coordSum b (g.map (a * ·)) e = a * coordSum b g e := by
  induction g generalizing e with
  | nil => simp [coordSum]
  | cons c g ih => simp only [List.map_cons, coordSum, ih]; ring

/-- Multiplying coefficient lists composes the coefficient sums. -/
theorem coordSum_lpMul (b : ℕ → K) (f g : List K) (e : ℕ) :
    coordSum b (lpMul f g) e = coordSum (fun e' => coordSum b g e') f e := by
  induction f generalizing e with
  | nil => simp [lpMul, coordSum]
  | cons a f ih =>
    simp only [lpMul, coordSum_lpAdd, coordSum_map_mul, coordSum, ih]; ring

theorem coordSum_shift (b : ℕ → K) (f : List K) (e e' : ℕ) :
    coordSum b f (e + e') = coordSum (fun j => b (e + j)) f e' := by
  induction f generalizing e' with
  | nil => rfl
  | cons c f ih => simp only [coordSum, ih, add_assoc]

theorem coordSum_shift0 (b : ℕ → K) (f : List K) (e : ℕ) :
    coordSum b f e = coordSum (fun j => b (e + j)) f 0 := by
  simpa using coordSum_shift b f e 0

theorem coordSum_add'' (b b' : ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => b e + b' e) f e = coordSum b f e + coordSum b' f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp only [coordSum, ih]; ring

theorem coordSum_mul'' (a : K) (b : ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => a * b e) f e = a * coordSum b f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp only [coordSum, ih]; ring

theorem coordSum_congr'' (b b' : ℕ → K) (h : ∀ e, b e = b' e) (f : List K) (e : ℕ) :
    coordSum b f e = coordSum b' f e := by
  have : b = b' := funext h
  subst this; rfl

/-- Exchange of two coefficient sums. -/
theorem coordSum_comm (F : ℕ → ℕ → K) (f g : List K) (e₀ e₁ : ℕ) :
    coordSum (fun e => coordSum (fun a => F e a) g e₁) f e₀ =
      coordSum (fun a => coordSum (fun e => F e a) f e₀) g e₁ := by
  induction f generalizing e₀ with
  | nil => simp [coordSum, coordSum_zero_body]
  | cons c f ih =>
    simp only [coordSum, ih]
    rw [coordSum_add'', coordSum_mul'']

theorem coordSum_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => ∑ i ∈ s, F i e) f e = ∑ i ∈ s, coordSum (F i) f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih =>
    simp only [coordSum, ih, Finset.mul_sum, ← Finset.sum_add_distrib]

/-! ## §2 Iterated coefficient sums over open coordinates -/

theorem msum_congr (d : ℕ) (fs : Fin d → List K) (F G : (Fin d → ℕ) → K) (h : ∀ e, F e = G e) :
    msum d fs F = msum d fs G := by
  have : F = G := funext h
  subst this; rfl

theorem msum_add (d : ℕ) (fs : Fin d → List K) (F G : (Fin d → ℕ) → K) :
    msum d fs (fun e => F e + G e) = msum d fs F + msum d fs G := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [msum]
    rw [← coordSum_add'']
    exact coordSum_congr'' _ _ (fun e₀ => ih _ _ _) _ _

theorem msum_mul (d : ℕ) (fs : Fin d → List K) (a : K) (F : (Fin d → ℕ) → K) :
    msum d fs (fun e => a * F e) = a * msum d fs F := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [msum]
    rw [← coordSum_mul'']
    exact coordSum_congr'' _ _ (fun e₀ => ih _ _) _ _

theorem msum_zero (d : ℕ) (fs : Fin d → List K) : msum d fs (fun _ => (0 : K)) = 0 := by
  have := msum_mul d fs 0 (fun _ => 0)
  simpa using this

theorem msum_finsetSum {ι : Type*} (s : Finset ι) (d : ℕ) (fs : Fin d → List K)
    (F : ι → (Fin d → ℕ) → K) :
    msum d fs (fun e => ∑ i ∈ s, F i e) = ∑ i ∈ s, msum d fs (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using msum_zero d fs
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [msum_add, ih]

theorem msum_coordSum (d : ℕ) (fs : Fin d → List K) (G : (Fin d → ℕ) → ℕ → K) (ψ : List K) :
    msum d fs (fun e => coordSum (G e) ψ 0) = coordSum (fun a => msum d fs (fun e => G e a)) ψ 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [msum]
    rw [coordSum_congr'' _ _ (fun e₀ => ih _ _) _ _]
    exact coordSum_comm _ _ _ _ _

theorem msum_cons (d : ℕ) (ψ : List K) (fs : Fin d → List K) (F : (Fin (d + 1) → ℕ) → K) :
    msum (d + 1) (Fin.cons ψ fs) F = coordSum (fun a => msum d fs (fun e => F (Fin.cons a e))) ψ 0 := by
  simp only [msum, Fin.cons_zero, Fin.cons_succ]

/-- Merging a polynomial `ψ` into the open coordinate `j`. -/
theorem msum_update_lpMul (d : ℕ) (fs : Fin d → List K) (j : Fin d) (ψ : List K)
    (F : (Fin d → ℕ) → K) :
    msum d (Function.update fs j (lpMul (fs j) ψ)) F =
      msum d fs (fun e => coordSum (fun a => F (Function.update e j (e j + a))) ψ 0) := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [msum, Function.update_self]
      have h1 : (fun i : Fin d => Function.update fs 0 (lpMul (fs 0) ψ) i.succ) = fun i => fs i.succ :=
        funext fun i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
      rw [h1, coordSum_lpMul]
      refine coordSum_congr'' _ _ (fun e₀ => ?_) _ _
      rw [coordSum_shift0, msum_coordSum]
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      refine msum_congr _ _ _ _ (fun e => ?_)
      simp only [Fin.cons_zero, Fin.update_cons_zero]
    · simp only [msum]
      have h0 : Function.update fs j.succ (lpMul (fs j.succ) ψ) 0 = fs 0 :=
        Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
      have h1 : (fun i : Fin d => Function.update fs j.succ (lpMul (fs j.succ) ψ) i.succ) =
          Function.update (fun i => fs i.succ) j (lpMul (fs j.succ) ψ) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne (fun h => hij (Fin.succ_injective _ h)),
            Function.update_of_ne hij]
      rw [h0, h1]
      refine coordSum_congr'' _ _ (fun e₀ => ?_) _ _
      rw [ih (fun i => fs i.succ) j]
      refine msum_congr _ _ _ _ (fun e => ?_)
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      simp only [Fin.cons_succ, Fin.cons_update]

end Algebra

section Spec

variable {K : Type*} [Field K] [LinearOrder K]

theorem msOf_cons {d : ℕ} (c' : Fin 3) (c : Fin d → Fin 3) (a : ℕ) (e : Fin d → ℕ) :
    msOf (Fin.cons c' c : Fin (d + 1) → Fin 3) (Fin.cons a e) = (c', a) ::ₘ msOf c e := by
  simp only [msOf, Fin.univ_succ, Finset.cons_val, Multiset.map_cons, Fin.cons_zero,
    Finset.map_val, Multiset.map_map, Function.comp_def, Function.Embedding.coeFn_mk, Fin.cons_succ]

theorem msOf_zero (c : Fin 0 → Fin 3) (e : Fin 0 → ℕ) : msOf c e = 0 := by
  simp [msOf]

omit [LinearOrder K] in
/-- The base: `stateVal` is the iterated coefficient sum of `∏ e! · M(A + rough, B + smooth)`. -/
theorem stateVal_eq_msum (M : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal M d c fs A B = msum d fs (fun e => (∏ j, ((e j).factorial : K)) *
        M (A + ∑ j, roughPart (c j) (e j)) (B + ∑ j, smoothPart (c j) (e j))) := by
  intro d
  induction d with
  | zero => intro c fs A B; simp [stateVal, msum]
  | succ d ih =>
    intro c fs A B
    simp only [stateVal, msum]
    refine coordSum_congr'' _ _ (fun e₀ => ?_) _ _
    rw [ih, ← msum_mul]
    refine msum_congr _ _ _ _ (fun e => ?_)
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
    ring

omit [LinearOrder K] in
theorem msVal_nil_msOf (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) {d : ℕ} (c : Fin d → Fin 3)
    (e : Fin d → ℕ) :
    msVal M n [] (msOf c e) = (∏ j, ((e j).factorial : K)) *
      M (0 + ∑ j, roughPart (c j) (e j)) (0 + ∑ j, smoothPart (c j) (e j)) := by
  simp only [msVal, msOf, Multiset.map_map, Function.comp_def, zero_add]
  rfl

theorem msOf_erase {d : ℕ} (c : Fin d → Fin 3) (e : Fin d → ℕ) (j : Fin d) :
    (msOf c e).erase (c j, e j) = ((Finset.univ : Finset (Fin d)).val.erase j).map
      fun i => (c i, e i) := by
  rw [msOf, Multiset.map_erase_of_mem _ _ (Finset.mem_univ j)]

theorem msOf_update {d : ℕ} (c : Fin d → Fin 3) (e : Fin d → ℕ) (j : Fin d) (v : ℕ) :
    (c j, v) ::ₘ ((Finset.univ : Finset (Fin d)).val.erase j).map (fun i => (c i, e i)) =
      msOf c (Function.update e j v) := by
  rw [msOf]
  conv_rhs => rw [← Multiset.cons_erase (Finset.mem_univ_val j)]
  rw [Multiset.map_cons, Function.update_self]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  have hij : i ≠ j := by
    intro h; subst h
    exact (Multiset.Nodup.notMem_erase Finset.univ.nodup) hi
  rw [Function.update_of_ne hij]

theorem msOf_countP {d : ℕ} (c : Fin d → Fin 3) (e : Fin d → ℕ) (c' : Fin 3) :
    (msOf c e).countP (fun x => x.1 = c') = (Finset.univ.filter fun j => c j = c').card := by
  rw [msOf, Multiset.countP_map, Finset.card, Finset.filter_val]

omit [LinearOrder K] in
theorem msOf_mergeSum {d : ℕ} (c : Fin d → Fin 3) (e : Fin d → ℕ) (F : SPart → Multiset SPart → K) :
    ((msOf c e).map fun x => F x ((msOf c e).erase x)).sum =
      ∑ j, F (c j, e j) (((Finset.univ : Finset (Fin d)).val.erase j).map fun i => (c i, e i)) := by
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [msOf]
  rw [Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun j _ => ?_
  exact congrArg _ (msOf_erase c e j)

omit [LinearOrder K] in
/-- **Placement as an iterated coefficient sum of the multiset-state value.** -/
theorem placeVal_eq_msum (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (rest : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal M n d c fs rest = msum d fs (fun e => msVal M n rest (msOf c e)) := by
  intro rest
  induction rest with
  | nil =>
    intro d c fs
    rw [placeVal, stateVal_eq_msum]
    exact msum_congr _ _ _ _ fun e => (msVal_nil_msOf M n c e).symm
  | cons φ rest ih =>
    intro d c fs
    rw [placeVal]
    simp only [ih]
    simp only [msum_update_lpMul, msum_cons, ← msum_coordSum, ← msum_mul, ← msum_finsetSum,
      ← msum_add]
    refine msum_congr _ _ _ _ fun e => ?_
    rw [msVal, msOf_mergeSum c e (fun x m =>
      coordSum (fun a => msVal M n rest ((x.1, x.2 + a) ::ₘ m)) (φ x.1) 0)]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      rw [msOf_update]
    · refine Finset.sum_congr rfl fun c' _ => ?_
      rw [msOf_countP]
      congr 1
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      rw [msOf_cons]

omit [LinearOrder K] in
/-- **V2i's placement value from no open coordinate is the multiset-state value of the empty
state.** -/
theorem placeVal_eq_msVal (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = msVal M n φs 0 := by
  rw [placeVal_eq_msum]
  simp only [msum, msOf_zero]

/-! ## §4 Parts of exponent zero -/

/-! ## §4 Parts of exponent zero -/

omit [LinearOrder K] in
/-- A part of exponent `0` can be removed: `m̃_{ν ∪ (0)} = (n_c − ℓ) m̃_ν`, whose weight was
applied when the part opened. -/
theorem msVal_zero_part (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (rest : List (Fin 3 → List K)) (S : Multiset SPart) (c : Fin 3),
      msVal M n rest ((c, 0) ::ₘ S) = msVal M n rest S := by
  intro rest
  induction rest with
  | nil =>
    intro S c
    simp [msVal, roughPart, smoothPart]
  | cons φ rest ih =>
    intro S c
    rw [msVal, msVal, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    simp only [zero_add]
    have hm : (S.map fun x => coordSum (fun a => msVal M n rest ((x.1, x.2 + a) ::ₘ
        ((c, 0) ::ₘ S).erase x)) (φ x.1) 0) = (S.map fun x => coordSum (fun a =>
          msVal M n rest ((x.1, x.2 + a) ::ₘ S.erase x)) (φ x.1) 0) := by
      refine Multiset.map_congr rfl fun x hx => ?_
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      rw [Multiset.erase_cons_tail_of_mem hx, Multiset.cons_swap, ih]
    have ho : ∀ c' : Fin 3, coordSum (fun a => msVal M n rest ((c', a) ::ₘ (c, 0) ::ₘ S)) (φ c') 0 =
        coordSum (fun a => msVal M n rest ((c', a) ::ₘ S)) (φ c') 0 := by
      intro c'
      refine coordSum_congr'' _ _ (fun a => ?_) _ _
      rw [Multiset.cons_swap, ih]
    rw [hm]
    simp only [ho, Multiset.countP_cons, Fin.sum_univ_three]
    fin_cases c <;> simp <;> ring

end Spec

/-! ## §5 The canonical evaluator -/

section Eval

variable {K : Type*} [Field K] [LinearOrder K]

theorem sIns_coe (y : SPart) (l : SKey) : ((sIns y l : SKey) : Multiset SPart) = y ::ₘ (l : Multiset SPart) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [sIns]
    split_ifs
    · rfl
    · rw [← Multiset.cons_coe, ih, ← Multiset.cons_coe, Multiset.cons_swap]

omit [LinearOrder K] in
theorem picks_sum {α : Type*} [DecidableEq α] (l : List α) (F : α → Multiset α → K) :
    (((l : Multiset α)).map fun x => F x ((l : Multiset α).erase x)).sum =
      ((picks l).map fun p => F p.1 (p.2 : Multiset α)).sum := by
  induction l generalizing F with
  | nil => simp [picks]
  | cons x t ih =>
    rw [← Multiset.cons_coe, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    have h1 : ((t : Multiset α).map fun y => F y ((x ::ₘ (t : Multiset α)).erase y)) =
        ((t : Multiset α).map fun y => F y (x ::ₘ (t : Multiset α).erase y)) :=
      Multiset.map_congr rfl fun y hy => by rw [Multiset.erase_cons_tail_of_mem hy]
    have h2 := ih (fun y m => F y (x ::ₘ m))
    rw [h1, h2]
    simp [picks, List.map_map, Function.comp_def, Multiset.cons_coe]

omit [LinearOrder K] in
theorem cterms_sum (F : ℕ → K) (f : List K) (e : ℕ) :
    ((cterms f e).map fun p => p.2 * F p.1).sum = coordSum F f e := by
  induction f generalizing e with
  | nil => rfl
  | cons c f ih => simp [cterms, coordSum, ih]

theorem filter_ne_zero_sum (l : List (ℕ × K)) (G : ℕ → K) :
    ((l.filter fun p => p.2 ≠ 0).map fun p => p.2 * G p.1).sum = (l.map fun p => p.2 * G p.1).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : p.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.map_cons, List.sum_cons, h, zero_mul, zero_add, ih]
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.sum_cons, ih]

/-- A coefficient sum splits into the constant term and the nonzero terms of positive degree. -/
theorem coordSum_split (F : ℕ → K) (f : List K) :
    coordSum F f 0 = constTerm f * F 0 + ((posTerms f).map fun p => p.2 * F p.1).sum := by
  cases f with
  | nil => simp [coordSum, constTerm, posTerms]
  | cons c f => simp only [coordSum, constTerm, posTerms, filter_ne_zero_sum, cterms_sum]

omit [LinearOrder K] in
theorem sum_class (S : Multiset SPart) (h : Fin 3 → K) :
    (S.map fun x => h x.1).sum = ∑ c : Fin 3, ((S.countP fun x => x.1 = c : ℕ) : K) * h c := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons y S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    simp only [Multiset.countP_cons, Fin.sum_univ_three]
    rcases y with ⟨y₁, y₂⟩
    fin_cases y₁ <;> simp <;> ring

theorem clsCnt_eq (k : SKey) (c : Fin 3) :
    clsCnt k c = (k : Multiset SPart).countP fun x => x.1 = c := by
  rw [clsCnt, Multiset.coe_countP]
  congr 1
  funext x
  exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, decide_eq_true_iff, Fin.val_inj])

theorem partCmp_eq (x y : SPart) (h : partCmp x y = .eq) : x = y := by
  unfold partCmp at h
  split_ifs at h with h1 h2 h3 h4
  exact Prod.ext (Fin.ext (by omega)) (by omega)

theorem keyCmp_eq (a b : SKey) (h : keyCmp a b = .eq) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [keyCmp]
  | cons x l ih =>
    cases b with
    | nil => simp [keyCmp] at h
    | cons y m =>
      simp only [keyCmp] at h
      cases hc : partCmp x y with
      | lt => simp [hc] at h
      | gt => simp [hc] at h
      | eq =>
        simp only [hc] at h
        rw [partCmp_eq x y hc, ih m h]

omit [LinearOrder K] in
theorem flatMap_map_sum {α β : Type*} (l : List α) (f : α → List β) (g : β → K) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

omit [LinearOrder K] in
theorem pairSums_sum (l : List K) : (pairSums l).sum = l.sum := by
  induction l using pairSums.induct with
  | case1 a b rest ih => rw [pairSums, List.sum_cons, ih, List.sum_cons, List.sum_cons, add_assoc]
  | case2 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · exact absurd rfl (h a b rest)

omit [LinearOrder K] in
theorem bsumAux_eq : ∀ (fuel : ℕ) (l : List K), bsumAux fuel l = l.sum := by
  intro fuel
  induction fuel with
  | zero => intro l; rfl
  | succ fuel ih =>
    intro l
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · simp [bsumAux]
    · rw [bsumAux, ih, pairSums_sum]

omit [LinearOrder K] in
/-- Balanced summation is summation. -/
theorem bsum_eq (l : List K) : bsum l = l.sum := bsumAux_eq 64 l

/-- **One step** of the canonical evaluator is one factor of the specification. -/
theorem symStep_val (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (φ : Fin 3 → List K) (p : SKey × K) :
    ((symStep n φ p).map fun q => q.2 * msVal M n rest (q.1 : Multiset SPart)).sum =
      p.2 * msVal M n (φ :: rest) (p.1 : Multiset SPart) := by
  obtain ⟨k, κ⟩ := p
  have h1 : ∀ x ∈ (k : Multiset SPart), coordSum (fun a => msVal M n rest ((x.1, x.2 + a) ::ₘ (k : Multiset SPart).erase x)) (φ x.1) 0 =
      constTerm (φ x.1) * msVal M n rest (k : Multiset SPart) + ((posTerms (φ x.1)).map fun ac =>
        ac.2 * msVal M n rest ((x.1, x.2 + ac.1) ::ₘ (k : Multiset SPart).erase x)).sum := by
    intro x hx
    rw [coordSum_split]
    simp only [add_zero, Prod.mk.eta, Multiset.cons_erase hx]
  have h2 : ∀ c : Fin 3, coordSum (fun a => msVal M n rest ((c, a) ::ₘ (k : Multiset SPart))) (φ c) 0 =
      constTerm (φ c) * msVal M n rest (k : Multiset SPart) + ((posTerms (φ c)).map fun ac =>
        ac.2 * msVal M n rest ((c, ac.1) ::ₘ (k : Multiset SPart))).sum := by
    intro c
    rw [coordSum_split, msVal_zero_part]
  have hm := picks_sum k (fun x m => ((posTerms (φ x.1)).map fun ac =>
    ac.2 * msVal M n rest ((x.1, x.2 + ac.1) ::ₘ m)).sum)
  rw [msVal, Multiset.map_congr rfl h1, Multiset.sum_map_add,
    sum_class (k : Multiset SPart) (fun c => constTerm (φ c) * msVal M n rest (k : Multiset SPart)), hm]
  by_cases hT : (n 0 : K) * constTerm (φ 0) + (n 1 : K) * constTerm (φ 1) +
      (n 2 : K) * constTerm (φ 2) = 0
  · rw [symStep, ite_eq_left_of_eq_true _ _ (eq_true hT)]
    simp only [h2, List.nil_append, List.map_append, List.sum_append,
      flatMap_map_sum, List.map_map, Function.comp_def, sIns_coe, clsCnt_eq, mul_assoc,
      List.sum_map_mul_left, Fin.sum_univ_three, List.map_cons, List.sum_cons, List.map_nil,
      List.sum_nil]
    linear_combination (-(κ * msVal M n rest (k : Multiset SPart))) * hT
  · rw [symStep, ite_eq_right_of_eq_false _ _ (eq_false hT)]
    simp only [h2, List.singleton_append, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, flatMap_map_sum, List.map_map, Function.comp_def, sIns_coe, clsCnt_eq,
      mul_assoc, List.sum_map_mul_left, Fin.sum_univ_three, List.map_nil, List.sum_nil]
    ring

section MergeVal

variable {α : Type*} (cmp : α → α → Ordering) (hcmp : ∀ a b, cmp a b = .eq → a = b)
  (F : α → K)

/-- **Definition.** The value `Σ κ · F(key)` of a combination. -/
def valBy (L : List (α × K)) : K := (L.map fun q => q.2 * F q.1).sum

include hcmp in
omit [LinearOrder K] in
theorem mergeGo_val (a : α × K) (l₁ : List (α × K)) (rec : List (α × K) → List (α × K))
    (hrec : ∀ l, valBy F (rec l) = valBy F l₁ + valBy F l) :
    ∀ l₂, valBy F (mergeGo cmp a l₁ rec l₂) = a.2 * F a.1 + valBy F l₁ + valBy F l₂ := by
  intro l₂
  induction l₂ with
  | nil => simp [mergeGo, valBy]
  | cons b l₂ ih =>
    cases h : cmp a.1 b.1
    · simp only [mergeGo, h]
      simp only [valBy, List.map_cons, List.sum_cons] at hrec ih ⊢
      rw [hrec, List.map_cons, List.sum_cons]; ring
    · simp only [mergeGo, h]
      have hab := hcmp _ _ h
      simp only [valBy, List.map_cons, List.sum_cons] at hrec ih ⊢
      rw [hrec, hab]; ring
    · simp only [mergeGo, h]
      simp only [valBy, List.map_cons, List.sum_cons] at hrec ih ⊢
      rw [ih]; ring

include hcmp in
omit [LinearOrder K] in
theorem mergeT_val : ∀ l₁ l₂ : List (α × K), valBy F (mergeT cmp l₁ l₂) = valBy F l₁ + valBy F l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [mergeT, valBy]
  | cons a l₁ ih =>
    intro l₂
    rw [mergeT, mergeGo_val cmp hcmp F a l₁ _ ih]
    simp [valBy]

include hcmp in
omit [LinearOrder K] in
theorem mergePairs_val (rs : List (List (α × K))) :
    ((mergePairs cmp rs).map (valBy F)).sum = (rs.map (valBy F)).sum := by
  induction rs using mergePairs.induct with
  | case1 a b rest ih =>
    rw [mergePairs, List.map_cons, List.sum_cons, ih, mergeT_val cmp hcmp]
    simp only [List.map_cons, List.sum_cons]
    ring
  | case2 rs h =>
    rcases rs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · exact absurd rfl (h a b rest)

include hcmp in
omit [LinearOrder K] in
theorem mergeAll_val : ∀ (fuel : ℕ) (rs : List (List (α × K))),
    valBy F (mergeAll cmp fuel rs) = (rs.map (valBy F)).sum := by
  intro fuel
  induction fuel with
  | zero =>
    intro rs
    induction rs with
    | nil => rfl
    | cons a rs ih =>
      simp only [mergeAll, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [mergeT_val cmp hcmp, ih]
  | succ fuel ih =>
    intro rs
    rcases rs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · simp [mergeAll]
    · rw [mergeAll, ih, mergePairs_val cmp hcmp]

include hcmp in
omit [LinearOrder K] in
/-- **Sorting and merging preserves the value** of a combination. -/
theorem normalizeBy_val (L : List (α × K)) : valBy F (normalizeBy cmp L) = valBy F L := by
  rw [normalizeBy, mergeAll_val cmp hcmp, List.map_map]
  simp only [valBy, Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

end MergeVal

omit [LinearOrder K] in
theorem normalize_val (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (L : List (SKey × K)) : symVal M n rest (normalize L) = symVal M n rest L :=
  normalizeBy_val keyCmp keyCmp_eq (fun k => msVal M n rest (k : Multiset SPart)) L

theorem symRun_val (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)), symFinal M (symRun n φs L) = symVal M n φs L := by
  intro φs
  induction φs with
  | nil =>
    intro L
    simp only [symRun, symFinal, symVal, bsum_eq]
    congr 1
  | cons φ rest ih =>
    intro L
    rw [symRun, ih, normalize_val]
    simp only [symVal, flatMap_map_sum]
    congr 1
    exact List.map_congr_left fun p _ => symStep_val M n rest φ p

/-! ## §6 Main theorems -/

/-- **The symmetric-function evaluator equals V2i's placement recursion.** -/
theorem symPlaceVal_eq (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    symPlaceVal M n φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs := by
  rw [placeVal_eq_msVal, symPlaceVal, symRun_val]
  simp [symVal]

/-- **Piece values agree for every moment oracle.** -/
theorem genPieceSym_eq (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ)
    (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceSym N r k g Mo a₁ l₁ a₂ l₂ = genPieceWith N r k g Mo a₁ l₁ a₂ l₂ := by
  simp only [genPieceSym, genPieceWith, symPlaceVal_eq]

/-- **Entry values agree.** -/
theorem genEntrySym_eq (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    genEntrySym N g L τ C a₁ l₁ a₂ l₂ = genEntryVal N g L τ C a₁ l₁ a₂ l₂ := by
  simp only [genEntrySym, genEntryVal, genRow, genPiece, genPieceSym_eq]

/-- **V2j's collapsed coefficients through the symmetric-function evaluator.** -/
theorem aggCoeff_eq_sym (N r k : ℕ) (g : K) (ws : List (WPair K)) (s : MKey) :
    aggCoeff N r k g ws s =
      (ws.map fun w => w.1 * genPieceSym N r k g (delta s) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  simp only [aggCoeff, genPieceSym_eq]

/-! ## §7 Transition to the augmented monomial basis and the Dirichlet moment -/

omit [LinearOrder K] in
theorem picks_coe {α : Type*} (l : List α) :
    ∀ p ∈ picks l, p.1 ::ₘ (p.2 : Multiset α) = (l : Multiset α) := by
  induction l with
  | nil => simp [picks]
  | cons x t ih =>
    intro p hp
    simp only [picks, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · rfl
    · rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.cons_swap, ih q hq]

theorem clsCnt_cons (y : SPart) (k : SKey) (c : Fin 3) :
    clsCnt (sIns y k) c = clsCnt k c + if y.1 = c then 1 else 0 := by
  rw [clsCnt_eq, clsCnt_eq, sIns_coe, Multiset.countP_cons]

theorem clsCnt_merge (k : SKey) (xr : SPart × SKey) (hxr : xr ∈ picks k) (a : ℕ) (c : Fin 3) :
    clsCnt (sIns (xr.1.1, xr.1.2 + a) xr.2) c = clsCnt k c := by
  rw [clsCnt_eq, clsCnt_eq, sIns_coe, ← picks_coe k xr hxr, Multiset.countP_cons,
    Multiset.countP_cons]

omit [LinearOrder K] in
theorem descFactorial_succ_cast (m l : ℕ) :
    ((m.descFactorial (l + 1) : ℕ) : K) = ((m : K) - (l : K)) * (m.descFactorial l : K) := by
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  by_cases h : l ≤ m
  · rw [Nat.cast_sub h]
  · have h0 : m.descFactorial l = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

omit [LinearOrder K] in
theorem fallW_merge (n : Fin 3 → ℕ) (k : SKey) (xr : SPart × SKey) (hxr : xr ∈ picks k) (a : ℕ) :
    fallW (K := K) n (sIns (xr.1.1, xr.1.2 + a) xr.2) = fallW n k := by
  simp only [fallW, clsCnt_merge k xr hxr]

omit [LinearOrder K] in
theorem fallW_open (n : Fin 3 → ℕ) (k : SKey) (c : Fin 3) (a : ℕ) :
    fallW (K := K) n (sIns (c, a) k) = ((n c : K) - (clsCnt k c : K)) * fallW n k := by
  have key : ∀ m l : ℕ, ((m - l : ℕ) : K) * (m.descFactorial l : K) =
      ((m : K) - (l : K)) * (m.descFactorial l : K) := by
    intro m l
    have := descFactorial_succ_cast (K := K) m l
    rwa [Nat.descFactorial_succ, Nat.cast_mul] at this
  simp only [fallW, clsCnt_cons]
  fin_cases c <;> simp <;> rw [key] <;> ring

omit [LinearOrder K] in
theorem fallW_nil (n : Fin 3 → ℕ) : fallW (K := K) n [] = 1 := by
  simp [fallW, clsCnt]

omit [LinearOrder K] in
theorem flatMap_congr_mem {α β : Type*} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem symStep_scale (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (p : SKey × K) :
    symStep n φ (scaleQ n p) = (symStep1 n φ p).map (scaleQ n) := by
  obtain ⟨k, κ⟩ := p
  have hM : ((picks k).flatMap fun xr => (posTerms (φ xr.1.1)).map fun ac =>
      (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, κ * fallW n k * ac.2)) =
      ((picks k).flatMap fun xr => (posTerms (φ xr.1.1)).map fun ac =>
        (sIns (xr.1.1, xr.1.2 + ac.1) xr.2, κ * ac.2)).map (scaleQ n) := by
    rw [List.map_flatMap]
    refine flatMap_congr_mem _ _ _ fun xr hxr => ?_
    rw [List.map_map]
    refine List.map_congr_left fun ac _ => ?_
    simp only [Function.comp_apply, scaleQ, fallW_merge n k xr hxr]
    ext <;> simp; ring
  have hO : (([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
      (sIns (c, ac.1) k, κ * fallW n k * ((n c : K) - (clsCnt k c : K)) * ac.2)) =
      (([0, 1, 2] : List (Fin 3)).flatMap fun c => (posTerms (φ c)).map fun ac =>
        (sIns (c, ac.1) k, κ * ac.2)).map (scaleQ n) := by
    rw [List.map_flatMap]
    refine flatMap_congr_mem _ _ _ fun c _ => ?_
    rw [List.map_map]
    refine List.map_congr_left fun ac _ => ?_
    simp only [Function.comp_apply, scaleQ, fallW_open]
    ext <;> simp; ring
  show symStep n φ (k, κ * fallW n k) = (symStep1 n φ (k, κ)).map (scaleQ n)
  simp only [symStep, symStep1]
  split_ifs with hT
  · simp only [List.nil_append, List.map_append]
    rw [hM, hO]
  · simp only [List.cons_append, List.nil_append, List.map_cons, List.map_append]
    rw [hM, hO]
    simp only [scaleQ, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    ring

section MergeScale

variable {α : Type*} (cmp : α → α → Ordering) (hcmp : ∀ a b, cmp a b = .eq → a = b) (w : α → K)

/-- **Definition.** Multiply each coefficient by a weight of its key. -/
def scaleBy (q : α × K) : α × K := (q.1, q.2 * w q.1)

include hcmp in
omit [LinearOrder K] in
theorem mergeGo_scale (a : α × K) (l₁ : List (α × K)) (rec rec' : List (α × K) → List (α × K))
    (hrec : ∀ l, rec' (l.map (scaleBy w)) = (rec l).map (scaleBy w)) :
    ∀ l₂, mergeGo cmp (scaleBy w a) (l₁.map (scaleBy w)) rec' (l₂.map (scaleBy w)) =
      (mergeGo cmp a l₁ rec l₂).map (scaleBy w) := by
  intro l₂
  induction l₂ with
  | nil => rfl
  | cons b l₂ ih =>
    have hk : cmp (scaleBy w a).1 (scaleBy w b).1 = cmp a.1 b.1 := rfl
    rw [List.map_cons]
    cases h : cmp a.1 b.1
    · simp only [mergeGo, hk, h, List.map_cons]
      rw [← List.map_cons, hrec]
    · simp only [mergeGo, hk, h, List.map_cons]
      have hab := hcmp _ _ h
      rw [hrec]
      congr 1
      simp only [scaleBy, hab]
      ext <;> simp; ring
    · simp only [mergeGo, hk, h, List.map_cons]
      rw [ih]

include hcmp in
omit [LinearOrder K] in
theorem mergeT_scale : ∀ l₁ l₂ : List (α × K), mergeT cmp (l₁.map (scaleBy w)) (l₂.map (scaleBy w)) =
    (mergeT cmp l₁ l₂).map (scaleBy w) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons a l₁ ih =>
    intro l₂
    rw [List.map_cons, mergeT, mergeT]
    exact mergeGo_scale cmp hcmp w a l₁ _ _ ih l₂

include hcmp in
omit [LinearOrder K] in
theorem mergePairs_scale (rs : List (List (α × K))) :
    mergePairs cmp (rs.map (List.map (scaleBy w))) = (mergePairs cmp rs).map (List.map (scaleBy w)) := by
  induction rs using mergePairs.induct with
  | case1 a b rest ih =>
    simp only [List.map_cons, mergePairs]
    rw [mergeT_scale cmp hcmp, ih]
  | case2 rs h =>
    rcases rs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · exact absurd rfl (h a b rest)

include hcmp in
omit [LinearOrder K] in
theorem mergeAll_scale : ∀ (fuel : ℕ) (rs : List (List (α × K))),
    mergeAll cmp fuel (rs.map (List.map (scaleBy w))) = (mergeAll cmp fuel rs).map (scaleBy w) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rs
    induction rs with
    | nil => rfl
    | cons a rs ih =>
      simp only [mergeAll, List.foldr_cons, List.map_cons] at ih ⊢
      rw [ih, mergeT_scale cmp hcmp]
  | succ fuel ih =>
    intro rs
    rcases rs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · simp only [List.map_cons, mergeAll]
      rw [← List.map_cons, ← List.map_cons, mergePairs_scale cmp hcmp, ih]

include hcmp in
omit [LinearOrder K] in
/-- **Sorting and merging commutes with key-dependent weights.** -/
theorem normalizeBy_scale (L : List (α × K)) :
    normalizeBy cmp (L.map (scaleBy w)) = (normalizeBy cmp L).map (scaleBy w) := by
  rw [normalizeBy, normalizeBy, ← mergeAll_scale cmp hcmp, List.map_map, List.map_map]
  rfl

end MergeScale

omit [LinearOrder K] in
theorem normalize_scale (n : Fin 3 → ℕ) (L : List (SKey × K)) :
    normalize (L.map (scaleQ n)) = (normalize L).map (scaleQ n) :=
  normalizeBy_scale keyCmp keyCmp_eq (fallW n) L

/-- **The index-count weights factor out**: running with the weights `n_c − ℓ(ν_c)` is running in
the augmented monomial basis and multiplying each state by `∏_c (n_c)_{ℓ(ν_c)}`. -/
theorem symRun_scale (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)),
      symRun n φs (L.map (scaleQ n)) = (symRun1 n φs L).map (scaleQ n) := by
  intro φs
  induction φs with
  | nil => intro L; rfl
  | cons φ rest ih =>
    intro L
    rw [symRun, symRun1, List.flatMap_map]
    simp only [symStep_scale]
    rw [← List.map_flatMap, normalize_scale, ih]

/-- **Dirichlet-weighted moment formula.** The placement value of any product of
class-dependent power sums is `Σ_ν R_ν · monoMoment ν`, with `R_ν` the coefficients of the
product in the augmented monomial basis and `monoMoment ν = ∏_c (n_c)_{ℓ(ν_c)} ∏ νᵢ! M(A, B)`. -/
theorem symPlaceVal_eq_trans (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    symPlaceVal M n φs = ((symRun1 n φs [([], 1)]).map fun q => q.2 * monoMoment M n q.1).sum := by
  have h0 : ([([], 1)] : List (SKey × K)) = [([], 1)].map (scaleQ n) := by
    simp [scaleQ, fallW_nil]
  conv_lhs => rw [symPlaceVal, h0, symRun_scale, symFinal, bsum_eq, List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, scaleQ, monoMoment]
  ring

theorem placeVal_eq_trans (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs =
      ((symRun1 n φs [([], 1)]).map fun q => q.2 * monoMoment M n q.1).sum := by
  rw [← symPlaceVal_eq, symPlaceVal_eq_trans]

omit [LinearOrder K] in
/-- `psFactor c a` is the class power sum `p_{c,a}`: its polynomial on class `c'` is `y^a` if
`c' = c`, else `0`. -/
theorem lpEval_psFactor (c c' : Fin 3) (a : ℕ) (y : K) :
    lpEval (psFactor c a c') y = if c' = c then y ^ a else 0 := by
  unfold psFactor
  split_ifs
  · induction a with
    | zero => simp [lpEval]
    | succ a ih =>
      simp only [List.replicate_succ, List.cons_append, lpEval, List.foldr_cons] at ih ⊢
      rw [ih]; ring
  · rfl

theorem symStep1_indep (n n' : Fin 3 → ℕ) (φ : Fin 3 → List K) (h : ∀ c, constTerm (φ c) = 0)
    (p : SKey × K) : symStep1 n φ p = symStep1 n' φ p := by
  simp only [symStep1, h, mul_zero, add_zero]

theorem symRun1_indep (n n' : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)), (∀ φ ∈ φs, ∀ c, constTerm (φ c) = 0) →
      ∀ L : List (SKey × K), symRun1 n φs L = symRun1 n' φs L := by
  intro φs
  induction φs with
  | nil => intro _ L; rfl
  | cons φ rest ih =>
    intro h L
    have hφ := h φ List.mem_cons_self
    simp only [symRun1]
    rw [show L.flatMap (symStep1 n φ) = L.flatMap (symStep1 n' φ) from
      congrArg L.flatMap (funext fun p => symStep1_indep n n' φ hφ p)]
    exact ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)) _

omit [LinearOrder K] in
theorem constTerm_psFactor (c c' : Fin 3) (a : ℕ) (ha : 0 < a) :
    constTerm (K := K) (psFactor c a c') = 0 := by
  unfold psFactor
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt ha
  split_ifs <;> simp [constTerm, List.replicate_succ]

/-- **The transition coefficients `R_{α,ν}` do not depend on the class sizes** (all parts of `α`
positive). -/
theorem psTrans_indep (n n' : Fin 3 → ℕ) (α : List SPart) (hα : ∀ x ∈ α, 0 < x.2) :
    psTrans (K := K) n α = psTrans n' α := by
  refine symRun1_indep n n' _ ?_ _
  intro φ hφ c
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
  exact constTerm_psFactor _ _ _ (hα x hx)

/-- **Products of class power sums.** `∫ p_α = Σ_ν R_{α,ν} · monoMoment ν` against any moment
oracle, with V2i's placement value on the left. -/
theorem placeVal_psTrans (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (α : List SPart) :
    placeVal M n 0 Fin.elim0 Fin.elim0 (α.map fun x => psFactor x.1 x.2) =
      ((psTrans n α).map fun q => q.2 * monoMoment M n q.1).sum :=
  placeVal_eq_trans M n _

/-! ## §8 Moment-coefficient tables -/

theorem mkeyCmp_eq (s t : MKey) (h : mkeyCmp s t = .eq) : s = t := by
  rcases s with ⟨a, b, c, d⟩
  rcases t with ⟨a', b', c', d'⟩
  unfold mkeyCmp at h
  simp only at h
  split_ifs at h
  simp only [Prod.mk.injEq]
  omega

omit [LinearOrder K] in
theorem valBy_flatMap {α β : Type*} (F : α → K) (l : List β) (f : β → List (α × K)) :
    valBy F (l.flatMap f) = (l.map fun x => valBy F (f x)).sum := by
  simp only [valBy, flatMap_map_sum]

/-- **All moment coefficients of a piece from one evaluation**: V2i's piece value is the table
`genTable` evaluated against the moment oracle, for every oracle. -/
theorem genPieceWith_eq_table (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (genTable N r k g a₁ l₁ a₂ l₂) Mo := by
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  rw [hT, genTable, normalizeBy_val mkeyCmp mkeyCmp_eq, genPieceWith, valBy_flatMap]
  congr 1
  refine List.map_congr_left fun t₁ _ => ?_
  rw [valBy_flatMap]
  congr 1
  refine List.map_congr_left fun t₂ _ => ?_
  rw [← symPlaceVal_eq, symPlaceVal, symFinal, bsum_eq, valBy, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, keyW, keyA, keyB, factW]
  ring

/-- **Weighted pairs**: `Σ_{w ∈ ws} w · genPieceWith … = tableVal (aggTable …)`. -/
theorem aggTable_eq (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (aggTable N r k g ws) Mo := by
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  rw [hT, aggTable, normalizeBy_val mkeyCmp mkeyCmp_eq, valBy_flatMap]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  rw [genPieceWith_eq_table, hT, valBy, valBy, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply]
  ring

/-- **The entry from the tables of its pieces.** -/
theorem genEntryVal_eq_table (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    genEntryVal N g L τ C a₁ l₁ a₂ l₂ = (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
      ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
        tableVal (genTable N r k g a₁ l₁ a₂ l₂) (fun A B m n => pieceMn N r k A B g L τ C m n) := by
  simp only [genEntryVal, genRow, genPiece, genPieceWith_eq_table]

end Eval

/-- **`J_T[G_{a₁,λ₁}, G_{a₂,λ₂}]` by the symmetric-function evaluator** (every `N ≥ 1`,
admissible data). -/
theorem jT_eq_genEntrySym {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (hC1 : g ≤ C 1) (hCN : C N - N * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil N g L τ C (genFun L a₁ l₁) (genFun L a₂ l₂) = genEntrySym N g L τ C a₁ l₁ a₂ l₂ := by
  rw [genEntrySym_eq, genEntry_eq hN g L τ C hg hC1 hCN]

end BGP212.V2e

#print axioms BGP212.V2e.symPlaceVal_eq
#print axioms BGP212.V2e.jT_eq_genEntrySym
