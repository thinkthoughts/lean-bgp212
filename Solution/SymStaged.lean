/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymStaged
import Solution.SymReduce
import Solution.SymPerm

/-! # V2ℓ: staged certificates compose to V2k's run and V2i's placement value (proofs)

* §1 values of combinations: appends and one factor;
* §2 step certificates: from a list equality, from chunks and a merge, from a Boolean check;
* §3 chains: composition, prefix reuse, `chainCert_placeVal` (the central theorem), and the
  list-level form `symRun_of_steps`;
* §4 tables from certified runs: `stagedTable_eq`. -/

namespace BGP212.V2e

section Staged

variable {K : Type*} [Field K] [LinearOrder K]

/-! ## §1 Values of combinations -/

omit [LinearOrder K] in
theorem symVal_append (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (L₁ L₂ : List (SKey × K)) :
    symVal M n rest (L₁ ++ L₂) = symVal M n rest L₁ + symVal M n rest L₂ := by
  simp [symVal, List.map_append, List.sum_append]

theorem symVal_flatMap_step (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (φ : Fin 3 → List K) (L : List (SKey × K)) :
    symVal M n rest (L.flatMap (symStep n φ)) = symVal M n (φ :: rest) L := by
  simp only [symVal, flatMap_map_sum]
  congr 1
  exact List.map_congr_left fun p _ => symStep_val M n rest φ p

/-! ## §2 Step certificates -/

theorem stepCert_symStepAll (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L : List (SKey × K)) :
    StepCert n φ L (symStepAll n φ L) := by
  intro M rest
  rw [symStepAll, normalize_val, symVal_flatMap_step]

/-- **A certified step**: the list equality `normalize (L.flatMap (symStep n φ)) = L'`. -/
theorem stepCert_of_eq (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' : List (SKey × K))
    (h : symStepAll n φ L = L') : StepCert n φ L L' :=
  h ▸ stepCert_symStepAll n φ L

omit [LinearOrder K] in
/-- **Chunks**: certified steps of two parts of a combination certify the whole. -/
theorem stepCert_append (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L₁ L₂ L₁' L₂' : List (SKey × K))
    (h₁ : StepCert n φ L₁ L₁') (h₂ : StepCert n φ L₂ L₂') :
    StepCert n φ (L₁ ++ L₂) (L₁' ++ L₂') := by
  intro M rest
  rw [symVal_append, symVal_append, h₁, h₂]

omit [LinearOrder K] in
theorem valEq_refl (n : Fin 3 → ℕ) (L : List (SKey × K)) : ValEq n L L := fun _ _ => rfl

omit [LinearOrder K] in
theorem valEq_trans (n : Fin 3 → ℕ) (L L' L'' : List (SKey × K)) (h : ValEq n L L')
    (h' : ValEq n L' L'') : ValEq n L L'' := fun M rest => (h' M rest).trans (h M rest)

omit [LinearOrder K] in
theorem valEq_normalize (n : Fin 3 → ℕ) (L : List (SKey × K)) : ValEq n L (normalize L) :=
  fun M rest => normalize_val M n rest L

omit [LinearOrder K] in
/-- A step certificate followed by a value-preserving rewrite (e.g. a merge `normalize`). -/
theorem stepCert_valEq (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' L'' : List (SKey × K))
    (h : StepCert n φ L L') (h' : ValEq n L' L'') : StepCert n φ L L'' :=
  fun M rest => (h' M rest).trans (h M rest)

omit [LinearOrder K] in
/-- **Merging certified chunks**: `normalize (D₁ ++ D₂) = L'`. -/
theorem stepCert_merge (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L₁ L₂ D₁ D₂ L' : List (SKey × K))
    (h₁ : StepCert n φ L₁ D₁) (h₂ : StepCert n φ L₂ D₂) (hm : normalize (D₁ ++ D₂) = L') :
    StepCert n φ (L₁ ++ L₂) L' :=
  stepCert_valEq n φ _ _ _ (stepCert_append n φ L₁ L₂ D₁ D₂ h₁ h₂)
    (hm ▸ valEq_normalize n (D₁ ++ D₂))

theorem partCmp_self (x : SPart) : partCmp x x = .eq := by
  simp [partCmp]

theorem keyCmp_self (a : SKey) : keyCmp a a = .eq := by
  induction a with
  | nil => rfl
  | cons x l ih => simp [keyCmp, partCmp_self, ih]

set_option linter.unusedSectionVars false in
theorem combBEq_iff (L L' : List (SKey × K)) : combBEq L L' = true ↔ L = L' := by
  induction L generalizing L' with
  | nil => cases L' <;> simp [combBEq]
  | cons p L ih =>
    cases L' with
    | nil => simp [combBEq]
    | cons q L' =>
      simp only [combBEq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ih, List.cons.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨Prod.ext (keyCmp_eq _ _ h1) h2, h3⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨keyCmp_self _, rfl⟩, rfl⟩

/-- **A certified step from a Boolean check** (one kernel evaluation of `combBEq`). -/
theorem stepCert_of_beq (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' : List (SKey × K))
    (h : combBEq (symStepAll n φ L) L' = true) : StepCert n φ L L' :=
  stepCert_of_eq n φ L L' ((combBEq_iff _ _).mp h)

/-- **A certified merge from a Boolean check.** -/
theorem stepCert_merge_beq (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L₁ L₂ D₁ D₂ L' : List (SKey × K))
    (h₁ : StepCert n φ L₁ D₁) (h₂ : StepCert n φ L₂ D₂) (hm : combBEq (normalize (D₁ ++ D₂)) L' = true) :
    StepCert n φ (L₁ ++ L₂) L' :=
  stepCert_merge n φ L₁ L₂ D₁ D₂ L' h₁ h₂ ((combBEq_iff _ _).mp hm)

/-! ## §3 Chains -/

omit [LinearOrder K] in
theorem chainCert_nil (n : Fin 3 → ℕ) (L : List (SKey × K)) : ChainCert n [] L L :=
  valEq_refl n L

omit [LinearOrder K] in
theorem chainCert_cons (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (φs : List (Fin 3 → List K))
    (L L₁ L' : List (SKey × K)) (h : StepCert n φ L L₁) (hs : ChainCert n φs L₁ L') :
    ChainCert n (φ :: φs) L L' :=
  ⟨L₁, h, hs⟩

omit [LinearOrder K] in
theorem chainCert_valEq_left (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L L₁ L' : List (SKey × K)), ValEq n L L₁ →
      ChainCert n φs L₁ L' → ChainCert n φs L L' := by
  intro φs
  cases φs with
  | nil => intro L L₁ L' h h'; exact valEq_trans n L L₁ L' h h'
  | cons φ φs =>
    intro L L₁ L' h ⟨L₂, hs, hc⟩
    exact ⟨L₂, fun M rest => (hs M rest).trans (h M (φ :: rest)), hc⟩

omit [LinearOrder K] in
/-- **Prefix reuse**: a chain for `φs₁` composes with any chain for a continuation `φs₂`. -/
theorem chainCert_append (n : Fin 3 → ℕ) :
    ∀ (φs₁ φs₂ : List (Fin 3 → List K)) (L L₁ L₂ : List (SKey × K)),
      ChainCert n φs₁ L L₁ → ChainCert n φs₂ L₁ L₂ → ChainCert n (φs₁ ++ φs₂) L L₂ := by
  intro φs₁
  induction φs₁ with
  | nil => intro φs₂ L L₁ L₂ h h'; exact chainCert_valEq_left n φs₂ L L₁ L₂ h h'
  | cons φ φs ih =>
    intro φs₂ L L₁ L₂ ⟨L₃, hs, hc⟩ h'
    exact ⟨L₃, hs, ih φs₂ L₃ L₁ L₂ hc h'⟩

omit [LinearOrder K] in
/-- A chain carries the value of all its factors. -/
theorem chainCert_val (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L L' : List (SKey × K)), ChainCert n φs L L' →
      ∀ (M : ℕ → ℕ → K) (rest : List (Fin 3 → List K)),
        symVal M n rest L' = symVal M n (φs ++ rest) L := by
  intro φs
  induction φs with
  | nil => intro L L' h M rest; exact h M rest
  | cons φ φs ih =>
    intro L L' ⟨L₁, hs, hc⟩ M rest
    rw [ih L₁ L' hc M rest, List.cons_append, hs M (φs ++ rest)]

/-- **Central theorem.** A chain of certified steps from the empty state gives V2i's placement
value: `placeVal M n 0 Fin.elim0 Fin.elim0 φs = symFinal M L`, for every moment oracle. -/
theorem chainCert_placeVal (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (L : List (SKey × K))
    (h : ChainCert n φs [([], 1)] L) (M : ℕ → ℕ → K) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = symFinal M L := by
  have h1 : symFinal M L = symVal M n [] L := symRun_val M n [] L
  rw [h1, chainCert_val n φs _ L h M [], List.append_nil, placeVal_eq_msVal]
  simp [symVal]

/-- The same chain gives V2k's `symPlaceVal`. -/
theorem chainCert_symPlaceVal (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (L : List (SKey × K))
    (h : ChainCert n φs [([], 1)] L) (M : ℕ → ℕ → K) : symPlaceVal M n φs = symFinal M L := by
  rw [symPlaceVal_eq, chainCert_placeVal n φs L h M]

/-- V2k's run is a chain. -/
theorem chainCert_symRun (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)), ChainCert n φs L (symRun n φs L) := by
  intro φs
  induction φs with
  | nil => intro L; exact valEq_refl n L
  | cons φ φs ih =>
    intro L
    exact ⟨symStepAll n φ L, stepCert_symStepAll n φ L, ih _⟩

/-- **List-level staging**: certified steps `symStepAll n φᵢ Lᵢ = Lᵢ₊₁` compose to `symRun`. -/
theorem symRun_of_steps (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)) (Ls : List (List (SKey × K))),
      StepsOK n φs (L :: Ls) → symRun n φs L = (L :: Ls).getLast (List.cons_ne_nil _ _) := by
  intro φs
  induction φs with
  | nil =>
    intro L Ls h
    cases Ls with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [StepsOK])
  | cons φ φs ih =>
    intro L Ls h
    cases Ls with
    | nil => exact absurd h (by simp [StepsOK])
    | cons L' Ls =>
      obtain ⟨h1, h2⟩ := h
      rw [symRun, ← symStepAll, h1, ih L' Ls h2]
      exact List.getLast_cons_cons.symm

theorem chainCert_of_steps (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (L : List (SKey × K))
    (Ls : List (List (SKey × K))) (h : StepsOK n φs (L :: Ls)) :
    ChainCert n φs L ((L :: Ls).getLast (List.cons_ne_nil _ _)) := by
  rw [← symRun_of_steps n φs L Ls h]
  exact chainCert_symRun n φs L

/-- **List-level staging gives V2i's placement value.** -/
theorem placeVal_of_steps (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (Ls : List (List (SKey × K)))
    (h : StepsOK n φs (([([], 1)] : List (SKey × K)) :: Ls)) (M : ℕ → ℕ → K) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs =
      symFinal M ((([([], 1)] : List (SKey × K)) :: Ls).getLast (List.cons_ne_nil _ _)) :=
  chainCert_placeVal n φs _ (chainCert_of_steps n φs _ Ls h) M

omit [LinearOrder K] in
/-- **Extending a chain by one certified step** (prefix reuse along a run of power sums). -/
theorem chainCert_snoc (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q : ℕ) (L₀ L L' : List (SKey × K))
    (h : ChainCert n (psFactors g Q) L₀ L) (hs : StepCert n (fun c => lpShiftPow (clsShift g c) q) L L') :
    ChainCert n (psFactors g (Q ++ [q])) L₀ L' := by
  rw [psFactors, List.map_append]
  exact chainCert_append n _ _ L₀ L L' h ⟨L', hs, chainCert_nil n L'⟩

omit [LinearOrder K] in
theorem stepCert_nil (n : Fin 3 → ℕ) (φ : Fin 3 → List K) : StepCert n φ [] [] := by
  intro M rest; simp [symVal]

omit [LinearOrder K] in
theorem stepCert_flatten_of_forall₂ (n : Fin 3 → ℕ) (φ : Fin 3 → List K)
    (Cs Ds : List (List (SKey × K))) (h : List.Forall₂ (StepCert n φ) Cs Ds) :
    StepCert n φ Cs.flatten Ds.flatten := by
  induction h with
  | nil => exact stepCert_nil n φ
  | cons h₁ _ ih => exact stepCert_append n φ _ _ _ _ h₁ ih

/-- **A step certified chunk by chunk**: certified steps of the chunks `Cs` and one merge
`normalize Ds.flatten = L'` certify the step of `Cs.flatten`. -/
theorem stepCert_chunks (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (Cs Ds : List (List (SKey × K)))
    (L' : List (SKey × K)) (h : List.Forall₂ (StepCert n φ) Cs Ds)
    (hm : combBEq (normalize Ds.flatten) L' = true) : StepCert n φ Cs.flatten L' :=
  stepCert_valEq n φ _ _ _ (stepCert_flatten_of_forall₂ n φ Cs Ds h)
    (((combBEq_iff _ _).mp hm) ▸ valEq_normalize n _)

omit [LinearOrder K] in
/-- Merging sorted runs (`mergeAll`, linear merges in rounds) preserves the value; the runs need
not be sorted for this. -/
theorem valEq_mergeAll (n : Fin 3 → ℕ) (Ds : List (List (SKey × K))) :
    ValEq n Ds.flatten (mergeAll keyCmp 64 Ds) := by
  intro M rest
  have h := mergeAll_val keyCmp keyCmp_eq (fun k => msVal M n rest (k : Multiset SPart)) 64 Ds
  simp only [valBy] at h
  rw [symVal, h]
  clear h
  induction Ds with
  | nil => simp [symVal]
  | cons D Ds ih => rw [List.map_cons, List.sum_cons, ih, List.flatten_cons, symVal_append]; rfl

/-- **A step certified chunk by chunk with a linear merge** of the chunk results
(`mergeAll keyCmp 64 Ds = L'`, checked by `combBEq`). -/
theorem stepCert_runs (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (Cs Ds : List (List (SKey × K)))
    (L' : List (SKey × K)) (h : List.Forall₂ (StepCert n φ) Cs Ds)
    (hm : combBEq (mergeAll keyCmp 64 Ds) L' = true) : StepCert n φ Cs.flatten L' :=
  stepCert_valEq n φ _ _ _ (stepCert_flatten_of_forall₂ n φ Cs Ds h)
    (((combBEq_iff _ _).mp hm) ▸ valEq_mergeAll n Ds)

omit [LinearOrder K] in
/-- The value of a combination given in chunks is the sum over the chunks. -/
theorem symFinal_flatten (M : ℕ → ℕ → K) (Ls : List (List (SKey × K))) :
    symFinal M Ls.flatten = (Ls.map (symFinal M)).sum := by
  induction Ls with
  | nil => simp [symFinal, bsum_eq]
  | cons L Ls ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [symFinal, bsum_eq, List.map_append, List.sum_append]

end Staged

/-! ## §4 Tables from certified runs -/

theorem natListCmp_eq (a b : List ℕ) (h : natListCmp a b = .eq) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [natListCmp]
  | cons x l ih =>
    cases b with
    | nil => simp [natListCmp] at h
    | cons y m =>
      simp only [natListCmp] at h
      split_ifs at h with h1 h2
      rw [ih m h, show x = y by omega]

theorem qmnCmp_eq (s t : List ℕ × ℕ × ℕ) (h : qmnCmp s t = .eq) : s = t := by
  rcases s with ⟨Q, m, n⟩
  rcases t with ⟨Q', m', n'⟩
  unfold qmnCmp at h
  simp only at h
  cases hc : natListCmp Q Q' with
  | lt => simp [hc] at h
  | gt => simp [hc] at h
  | eq =>
    simp only [hc] at h
    split_ifs at h
    rw [natListCmp_eq Q Q' hc, show m = m' by omega, show n = n' by omega]

section Tables

variable {K : Type*} [Field K] [LinearOrder K]

/-- A run from the table of certified runs (or V2k's `symRun`) gives V2i's placement value. -/
theorem runLookup_val (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List (SKey × K)))
    (hR : ∀ p ∈ R, ChainCert n (psFactors g p.1) [([], 1)] p.2) (Q : List ℕ) (M : ℕ → ℕ → K) :
    symFinal M (runLookup n g R Q) = placeVal M n 0 Fin.elim0 Fin.elim0 (psFactors g Q) := by
  unfold runLookup
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hq : p.1 = Q := by simpa using List.find?_some hp
    rw [← chainCert_placeVal n _ p.2 (hR p hmem) M, hq]
  · rw [← symPlaceVal_eq]; rfl

/-- **Staged tables.** For a list `R` of certified runs, the weighted sum of V2i's piece values
of the pairs `ws` is the staged table evaluated against the moment oracle; every group
`(Q, m, n)` is evaluated once and every run of `R` is shared by all pairs with the same `Q`. -/
theorem stagedTable_eq (N r k : ℕ) (g : K) (R : List (List ℕ × List (SKey × K)))
    (hR : ∀ p ∈ R, ChainCert (clsCount N r k) (psFactors g p.1) [([], 1)] p.2)
    (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (stagedTable N r k g R ws) Mo := by
  set P : List ℕ × ℕ × ℕ → K := fun G =>
    placeVal (fun A B => Mo A B G.2.1 G.2.2) (clsCount N r k) 0 Fin.elim0 Fin.elim0 (psFactors g G.1)
    with hP
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  rw [hT, stagedTable, normalizeBy_val mkeyCmp mkeyCmp_eq, valBy_flatMap]
  have hG : ∀ G : (List ℕ × ℕ × ℕ) × K,
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2)
        ((runLookup (clsCount N r k) g R G.1.1).map fun q =>
          ((keyA q.1, keyB q.1, G.1.2.1, G.1.2.2), G.2 * q.2 * factW q.1)) = G.2 * P G.1 := by
    intro G
    rw [hP]
    beta_reduce
    rw [← runLookup_val (clsCount N r k) g R hR G.1.1, symFinal, bsum_eq, valBy, List.map_map,
      ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply, keyW, keyA, keyB, factW]
    ring
  rw [List.map_congr_left fun G _ => hG G]
  have h2 : ((pairGroups ws).map fun G => G.2 * P G.1).sum = valBy P (pairGroups ws) := rfl
  rw [h2, pairGroups, normalizeBy_val qmnCmp qmnCmp_eq, valBy_flatMap]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  rw [valBy_flatMap, genPieceWith, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t₁ _ => ?_
  simp only [valBy, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t₂ _ => ?_
  simp only [Function.comp_apply, hP, psFactors]
  rw [placeVal_perm _ _ ((List.perm_insertionSort _ _).map _)]
  ring

/-- One generator pair through certified runs. -/
theorem genPieceWith_eq_stagedTable (N r k : ℕ) (g : K) (R : List (List ℕ × List (SKey × K)))
    (hR : ∀ p ∈ R, ChainCert (clsCount N r k) (psFactors g p.1) [([], 1)] p.2)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (stagedTable N r k g R [(1, a₁, l₁, a₂, l₂)]) Mo := by
  rw [← stagedTable_eq N r k g R hR [(1, a₁, l₁, a₂, l₂)] Mo]
  simp

theorem abCmp_eq (s t : ℕ × ℕ) (h : abCmp s t = .eq) : s = t := by
  rcases s with ⟨a, b⟩
  rcases t with ⟨a', b'⟩
  unfold abCmp at h
  simp only at h
  split_ifs at h
  simp only [Prod.mk.injEq]
  omega

omit [LinearOrder K] in
/-- `symFinal` through the moment profile. -/
theorem symFinal_abProfile (M : ℕ → ℕ → K) (L : List (SKey × K)) :
    symFinal M L = ((abProfile L).map fun e => e.2 * M e.1.1 e.1.2).sum := by
  have h := normalizeBy_val abCmp abCmp_eq (fun ab : ℕ × ℕ => M ab.1 ab.2)
    (L.map fun q => ((keyA q.1, keyB q.1), q.2 * factW q.1))
  simp only [valBy] at h
  rw [abProfile, h, symFinal, bsum_eq, List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, keyW, keyA, keyB, factW]
  ring

/-- **A certified profile from a chain** and one kernel evaluation of `abProfile`. -/
theorem profCert_of_chain (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (L : List (SKey × K))
    (P : List ((ℕ × ℕ) × K)) (h : ChainCert n (psFactors g Q) [([], 1)] L) (hP : abProfile L = P) :
    ProfCert n g Q P := by
  intro M
  rw [chainCert_placeVal n _ L h M, symFinal_abProfile, hP]

/-- **A certified profile chunk by chunk**: profiles of the chunks of the final states, merged. -/
theorem profCert_of_chunks (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (Cs : List (List (SKey × K)))
    (Ps : List (List ((ℕ × ℕ) × K))) (P : List ((ℕ × ℕ) × K))
    (h : ChainCert n (psFactors g Q) [([], 1)] Cs.flatten)
    (hP : List.Forall₂ (fun C P => abProfile C = P) Cs Ps) (hm : mergeAll abCmp 64 Ps = P) :
    ProfCert n g Q P := by
  intro M
  rw [chainCert_placeVal n _ _ h M, symFinal_flatten, ← hm]
  have hm' := mergeAll_val abCmp abCmp_eq (fun ab : ℕ × ℕ => M ab.1 ab.2) 64 Ps
  simp only [valBy] at hm'
  rw [hm']
  clear hm' h hm
  induction hP with
  | nil => rfl
  | cons h₁ _ ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, symFinal_abProfile, h₁]
    rfl

theorem profLookup_val (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K)))
    (hR : ∀ p ∈ R, ProfCert n g p.1 p.2) (Q : List ℕ) (M : ℕ → ℕ → K) :
    ((profLookup n g R Q).map fun e => e.2 * M e.1.1 e.1.2).sum =
      placeVal M n 0 Fin.elim0 Fin.elim0 (psFactors g Q) := by
  unfold profLookup
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hq : p.1 = Q := by simpa using List.find?_some hp
    rw [← hq, hR p hmem M]
  · rw [← symFinal_abProfile, ← symPlaceVal_eq]; rfl

/-- **Tables from certified profiles.** The weighted sum of V2i's piece values is the profile
table evaluated against the moment oracle. -/
theorem profTable_eq (N r k : ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K)))
    (hR : ∀ p ∈ R, ProfCert (clsCount N r k) g p.1 p.2)
    (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (profTable N r k g R ws) Mo := by
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  rw [hT, profTable, normalizeBy_val mkeyCmp mkeyCmp_eq, valBy_flatMap]
  set P : List ℕ × ℕ × ℕ → K := fun G =>
    placeVal (fun A B => Mo A B G.2.1 G.2.2) (clsCount N r k) 0 Fin.elim0 Fin.elim0 (psFactors g G.1)
    with hP
  have hG : ∀ G : (List ℕ × ℕ × ℕ) × K,
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2)
        ((profLookup (clsCount N r k) g R G.1.1).map fun e =>
          ((e.1.1, e.1.2, G.1.2.1, G.1.2.2), G.2 * e.2)) = G.2 * P G.1 := by
    intro G
    rw [hP]
    beta_reduce
    rw [← profLookup_val (clsCount N r k) g R hR G.1.1, valBy, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply]
    ring
  rw [List.map_congr_left fun G _ => hG G]
  have h2 : ((pairGroups ws).map fun G => G.2 * P G.1).sum = valBy P (pairGroups ws) := rfl
  rw [h2, pairGroups, normalizeBy_val qmnCmp qmnCmp_eq, valBy_flatMap]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  rw [valBy_flatMap, genPieceWith, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t₁ _ => ?_
  simp only [valBy, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t₂ _ => ?_
  simp only [Function.comp_apply, hP, psFactors]
  rw [placeVal_perm _ _ ((List.perm_insertionSort _ _).map _)]
  ring

/-- One generator pair through certified profiles. -/
theorem genPieceWith_eq_profTable (N r k : ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K)))
    (hR : ∀ p ∈ R, ProfCert (clsCount N r k) g p.1 p.2)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (profTable N r k g R [(1, a₁, l₁, a₂, l₂)]) Mo := by
  rw [← profTable_eq N r k g R hR [(1, a₁, l₁, a₂, l₂)] Mo]
  simp

end Tables

end BGP212.V2e

#print axioms BGP212.V2e.chainCert_placeVal
#print axioms BGP212.V2e.stagedTable_eq
#print axioms BGP212.V2e.profTable_eq
