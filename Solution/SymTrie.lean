/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymTrie
import Solution.SymStaged
import Solution.SymPerm

/-! # V2m: certified prefix-trie evaluation (proofs)

* §1 tries: the root, extension by one certified step (`trieOK_cons`), and the value of every node
  and every permutation of its degrees (`trieOK_placeVal`), the central correctness theorem;
* §2 moment profiles of trie nodes, of children computed from a stored parent (with or without
  chunks), independence of the order of the degrees;
* §3 tables of Gram-entry coefficients from certified profiles (`trieProf_table_eq`). -/

namespace BGP212.V2e

section Trie

variable {K : Type*} [Field K] [LinearOrder K]

/-! ## §1 Tries -/

omit [LinearOrder K] in
theorem trieOK_nil (n : Fin 3 → ℕ) (g : K) : TrieOK n g [] := fun _ h => absurd h List.not_mem_nil

omit [LinearOrder K] in
/-- The root: the empty multiset and the empty state. -/
theorem trieOK_root (n : Fin 3 → ℕ) (g : K) : TrieOK n g [([], [([], 1)])] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact chainCert_nil n _

omit [LinearOrder K] in
/-- **Extension by one certified step** from a node of the trie (prefix reuse). -/
theorem trieOK_cons (n : Fin 3 → ℕ) (g : K) (T : List (List ℕ × List (SKey × K))) (Q : List ℕ)
    (L : List (SKey × K)) (q : ℕ) (L' : List (SKey × K)) (hT : TrieOK n g T) (hp : (Q, L) ∈ T)
    (hs : StepCert n (stepFactor g q) L L') : TrieOK n g ((Q ++ [q], L') :: T) := by
  intro p hp'
  rcases List.mem_cons.mp hp' with rfl | h
  · exact chainCert_snoc n g Q q _ L L' (hT _ hp) hs
  · exact hT p h

omit [LinearOrder K] in
/-- Adding a node with its own chain. -/
theorem trieOK_cons_chain (n : Fin 3 → ℕ) (g : K) (T : List (List ℕ × List (SKey × K)))
    (Q : List ℕ) (L : List (SKey × K)) (h : ChainCert n (psFactors g Q) [([], 1)] L)
    (hT : TrieOK n g T) : TrieOK n g ((Q, L) :: T) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h'
  · exact h
  · exact hT p h'

/-- **Central theorem (trie evaluation).** For every node `(Q, L)` of a certified trie and every
reordering `Q'` of its degrees, V2i's placement value of `P̂_q`, `q ∈ Q'`, is `symFinal M L`, for every
moment oracle. -/
theorem trieOK_placeVal (n : Fin 3 → ℕ) (g : K) (T : List (List ℕ × List (SKey × K)))
    (hT : TrieOK n g T) (Q : List ℕ) (L : List (SKey × K)) (hp : (Q, L) ∈ T) (Q' : List ℕ)
    (hQ : Q'.Perm Q) (M : ℕ → ℕ → K) :
    placeVal M n 0 Fin.elim0 Fin.elim0 (psFactors g Q') = symFinal M L := by
  rw [psFactors, placeVal_perm M n (hQ.map _), ← psFactors, chainCert_placeVal n _ L (hT _ hp) M]

/-! ## §2 Moment profiles -/

omit [LinearOrder K] in
theorem profOK_nil (n : Fin 3 → ℕ) (g : K) : ProfOK n g [] := fun _ h => absurd h List.not_mem_nil

omit [LinearOrder K] in
theorem profOK_cons (n : Fin 3 → ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K))) (Q : List ℕ)
    (P : List ((ℕ × ℕ) × K)) (h : ProfCert n g Q P) (hR : ProfOK n g R) : ProfOK n g ((Q, P) :: R) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h'
  · exact h
  · exact hR p h'

omit [LinearOrder K] in
/-- A profile does not depend on the order of the degrees. -/
theorem profCert_perm (n : Fin 3 → ℕ) (g : K) (Q Q' : List ℕ) (P : List ((ℕ × ℕ) × K))
    (h : ProfCert n g Q P) (hQ : Q'.Perm Q) : ProfCert n g Q' P := by
  intro M
  rw [psFactors, placeVal_perm M n (hQ.map _), ← psFactors, h M]

/-- The profile of a node of the trie. -/
theorem profCert_of_trie (n : Fin 3 → ℕ) (g : K) (T : List (List ℕ × List (SKey × K)))
    (hT : TrieOK n g T) (Q : List ℕ) (L : List (SKey × K)) (hp : (Q, L) ∈ T)
    (P : List ((ℕ × ℕ) × K)) (hP : abProfile L = P) : ProfCert n g Q P :=
  profCert_of_chain n g Q L P (hT _ hp) hP

/-- **A child's profile from its stored parent**, without storing the child's states. -/
theorem profCert_of_step (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (L : List (SKey × K)) (q : ℕ)
    (P : List ((ℕ × ℕ) × K)) (h : ChainCert n (psFactors g Q) [([], 1)] L)
    (hP : abProfile (symStepAll n (stepFactor g q) L) = P) : ProfCert n g (Q ++ [q]) P :=
  profCert_of_chain n g _ _ P (chainCert_snoc n g Q q _ L _ h (stepCert_symStepAll n _ L)) hP

theorem forall₂_steps (n : Fin 3 → ℕ) (φ : Fin 3 → List K) :
    ∀ Cs : List (List (SKey × K)), List.Forall₂ (StepCert n φ) Cs (Cs.map (symStepAll n φ))
  | [] => List.Forall₂.nil
  | C :: Cs => List.Forall₂.cons (stepCert_symStepAll n φ C) (forall₂_steps n φ Cs)

/-- **A child's profile from a parent stored in chunks**: the step of each chunk, its profile,
and one merge of the profiles. -/
theorem profCert_of_step_chunks (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (Cs : List (List (SKey × K)))
    (q : ℕ) (Ps : List (List ((ℕ × ℕ) × K))) (P : List ((ℕ × ℕ) × K))
    (h : ChainCert n (psFactors g Q) [([], 1)] Cs.flatten)
    (hP : List.Forall₂ (fun C P => abProfile (symStepAll n (stepFactor g q) C) = P) Cs Ps)
    (hm : mergeAll abCmp 64 Ps = P) : ProfCert n g (Q ++ [q]) P := by
  have hc : ChainCert n (psFactors g (Q ++ [q])) [([], 1)]
      (Cs.map (symStepAll n (stepFactor g q))).flatten :=
    chainCert_snoc n g Q q _ _ _ h (stepCert_flatten_of_forall₂ n _ _ _ (forall₂_steps n _ Cs))
  refine profCert_of_chunks n g _ _ Ps P hc ?_ hm
  clear hc hm h
  induction hP with
  | nil => exact List.Forall₂.nil
  | cons h₁ _ ih => exact List.Forall₂.cons h₁ ih

end Trie

/-! ## §3 Tables from certified profiles -/

/-- **Gram-entry coefficient tables from certified trie profiles.** For certified profiles `R`
(`ProfOK`), the weighted sum of V2i's piece values of the generator pairs `ws` is the profile table
evaluated against the moment oracle. The table is a coefficient representation; the moments
`Mo` are evaluated separately. -/
theorem trieProf_table_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K)
    (R : List (List ℕ × List ((ℕ × ℕ) × K))) (hR : ProfOK (clsCount N r k) g R)
    (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (profTable N r k g R ws) Mo :=
  profTable_eq N r k g R hR ws Mo

/-- **Merging part tables.** If the weighted sum of piece values of each part `wsᵢ` of the generator
pairs is the table `Tᵢ` evaluated against the moment oracle, the weighted sum over all parts is the
merged table evaluated against the same oracle. Applied repeatedly, parts merge in a tree. -/
theorem table_parts_merge {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) (wss : List (List (WPair K))) (ws : List (WPair K))
    (hw : wss.flatten = ws) (Ts : List (List (MKey × K)))
    (h : List.Forall₂ (fun ws T => (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1
      w.2.2.2.1 w.2.2.2.2).sum = tableVal T Mo) wss Ts)
    (T : List (MKey × K)) (hm : mergeAll mkeyCmp 64 Ts = T) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal T Mo := by
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  subst hw hm
  rw [hT, mergeAll_val mkeyCmp mkeyCmp_eq]
  induction h with
  | nil => simp
  | cons hd _ ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons, hd,
      hT]

/-- **Tables in parts.** The generator pairs split into parts `wss` (flattening to `ws`), each part's
profile table certified separately, and the part tables merged once: the weighted sum of piece
values is the merged table evaluated against the moment oracle. -/
theorem trieProf_table_parts {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K)
    (R : List (List ℕ × List ((ℕ × ℕ) × K))) (hR : ProfOK (clsCount N r k) g R)
    (wss : List (List (WPair K))) (ws : List (WPair K)) (hw : wss.flatten = ws)
    (Ts : List (List (MKey × K)))
    (h : List.Forall₂ (fun ws T => profTable N r k g R ws = T) wss Ts)
    (T : List (MKey × K)) (hm : mergeAll mkeyCmp 64 Ts = T) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal T Mo := by
  have hT : ∀ T : List (MKey × K), tableVal T Mo =
      valBy (fun s : MKey => Mo s.1 s.2.1 s.2.2.1 s.2.2.2) T := fun T => rfl
  subst hw hm
  rw [hT, mergeAll_val mkeyCmp mkeyCmp_eq]
  induction h with
  | nil => simp
  | cons hd _ ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      ← hd, ← hT, trieProf_table_eq N r k g R hR _ Mo]

end BGP212.V2e

#print axioms BGP212.V2e.trieOK_placeVal
#print axioms BGP212.V2e.trieProf_table_eq
#print axioms BGP212.V2e.trieProf_table_parts
#print axioms BGP212.V2e.table_parts_merge
