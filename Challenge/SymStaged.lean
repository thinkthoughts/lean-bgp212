/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.SymStaged
import BGP212.GenEntryBlock
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2ℓ: staged symmetric-function evaluation and reusable coefficient tables

Statements only; proofs live in `Solution/SymStaged.lean` and `Solution/SymPerm.lean`, the staged
certificates in `Solution/SymStagedCert/` and the demonstrations in `Solution/SymStagedDemo1.lean`
… `SymStagedDemo6.lean`. Objects are defined in `BGP212/SymStaged.lean` (`symStepAll`, `StepCert`,
`ValEq`, `ChainCert`, `StepsOK`, `combBEq`, `psFactors`, `runLookup`, `pairGroups`, `stagedTable`,
`abProfile`, `ProfCert`, `profLookup`, `profTable`, the compact encodings) over V2k's
`BGP212/SymReduce.lean`. -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

/-- **The multiset-state value depends only on the multiset of factors.** -/
theorem msVal_perm {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) {φs φs' : List (Fin 3 → List K)}
    (h : φs.Perm φs') : ∀ S, msVal M n φs S = msVal M n φs' S :=
  sorry

/-- **V2i's placement value depends only on the multiset of factors.** -/
theorem placeVal_perm {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ)
    {φs φs' : List (Fin 3 → List K)} (h : φs.Perm φs') :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs' :=
  sorry

/-- **A certified step**: the list equality `normalize (L.flatMap (symStep n φ)) = L'`. -/
theorem stepCert_of_eq {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' : List (SKey × K))
    (h : symStepAll n φ L = L') : StepCert n φ L L' :=
  sorry

/-- **Chunks**: certified steps of two parts of a combination certify the whole. -/
theorem stepCert_append {K : Type*} [Field K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L₁ L₂ L₁' L₂' : List (SKey × K))
    (h₁ : StepCert n φ L₁ L₁') (h₂ : StepCert n φ L₂ L₂') :
    StepCert n φ (L₁ ++ L₂) (L₁' ++ L₂') :=
  sorry

/-- **Merging certified chunks**: `normalize (D₁ ++ D₂) = L'`. -/
theorem stepCert_merge {K : Type*} [Field K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L₁ L₂ D₁ D₂ L' : List (SKey × K))
    (h₁ : StepCert n φ L₁ D₁) (h₂ : StepCert n φ L₂ D₂) (hm : normalize (D₁ ++ D₂) = L') :
    StepCert n φ (L₁ ++ L₂) L' :=
  sorry


theorem combBEq_iff {K : Type*} [Field K] [LinearOrder K] (L L' : List (SKey × K)) : combBEq L L' = true ↔ L = L' :=
  sorry

/-- **A certified step from a Boolean check** (one kernel evaluation of `combBEq`). -/
theorem stepCert_of_beq {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (L L' : List (SKey × K))
    (h : combBEq (symStepAll n φ L) L' = true) : StepCert n φ L L' :=
  sorry

/-- **A step certified chunk by chunk**: certified steps of the chunks `Cs` and one merge
`normalize Ds.flatten = L'` certify the step of `Cs.flatten`. -/
theorem stepCert_chunks {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (Cs Ds : List (List (SKey × K)))
    (L' : List (SKey × K)) (h : List.Forall₂ (StepCert n φ) Cs Ds)
    (hm : combBEq (normalize Ds.flatten) L' = true) : StepCert n φ Cs.flatten L' :=
  sorry

/-- **A step certified chunk by chunk with a linear merge** of the chunk results
(`mergeAll keyCmp 64 Ds = L'`, checked by `combBEq`). -/
theorem stepCert_runs {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (Cs Ds : List (List (SKey × K)))
    (L' : List (SKey × K)) (h : List.Forall₂ (StepCert n φ) Cs Ds)
    (hm : combBEq (mergeAll keyCmp 64 Ds) L' = true) : StepCert n φ Cs.flatten L' :=
  sorry

/-- **Prefix reuse**: a chain for `φs₁` composes with any chain for a continuation `φs₂`. -/
theorem chainCert_append {K : Type*} [Field K] (n : Fin 3 → ℕ) :
    ∀ (φs₁ φs₂ : List (Fin 3 → List K)) (L L₁ L₂ : List (SKey × K)),
      ChainCert n φs₁ L L₁ → ChainCert n φs₂ L₁ L₂ → ChainCert n (φs₁ ++ φs₂) L L₂ :=
  sorry

/-- **Extending a chain by one certified step** (prefix reuse along a run of power sums). -/
theorem chainCert_snoc {K : Type*} [Field K] (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (q : ℕ) (L₀ L L' : List (SKey × K))
    (h : ChainCert n (psFactors g Q) L₀ L) (hs : StepCert n (fun c => lpShiftPow (clsShift g c) q) L L') :
    ChainCert n (psFactors g (Q ++ [q])) L₀ L' :=
  sorry

/-- A chain carries the value of all its factors. -/
theorem chainCert_val {K : Type*} [Field K] (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L L' : List (SKey × K)), ChainCert n φs L L' →
      ∀ (M : ℕ → ℕ → K) (rest : List (Fin 3 → List K)),
        symVal M n rest L' = symVal M n (φs ++ rest) L :=
  sorry

/-- **Central theorem.** A chain of certified steps from the empty state gives V2i's placement
value: `placeVal M n 0 Fin.elim0 Fin.elim0 φs = symFinal M L`, for every moment oracle. -/
theorem chainCert_placeVal {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (L : List (SKey × K))
    (h : ChainCert n φs [([], 1)] L) (M : ℕ → ℕ → K) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = symFinal M L :=
  sorry

/-- The same chain gives V2k's `symPlaceVal`. -/
theorem chainCert_symPlaceVal {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (L : List (SKey × K))
    (h : ChainCert n φs [([], 1)] L) (M : ℕ → ℕ → K) : symPlaceVal M n φs = symFinal M L :=
  sorry

/-- V2k's run is a chain. -/
theorem chainCert_symRun {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)), ChainCert n φs L (symRun n φs L) :=
  sorry

/-- **List-level staging**: certified steps `symStepAll n φᵢ Lᵢ = Lᵢ₊₁` compose to `symRun`. -/
theorem symRun_of_steps {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)) (Ls : List (List (SKey × K))),
      StepsOK n φs (L :: Ls) → symRun n φs L = (L :: Ls).getLast (List.cons_ne_nil _ _) :=
  sorry

/-- **List-level staging gives V2i's placement value.** -/
theorem placeVal_of_steps {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) (Ls : List (List (SKey × K)))
    (h : StepsOK n φs (([([], 1)] : List (SKey × K)) :: Ls)) (M : ℕ → ℕ → K) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs =
      symFinal M ((([([], 1)] : List (SKey × K)) :: Ls).getLast (List.cons_ne_nil _ _)) :=
  sorry

/-- The value of a combination given in chunks is the sum over the chunks. -/
theorem symFinal_flatten {K : Type*} [Field K] (M : ℕ → ℕ → K) (Ls : List (List (SKey × K))) :
    symFinal M Ls.flatten = (Ls.map (symFinal M)).sum :=
  sorry

/-- **Staged tables.** For a list `R` of certified runs, the weighted sum of V2i's piece values
of the pairs `ws` is the staged table evaluated against the moment oracle; every group
`(Q, m, n)` is evaluated once and every run of `R` is shared by all pairs with the same `Q`. -/
theorem stagedTable_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (R : List (List ℕ × List (SKey × K)))
    (hR : ∀ p ∈ R, ChainCert (clsCount N r k) (psFactors g p.1) [([], 1)] p.2)
    (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (stagedTable N r k g R ws) Mo :=
  sorry

/-- One generator pair through certified runs. -/
theorem genPieceWith_eq_stagedTable {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (R : List (List ℕ × List (SKey × K)))
    (hR : ∀ p ∈ R, ChainCert (clsCount N r k) (psFactors g p.1) [([], 1)] p.2)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (stagedTable N r k g R [(1, a₁, l₁, a₂, l₂)]) Mo :=
  sorry

/-- `symFinal` through the moment profile. -/
theorem symFinal_abProfile {K : Type*} [Field K] (M : ℕ → ℕ → K) (L : List (SKey × K)) :
    symFinal M L = ((abProfile L).map fun e => e.2 * M e.1.1 e.1.2).sum :=
  sorry

/-- **A certified profile from a chain** and one kernel evaluation of `abProfile`. -/
theorem profCert_of_chain {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (L : List (SKey × K))
    (P : List ((ℕ × ℕ) × K)) (h : ChainCert n (psFactors g Q) [([], 1)] L) (hP : abProfile L = P) :
    ProfCert n g Q P :=
  sorry

/-- **A certified profile chunk by chunk**: profiles of the chunks of the final states, merged. -/
theorem profCert_of_chunks {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) (g : K) (Q : List ℕ) (Cs : List (List (SKey × K)))
    (Ps : List (List ((ℕ × ℕ) × K))) (P : List ((ℕ × ℕ) × K))
    (h : ChainCert n (psFactors g Q) [([], 1)] Cs.flatten)
    (hP : List.Forall₂ (fun C P => abProfile C = P) Cs Ps) (hm : mergeAll abCmp 64 Ps = P) :
    ProfCert n g Q P :=
  sorry

/-- **Tables from certified profiles.** The weighted sum of V2i's piece values is the profile
table evaluated against the moment oracle. -/
theorem profTable_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K)))
    (hR : ∀ p ∈ R, ProfCert (clsCount N r k) g p.1 p.2)
    (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (profTable N r k g R ws) Mo :=
  sorry

/-- One generator pair through certified profiles. -/
theorem genPieceWith_eq_profTable {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (R : List (List ℕ × List ((ℕ × ℕ) × K)))
    (hR : ∀ p ∈ R, ProfCert (clsCount N r k) g p.1 p.2)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (profTable N r k g R [(1, a₁, l₁, a₂, l₂)]) Mo :=
  sorry


theorem demo_place_22_staged : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2]) =
    (1381615373 / 22822800 : ℚ) :=
  sorry


theorem demo_place_222_staged : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2]) =
    (21901244073952449 / 11626695080000 : ℚ) :=
  sorry

/-- **Permutation of factors** (`placeVal_perm`), and both orders evaluated by the kernel. -/
theorem perm_42 : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [4, 2]) =
    placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 4]) :=
  sorry


theorem perm_42_val : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [4, 2]) = (3162065092438401 / 3419616200000 : ℚ) :=
  sorry


theorem perm_24_val : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 4]) = (3162065092438401 / 3419616200000 : ℚ) :=
  sorry


theorem demo_place_22222_staged : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2, 2, 2]) =
    (1523637806749637314901732798240307 / 249583007568884477488000000 : ℚ) :=
  sorry

/-- **Degree 12**: six shifted `P̂₂` on the example data. -/
theorem demo_place_222222_staged :
    placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2, 2, 2, 2]) = (7660407294494170883814115028993197537000319 / 12539428953337953513732966080000000 : ℚ) :=
  sorry

/-- The table is V2k's `tab_PP_6_3`; with V2k's `tv_PP_6_3` this is V2i's `gpPP_6_3`. -/
theorem genPiecePP_6_3_staged : genPiece 44 6 3 g L τ C 0 [2] 0 [2] =
    (131137324816032597206337084670791861367797826223071138605212410307363604674514849122712053237683605204139308010564930821851425446428402597303 / 3329626726358813710105275696049091166319247197034093404631815321345402691587029260565470945021360194004955701529979705810546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem genPieceP22_6_3_staged_expansion : genPiece 44 6 3 g L τ C 0 [2, 2] 0 [2, 2] =
    tableVal ([((0, 0, 2, 0), 52389094428262881 / 23283064365386962890625),
    ((0, 0, 4, 0), 4617101322252 / 59604644775390625),
    ((0, 0, 6, 0), 966410262 / 762939453125),
    ((0, 0, 8, 0), 20172 / 1953125),
    ((0, 0, 10, 0), 1 / 25),
    ((0, 1, 2, 0), 3407420775821976 / 37252902984619140625),
    ((0, 1, 4, 0), 225224454744 / 95367431640625),
    ((0, 1, 6, 0), 31427976 / 1220703125),
    ((0, 1, 8, 0), 328 / 3125),
    ((0, 2, 2, 0), 1163509533207504 / 59604644775390625),
    ((0, 2, 4, 0), 74464453872 / 152587890625),
    ((0, 2, 6, 0), 30150416 / 5859375),
    ((0, 2, 8, 0), 304 / 15),
    ((0, 3, 2, 0), 11211172858368 / 19073486328125),
    ((0, 3, 4, 0), 97040768 / 9765625),
    ((0, 3, 6, 0), 99712 / 1875),
    ((0, 4, 2, 0), 10237438223856 / 152587890625),
    ((0, 4, 4, 0), 422966496 / 390625),
    ((0, 4, 6, 0), 248368 / 45),
    ((0, 5, 2, 0), 334671554112 / 244140625),
    ((0, 5, 4, 0), 7108416 / 625),
    ((0, 6, 2, 0), 42357326976 / 390625),
    ((0, 6, 4, 0), 846336),
    ((0, 7, 2, 0), 723216384 / 625),
    ((0, 8, 2, 0), 69560064),
    ((1, 0, 2, 0), 6814841551643952 / 37252902984619140625),
    ((1, 0, 4, 0), 450448909488 / 95367431640625),
    ((1, 0, 6, 0), 62855952 / 1220703125),
    ((1, 0, 8, 0), 656 / 3125),
    ((1, 1, 2, 0), 332431295202144 / 59604644775390625),
    ((1, 1, 4, 0), 14648745024 / 152587890625),
    ((1, 1, 6, 0), 1022048 / 1953125),
    ((1, 2, 2, 0), 109909533915072 / 95367431640625),
    ((1, 2, 4, 0), 4684422528 / 244140625),
    ((1, 2, 6, 0), 947264 / 9375),
    ((1, 3, 2, 0), 143232173568 / 6103515625),
    ((1, 3, 4, 0), 15492096 / 78125),
    ((1, 4, 2, 0), 624298548096 / 244140625),
    ((1, 4, 4, 0), 12862848 / 625),
    ((1, 5, 2, 0), 10492022016 / 390625),
    ((1, 6, 2, 0), 1249191936 / 625),
    ((2, 0, 2, 0), 110810431734048 / 11920928955078125),
    ((2, 0, 4, 0), 28076761296 / 152587890625),
    ((2, 0, 6, 0), 8176384 / 5859375),
    ((2, 0, 8, 0), 16 / 5),
    ((2, 1, 2, 0), 20720649836448 / 95367431640625),
    ((2, 1, 4, 0), 635175936 / 244140625),
    ((2, 1, 6, 0), 24928 / 3125),
    ((2, 2, 2, 0), 53712065088 / 1220703125),
    ((2, 2, 4, 0), 40021248 / 78125),
    ((2, 2, 6, 0), 23104 / 15),
    ((2, 3, 2, 0), 30806032896 / 48828125),
    ((2, 3, 4, 0), 377856 / 125),
    ((2, 4, 2, 0), 26301705984 / 390625),
    ((2, 4, 4, 0), 313728),
    ((2, 5, 2, 0), 255902976 / 625),
    ((2, 6, 2, 0), 30468096),
    ((3, 0, 2, 0), 32832720513792 / 95367431640625),
    ((3, 0, 4, 0), 1199776768 / 244140625),
    ((3, 0, 6, 0), 199424 / 9375),
    ((3, 1, 2, 0), 885435254784 / 152587890625),
    ((3, 1, 4, 0), 15492096 / 390625),
    ((3, 2, 2, 0), 281171214336 / 244140625),
    ((3, 2, 4, 0), 4786176 / 625),
    ((3, 3, 2, 0), 743620608 / 78125),
    ((3, 4, 2, 0), 617416704 / 625),
    ((4, 0, 2, 0), 1553987701296 / 152587890625),
    ((4, 0, 4, 0), 39214368 / 390625),
    ((4, 0, 6, 0), 3344 / 15),
    ((4, 1, 2, 0), 28940203584 / 244140625),
    ((4, 1, 4, 0), 259776 / 625),
    ((4, 2, 2, 0), 9068685696 / 390625),
    ((4, 2, 4, 0), 80256),
    ((4, 3, 2, 0), 12469248 / 125),
    ((4, 4, 2, 0), 10353024),
    ((5, 0, 2, 0), 11671357824 / 48828125),
    ((5, 0, 4, 0), 173184 / 125),
    ((5, 1, 2, 0), 127809792 / 78125),
    ((5, 2, 2, 0), 39485952 / 125),
    ((6, 0, 2, 0), 350508672 / 78125),
    ((6, 0, 4, 0), 12800),
    ((6, 1, 2, 0), 377856 / 25),
    ((6, 2, 2, 0), 2918400),
    ((7, 0, 2, 0), 1511424 / 25),
    ((8, 0, 2, 0), 541440)] : List (MKey × ℚ))
      (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) :=
  sorry


theorem genPieceP222_6_3_staged_expansion : genPiece 44 6 3 g L τ C 0 [2, 2, 2] 0 [2, 2, 2] =
    tableVal (decTable [[0, 0, 2, 0, 0, 11991163848716906297072721, 3552713678800500929355621337890625],
    [0, 0, 4, 0, 0, 1585189219210378253298, 9094947017729282379150390625],
    [0, 0, 6, 0, 0, 576280038710891691, 116415321826934814453125],
    [0, 0, 8, 0, 0, 180066951567828, 2086162567138671875],
    [0, 0, 10, 0, 0, 25864190433, 26702880859375],
    [0, 0, 12, 0, 0, 90774, 13671875],
    [0, 0, 14, 0, 0, 1, 49],
    [0, 1, 2, 0, 0, 1169869643777259150933924, 5684341886080801486968994140625],
    [0, 1, 4, 0, 0, 25775434458705337452, 2910383045673370361328125],
    [0, 1, 6, 0, 0, 37481628534041736, 186264514923095703125],
    [0, 1, 8, 0, 0, 8783753735016, 3337860107421875],
    [0, 1, 10, 0, 0, 841111884, 42724609375],
    [0, 1, 12, 0, 0, 1476, 21875],
    [0, 2, 2, 0, 0, 424830710748381371883864, 9094947017729282379150390625],
    [0, 2, 4, 0, 0, 1816155273513113208, 931322574615478515625],
    [0, 2, 6, 0, 0, 12798604865282544, 298023223876953125],
    [0, 2, 8, 0, 0, 2904113701008, 5340576171875],
    [0, 2, 10, 0, 0, 268973448, 68359375],
    [0, 2, 12, 0, 0, 456, 35],
    [0, 3, 2, 0, 0, 1328866843204364064192, 582076609134674072265625],
    [0, 3, 4, 0, 0, 115095101761097856, 1490116119384765625],
    [0, 3, 6, 0, 0, 123322901442048, 95367431640625],
    [0, 3, 8, 0, 0, 3784589952, 341796875],
    [0, 3, 10, 0, 0, 889536, 21875],
    [0, 4, 2, 0, 0, 1323418377383824724568, 4656612873077392578125],
    [0, 4, 4, 0, 0, 109862386929212256, 11920928955078125],
    [0, 4, 6, 0, 0, 112611820462416, 762939453125],
    [0, 4, 8, 0, 0, 16495693344, 13671875],
    [0, 4, 10, 0, 0, 738568, 175],
    [0, 5, 2, 0, 0, 82283911303782775104, 7450580596923828125],
    [0, 5, 4, 0, 0, 5249164558728384, 19073486328125],
    [0, 5, 6, 0, 0, 3681387095232, 1220703125],
    [0, 5, 8, 0, 0, 39604032, 3125],
    [0, 6, 2, 0, 0, 11646811141178378112, 11920928955078125],
    [0, 6, 4, 0, 0, 140738631637248, 6103515625],
    [0, 6, 6, 0, 0, 465930596736, 1953125],
    [0, 6, 8, 0, 0, 33007104, 35],
    [0, 7, 2, 0, 0, 553926433374614016, 19073486328125],
    [0, 7, 4, 0, 0, 4623974951424, 9765625],
    [0, 7, 6, 0, 0, 7955380224, 3125],
    [0, 8, 2, 0, 0, 61183139898500352, 30517578125],
    [0, 8, 4, 0, 0, 2388718536192, 78125],
    [0, 8, 6, 0, 0, 765160704, 5],
    [0, 9, 2, 0, 0, 2023700385364992, 48828125],
    [0, 9, 4, 0, 0, 41428509696, 125],
    [0, 10, 2, 0, 0, 182209264625664, 78125],
    [0, 10, 4, 0, 0, 17217976320, 1],
    [0, 11, 2, 0, 0, 3210155753472, 125],
    [0, 12, 2, 0, 0, 1206941091840, 1],
    [1, 0, 2, 0, 0, 2339739287554518301867848, 5684341886080801486968994140625],
    [1, 0, 4, 0, 0, 51550868917410674904, 2910383045673370361328125],
    [1, 0, 6, 0, 0, 74963257068083472, 186264514923095703125],
    [1, 0, 8, 0, 0, 17567507470032, 3337860107421875],
    [1, 0, 10, 0, 0, 1682223768, 42724609375],
    [1, 0, 12, 0, 0, 2952, 21875],
    [1, 1, 2, 0, 0, 38044541261049078079152, 1818989403545856475830078125],
    [1, 1, 4, 0, 0, 3352902043408824384, 4656612873077392578125],
    [1, 1, 6, 0, 0, 3656744247223584, 298023223876953125],
    [1, 1, 8, 0, 0, 571301055936, 5340576171875],
    [1, 1, 10, 0, 0, 27353232, 68359375],
    [1, 2, 2, 0, 0, 2680645183705355095008, 582076609134674072265625],
    [1, 2, 4, 0, 0, 1144893380676183936, 7450580596923828125],
    [1, 2, 6, 0, 0, 1209004873065792, 476837158203125],
    [1, 2, 8, 0, 0, 182692478592, 8544921875],
    [1, 2, 10, 0, 0, 8450592, 109375],
    [1, 3, 2, 0, 0, 169880370199380435456, 931322574615478515625],
    [1, 3, 4, 0, 0, 11031794092634112, 2384185791015625],
    [1, 3, 6, 0, 0, 1575553909248, 30517578125],
    [1, 3, 8, 0, 0, 604191744, 2734375],
    [1, 4, 2, 0, 0, 162156883107517289856, 7450580596923828125],
    [1, 4, 4, 0, 0, 10073639212274304, 19073486328125],
    [1, 4, 6, 0, 0, 6867284029056, 1220703125],
    [1, 4, 8, 0, 0, 501651072, 21875],
    [1, 5, 2, 0, 0, 7747766888683094784, 11920928955078125],
    [1, 5, 4, 0, 0, 329316809246208, 30517578125],
    [1, 5, 6, 0, 0, 115412242176, 1953125],
    [1, 6, 2, 0, 0, 207730220296578048, 3814697265625],
    [1, 6, 4, 0, 0, 41679609744384, 48828125],
    [1, 6, 6, 0, 0, 13741111296, 3125],
    [1, 7, 2, 0, 0, 6824987028301824, 6103515625],
    [1, 7, 4, 0, 0, 711644921856, 78125],
    [1, 8, 2, 0, 0, 3525748559419392, 48828125],
    [1, 8, 4, 0, 0, 68447102976, 125],
    [1, 9, 2, 0, 0, 61148480311296, 78125],
    [1, 10, 2, 0, 0, 5082746609664, 125],
    [2, 0, 2, 0, 0, 278993302581026572580448, 9094947017729282379150390625],
    [2, 0, 4, 0, 0, 5169057316921937592, 4656612873077392578125],
    [2, 0, 6, 0, 0, 1218914749074528, 59604644775390625],
    [2, 0, 8, 0, 0, 1094993690544, 5340576171875],
    [2, 0, 10, 0, 0, 72941952, 68359375],
    [2, 0, 12, 0, 0, 72, 35],
    [2, 1, 2, 0, 0, 3814764299888389942896, 2910383045673370361328125],
    [2, 1, 4, 0, 0, 54518732413151616, 1490116119384765625],
    [2, 1, 6, 0, 0, 227927148200928, 476837158203125],
    [2, 1, 8, 0, 0, 24771861504, 8544921875],
    [2, 1, 10, 0, 0, 667152, 109375],
    [2, 2, 2, 0, 0, 1312661149994554746336, 4656612873077392578125],
    [2, 2, 4, 0, 0, 91012301264231424, 11920928955078125],
    [2, 2, 6, 0, 0, 590832715968, 6103515625],
    [2, 2, 8, 0, 0, 1560828672, 2734375],
    [2, 2, 10, 0, 0, 206112, 175],
    [2, 3, 2, 0, 0, 13641798377157493248, 1490116119384765625],
    [2, 3, 4, 0, 0, 680144486740992, 3814697265625],
    [2, 3, 6, 0, 0, 338866361856, 244140625],
    [2, 3, 8, 0, 0, 14736384, 4375],
    [2, 4, 2, 0, 0, 2525689858243963392, 2384185791015625],
    [2, 4, 4, 0, 0, 604045883979648, 30517578125],
    [2, 4, 6, 0, 0, 289318765824, 1953125],
    [2, 4, 8, 0, 0, 12235392, 35],
    [2, 5, 2, 0, 0, 472511696875206912, 19073486328125],
    [2, 5, 4, 0, 0, 14054537935872, 48828125],
    [2, 5, 6, 0, 0, 2814932736, 3125],
    [2, 6, 2, 0, 0, 61219097684619264, 30517578125],
    [2, 6, 4, 0, 0, 1733612018688, 78125],
    [2, 6, 6, 0, 0, 335149056, 5],
    [2, 7, 2, 0, 0, 1445041768974336, 48828125],
    [2, 7, 4, 0, 0, 17357193216, 125],
    [2, 8, 2, 0, 0, 144926822965248, 78125],
    [2, 8, 4, 0, 0, 8347207680, 1],
    [2, 9, 2, 0, 0, 1491426349056, 125],
    [2, 10, 2, 0, 0, 619847147520, 1],
    [3, 0, 2, 0, 0, 1008105881051586531456, 582076609134674072265625],
    [3, 0, 4, 0, 0, 387688763826855936, 7450580596923828125],
    [3, 0, 6, 0, 0, 361159925651712, 476837158203125],
    [3, 0, 8, 0, 0, 46791293952, 8544921875],
    [3, 0, 10, 0, 0, 1779072, 109375],
    [3, 1, 2, 0, 0, 286114307704219680768, 4656612873077392578125],
    [3, 1, 4, 0, 0, 16153698492785664, 11920928955078125],
    [3, 1, 6, 0, 0, 9739787802624, 762939453125],
    [3, 1, 8, 0, 0, 604191744, 13671875],
    [3, 2, 2, 0, 0, 96340657810973700096, 7450580596923828125],
    [3, 2, 4, 0, 0, 5280996281665536, 19073486328125],
    [3, 2, 6, 0, 0, 3092883357696, 1220703125],
    [3, 2, 8, 0, 0, 186660864, 21875],
    [3, 3, 2, 0, 0, 799192194266382336, 2384185791015625],
    [3, 3, 4, 0, 0, 28750603567104, 6103515625],
    [3, 3, 6, 0, 0, 8179826688, 390625],
    [3, 4, 2, 0, 0, 718610554683426816, 19073486328125],
    [3, 4, 4, 0, 0, 24820981776384, 48828125],
    [3, 4, 6, 0, 0, 6791583744, 3125],
    [3, 5, 2, 0, 0, 19757914781810688, 30517578125],
    [3, 5, 4, 0, 0, 335744704512, 78125],
    [3, 6, 2, 0, 0, 2470996996079616, 48828125],
    [3, 6, 4, 0, 0, 39974141952, 125],
    [3, 7, 2, 0, 0, 34158956249088, 78125],
    [3, 8, 2, 0, 0, 3285460942848, 125],
    [4, 0, 2, 0, 0, 376782367128066640152, 4656612873077392578125],
    [4, 0, 4, 0, 0, 23750369201664288, 11920928955078125],
    [4, 0, 6, 0, 0, 17093864714256, 762939453125],
    [4, 0, 8, 0, 0, 1529360352, 13671875],
    [4, 0, 10, 0, 0, 29832, 175],
    [4, 1, 2, 0, 0, 17527772470828244544, 7450580596923828125],
    [4, 1, 4, 0, 0, 764561949037632, 19073486328125],
    [4, 1, 6, 0, 0, 318342239424, 1220703125],
    [4, 1, 8, 0, 0, 10131264, 21875],
    [4, 2, 2, 0, 0, 5791248656905972608, 11920928955078125],
    [4, 2, 4, 0, 0, 245698517372544, 30517578125],
    [4, 2, 6, 0, 0, 99755542656, 1953125],
    [4, 2, 8, 0, 0, 3129984, 35],
    [4, 3, 2, 0, 0, 1499093970776064, 152587890625],
    [4, 3, 4, 0, 0, 933073449984, 9765625],
    [4, 3, 6, 0, 0, 137161728, 625],
    [4, 4, 2, 0, 0, 32904040370398848, 30517578125],
    [4, 4, 4, 0, 0, 790642992384, 78125],
    [4, 4, 6, 0, 0, 113883264, 5],
    [4, 5, 2, 0, 0, 636729258751488, 48828125],
    [4, 5, 4, 0, 0, 5629865472, 125],
    [4, 6, 2, 0, 0, 77798378105856, 78125],
    [4, 6, 4, 0, 0, 3351490560, 1],
    [4, 7, 2, 0, 0, 572787376128, 125],
    [4, 8, 2, 0, 0, 275457853440, 1],
    [5, 0, 2, 0, 0, 24115452637417398144, 7450580596923828125],
    [5, 0, 4, 0, 0, 1216011856102272, 19073486328125],
    [5, 0, 6, 0, 0, 128384936064, 244140625],
    [5, 0, 8, 0, 0, 6754176, 4375],
    [5, 1, 2, 0, 0, 897416749803476736, 11920928955078125],
    [5, 1, 4, 0, 0, 5742308049408, 6103515625],
    [5, 1, 6, 0, 0, 1405907712, 390625],
    [5, 2, 2, 0, 0, 291376780992861696, 19073486328125],
    [5, 2, 4, 0, 0, 1815968001024, 9765625],
    [5, 2, 6, 0, 0, 434345472, 625],
    [5, 3, 2, 0, 0, 279068358537216, 1220703125],
    [5, 3, 4, 0, 0, 4089913344, 3125],
    [5, 4, 2, 0, 0, 239541995215872, 9765625],
    [5, 4, 4, 0, 0, 3395791872, 25],
    [5, 5, 2, 0, 0, 2769893812224, 15625],
    [5, 6, 2, 0, 0, 329786671104, 25],
    [6, 0, 2, 0, 0, 1347733928010390912, 11920928955078125],
    [6, 0, 4, 0, 0, 10566628077312, 6103515625],
    [6, 0, 6, 0, 0, 3855595392, 390625],
    [6, 0, 8, 0, 0, 99840, 7],
    [6, 1, 2, 0, 0, 7798171521056256, 3814697265625],
    [6, 1, 4, 0, 0, 172450266624, 9765625],
    [6, 1, 6, 0, 0, 4156416, 125],
    [6, 2, 2, 0, 0, 2494036732806144, 6103515625],
    [6, 2, 4, 0, 0, 53897001984, 15625],
    [6, 2, 6, 0, 0, 6420480, 1],
    [6, 3, 2, 0, 0, 8328426872832, 1953125],
    [6, 3, 4, 0, 0, 12091392, 1],
    [6, 4, 2, 0, 0, 7030793419776, 15625],
    [6, 4, 4, 0, 0, 1254912000, 1],
    [6, 5, 2, 0, 0, 8188895232, 5],
    [6, 6, 2, 0, 0, 121872384000, 1],
    [7, 0, 2, 0, 0, 65902477253732352, 19073486328125],
    [7, 0, 4, 0, 0, 382375913472, 9765625],
    [7, 0, 6, 0, 0, 16625664, 125],
    [7, 1, 2, 0, 0, 282193424142336, 6103515625],
    [7, 1, 4, 0, 0, 743620608, 3125],
    [7, 2, 2, 0, 0, 89011014967296, 9765625],
    [7, 2, 4, 0, 0, 229736448, 5],
    [7, 3, 2, 0, 0, 35693789184, 625],
    [7, 4, 2, 0, 0, 29636001792, 5],
    [8, 0, 2, 0, 0, 562882910462208, 6103515625],
    [8, 0, 4, 0, 0, 11332468224, 15625],
    [8, 0, 6, 0, 0, 1191168, 1],
    [8, 1, 2, 0, 0, 8363361549312, 9765625],
    [8, 1, 4, 0, 0, 53277696, 25],
    [8, 2, 2, 0, 0, 2610015381504, 15625],
    [8, 2, 4, 0, 0, 411494400, 1],
    [8, 3, 2, 0, 0, 2557329408, 5],
    [8, 4, 2, 0, 0, 53082777600, 1],
    [9, 0, 2, 0, 0, 20532697307136, 9765625],
    [9, 0, 4, 0, 0, 248629248, 25],
    [9, 1, 2, 0, 0, 183488385024, 15625],
    [9, 2, 2, 0, 0, 56687468544, 25],
    [10, 0, 2, 0, 0, 3115956252672, 78125],
    [10, 0, 4, 0, 0, 90593280, 1],
    [10, 1, 2, 0, 0, 13371568128, 125],
    [10, 2, 2, 0, 0, 20655267840, 1],
    [11, 0, 2, 0, 0, 71315030016, 125],
    [12, 0, 2, 0, 0, 5418362880, 1]])
      (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) :=
  sorry

end BGP212.Challenge
