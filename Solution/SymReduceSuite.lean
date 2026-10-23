/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import Solution.SymReduce
import Solution.SymReduceDemo1
import Solution.SymReduceDemo2
import Solution.SymReduceDemo3

/-! # V2k: Comparator wrappers (proofs in `Solution/SymReduce.lean` and the demonstration files) -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem placeVal_eq_msum {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (rest : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal M n d c fs rest = msum d fs (fun e => msVal M n rest (msOf c e)) := by
  apply BGP212.V2e.placeVal_eq_msum <;> assumption

theorem placeVal_eq_msVal {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = msVal M n φs 0 := by
  apply BGP212.V2e.placeVal_eq_msVal <;> assumption

theorem msVal_zero_part {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (rest : List (Fin 3 → List K)) (S : Multiset SPart) (c : Fin 3),
      msVal M n rest ((c, 0) ::ₘ S) = msVal M n rest S := by
  apply BGP212.V2e.msVal_zero_part <;> assumption

theorem symStep_val {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (φ : Fin 3 → List K) (p : SKey × K) :
    ((symStep n φ p).map fun q => q.2 * msVal M n rest (q.1 : Multiset SPart)).sum =
      p.2 * msVal M n (φ :: rest) (p.1 : Multiset SPart) := by
  apply BGP212.V2e.symStep_val <;> assumption

theorem normalize_val {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (rest : List (Fin 3 → List K))
    (L : List (SKey × K)) : symVal M n rest (normalize L) = symVal M n rest L := by
  apply BGP212.V2e.normalize_val <;> assumption

theorem symRun_val {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)), symFinal M (symRun n φs L) = symVal M n φs L := by
  apply BGP212.V2e.symRun_val <;> assumption

theorem symPlaceVal_eq {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    symPlaceVal M n φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs := by
  apply BGP212.V2e.symPlaceVal_eq <;> assumption

theorem genPieceSym_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ)
    (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceSym N r k g Mo a₁ l₁ a₂ l₂ = genPieceWith N r k g Mo a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genPieceSym_eq <;> assumption

theorem genEntrySym_eq {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    genEntrySym N g L τ C a₁ l₁ a₂ l₂ = genEntryVal N g L τ C a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genEntrySym_eq <;> assumption

theorem jT_eq_genEntrySym {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (hC1 : g ≤ C 1) (hCN : C N - N * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil N g L τ C (genFun L a₁ l₁) (genFun L a₂ l₂) = genEntrySym N g L τ C a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.jT_eq_genEntrySym <;> assumption

theorem aggCoeff_eq_sym {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (ws : List (WPair K)) (s : MKey) :
    aggCoeff N r k g ws s =
      (ws.map fun w => w.1 * genPieceSym N r k g (delta s) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  apply BGP212.V2e.aggCoeff_eq_sym <;> assumption

theorem symRun_scale {K : Type*} [Field K] [LinearOrder K] (n : Fin 3 → ℕ) :
    ∀ (φs : List (Fin 3 → List K)) (L : List (SKey × K)),
      symRun n φs (L.map (scaleQ n)) = (symRun1 n φs L).map (scaleQ n) := by
  apply BGP212.V2e.symRun_scale <;> assumption

theorem symPlaceVal_eq_trans {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    symPlaceVal M n φs = ((symRun1 n φs [([], 1)]).map fun q => q.2 * monoMoment M n q.1).sum := by
  apply BGP212.V2e.symPlaceVal_eq_trans <;> assumption

theorem placeVal_eq_trans {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φs : List (Fin 3 → List K)) :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs =
      ((symRun1 n φs [([], 1)]).map fun q => q.2 * monoMoment M n q.1).sum := by
  apply BGP212.V2e.placeVal_eq_trans <;> assumption

theorem lpEval_psFactor {K : Type*} [Field K] (c c' : Fin 3) (a : ℕ) (y : K) :
    lpEval (psFactor c a c') y = if c' = c then y ^ a else 0 := by
  apply BGP212.V2e.lpEval_psFactor <;> assumption

theorem psTrans_indep {K : Type*} [Field K] [LinearOrder K] (n n' : Fin 3 → ℕ) (α : List SPart) (hα : ∀ x ∈ α, 0 < x.2) :
    psTrans (K := K) n α = psTrans n' α := by
  apply BGP212.V2e.psTrans_indep <;> assumption

theorem placeVal_psTrans {K : Type*} [Field K] [LinearOrder K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (α : List SPart) :
    placeVal M n 0 Fin.elim0 Fin.elim0 (α.map fun x => psFactor x.1 x.2) =
      ((psTrans n α).map fun q => q.2 * monoMoment M n q.1).sum := by
  apply BGP212.V2e.placeVal_psTrans <;> assumption

theorem genPieceWith_eq_table {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (genTable N r k g a₁ l₁ a₂ l₂) Mo := by
  apply BGP212.V2e.genPieceWith_eq_table <;> assumption

theorem aggTable_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum =
      tableVal (aggTable N r k g ws) Mo := by
  apply BGP212.V2e.aggTable_eq <;> assumption

theorem genEntryVal_eq_table {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    genEntryVal N g L τ C a₁ l₁ a₂ l₂ = (N + 1) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
      ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
        tableVal (genTable N r k g a₁ l₁ a₂ l₂) (fun A B m n => pieceMn N r k A B g L τ C m n) := by
  apply BGP212.V2e.genEntryVal_eq_table <;> assumption

theorem trans_p2_p2 : psTrans (K := ℚ) demoN [(0, 2), (0, 2)] =
    ([([(0, 4)], 1), ([(0, 2), (0, 2)], 1)] : List (SKey × ℚ)) := by
  apply BGP212.V2e.trans_p2_p2 <;> assumption

theorem trans_p1_cubed : psTrans (K := ℚ) demoN [(0, 1), (0, 1), (0, 1)] =
    ([([(0, 3)], 1), ([(0, 2), (0, 1)], 3), ([(0, 1), (0, 1), (0, 1)], 1)] : List (SKey × ℚ)) := by
  apply BGP212.V2e.trans_p1_cubed <;> assumption

theorem trans_mixed : psTrans (K := ℚ) demoN [(0, 2), (1, 1), (0, 1)] =
    ([([(0, 3), (1, 1)], 1), ([(0, 2), (0, 1), (1, 1)], 1)] : List (SKey × ℚ)) := by
  apply BGP212.V2e.trans_mixed <;> assumption

theorem demo_place_22 : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2]) =
    (1381615373 / 22822800 : ℚ) := by
  apply BGP212.V2e.demo_place_22 <;> assumption

theorem demo_sym_22 : symPlaceVal demoM demoN (demoF [2, 2]) = (1381615373 / 22822800 : ℚ) := by
  apply BGP212.V2e.demo_sym_22 <;> assumption

theorem demo_place_222 : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2]) =
    (21901244073952449 / 11626695080000 : ℚ) := by
  apply BGP212.V2e.demo_place_222 <;> assumption

theorem demo_sym_222 : symPlaceVal demoM demoN (demoF [2, 2, 2]) = (21901244073952449 / 11626695080000 : ℚ) := by
  apply BGP212.V2e.demo_sym_222 <;> assumption

theorem demo_sym_2222 : symPlaceVal demoM demoN (demoF [2, 2, 2, 2]) = (319427165402625415923 / 3622000086880000 : ℚ) := by
  apply BGP212.V2e.demo_sym_2222 <;> assumption

theorem demo_place_2222 : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2, 2]) =
    (319427165402625415923 / 3622000086880000 : ℚ) := by
  apply BGP212.V2e.demo_place_2222 <;> assumption

theorem demo_sym_22222 : symPlaceVal demoM demoN (demoF [2, 2, 2, 2, 2]) = (1523637806749637314901732798240307 / 249583007568884477488000000 : ℚ) := by
  apply BGP212.V2e.demo_sym_22222 <;> assumption

theorem demo_place_22222 : placeVal demoM demoN 0 Fin.elim0 Fin.elim0 (demoF [2, 2, 2, 2, 2]) =
    (1523637806749637314901732798240307 / 249583007568884477488000000 : ℚ) := by
  apply BGP212.V2e.demo_place_22222 <;> assumption

theorem genPiecePP_6_3_viaTable : genPiece 44 6 3 g L τ C 0 [2] 0 [2] = (131137324816032597206337084670791861367797826223071138605212410307363604674514849122712053237683605204139308010564930821851425446428402597303 / 3329626726358813710105275696049091166319247197034093404631815321345402691587029260565470945021360194004955701529979705810546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genPiecePP_6_3_viaTable <;> assumption

theorem agg4_6_3_viaTable : (List.map (fun w : WPair ℚ => w.1 * genPieceWith 44 6 3 g
    (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) [((1 : ℚ), 0, [2], 0, [2]), ((1 : ℚ), 0, [4], 0, []), ((1 : ℚ), 0, [2, 2], 0, []), ((1 : ℚ), 1, [], 0, [])]).sum =
    (72121648658152103771075998445448222548953334339394094445742959230265568635264428681768782928376283012297999592355903824370683099662114760933 / 138734446931617237921053154002045465263301966543087225192992305056058445482792885856894622709223341416873154230415821075439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.agg4_6_3_viaTable <;> assumption

theorem tab_P22_6_3 : genTable 44 6 3 g 0 [2, 2] 0 [2, 2] =
    ([((0, 0, 2, 0), 52389094428262881 / 23283064365386962890625),
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
    ((8, 0, 2, 0), 541440)] : List (MKey × ℚ)) := by
  apply BGP212.V2e.tab_P22_6_3 <;> assumption

theorem genPieceP22_6_3_expansion : genPiece 44 6 3 g L τ C 0 [2, 2] 0 [2, 2] =
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
      (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) := by
  apply BGP212.V2e.genPieceP22_6_3_expansion <;> assumption

theorem genEntrySmall_PP_viaTable : genEntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) synthC 0 [2] 0 [2] = (775434251 / 567000000000 : ℚ) := by
  apply BGP212.V2e.genEntrySmall_PP_viaTable <;> assumption

end BGP212.Challenge
