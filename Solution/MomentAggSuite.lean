/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import Solution.MomentAgg
import Solution.MomentAggDemo3
import Solution.MomentAggDemo4

/-! # V2j: Comparator wrappers (proofs in `Solution/MomentAgg.lean` and the demonstration files) -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem stateVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => M A B + M' A B) d c fs A B =
        stateVal M d c fs A B + stateVal M' d c fs A B := by
  apply BGP212.V2e.stateVal_add <;> assumption

theorem stateVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => a * M A B) d c fs A B = a * stateVal M d c fs A B := by
  apply BGP212.V2e.stateVal_smul <;> assumption

theorem placeVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => M A B + M' A B) n d c fs fac =
        placeVal M n d c fs fac + placeVal M' n d c fs fac := by
  apply BGP212.V2e.placeVal_add <;> assumption

theorem placeVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => a * M A B) n d c fs fac = a * placeVal M n d c fs fac := by
  apply BGP212.V2e.placeVal_smul <;> assumption

theorem genPieceWith_add {K : Type*} [Field K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ)
    (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => Mo A B m n + Mo' A B m n) a₁ l₁ a₂ l₂ =
      genPieceWith N r k g Mo a₁ l₁ a₂ l₂ + genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genPieceWith_add <;> assumption

theorem genPieceWith_smul {K : Type*} [Field K] (N r k : ℕ) (g : K) (a : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => a * Mo A B m n) a₁ l₁ a₂ l₂ =
      a * genPieceWith N r k g Mo a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genPieceWith_smul <;> assumption

theorem genPieceWith_zero {K : Type*} [Field K] (N r k : ℕ) (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun _ _ _ _ => (0 : K)) a₁ l₁ a₂ l₂ = 0 := by
  apply BGP212.V2e.genPieceWith_zero <;> assumption

theorem genPieceWith_listSum {K : Type*} [Field K] [LinearOrder K] {ι : Type*} (N r k : ℕ) (g : K) (S : List ι) (c : ι → K)
    (F : ι → ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => (S.map fun t => c t * F t A B m n).sum) a₁ l₁ a₂ l₂ =
      (S.map fun t => c t * genPieceWith N r k g (F t) a₁ l₁ a₂ l₂).sum := by
  apply BGP212.V2e.genPieceWith_listSum <;> assumption

theorem stateVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      (∀ p ∈ stateKeys d c fs A B, M p.1 p.2 = M' p.1 p.2) →
        stateVal M d c fs A B = stateVal M' d c fs A B := by
  apply BGP212.V2e.stateVal_congr <;> assumption

theorem placeVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      (∀ p ∈ placeKeys d c fs fac, M p.1 p.2 = M' p.1 p.2) →
        placeVal M n d c fs fac = placeVal M' n d c fs fac := by
  apply BGP212.V2e.placeVal_congr <;> assumption

theorem genPieceWith_congr {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (h : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, Mo s.1 s.2.1 s.2.2.1 s.2.2.2 = Mo' s.1 s.2.1 s.2.2.1 s.2.2.2) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genPieceWith_congr <;> assumption

theorem genPieceWith_eq_keys {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) (S : List MKey) (hS : S.Nodup)
    (hcov : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, s ∈ S) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      (S.map fun s => genPieceWith N r k g (delta s) a₁ l₁ a₂ l₂ *
        Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum := by
  apply BGP212.V2e.genPieceWith_eq_keys <;> assumption

theorem genPieceWith_eq_coeffs {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      ((genCoeffs N r k g a₁ l₁ a₂ l₂).map fun p => p.2 * Mo p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2).sum := by
  apply BGP212.V2e.genPieceWith_eq_coeffs <;> assumption

theorem aggPieceOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N r k : ℕ) (g : K) (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPieceOn S N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  apply BGP212.V2e.aggPieceOn_eq <;> assumption

theorem aggPiece_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPiece N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  apply BGP212.V2e.aggPiece_eq <;> assumption

theorem aggEntryValOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K)
    (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    aggEntryValOn S N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  apply BGP212.V2e.aggEntryValOn_eq <;> assumption

theorem aggEntryVal_eq {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L τ : K) (C : ℕ → K) (ws : List (WPair K)) :
    aggEntryVal N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  apply BGP212.V2e.aggEntryVal_eq <;> assumption

theorem genPiece_eq_aggPieceOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup)
    (N r k : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ =
      aggPieceOn S N r k g [(1, a₁, l₁, a₂, l₂)] (fun A B m n => pieceMn N r k A B g L τ C m n) := by
  apply BGP212.V2e.genPiece_eq_aggPieceOn <;> assumption

theorem genEntryVal_eq_aggEntryValOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey)
    (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genEntryVal N g L τ C a₁ l₁ a₂ l₂ = aggEntryValOn S N g L τ C [(1, a₁, l₁, a₂, l₂)] := by
  apply BGP212.V2e.genEntryVal_eq_aggEntryValOn <;> assumption

theorem jT_weighted_eq_agg {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (hC1 : g ≤ C 1) (hCN : C N - N * g < 0) (ws : List (WPair ℝ)) :
    (ws.map fun w => w.1 * jTbil N g L τ C (genFun L w.2.1 w.2.2.1) (genFun L w.2.2.2.1 w.2.2.2.2)).sum =
      aggEntryVal N g L τ C ws := by
  apply BGP212.V2e.jT_weighted_eq_agg <;> assumption

theorem genPiecePP_6_3_viaAgg : genPiece 44 6 3 g L τ C 0 [2] 0 [2] = (131137324816032597206337084670791861367797826223071138605212410307363604674514849122712053237683605204139308010564930821851425446428402597303 / 3329626726358813710105275696049091166319247197034093404631815321345402691587029260565470945021360194004955701529979705810546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genPiecePP_6_3_viaAgg <;> assumption

theorem agg4_6_3_eq : (List.map (fun w : WPair ℚ => w.1 * genPieceWith 44 6 3 g
    (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) [((1 : ℚ), 0, [2], 0, [2]), ((1 : ℚ), 0, [4], 0, []), ((1 : ℚ), 0, [2, 2], 0, []), ((1 : ℚ), 1, [], 0, [])]).sum =
    (72121648658152103771075998445448222548953334339394094445742959230265568635264428681768782928376283012297999592355903824370683099662114760933 / 138734446931617237921053154002045465263301966543087225192992305056058445482792885856894622709223341416873154230415821075439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.agg4_6_3_eq <;> assumption

theorem aggSmall_PP : aggEntryValOn [(0, 0, 2, 0), (0, 0, 4, 0), (0, 0, 6, 0), (0, 1, 2, 0), (0, 1, 4, 0), (0, 2, 2, 0), (0, 2, 4, 0), (0, 3, 2, 0), (0, 4, 2, 0), (1, 0, 2, 0), (1, 0, 4, 0), (1, 1, 2, 0), (1, 2, 2, 0), (2, 0, 2, 0), (2, 0, 4, 0), (2, 1, 2, 0), (2, 2, 2, 0), (3, 0, 2, 0), (4, 0, 2, 0)] 3 (3 / 10 : ℚ) 1 (9 / 10) synthC [((1 : ℚ), 0, [2], 0, [2])] = (775434251 / 567000000000 : ℚ) := by
  apply BGP212.V2e.aggSmall_PP <;> assumption

theorem genEntrySmall_PP : genEntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) synthC 0 [2] 0 [2] = (775434251 / 567000000000 : ℚ) := by
  apply BGP212.V2e.genEntrySmall_PP <;> assumption

end BGP212.Challenge
