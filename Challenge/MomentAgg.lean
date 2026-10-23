/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.MomentAgg
import BGP212.GenEntryBlock
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2j: shared-moment aggregation of marginal Gram entries

Statements only; proofs live in `Solution/MomentAgg.lean`, the kernel demonstration in
`Solution/MomentAggDemo1.lean` … `MomentAggDemo4.lean`. Objects are defined in
`BGP212/MomentAgg.lean` (`MKey`, `WPair`, `delta`, `stateKeys`, `placeKeys`, `genKeys`, `genCoeffs`,
`aggKeys`, `aggCoeff`, `aggPieceOn`, `aggPiece`, `aggEntryValOn`, `aggEntryVal`) over V2i's
`BGP212/GenEntry.lean`. The general statements keep `g`, `L`, `τ`, `C` as parameters; Table 3
enters only through `BGP212.Params`. -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory


theorem stateVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => M A B + M' A B) d c fs A B =
        stateVal M d c fs A B + stateVal M' d c fs A B :=
  sorry


theorem stateVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => a * M A B) d c fs A B = a * stateVal M d c fs A B :=
  sorry


theorem placeVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => M A B + M' A B) n d c fs fac =
        placeVal M n d c fs fac + placeVal M' n d c fs fac :=
  sorry


theorem placeVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => a * M A B) n d c fs fac = a * placeVal M n d c fs fac :=
  sorry


theorem genPieceWith_add {K : Type*} [Field K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ)
    (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => Mo A B m n + Mo' A B m n) a₁ l₁ a₂ l₂ =
      genPieceWith N r k g Mo a₁ l₁ a₂ l₂ + genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ :=
  sorry


theorem genPieceWith_smul {K : Type*} [Field K] (N r k : ℕ) (g : K) (a : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => a * Mo A B m n) a₁ l₁ a₂ l₂ =
      a * genPieceWith N r k g Mo a₁ l₁ a₂ l₂ :=
  sorry


theorem genPieceWith_zero {K : Type*} [Field K] (N r k : ℕ) (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun _ _ _ _ => (0 : K)) a₁ l₁ a₂ l₂ = 0 :=
  sorry

/-- **Linearity in the oracle**: the value of a finite combination of oracles is the combination
of the values. -/
theorem genPieceWith_listSum {K : Type*} [Field K] [LinearOrder K] {ι : Type*} (N r k : ℕ) (g : K) (S : List ι) (c : ι → K)
    (F : ι → ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => (S.map fun t => c t * F t A B m n).sum) a₁ l₁ a₂ l₂ =
      (S.map fun t => c t * genPieceWith N r k g (F t) a₁ l₁ a₂ l₂).sum :=
  sorry


theorem stateVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      (∀ p ∈ stateKeys d c fs A B, M p.1 p.2 = M' p.1 p.2) →
        stateVal M d c fs A B = stateVal M' d c fs A B :=
  sorry


theorem placeVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      (∀ p ∈ placeKeys d c fs fac, M p.1 p.2 = M' p.1 p.2) →
        placeVal M n d c fs fac = placeVal M' n d c fs fac :=
  sorry

/-- **Locality**: `genPieceWith` reads its oracle only at `genKeys`. -/
theorem genPieceWith_congr {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (h : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, Mo s.1 s.2.1 s.2.2.1 s.2.2.2 = Mo' s.1 s.2.1 s.2.2.1 s.2.2.2) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ :=
  sorry

/-- **Coefficient collapse**: for any duplicate-free key list `S` containing the queried keys,
`genPieceWith … Mo … = Σ_{s ∈ S} genPieceWith … (delta s) … · Mo s`. -/
theorem genPieceWith_eq_keys {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) (S : List MKey) (hS : S.Nodup)
    (hcov : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, s ∈ S) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      (S.map fun s => genPieceWith N r k g (delta s) a₁ l₁ a₂ l₂ *
        Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum :=
  sorry

/-- **Coefficient collapse** with V2i's own keys: `genPieceWith = Σ_{(s, c) ∈ genCoeffs} c · Mo s`. -/
theorem genPieceWith_eq_coeffs {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      ((genCoeffs N r k g a₁ l₁ a₂ l₂).map fun p => p.2 * Mo p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2).sum :=
  sorry

/-- **Shared moments across generator pairs**, over a key list `S`: if `S` is duplicate-free and
contains the keys of every pair, the aggregated piece value is the weighted sum of V2i's piece
values. -/
theorem aggPieceOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N r k : ℕ) (g : K) (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPieceOn S N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  sorry

/-- **Shared moments across generator pairs** with the canonical keys `aggKeys`. -/
theorem aggPiece_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPiece N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  sorry

/-- **The aggregated entry** over a key list `S` (duplicate-free, covering the keys):
`aggEntryValOn S N g L τ C ws = Σ_{(w, a₁, l₁, a₂, l₂) ∈ ws} w · genEntryVal N g L τ C a₁ l₁ a₂ l₂`. -/
theorem aggEntryValOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K)
    (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    aggEntryValOn S N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  sorry

/-- **The aggregated entry**: `aggEntryVal N g L τ C ws = Σ_{(w, a₁, l₁, a₂, l₂) ∈ ws} w ·
genEntryVal N g L τ C a₁ l₁ a₂ l₂`. Each piece evaluates every distinct moment once. -/
theorem aggEntryVal_eq {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L τ : K) (C : ℕ → K) (ws : List (WPair K)) :
    aggEntryVal N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  sorry

/-- **One pair as an aggregated piece value** (term-mode bridge for certificates). -/
theorem genPiece_eq_aggPieceOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup)
    (N r k : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ =
      aggPieceOn S N r k g [(1, a₁, l₁, a₂, l₂)] (fun A B m n => pieceMn N r k A B g L τ C m n) :=
  sorry

/-- **One pair as an aggregated entry** (term-mode bridge for certificates). -/
theorem genEntryVal_eq_aggEntryValOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey)
    (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genEntryVal N g L τ C a₁ l₁ a₂ l₂ = aggEntryValOn S N g L τ C [(1, a₁, l₁, a₂, l₂)] :=
  sorry

/-- **A weighted sum of marginal Gram entries is the aggregated value**: for every `N ≥ 1`,
admissible data and weighted generator pairs `ws`, `Σ w · J_T[G_{a₁,l₁}, G_{a₂,l₂}] =
aggEntryVal N g L τ C ws` (the shape of `J_T(P⋆) = Σ cᵢ cⱼ J_T[Gᵢ, Gⱼ]`). -/
theorem jT_weighted_eq_agg {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (hC1 : g ≤ C 1) (hCN : C N - N * g < 0) (ws : List (WPair ℝ)) :
    (ws.map fun w => w.1 * jTbil N g L τ C (genFun L w.2.1 w.2.2.1) (genFun L w.2.2.2.1 w.2.2.2.2)).sum =
      aggEntryVal N g L τ C ws :=
  sorry


theorem genPiecePP_6_3_viaAgg : genPiece 44 6 3 g L τ C 0 [2] 0 [2] = (131137324816032597206337084670791861367797826223071138605212410307363604674514849122712053237683605204139308010564930821851425446428402597303 / 3329626726358813710105275696049091166319247197034093404631815321345402691587029260565470945021360194004955701529979705810546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- The four V2i entries on piece `(6, 3)`: `Σ_{w ∈ ws} w · genPieceWith … = …` from 21 shared keys. -/
theorem agg4_6_3_eq : (List.map (fun w : WPair ℚ => w.1 * genPieceWith 44 6 3 g
    (fun A B m n => pieceMn 44 6 3 A B g L τ C m n) w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) [((1 : ℚ), 0, [2], 0, [2]), ((1 : ℚ), 0, [4], 0, []), ((1 : ℚ), 0, [2, 2], 0, []), ((1 : ℚ), 1, [], 0, [])]).sum =
    (72121648658152103771075998445448222548953334339394094445742959230265568635264428681768782928376283012297999592355903824370683099662114760933 / 138734446931617237921053154002045465263301966543087225192992305056058445482792885856894622709223341416873154230415821075439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem aggSmall_PP : aggEntryValOn [(0, 0, 2, 0), (0, 0, 4, 0), (0, 0, 6, 0), (0, 1, 2, 0), (0, 1, 4, 0), (0, 2, 2, 0), (0, 2, 4, 0), (0, 3, 2, 0), (0, 4, 2, 0), (1, 0, 2, 0), (1, 0, 4, 0), (1, 1, 2, 0), (1, 2, 2, 0), (2, 0, 2, 0), (2, 0, 4, 0), (2, 1, 2, 0), (2, 2, 2, 0), (3, 0, 2, 0), (4, 0, 2, 0)] 3 (3 / 10 : ℚ) 1 (9 / 10) synthC [((1 : ℚ), 0, [2], 0, [2])] = (775434251 / 567000000000 : ℚ) :=
  sorry


theorem genEntrySmall_PP : genEntryVal 3 (3 / 10 : ℚ) 1 (9 / 10) synthC 0 [2] 0 [2] = (775434251 / 567000000000 : ℚ) :=
  sorry

end BGP212.Challenge
