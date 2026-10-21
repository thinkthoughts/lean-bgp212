/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.PowerSumPlace
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2h: the marginal Gram entry `J_T[P₂, P₂]`

Statements only; proofs live in `Solution/PowerSumSquare.lean` and the computational certificate in
`Solution/PowerSumSquareCert0.lean` … `Cert13.lean` and `Solution/PowerSumSquareCertSum.lean`. Objects are
defined in `BGP212/PowerSumSquare.lean` (`pieceM`, the classes and `q2J`) and
`BGP212/PowerSumPlace.lean` (`cls`, `diagT`, `pairT`), with V2g's `jTbil`, `pieceE`, `p2J`, V2f's
`cellsVal`, `seg0Val`, `pieceJ`, V2e-A's aggregates and `endpointAgg`, V2d's `jT`, `endpoint`, V2b's
`supportT`, `pieceSet`, `shiftV`, V0's `gen`. The general statements keep `g`, `L`, `τ`, `C` as
parameters; Table 3 enters only through `BGP212.Params` (`g3`, `L3`, `τ3`, `C3`). -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory


theorem agg_mem_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∈ R} (fun j => t j) =
        (∏ i ∈ R, ((t i).factorial : ℝ)) / ((R.card + ∑ i ∈ R, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∈ R} (fun j => t j) = R.card + ∑ i ∈ R, t i - 1 :=
  sorry


theorem agg_compl_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∉ R} (fun j => t j) =
        (∏ i ∈ Rᶜ, ((t i).factorial : ℝ)) / ((N - R.card + ∑ i ∈ Rᶜ, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∉ R} (fun j => t j) = N - R.card + ∑ i ∈ Rᶜ, t i - 1 :=
  sorry

/-- **A monomial weight on a piece**: `∫_{piece} yᵗ U^m = (∏ tᵢ!) · pieceM N r k a b … m` with
`a = Σ_{i ∈ R} tᵢ` and `b = Σ_{i ∉ R} tᵢ`. -/
theorem piece_mono {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceM N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m :=
  sorry


theorem roughPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    roughPart (cls R K i) a = if i ∈ R then a else 0 :=
  sorry


theorem smoothPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    smoothPart (cls R K i) a = if i ∈ Rᶜ then a else 0 :=
  sorry


theorem shift_cls {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (i : Fin N) :
    shiftV g (R ∪ K) i = clsShift g (cls R K i) :=
  sorry

/-- **One distinguished coordinate**: `∫_{piece} yᵢ^a U^m = a! · pieceM` at the class of `i`. -/
theorem piece_w1 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (a m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (a.factorial : ℝ) * pieceM N R.card K.card (roughPart (cls R K i) a)
        (smoothPart (cls R K i) a) g L τ C m :=
  sorry

/-- **Two distinct distinguished coordinates**: `∫_{piece} yᵢ^a yⱼ^b U^m = a! b! · pieceM` at
the classes of `i` and `j` (their degrees add within a group). -/
theorem piece_w2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i j : Fin N) (hij : i ≠ j) (a b m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * y j ^ b * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      ((a.factorial : ℝ) * (b.factorial : ℝ)) *
        pieceM N R.card K.card (roughPart (cls R K i) a + roughPart (cls R K j) b)
          (smoothPart (cls R K i) a + smoothPart (cls R K j) b) g L τ C m :=
  sorry

/-- Summing a class function over the coordinates. -/
theorem sum_cls {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (h : Fin 3 → ℝ) :
    ∑ i, h (cls R K i) = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * h c :=
  sorry

/-- **Placing an ordered pair of distinguished coordinates** (V2c's placements collapsed by the
symmetry within each class): off the diagonal the pair of classes `(c, d)` occurs
`n_c n_d − [c = d] n_c` times, on the diagonal `i = j` the class `c` occurs `n_c` times. -/
theorem sum_place2 {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → Fin N → ℝ)
    (φ : Fin 3 → Fin 3 → ℝ) (ψ : Fin 3 → ℝ)
    (hoff : ∀ i j, i ≠ j → f i j = φ (cls R K i) (cls R K j))
    (hdiag : ∀ i, f i i = ψ (cls R K i)) :
    ∑ i, ∑ j, f i j = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * ψ c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N R.card K.card c d * φ c d :=
  sorry

/-- **Collecting by moments**: the placement sum is `q2J`. -/
theorem q2J_expand (N r k : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (m : ℕ) :
    q2J N r k g L τ C m = ∑ c : Fin 3, (clsCount N r k c : ℝ) * diagT N r k g L τ C m c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N r k c d * pairT N r k g L τ C m c d :=
  sorry

/-- **`∫_{piece} U^m P̂₂(y + g·1_{R∪K})²` in closed form** (two distinguished coordinates). -/
theorem piece_P2sq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) ^ 2 *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      q2J N R.card K.card g L τ C m :=
  sorry

/-- **`∫_{piece} U^m P̂₂(y + g·1_{R∪K})`** for any power `m` (V2g's `p2J`). -/
theorem piece_P2m {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      p2J N R.card K.card g L τ C m :=
  sorry

/-- **`∫_{piece} U^m`** for any power `m` (V2f's `pieceJ … m 0`). -/
theorem piece_pow {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      pieceJ N R.card K.card g L τ C m 0 :=
  sorry

/-- **`(N + 1) ∫_{T̂} (U P̂₂ + U³/3)²` in closed form** (any `N ≥ 1`, data with `0 ≤ g ≤ C(1)`,
`C(N) < N g`). -/
theorem p2p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) *
          (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) =
      p2p2EntryVal N g L τ C :=
  sorry


theorem pieceM_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceM N r k a b g L τ C m : ℚ) : ℝ) =
      pieceM N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m :=
  sorry


theorem clsShift_cast (g : ℚ) (c : Fin 3) : ((clsShift g c : ℚ) : ℝ) = clsShift (g : ℝ) c :=
  sorry


theorem q2Coef_cast (N r k : ℕ) (g : ℚ) (A B : ℕ) :
    ((q2Coef N r k g A B : ℚ) : ℝ) = q2Coef N r k (g : ℝ) A B :=
  sorry


theorem q2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((q2Sum N g L τ C m : ℚ) : ℝ) = q2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m :=
  sorry


theorem p2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((p2Sum N g L τ C m : ℚ) : ℝ) = p2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m :=
  sorry


theorem p2p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2p2EntryVal N g L τ C : ℚ) : ℝ) =
      p2p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) :=
  sorry


theorem q2Sum_table3 : q2Sum 44 g L τ C 2 = (3721212168331028519748308970328951038185792337510810540226343119085005100382118243388939929073974240705194256627670803250493222973048404504729378100815164851 / 19218624683167755902483553801149155361150055971336758468293306328111992447832780724764623059286350326146930456161499023437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem p2Sum4_table3 : p2Sum 44 g L τ C 4 = (1054922107983414915906906937769327296716403318132917952691051050531767556339980615191742253819953865176715501384481084502270708223994744906216464469200181833 / 22421728797029048552897479434674014588008398633226218213008857382797324522471577512225393569167408713838085532188415527343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem jtSum6_table3 : jtSum 44 g L τ C 6 0 = (1252155086603792447152587540484619879680414957541407403502562097249654124935188516248764747333977754631495416814468563894505101186320460294467373088090599993 / 65770404471285209088499273008377109458157969324130240091492648322872151932583294035861154469557732227258384227752685546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- **`J_T[P₂, P₂]` at Table 3** as a rational. -/
theorem p2p2EntryVal_table3 : p2p2EntryVal 44 g L τ C = (7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- **`J_T[P₂, P₂]` at Table 3** (computational certificate `p2p2EntryVal_table3`): the diagonal
bilinear `J_T` entry of the generator `gen 0 {2} = P₂` of `B₂₁`,
`45 ∫_{T̂} (U P̂₂ + U³/3)² ≈ 2.27107 × 10⁻⁵⁸`, is an explicit rational. -/
theorem jT_P2_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- The diagonal entry is `J_T(P₂)` of §9.4 (`jTbil_self`). -/
theorem jT_P2_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

end BGP212.Challenge
