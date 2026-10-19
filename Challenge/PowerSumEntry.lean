/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.PowerSumEntry
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2g: a marginal Gram entry with a power sum, `J_T[P₂, 1]`

Statements only; proofs live in `Solution/PowerSumEntry.lean` and the computational certificate in
`Solution/PowerSumEntryCert.lean`. Objects are defined in `BGP212/MarginalEntry.lean` (with V2e-B's
`boxTri`, `boxVal`, `innerVal`, V2e-A's aggregates and `endpointAgg`, V2d's `jT`, `marginalJ`,
`endpoint`, V2b's `supportT`, `Qset`, `pieceSet`, V0's `gen`). The general statements keep `g`,
`L`, `τ`, `C` as parameters; Table 3 enters only through `BGP212.Params` (`g3`, `L3`, `τ3`, `C3`). -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory


theorem jTbil_self (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F F = jT n g L τ C F :=
  sorry


theorem jTbil_comm (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F G : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F G = jTbil n g L τ C G F :=
  sorry

/-- `P₂ = gen 0 {2}` evaluates to `Σᵢ yᵢ²`. -/
theorem eval_gen_P2 (y : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (BGP212.Var.gen 0 {2}) = ∑ i, y i ^ 2 :=
  sorry

/-- **The inner integral of `P₂`**: `∫₀^U P₂(x̂, u) du = U P̂₂(x̂) + U³/3`. -/
theorem inner_P2 (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 {2}) = U * ∑ i, x i ^ 2 + U ^ 3 / 3 :=
  sorry

/-- The constant generator: `∫₀^U 1 du = U`. -/
theorem inner_one (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 0) = U :=
  sorry

/-- **Stratified integration.** For a stratum-dependent integrand `Φ R` (continuous for each
`R`), the integral over the support is the signed sum over pieces of the translated integrands. -/
theorem strat_integral {N : ℕ} (g τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ) (hΦ : ∀ R, Continuous (Φ R)) :
    ∫ x in supportT N g τ C, Φ (roughSet g x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          Φ R (y + shiftV g (R ∪ K)) :=
  sorry

/-- The one-aggregate segment integral `∫_{[0,M]} s^β U(0, s)^m (L − S)^n` (stratum `R = ∅`). -/
theorem seg_integral (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (β m n : ℕ) :
    ∫ s in Set.Icc 0 M, s ^ β * ((endpointAgg g L C 0 k 0 s) ^ m *
        (L - (((0 : ℕ) + k) * g + 0 + s)) ^ n) = seg0Val g L C k M β m n :=
  sorry

/-- **A weighted piece with no rough coordinates** (`R = ∅`), any monomial weight `yᵗ`. -/
theorem piece_r0_w {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) * ((endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n) =
      aggConst (Fin N) t * seg0Val g L C k M (aggExp (Fin N) t) m n :=
  sorry

/-- **A single-coordinate weight on a piece** (`R` and `Rᶜ` nonempty): the Dirichlet exponent of
the group of `i` rises by `e`. -/
theorem piece_single {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (i : Fin N) (e m : ℕ) :
    ∫ y in pieceSet N R c M, y i ^ e * (endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m =
      if i ∈ R then (e.factorial : ℝ) / ((R.card + e - 1).factorial : ℝ) *
          (1 / ((N - R.card - 1).factorial : ℝ)) *
          cellsVal g L C R.card k c M (R.card + e - 1) (N - R.card - 1) m 0
      else 1 / ((R.card - 1).factorial : ℝ) *
          ((e.factorial : ℝ) / ((N - R.card + e - 1).factorial : ℝ)) *
          cellsVal g L C R.card k c M (R.card - 1) (N - R.card + e - 1) m 0 :=
  sorry

/-- Every weighted piece integral is `pieceE` at its cardinalities. -/
theorem piece_single_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (e m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ e * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      if i ∈ R then pieceE N R.card K.card e 0 g L τ C m
      else pieceE N R.card K.card 0 e g L τ C m :=
  sorry

/-- **Placing a distinguished coordinate**: a sum over `i` of a function constant on `R`, on `K`
and on the rest is `r·a + k·b + (N − r − k)·c`. -/
theorem sum_place {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → ℝ)
    (a b c : ℝ) (ha : ∀ i ∈ R, f i = a) (hb : ∀ i ∈ K, f i = b) (hc : ∀ i ∉ R ∪ K, f i = c) :
    ∑ i, f i = R.card * a + K.card * b + ((N - R.card - K.card : ℕ) : ℝ) * c :=
  sorry

/-- **The `P₂` block of a piece**: `∫_{piece} (U P̂₂(y + g·1_{R∪K}) + U³/3) U` in closed form. -/
theorem piece_P2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        ((endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) *
            ∑ i, (y + shiftV g (R ∪ K)) i ^ 2 +
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 3 / 3) *
        endpointAgg g L C R.card K.card (aggR R y) (aggS R y) =
      p2J N R.card K.card g L τ C 2 + pieceJ N R.card K.card g L τ C 4 0 / 3 :=
  sorry

/-- **`(N + 1) ∫_{T̂} (U P̂₂ + U³/3) U` in closed form** (any `N ≥ 1`, data with `0 ≤ g ≤ C(1)`,
`C(N) < N g`). -/
theorem p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) * endpoint g L C x =
      p2EntryVal N g L τ C :=
  sorry


theorem pieceE_cast (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceE N r k eR eS g L τ C m : ℚ) : ℝ) =
      pieceE N r k eR eS (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m :=
  sorry


theorem p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2EntryVal N g L τ C : ℚ) : ℝ) = p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) :=
  sorry


theorem cond_tail (r k : ℕ) (h : 16 ≤ r + k) : C r - r * g < 0 ∨ τ - (r + k) * g < 0 :=
  sorry


theorem cond_high (r k : ℕ) (h : 14 ≤ r) : C r - r * g < 0 ∨ τ - (r + k) * g < 0 :=
  sorry


theorem p2EntryVal_table3 : p2EntryVal 44 g L τ C = (1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- **`J_T[P₂, 1]` at Table 3** (computational certificate `p2EntryVal_table3`): the bilinear
`J_T` entry of the generators `gen 0 {2} = P₂` and `gen 0 ∅ = 1` of `B₂₁`,
`45 ∫_{T̂} (U P̂₂ + U³/3) U ≈ 4.99944 × 10⁻⁵⁷`, is an explicit rational. -/
theorem jT_P2_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- The entry is symmetric: `J_T[1, P₂] = J_T[P₂, 1]`. -/
theorem jT_one_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- Consistency with V2f: the diagonal entry `J_T[1, 1]` of the bilinear form is V2f's `J_T(1)`. -/
theorem jTbil_one_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) :=
  sorry

end BGP212.Challenge
