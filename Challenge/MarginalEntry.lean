/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.MarginalEntry
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2f: all three endpoint branches and the marginal Gram entry `J_T[1, 1]`

Statements only; proofs live in `Solution/MarginalEntry.lean` and the computational certificate in
`Solution/MarginalEntryCert.lean`. Objects are defined in `BGP212/MarginalEntry.lean` (with V2e-B's
`boxTri`, `boxVal`, `innerVal`, V2e-A's aggregates and `endpointAgg`, V2d's `jT`, `marginalJ`,
`endpoint`, V2b's `supportT`, `Qset`, `pieceSet`, V0's `gen`). The general statements keep `g`,
`L`, `τ`, `C` as parameters; Table 3 enters only through `BGP212.Params` (`g3`, `L3`, `τ3`, `C3`). -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

/-- `∫_{boxTri A B D} u₁^α u₂^β (p − u₁)^{m₁} (L' − u₁ − u₂)^{m₂} = twoPowVal`. -/
theorem box_twoPow (A B D p L' : ℝ) (α β m₁ m₂ : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (p - q.1) ^ m₁ * (L' - q.1 - q.2) ^ m₂ =
      twoPowVal A B D p L' α β m₁ m₂ :=
  sorry

/-- **The four-cell decomposition.** On a piece region `boxTri c M M` the block
`u₁^α u₂^β U^m (L − S)^n` integrates to `cellsVal`: the cap cell, the `L − S` cell on the cap
side, the `g` cell and the `L − S` cell on the `g` side, each a signed combination of `boxTri`
cells (`setIntegral_sdiff`) on which `U` is one affine branch (V2e-B's branch lemmas). -/
theorem cells_integral (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (α β m n : ℕ) :
    ∫ q in boxTri c M M, q.1 ^ α * q.2 ^ β *
        ((endpointAgg g L C r k q.1 q.2) ^ m * (L - ((r + k) * g + q.1 + q.2)) ^ n) =
      cellsVal g L C r k c M α β m n :=
  sorry


theorem mem_pieceSet_agg {N : ℕ} (R : Finset (Fin N)) (c M : ℝ) (y : Fin N → ℝ)
    (hy : y ∈ simplexF (Fin N) M) :
    y ∈ pieceSet N R c M ↔ (aggR R y, aggS R y) ∈ boxTri c M M :=
  sorry

/-- **A piece, two aggregates.** For a piece with `R` and `Rᶜ` nonempty, the block
`yᵗ U^m (L − S)^n` integrates to `aggConst R t · aggConst Rᶜ t · cellsVal`. -/
theorem piece_block {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        ((endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m *
          (L - ((R.card + k) * g + aggR R y + aggS R y)) ^ n) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        cellsVal g L C R.card k c M (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m n :=
  sorry

/-- **A piece with no rough coordinates** (`R = ∅`): one aggregate `u₂ = Σ y`, with `U = C(1)`
up to `u₂ = L − k g − C(1)` and `U = L − k g − u₂` beyond (for `g ≤ C(1)`). -/
theorem piece_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n =
      1 / ((N - 1).factorial : ℝ) * seg0Val g L C k M (N - 1) m n :=
  sorry

/-- **Inclusion–exclusion with a stratum-dependent integrand**: V2b's `indicator_supportT` with the
integrand allowed to depend on the rough set (`G R` is used on the pieces `Qset R K`). -/
theorem indicator_supportT_strat {N : ℕ} (g L : ℝ) (C : ℕ → ℝ)
    (G : Finset (Fin N) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator (fun x => G (roughSet g x) x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x :=
  sorry

/-- **`J_T(1)` as a signed sum of piece integrals.** -/
theorem jT_one_pieces (N : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    jT N g L τ C (fun _ => 1) = (N + 1 : ℝ) * ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset,
      (-1 : ℝ) ^ K.card * ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 :=
  sorry


theorem count_by_card (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * F R.card K.card =
      ∑ r ∈ Finset.range (N + 1), (N.choose r : ℝ) *
        ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : ℝ) * (-1) ^ k * F r k :=
  sorry

/-- Every piece integral of `U²` is the closed form `pieceJ` at its cardinalities (empty pieces,
the stratum `R = ∅`, and two aggregates). -/
theorem piece_eq_pieceJ {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 =
      pieceJ N R.card K.card g L τ C 2 0 :=
  sorry

/-- **`J_T(1)` in closed form** (any dimension `N ≥ 1` and data with `0 ≤ g ≤ C(1)` whose full
rough stratum is empty, `C(N) < N g`): `jT N g L τ C 1 = jtSum N g L τ C 2 0`. -/
theorem jT_one_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    jT N g L τ C (fun _ => 1) = jtSum N g L τ C 2 0 :=
  sorry


theorem twoPowVal_cast (A B D p L' : ℚ) (α β m₁ m₂ : ℕ) :
    ((twoPowVal A B D p L' α β m₁ m₂ : ℚ) : ℝ) =
      twoPowVal (A : ℝ) (B : ℝ) (D : ℝ) (p : ℝ) (L' : ℝ) α β m₁ m₂ :=
  sorry


theorem cellsVal_cast (g L : ℚ) (C : ℕ → ℚ) (r k : ℕ) (c M : ℚ) (α β m n : ℕ) :
    ((cellsVal g L C r k c M α β m n : ℚ) : ℝ) =
      cellsVal (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) r k (c : ℝ) (M : ℝ) α β m n :=
  sorry


theorem seg0Val_cast (g L : ℚ) (C : ℕ → ℚ) (k : ℕ) (M : ℚ) (β m n : ℕ) :
    ((seg0Val g L C k M β m n : ℚ) : ℝ) =
      seg0Val (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) k (M : ℝ) β m n :=
  sorry


theorem pieceJ_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceJ N r k g L τ C m n : ℚ) : ℝ) =
      pieceJ N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n :=
  sorry


theorem jtSum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((jtSum N g L τ C m n : ℚ) : ℝ) = jtSum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n :=
  sorry


theorem pieceJ_tail (r k : ℕ) (h : 16 ≤ r + k) : pieceJ 44 r k g L τ C 2 0 = 0 :=
  sorry


theorem pieceJ_high (r k : ℕ) (h : 14 ≤ r) : pieceJ 44 r k g L τ C 2 0 = 0 :=
  sorry


theorem jtSum_table3 : jtSum 44 g L τ C 2 0 = (196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem table3_hyps : 0 ≤ g3 ∧ g3 ≤ C3 1 ∧ C3 44 - ((44 : ℕ) : ℝ) * g3 < 0 :=
  sorry

/-- **`J_T[1, 1]` at Table 3** (computational certificate `jtSum_table3`): with `F = 1`
(the generator `gen 0 ∅` of `B₂₁`), `J_T(1) = 45 ∫_{T̂} U(x̂)² dx̂` is the explicit rational
`V ≈ 1.11935 × 10⁻⁵⁵`. -/
theorem jT_one_table3 : jT 44 g3 L3 τ3 C3 (fun _ => 1) = ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry


theorem eval_gen_zero (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0) = 1 :=
  sorry

/-- **The marginal Gram entry for the generator `gen 0 ∅`**, in V2d's `J_T` form and in
Definition 4.6's marginal form (V2d's `marginal_agrees`). -/
theorem jT_gram_gen00_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ∧
      marginalJ 44 g3 L3 τ3 C3
          (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

end BGP212.Challenge
