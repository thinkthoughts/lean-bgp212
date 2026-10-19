/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.MarginalEntry
import Solution.CapCell
import Solution.MarginalEntryCert

/-! # V2f: all three endpoint branches and the marginal Gram entry `J_T[1, 1]` (proofs) -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## Products of two affine powers on a cell -/

theorem int_boxTri (A B D : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn f (boxTri A B D) :=
  hf.continuousOn.integrableOn_compact (boxTri_isCompact A B D)

/-- `∫_{boxTri A B D} u₁^α u₂^β (p − u₁)^{m₁} (L' − u₁ − u₂)^{m₂} = twoPowVal`. -/
theorem box_twoPow (A B D p L' : ℝ) (α β m₁ m₂ : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (p - q.1) ^ m₁ * (L' - q.1 - q.2) ^ m₂ =
      twoPowVal A B D p L' α β m₁ m₂ := by
  have hexp : ∀ q : ℝ × ℝ, q.1 ^ α * q.2 ^ β * (p - q.1) ^ m₁ * (L' - q.1 - q.2) ^ m₂ =
      ∑ i ∈ Finset.range (m₁ + 1), ∑ j ∈ Finset.range (m₂ + 1), ∑ l ∈ Finset.range (j + 1),
        (m₁.choose i : ℝ) * p ^ (m₁ - i) * (-1) ^ i * ((m₂.choose j : ℝ) * L' ^ (m₂ - j) * (-1) ^ j) *
          (j.choose l : ℝ) * (q.1 ^ (α + i + l) * q.2 ^ (β + (j - l))) := by
    intro q
    have h1 : (p - q.1) ^ m₁ = ∑ i ∈ Finset.range (m₁ + 1),
        (m₁.choose i : ℝ) * p ^ (m₁ - i) * (-1) ^ i * q.1 ^ i := by
      rw [show p - q.1 = -q.1 + p by ring, add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_pow]; ring
    have h2 : (L' - q.1 - q.2) ^ m₂ = ∑ j ∈ Finset.range (m₂ + 1),
        (m₂.choose j : ℝ) * L' ^ (m₂ - j) * (-1) ^ j *
          ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * q.1 ^ l * q.2 ^ (j - l) := by
      rw [show L' - q.1 - q.2 = -(q.1 + q.2) + L' by ring, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [neg_pow, add_pow]
      have : (∑ l ∈ Finset.range (j + 1), q.1 ^ l * q.2 ^ (j - l) * (j.choose l : ℝ)) =
          ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * q.1 ^ l * q.2 ^ (j - l) :=
        Finset.sum_congr rfl fun l _ => by ring
      rw [this]; ring
    rw [h1, h2, Finset.mul_sum (Finset.range (m₁ + 1)), Finset.sum_mul (Finset.range (m₁ + 1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum (Finset.range (m₂ + 1))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum (Finset.range (j + 1)), Finset.mul_sum (Finset.range (j + 1))]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun l _ => int_boxTri A B D _ (by fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    int_boxTri A B D _ (by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => int_boxTri A B D _ (by fun_prop)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, box_monomial]

/-! ## The four cells of a piece -/

theorem continuous_endpointAgg (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) :
    Continuous fun q : ℝ × ℝ => endpointAgg g L C r k q.1 q.2 := by
  unfold endpointAgg; fun_prop

/-- **The four-cell decomposition.** On a piece region `boxTri c M M` the block
`u₁^α u₂^β U^m (L − S)^n` integrates to `cellsVal`: the cap cell, the `L − S` cell on the cap
side, the `g` cell and the `L − S` cell on the `g` side, each a signed combination of `boxTri`
cells (`setIntegral_sdiff`) on which `U` is one affine branch (V2e-B's branch lemmas). -/
theorem cells_integral (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (α β m n : ℕ) :
    ∫ q in boxTri c M M, q.1 ^ α * q.2 ^ β *
        ((endpointAgg g L C r k q.1 q.2) ^ m * (L - ((r + k) * g + q.1 + q.2)) ^ n) =
      cellsVal g L C r k c M α β m n := by
  set Lp := L - (r + k) * g with hLp
  set c₁ := C (r + 1) - (r + 1) * g with hc₁
  set c₂ := L - k * g - C (r + 1) with hc₂
  set a := C (r + 1) - r * g with ha
  set A₁ := min c c₁ with hA₁
  set M₃ := min M (Lp - g) with hM₃
  set f : ℝ × ℝ → ℝ := fun q => q.1 ^ α * q.2 ^ β *
    ((endpointAgg g L C r k q.1 q.2) ^ m * (L - ((r + k) * g + q.1 + q.2)) ^ n) with hf
  have hfc : Continuous f := by
    simp only [hf]; have := continuous_endpointAgg g L C r k; fun_prop
  -- branch polynomials, in the shape of `box_twoPow`
  set fcap : ℝ × ℝ → ℝ := fun q => q.1 ^ α * q.2 ^ β * (a - q.1) ^ m * (Lp - q.1 - q.2) ^ n
  set fL : ℝ × ℝ → ℝ := fun q => q.1 ^ α * q.2 ^ β * (0 - q.1) ^ 0 * (Lp - q.1 - q.2) ^ (m + n)
  set fg : ℝ × ℝ → ℝ := fun q => q.1 ^ α * q.2 ^ β * (0 - q.1) ^ 0 * (Lp - q.1 - q.2) ^ n
  have hS : ∀ q : ℝ × ℝ, L - ((r + k) * g + q.1 + q.2) = Lp - q.1 - q.2 := fun q => by
    simp only [hLp]; ring
  -- the sets
  have hA₁c : A₁ ≤ c := min_le_left _ _
  have hA₁c₁ : A₁ ≤ c₁ := min_le_right _ _
  have hM₃M : M₃ ≤ M := min_le_left _ _
  have hM₃L : M₃ ≤ Lp - g := min_le_right _ _
  have hmeas : ∀ A B D, MeasurableSet (boxTri A B D) := fun A B D =>
    (boxTri_isClosed A B D).measurableSet
  have hZ₁P₁ : (boxTri A₁ c₂ M) ⊆ (boxTri A₁ M M) := by
    rintro q ⟨h1, h2, h3, -, h5⟩; exact ⟨h1, h2, h3, by linarith, h5⟩
  have hP₁P : (boxTri A₁ M M) ⊆ (boxTri c M M) := by
    rintro q ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, le_trans h2 hA₁c, h3, h4, h5⟩
  have hQ₁Q : (boxTri A₁ M M₃) ⊆ (boxTri c M M₃) := by
    rintro q ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, le_trans h2 hA₁c, h3, h4, h5⟩
  have hQP : (boxTri c M M₃) ⊆ (boxTri c M M) := by
    rintro q ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, le_trans h5 hM₃M⟩
  have hZ₃ : (boxTri c M M₃) \ (boxTri A₁ M M₃) ⊆ (boxTri c M M) \ (boxTri A₁ M M) := by
    rintro q ⟨hq, hq₁⟩
    refine ⟨hQP hq, fun hp => hq₁ ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hq.2.2.2.2⟩⟩
  -- the integrand on each cell
  have e₁ : ∀ q ∈ (boxTri A₁ c₂ M), f q = fcap q := by
    rintro q ⟨h1, h2, h3, h4, h5⟩
    simp only [hf, fcap, hS q]
    rw [endpointAgg_cap g L C r k q.1 q.2 (le_trans h2 hA₁c₁) h4,
      show C (r + 1) - (↑r * g + q.1) = a - q.1 by rw [ha]; ring]
    ring
  have e₂ : ∀ q ∈ (boxTri A₁ M M) \ (boxTri A₁ c₂ M), f q = fL q := by
    rintro q ⟨⟨h1, h2, h3, h4, h5⟩, hz⟩
    have h6 : c₂ ≤ q.2 := by
      by_contra hc; push Not at hc; exact hz ⟨h1, h2, h3, hc.le, h5⟩
    simp only [hf, fL, hS q]
    rw [endpointAgg_LBranch_cap g L C r k q.1 q.2 (le_trans h2 hA₁c₁) h6, hS q, pow_zero, mul_one,
      ← pow_add]
  have e₃ : ∀ q ∈ (boxTri c M M₃) \ (boxTri A₁ M M₃), f q = g ^ m * fg q := by
    rintro q ⟨⟨h1, h2, h3, h4, h5⟩, hq₁⟩
    have h6 : c₁ ≤ q.1 := by
      by_contra hc; push Not at hc
      exact hq₁ ⟨h1, le_min h2 hc.le, h3, h4, h5⟩
    simp only [hf, fg, hS q]
    rw [endpointAgg_gBranch g L C r k q.1 q.2 h6 (by
      have := le_trans h5 hM₃L; simp only [hLp] at this; linarith), pow_zero, mul_one]
    ring
  have e₄ : ∀ q ∈ ((boxTri c M M) \ (boxTri A₁ M M)) \ ((boxTri c M M₃) \ (boxTri A₁ M M₃)), f q = fL q := by
    rintro q ⟨⟨⟨h1, h2, h3, h4, h5⟩, hp₁⟩, hz⟩
    have h6 : c₁ ≤ q.1 := by
      by_contra hc; push Not at hc
      exact hp₁ ⟨h1, le_min h2 hc.le, h3, h4, h5⟩
    have h7 : Lp - g ≤ q.1 + q.2 := by
      by_contra hc; push Not at hc
      apply hz
      refine ⟨⟨h1, h2, h3, h4, le_min h5 hc.le⟩, fun hq₁ => hp₁ ?_⟩
      exact ⟨hq₁.1, hq₁.2.1, hq₁.2.2.1, hq₁.2.2.2.1, h5⟩
    simp only [hf, fL, hS q]
    rw [endpointAgg_LBranch_g g L C r k q.1 q.2 h6 (by simp only [hLp] at h7; linarith), hS q,
      pow_zero, mul_one, ← pow_add]
  -- integrability
  have iP : ∀ φ : ℝ × ℝ → ℝ, Continuous φ → ∀ A B D, IntegrableOn φ (boxTri A B D) :=
    fun φ hφ A B D => int_boxTri A B D φ hφ
  have cfL : Continuous fL := by simp only [fL]; fun_prop
  have cfg : Continuous fg := by simp only [fg]; fun_prop
  -- assemble
  have sd : ∀ (φ : ℝ × ℝ → ℝ) (S T : Set (ℝ × ℝ)), MeasurableSet T → IntegrableOn φ S → T ⊆ S →
      ∫ q in S \ T, φ q = (∫ q in S, φ q) - ∫ q in T, φ q :=
    fun φ S T hT hS hTS => setIntegral_sdiff hT hS hTS
  have s₁ : ∫ q in boxTri c M M, f q =
      (∫ q in boxTri A₁ M M, f q) + ∫ q in boxTri c M M \ boxTri A₁ M M, f q := by
    rw [sd f _ _ (hmeas _ _ _) (iP f hfc _ _ _) hP₁P]; ring
  have s₂ : ∫ q in boxTri A₁ M M, f q =
      (∫ q in boxTri A₁ c₂ M, f q) + ∫ q in boxTri A₁ M M \ boxTri A₁ c₂ M, f q := by
    rw [sd f _ _ (hmeas _ _ _) (iP f hfc _ _ _) hZ₁P₁]; ring
  have s₃ : ∫ q in boxTri c M M \ boxTri A₁ M M, f q =
      (∫ q in boxTri c M M₃ \ boxTri A₁ M M₃, f q) +
        ∫ q in (boxTri c M M \ boxTri A₁ M M) \ (boxTri c M M₃ \ boxTri A₁ M M₃), f q := by
    rw [sd f _ _ ((hmeas _ _ _).diff (hmeas _ _ _))
      ((iP f hfc _ _ _).mono_set Set.diff_subset) hZ₃]; ring
  have i₁ : ∫ q in (boxTri A₁ c₂ M), f q = twoPowVal A₁ c₂ M a Lp α β m n := by
    rw [setIntegral_congr_fun (hmeas _ _ _) e₁, box_twoPow]
  have i₂ : ∫ q in (boxTri A₁ M M) \ (boxTri A₁ c₂ M), f q =
      twoPowVal A₁ M M 0 Lp α β 0 (m + n) - twoPowVal A₁ c₂ M 0 Lp α β 0 (m + n) := by
    rw [setIntegral_congr_fun ((hmeas _ _ _).diff (hmeas _ _ _)) e₂,
      sd fL _ _ (hmeas _ _ _) (iP fL cfL _ _ _) hZ₁P₁, box_twoPow, box_twoPow]
  have i₃ : ∫ q in (boxTri c M M₃) \ (boxTri A₁ M M₃), f q =
      g ^ m * (twoPowVal c M M₃ 0 Lp α β 0 n - twoPowVal A₁ M M₃ 0 Lp α β 0 n) := by
    rw [setIntegral_congr_fun ((hmeas _ _ _).diff (hmeas _ _ _)) e₃, integral_const_mul,
      sd fg _ _ (hmeas _ _ _) (iP fg cfg _ _ _) hQ₁Q, box_twoPow, box_twoPow]
  have i₄ : ∫ q in ((boxTri c M M) \ (boxTri A₁ M M)) \ ((boxTri c M M₃) \ (boxTri A₁ M M₃)), f q =
      (twoPowVal c M M 0 Lp α β 0 (m + n) - twoPowVal A₁ M M 0 Lp α β 0 (m + n)) -
        (twoPowVal c M M₃ 0 Lp α β 0 (m + n) - twoPowVal A₁ M M₃ 0 Lp α β 0 (m + n)) := by
    rw [setIntegral_congr_fun (((hmeas _ _ _).diff (hmeas _ _ _)).diff
      ((hmeas _ _ _).diff (hmeas _ _ _))) e₄,
      sd fL _ _ ((hmeas _ _ _).diff (hmeas _ _ _))
        ((iP fL cfL _ _ _).mono_set Set.diff_subset) hZ₃,
      sd fL _ _ (hmeas _ _ _) (iP fL cfL _ _ _) hP₁P,
      sd fL _ _ (hmeas _ _ _) (iP fL cfL _ _ _) hQ₁Q,
      box_twoPow, box_twoPow, box_twoPow, box_twoPow]
  rw [s₁, s₂, s₃, i₁, i₂, i₃, i₄, cellsVal]
  simp only [← hc₁, ← hc₂, ← ha, ← hLp]
  rw [← hA₁, ← hM₃]
  ring

/-! ## Piece integrals -/

theorem mem_pieceSet_agg {N : ℕ} (R : Finset (Fin N)) (c M : ℝ) (y : Fin N → ℝ)
    (hy : y ∈ simplexF (Fin N) M) :
    y ∈ pieceSet N R c M ↔ (aggR R y, aggS R y) ∈ boxTri c M M := by
  have hsum := sum_eq_aggR_add_aggS R y
  have h1 : 0 ≤ aggR R y := Finset.sum_nonneg fun i _ => hy.1 i
  have h2 : 0 ≤ aggS R y := Finset.sum_nonneg fun i _ => hy.1 i
  simp only [pieceSet, boxTri, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hc, hM⟩
    exact ⟨h1, hc, h2, by linarith, by linarith⟩
  · rintro ⟨-, hc, -, -, hM⟩
    exact ⟨hy.1, hc, by linarith⟩

/-- **A piece, two aggregates.** For a piece with `R` and `Rᶜ` nonempty, the block
`yᵗ U^m (L − S)^n` integrates to `aggConst R t · aggConst Rᶜ t · cellsVal`. -/
theorem piece_block {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        ((endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m *
          (L - ((R.card + k) * g + aggR R y + aggS R y)) ^ n) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        cellsVal g L C R.card k c M (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m n := by
  set Φ : ℝ × ℝ → ℝ := fun q => (endpointAgg g L C R.card k q.1 q.2) ^ m *
    (L - ((R.card + k) * g + q.1 + q.2)) ^ n with hΦ
  have hΦc : Continuous Φ := by
    simp only [hΦ]; have := continuous_endpointAgg g L C R.card k; fun_prop
  set Z := boxTri c M M
  have hZm : MeasurableSet Z := (boxTri_isClosed _ _ _).measurableSet
  have step1 : ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        ((endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m *
          (L - ((R.card + k) * g + aggR R y + aggS R y)) ^ n) =
      ∫ y in simplexF (Fin N) M, (∏ i, y i ^ t i) * Z.indicator Φ (aggR R y, aggS R y) := by
    rw [setIntegral_congr_fun (pieceSet_measurableSet N R c M) (g := fun y =>
      (∏ i, y i ^ t i) * Z.indicator Φ (aggR R y, aggS R y)) (fun y hy => by
        simp only
        rw [Set.indicator_of_mem ((mem_pieceSet_agg R c M y ⟨hy.1, hy.2.2⟩).mp hy)])]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (simplexF_measurableSet M)
      (pieceSet_subset_simplexF N R c M) fun y hy => ?_).symm
    rw [Set.indicator_of_notMem (fun h => hy.2 ((mem_pieceSet_agg R c M y hy.1).mpr h)), mul_zero]
  obtain ⟨Bd, hBd⟩ := (tri_isCompact M).exists_bound_of_continuousOn hΦc.continuousOn
  rw [step1, two_group_fin R hR hRc M t _ (hΦc.measurable.indicator hZm) Bd (fun q hq => by
    rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    by_cases h : q ∈ Z
    · rw [Set.indicator_of_mem h]; exact hBd q hq
    · rw [Set.indicator_of_notMem h]; exact le_trans (norm_nonneg _) (hBd q hq))]
  congr 1
  rw [← cells_integral]
  have hfun : (fun q : ℝ × ℝ => q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
      q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * Z.indicator Φ q) =
      Z.indicator (fun q : ℝ × ℝ => q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
        q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * Φ q) := by
    funext q; by_cases h : q ∈ Z
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [hfun, setIntegral_indicator hZm, Set.inter_eq_right.mpr (boxTri_subset_tri _ _ _)]

/-- **A piece with no rough coordinates** (`R = ∅`): one aggregate `u₂ = Σ y`, with `U = C(1)`
up to `u₂ = L − k g − C(1)` and `U = L − k g − u₂` beyond (for `g ≤ C(1)`). -/
theorem piece_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n =
      1 / ((N - 1).factorial : ℝ) * seg0Val g L C k M (N - 1) m n := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hset : pieceSet N ∅ c M = simplexF (Fin N) M := by
    ext y; simp [pieceSet, simplexF, hc]
  have hagg : ∀ y : Fin N → ℝ, aggR ∅ y = 0 ∧ aggS ∅ y = ∑ i, y i := fun y => by
    simp [aggR, aggS]
  set h : ℝ → ℝ := fun s => (endpointAgg g L C 0 k 0 s) ^ m * (L - (((0 : ℕ) + k) * g + 0 + s)) ^ n
    with hh
  have hhc : Continuous h := by
    simp only [hh]; have := continuous_endpointAgg g L C 0 k
    exact ((this.comp (continuous_const.prodMk continuous_id)).pow m).mul (by fun_prop)
  rw [hset, setIntegral_congr_fun (simplexF_measurableSet M) (g := fun y =>
    (∏ i, y i ^ (fun _ => (0 : ℕ)) i) * h (∑ i, y i)) (fun y _ => by
      simp only [hh, (hagg y).1, (hagg y).2, pow_zero, Finset.prod_const_one, one_mul])]
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    hhc.continuousOn
  rw [one_group M (fun _ => 0) h hhc.measurable Bd (fun s hs => by
    rw [← Real.norm_eq_abs]; exact hBd s hs), aggConst_zero, aggExp_zero, Fintype.card_fin]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hM]
  set X := max 0 (min (L - k * g - C 1) M) with hX
  have hX0 : 0 ≤ X := le_max_left _ _
  have hXM : X ≤ M := max_le hM (min_le_right _ _)
  have hcont : Continuous fun s => s ^ (N - 1) * h s := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 X)
    (hcont.intervalIntegrable X M)]
  have hLp : ∀ s : ℝ, L - (((0 : ℕ) + k) * g + 0 + s) = L - k * g - s := fun s => by push_cast; ring
  have a1 : ∫ s in (0 : ℝ)..X, s ^ (N - 1) * h s =
      ∫ s in (0 : ℝ)..X, C 1 ^ m * ((L - k * g - s) ^ n * s ^ (N - 1)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le hX0] at hs
    have hXe : X = min (L - k * g - C 1) M := max_eq_right (by
      by_contra hc'; push Not at hc'
      have : X = 0 := max_eq_left hc'.le
      linarith [hs.1, hs.2])
    have hs2 : s ≤ L - k * g - C 1 := le_trans hs.2 (hXe ▸ min_le_left _ _)
    simp only [hh]
    rw [endpointAgg_cap g L C 0 k 0 s (by push_cast; linarith) (by push_cast; linarith), hLp]
    push_cast; ring
  have a2 : ∫ s in X..M, s ^ (N - 1) * h s =
      ∫ s in X..M, (L - k * g - s) ^ (m + n) * s ^ (N - 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le hXM] at hs
    have hs2 : L - k * g - C 1 ≤ s := by
      by_contra hc'; push Not at hc'
      have : s ≤ min (L - k * g - C 1) M := le_min hc'.le hs.2
      linarith [hs.1, le_max_right 0 (min (L - k * g - C 1) M)]
    simp only [hh]
    rw [endpointAgg_LBranch_cap g L C 0 k 0 s (by push_cast; linarith) (by push_cast; linarith),
      hLp, pow_add]; ring
  rw [a1, a2, intervalIntegral.integral_const_mul, innerVal_eq,
    ← intervalIntegral.integral_interval_sub_left (a := 0) (b := M) (c := X)
      ((by fun_prop : Continuous fun s : ℝ => (L - k * g - s) ^ (m + n) * s ^ (N - 1)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => (L - k * g - s) ^ (m + n) * s ^ (N - 1)).intervalIntegrable _ _),
    innerVal_eq, innerVal_eq, seg0Val]

/-! ## Stratified inclusion–exclusion -/

/-- **Inclusion–exclusion with a stratum-dependent integrand**: V2b's `indicator_supportT` with the
integrand allowed to depend on the rough set (`G R` is used on the pieces `Qset R K`). -/
theorem indicator_supportT_strat {N : ℕ} (g L : ℝ) (C : ℕ → ℝ)
    (G : Finset (Fin N) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator (fun x => G (roughSet g x) x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x := by
  classical
  set R0 := roughSet g x with hR0
  have hrow : ∀ R : Finset (Fin N),
      ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x =
        if R = R0 then (if (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card then G R x else 0)
        else 0 := by
    intro R
    have hmem : ∀ K, x ∈ Qset g L C R K ↔
        ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card ∧ R ⊆ R0) ∧ K ⊆ R0 := by
      intro K
      simp only [Qset, Set.mem_setOf_eq, Finset.mem_union]
      constructor
      · rintro ⟨h0, hg, hL, hC⟩
        exact ⟨⟨h0, hL, hC, fun i hi => (mem_roughSet g x i).mpr (hg i (Or.inl hi))⟩,
          fun i hi => (mem_roughSet g x i).mpr (hg i (Or.inr hi))⟩
      · rintro ⟨⟨h0, hL, hC, hRs⟩, hKs⟩
        refine ⟨h0, fun i hi => ?_, hL, hC⟩
        rcases hi with hi | hi
        · exact (mem_roughSet g x i).mp (hRs hi)
        · exact (mem_roughSet g x i).mp (hKs hi)
    by_cases hb : (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card ∧ R ⊆ R0
    · have hsum : ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x =
          G R x * ∑ K ∈ (Rᶜ ∩ R0).powerset, (-1 : ℝ) ^ K.card := by
        rw [Finset.mul_sum]
        have hfilt : (Rᶜ ∩ R0).powerset = Rᶜ.powerset.filter (· ⊆ R0) := by
          ext K; simp [Finset.subset_inter_iff]
        rw [hfilt, Finset.sum_filter]
        refine Finset.sum_congr rfl fun K _ => ?_
        by_cases hK : K ⊆ R0
        · rw [Set.indicator_of_mem ((hmem K).mpr ⟨hb, hK⟩), if_pos hK]; ring
        · rw [Set.indicator_of_notMem (fun h => hK ((hmem K).mp h).2), if_neg hK]; ring
      rw [hsum, sum_powerset_neg_one]
      have hiff : Rᶜ ∩ R0 = ∅ ↔ R = R0 := by
        constructor
        · intro h
          refine Finset.Subset.antisymm hb.2.2.2 fun i hi => ?_
          by_contra hiR
          have : i ∈ Rᶜ ∩ R0 := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hiR, hi⟩
          rw [h] at this; simp at this
        · rintro rfl; ext i; simp
      by_cases hRR : R = R0
      · rw [if_pos (hiff.mpr hRR), if_pos hRR, if_pos ⟨hb.1, hb.2.1, hb.2.2.1⟩, mul_one]
      · rw [if_neg (fun h => hRR (hiff.mp h)), if_neg hRR, mul_zero]
    · have hz : ∀ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x = 0 := by
        intro K _
        rw [Set.indicator_of_notMem (fun h => hb ((hmem K).mp h).1), mul_zero]
      rw [Finset.sum_eq_zero hz]
      by_cases hRR : R = R0
      · subst hRR
        rw [if_pos rfl, if_neg]
        rintro ⟨h0, hL, hC⟩
        exact hb ⟨h0, hL, hC, Finset.Subset.refl _⟩
      · rw [if_neg hRR]
  rw [Finset.sum_congr rfl fun R _ => hrow R, Finset.sum_ite_eq' Finset.univ R0]
  simp only [Finset.mem_univ, if_true, Set.indicator_apply, supportT, Set.mem_setOf_eq, ← hR0]

theorem continuous_stratumEndpoint {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R : Finset (Fin n)) :
    Continuous fun x : Fin n → ℝ => stratumEndpoint g L C R x := by
  unfold stratumEndpoint aggR; fun_prop

/-- **`J_T(1)` as a signed sum of piece integrals.** -/
theorem jT_one_pieces (N : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    jT N g L τ C (fun _ => 1) = (N + 1 : ℝ) * ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset,
      (-1 : ℝ) ^ K.card * ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 := by
  classical
  unfold jT
  congr 1
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [hatSupport_eq, ← integral_indicator (supportT_measurableSet N g τ C)]
  have hfun : (supportT N g τ C).indicator (fun x => (endpoint g L C x) ^ 2) =
      fun x => (supportT N g τ C).indicator
        (fun x => (fun R x => (stratumEndpoint g L C R x) ^ 2) (roughSet g x) x) x := by
    funext x
    congr 1
  rw [hfun]
  simp_rw [indicator_supportT_strat g τ C (fun R x => (stratumEndpoint g L C R x) ^ 2)]
  have hint : ∀ R K, Integrable ((Qset g τ C R K).indicator
      (fun x : Fin N → ℝ => (stratumEndpoint g L C R x) ^ 2)) := by
    intro R K
    rw [integrable_indicator_iff (Qset_measurableSet g τ C R K)]
    refine (((continuous_stratumEndpoint g L C R).pow 2).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin N) τ)).mono_set ?_
    exact fun x hx => ⟨hx.1, hx.2.2.1⟩
  rw [integral_finsetSum _ fun R _ => integrable_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [integral_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun K hK => ?_
  have hRK : Disjoint R K := Finset.disjoint_left.mpr fun i hiR hiK =>
    (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR
  rw [integral_const_mul, integral_Qset g τ C hg R K hRK]
  congr 1
  refine setIntegral_congr_fun (pieceSet_measurableSet _ _ _ _) fun y _ => ?_
  rw [stratumEndpoint_shift g L C R K hRK y]

/-! ## Counting by cardinalities -/

theorem count_by_card (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * F R.card K.card =
      ∑ r ∈ Finset.range (N + 1), (N.choose r : ℝ) *
        ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : ℝ) * (-1) ^ k * F r k := by
  classical
  have hin : ∀ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * F R.card K.card =
      ∑ k ∈ Finset.range (N - R.card + 1), ((N - R.card).choose k : ℝ) * (-1) ^ k * F R.card k := by
    intro R
    rw [Finset.sum_powerset_apply_card (fun k => (-1 : ℝ) ^ k * F R.card k),
      Finset.card_compl, Fintype.card_fin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [nsmul_eq_mul]; ring
  simp_rw [hin]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
    (fun r => ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : ℝ) * (-1) ^ k * F r k),
    Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [nsmul_eq_mul]

/-! ## Each piece in closed form, and `J_T(1)` -/

/-- Every piece integral of `U²` is the closed form `pieceJ` at its cardinalities (empty pieces,
the stratum `R = ∅`, and two aggregates). -/
theorem piece_eq_pieceJ {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 =
      pieceJ N R.card K.card g L τ C 2 0 := by
  unfold pieceJ
  by_cases he : C R.card - R.card * g < 0 ∨ τ - (R.card + K.card) * g < 0
  · rw [if_pos he, pieceSet_empty N R _ _ (by
      rintro ⟨h1, h2⟩; rcases he with h | h <;> linarith), Measure.restrict_empty,
      integral_zero_measure]
  rw [if_neg he]
  push Not at he
  by_cases hr : R.card = 0
  · rw [if_pos hr]
    have hR : R = ∅ := Finset.card_eq_zero.mp hr
    subst hR
    have := piece_r0 hN g L C hC1 K.card _ (τ - (0 + K.card) * g) (by simpa using he.1)
      (by simpa using he.2) 2 0
    simp only [pow_zero, mul_one, Finset.card_empty] at this ⊢
    rw [show τ - ((0 : ℕ) + K.card) * g = τ - (0 + K.card) * g by push_cast; ring]
    convert this using 2
    · simp
    · congr 1; push_cast; ring
  · rw [if_neg hr]
    have hRne : R.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hr)
    have hRc : Rᶜ.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
      subst h
      rw [Finset.card_univ, Fintype.card_fin] at he
      linarith [he.1]
    have key := piece_block R hRne hRc g L C K.card (C R.card - R.card * g)
      (τ - (R.card + K.card) * g) (fun _ => 0) 2 0
    simp only [pow_zero, Finset.prod_const_one, one_mul, mul_one] at key
    rw [key, aggConst_zero, aggConst_zero, aggExp_zero, aggExp_zero, Fintype.card_coe,
      card_compl_subtype]

/-- **`J_T(1)` in closed form** (any dimension `N ≥ 1` and data with `0 ≤ g ≤ C(1)` whose full
rough stratum is empty, `C(N) < N g`): `jT N g L τ C 1 = jtSum N g L τ C 2 0`. -/
theorem jT_one_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    jT N g L τ C (fun _ => 1) = jtSum N g L τ C 2 0 := by
  rw [jT_one_pieces N g L τ C hg]
  simp_rw [piece_eq_pieceJ hN g L τ C hC1 hCN]
  rw [count_by_card N (fun r k => pieceJ N r k g L τ C 2 0), jtSum]

/-! ## Rational values -/

theorem twoPowVal_cast (A B D p L' : ℚ) (α β m₁ m₂ : ℕ) :
    ((twoPowVal A B D p L' α β m₁ m₂ : ℚ) : ℝ) =
      twoPowVal (A : ℝ) (B : ℝ) (D : ℝ) (p : ℝ) (L' : ℝ) α β m₁ m₂ := by
  simp [twoPowVal, boxVal_cast]

theorem cellsVal_cast (g L : ℚ) (C : ℕ → ℚ) (r k : ℕ) (c M : ℚ) (α β m n : ℕ) :
    ((cellsVal g L C r k c M α β m n : ℚ) : ℝ) =
      cellsVal (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) r k (c : ℝ) (M : ℝ) α β m n := by
  simp only [cellsVal]
  push_cast [twoPowVal_cast, Rat.cast_min]
  rfl

theorem seg0Val_cast (g L : ℚ) (C : ℕ → ℚ) (k : ℕ) (M : ℚ) (β m n : ℕ) :
    ((seg0Val g L C k M β m n : ℚ) : ℝ) =
      seg0Val (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) k (M : ℝ) β m n := by
  simp only [seg0Val]
  push_cast [innerVal_cast, Rat.cast_min, Rat.cast_max]
  rfl

theorem pieceJ_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceJ N r k g L τ C m n : ℚ) : ℝ) =
      pieceJ N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  unfold pieceJ
  have hcond : (C r - r * g < 0 ∨ τ - (r + k) * g < 0) ↔
      ((C r : ℝ) - r * (g : ℝ) < 0 ∨ (τ : ℝ) - (r + k) * (g : ℝ) < 0) := by
    constructor <;> rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  by_cases h : C r - r * g < 0 ∨ τ - (r + k) * g < 0
  · rw [if_pos h, if_pos (hcond.mp h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h'))]
    split_ifs
    · push_cast [seg0Val_cast]; rfl
    · push_cast [cellsVal_cast]; rfl

theorem jtSum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((jtSum N g L τ C m n : ℚ) : ℝ) = jtSum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  simp [jtSum, pieceJ_cast]

/-! ## Table 3: the marginal Gram entry `J_T[1, 1]` -/

theorem table3_hyps : 0 ≤ g3 ∧ g3 ≤ C3 1 ∧ C3 44 - ((44 : ℕ) : ℝ) * g3 < 0 := by
  have h1 : BGP212.Params.C 1 = 777 / 1250 := by decide +kernel
  have h44 : BGP212.Params.C 44 = 1081 / 1250 := by decide +kernel
  simp only [g3, C3, h1, h44, BGP212.Params.g]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **`J_T[1, 1]` at Table 3** (computational certificate `jtSum_table3`): with `F = 1`
(the generator `gen 0 ∅` of `B₂₁`), `J_T(1) = 45 ∫_{T̂} U(x̂)² dx̂` is the explicit rational
`V ≈ 1.11935 × 10⁻⁵⁵`. -/
theorem jT_one_table3 : jT 44 g3 L3 τ3 C3 (fun _ => 1) = ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := table3_hyps
  rw [jT_one_eq (by norm_num) g3 L3 τ3 C3 h0 h1 h2,
    show jtSum 44 g3 L3 τ3 C3 2 0 = ((jtSum 44 BGP212.Params.g BGP212.Params.L BGP212.Params.τ
      BGP212.Params.C 2 0 : ℚ) : ℝ) from (jtSum_cast 44 _ _ _ _ 2 0).symm, jtSum_table3]

theorem eval_gen_zero (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0) = 1 := by
  simp [BGP212.Var.gen, BGP212.Var.Plam]

/-- **The marginal Gram entry for the generator `gen 0 ∅`**, in V2d's `J_T` form and in
Definition 4.6's marginal form (V2d's `marginal_agrees`). -/
theorem jT_gram_gen00_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ∧
      marginalJ 44 g3 L3 τ3 C3
          (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have hF : (fun x : Fin 45 → ℝ => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      fun _ => 1 := funext eval_gen_zero
  rw [hF]
  refine ⟨jT_one_table3, ?_⟩
  rw [marginal_agrees 44 g3 L3 τ3 C3 g_nonneg tau_le_L capStep_table3 C_zero_table3 _
    continuous_const, jT_one_table3]

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem box_twoPow (A B D p L' : ℝ) (α β m₁ m₂ : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (p - q.1) ^ m₁ * (L' - q.1 - q.2) ^ m₂ =
      twoPowVal A B D p L' α β m₁ m₂ := by
  apply BGP212.V2e.box_twoPow <;> assumption

theorem cells_integral (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (α β m n : ℕ) :
    ∫ q in boxTri c M M, q.1 ^ α * q.2 ^ β *
        ((endpointAgg g L C r k q.1 q.2) ^ m * (L - ((r + k) * g + q.1 + q.2)) ^ n) =
      cellsVal g L C r k c M α β m n := by
  apply BGP212.V2e.cells_integral <;> assumption

theorem mem_pieceSet_agg {N : ℕ} (R : Finset (Fin N)) (c M : ℝ) (y : Fin N → ℝ)
    (hy : y ∈ simplexF (Fin N) M) :
    y ∈ pieceSet N R c M ↔ (aggR R y, aggS R y) ∈ boxTri c M M := by
  apply BGP212.V2e.mem_pieceSet_agg <;> assumption

theorem piece_block {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        ((endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m *
          (L - ((R.card + k) * g + aggR R y + aggS R y)) ^ n) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        cellsVal g L C R.card k c M (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m n := by
  apply BGP212.V2e.piece_block <;> assumption

theorem piece_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n =
      1 / ((N - 1).factorial : ℝ) * seg0Val g L C k M (N - 1) m n := by
  apply BGP212.V2e.piece_r0 <;> assumption

theorem indicator_supportT_strat {N : ℕ} (g L : ℝ) (C : ℕ → ℝ)
    (G : Finset (Fin N) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator (fun x => G (roughSet g x) x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator (G R) x := by
  apply BGP212.V2e.indicator_supportT_strat <;> assumption

theorem jT_one_pieces (N : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    jT N g L τ C (fun _ => 1) = (N + 1 : ℝ) * ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset,
      (-1 : ℝ) ^ K.card * ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 := by
  apply BGP212.V2e.jT_one_pieces <;> assumption

theorem count_by_card (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * F R.card K.card =
      ∑ r ∈ Finset.range (N + 1), (N.choose r : ℝ) *
        ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : ℝ) * (-1) ^ k * F r k := by
  apply BGP212.V2e.count_by_card <;> assumption

theorem piece_eq_pieceJ {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 2 =
      pieceJ N R.card K.card g L τ C 2 0 := by
  apply BGP212.V2e.piece_eq_pieceJ <;> assumption

theorem jT_one_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    jT N g L τ C (fun _ => 1) = jtSum N g L τ C 2 0 := by
  apply BGP212.V2e.jT_one_eq <;> assumption

theorem twoPowVal_cast (A B D p L' : ℚ) (α β m₁ m₂ : ℕ) :
    ((twoPowVal A B D p L' α β m₁ m₂ : ℚ) : ℝ) =
      twoPowVal (A : ℝ) (B : ℝ) (D : ℝ) (p : ℝ) (L' : ℝ) α β m₁ m₂ := by
  apply BGP212.V2e.twoPowVal_cast <;> assumption

theorem cellsVal_cast (g L : ℚ) (C : ℕ → ℚ) (r k : ℕ) (c M : ℚ) (α β m n : ℕ) :
    ((cellsVal g L C r k c M α β m n : ℚ) : ℝ) =
      cellsVal (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) r k (c : ℝ) (M : ℝ) α β m n := by
  apply BGP212.V2e.cellsVal_cast <;> assumption

theorem seg0Val_cast (g L : ℚ) (C : ℕ → ℚ) (k : ℕ) (M : ℚ) (β m n : ℕ) :
    ((seg0Val g L C k M β m n : ℚ) : ℝ) =
      seg0Val (g : ℝ) (L : ℝ) (fun i => (C i : ℝ)) k (M : ℝ) β m n := by
  apply BGP212.V2e.seg0Val_cast <;> assumption

theorem pieceJ_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceJ N r k g L τ C m n : ℚ) : ℝ) =
      pieceJ N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  apply BGP212.V2e.pieceJ_cast <;> assumption

theorem jtSum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((jtSum N g L τ C m n : ℚ) : ℝ) = jtSum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  apply BGP212.V2e.jtSum_cast <;> assumption

theorem pieceJ_tail (r k : ℕ) (h : 16 ≤ r + k) : pieceJ 44 r k g L τ C 2 0 = 0 := by
  apply BGP212.V2e.pieceJ_tail <;> assumption

theorem pieceJ_high (r k : ℕ) (h : 14 ≤ r) : pieceJ 44 r k g L τ C 2 0 = 0 := by
  apply BGP212.V2e.pieceJ_high <;> assumption

theorem jtSum_table3 : jtSum 44 g L τ C 2 0 = (196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.jtSum_table3 <;> assumption

theorem table3_hyps : 0 ≤ g3 ∧ g3 ≤ C3 1 ∧ C3 44 - ((44 : ℕ) : ℝ) * g3 < 0 := by
  apply BGP212.V2e.table3_hyps <;> assumption

theorem jT_one_table3 : jT 44 g3 L3 τ3 C3 (fun _ => 1) = ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_one_table3 <;> assumption

theorem eval_gen_zero (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0) = 1 := by
  apply BGP212.V2e.eval_gen_zero <;> assumption

theorem jT_gram_gen00_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ∧
      marginalJ 44 g3 L3 τ3 C3
          (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
        ((196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141 / 1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_gram_gen00_table3 <;> assumption

end BGP212.Challenge
