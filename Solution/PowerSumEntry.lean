/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.PowerSumEntry
import Solution.MarginalEntry
import Solution.PowerSumEntryCert

/-! # V2g: a marginal Gram entry with a power sum, `J_T[P₂, 1]` (proofs) -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## The bilinear form and the generators -/

theorem jTbil_self (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F F = jT n g L τ C F := by
  simp [jTbil, jT, sq]

theorem jTbil_comm (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F G : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F G = jTbil n g L τ C G F := by
  simp only [jTbil, mul_comm (∫ u in (0 : ℝ)..(endpoint g L C _), F (Fin.snoc _ u))]

/-- `P₂ = gen 0 {2}` evaluates to `Σᵢ yᵢ²`. -/
theorem eval_gen_P2 (y : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (BGP212.Var.gen 0 {2}) = ∑ i, y i ^ 2 := by
  simp [BGP212.Var.gen, BGP212.Var.Plam, BGP212.Var.P, MvPolynomial.psum, MvPolynomial.eval₂_sum]

/-- **The inner integral of `P₂`**: `∫₀^U P₂(x̂, u) du = U P̂₂(x̂) + U³/3`. -/
theorem inner_P2 (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 {2}) = U * ∑ i, x i ^ 2 + U ^ 3 / 3 := by
  have h : ∀ u : ℝ, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
      (BGP212.Var.gen 0 {2}) = (∑ i, x i ^ 2) + u ^ 2 := by
    intro u
    rw [eval_gen_P2, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [h]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (by exact (continuous_pow 2).intervalIntegrable _ _), intervalIntegral.integral_const,
    integral_pow]
  simp; ring

/-- The constant generator: `∫₀^U 1 du = U`. -/
theorem inner_one (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 0) = U := by
  have h : ∀ u : ℝ, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
      (BGP212.Var.gen 0 0) = 1 := fun u => eval_gen_zero _
  simp_rw [h, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

/-! ## Stratified integration of a stratum-dependent integrand -/

/-- **Stratified integration.** For a stratum-dependent integrand `Φ R` (continuous for each
`R`), the integral over the support is the signed sum over pieces of the translated integrands. -/
theorem strat_integral {N : ℕ} (g τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ) (hΦ : ∀ R, Continuous (Φ R)) :
    ∫ x in supportT N g τ C, Φ (roughSet g x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          Φ R (y + shiftV g (R ∪ K)) := by
  classical
  rw [← integral_indicator (supportT_measurableSet N g τ C)]
  simp_rw [indicator_supportT_strat g τ C Φ]
  have hint : ∀ R K, Integrable ((Qset g τ C R K).indicator (Φ R)) := by
    intro R K
    rw [integrable_indicator_iff (Qset_measurableSet g τ C R K)]
    refine ((hΦ R).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin N) τ)).mono_set ?_
    exact fun x hx => ⟨hx.1, hx.2.2.1⟩
  rw [integral_finsetSum _ fun R _ => integrable_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [integral_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun K hK => ?_
  have hRK : Disjoint R K := Finset.disjoint_left.mpr fun i hiR hiK =>
    (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR
  rw [integral_const_mul, integral_Qset g τ C hg R K hRK]

/-! ## Single-coordinate weights -/

section Single

variable {N : ℕ}

/-- The exponent vector `e·δᵢ`. -/
def pw (i : Fin N) (e : ℕ) : Fin N → ℕ := fun j => if j = i then e else 0

theorem prod_pw (i : Fin N) (e : ℕ) (y : Fin N → ℝ) : ∏ j, y j ^ pw i e j = y i ^ e :=
  (single_facts i e y).1

theorem agg_pw_mem (R : Finset (Fin N)) (i : Fin N) (hi : i ∈ R) (e : ℕ) :
    aggConst {j // j ∈ R} (fun j => pw i e j) = (e.factorial : ℝ) / ((R.card + e - 1).factorial : ℝ) ∧
      aggExp {j // j ∈ R} (fun j => pw i e j) = R.card + e - 1 := by
  have hf : ∀ j : {j // j ∈ R}, pw i e j = if j = ⟨i, hi⟩ then e else 0 := by
    intro j; simp only [pw, Subtype.ext_iff]
  obtain ⟨-, h2, h3⟩ := single_facts (⟨i, hi⟩ : {j // j ∈ R}) e (fun _ => (0 : ℝ))
  refine ⟨?_, ?_⟩
  · simp only [aggConst, aggExp, hf]; rw [h3, h2, Fintype.card_coe]
  · simp only [aggExp, hf]; rw [h2, Fintype.card_coe]

theorem agg_pw_notMem (R : Finset (Fin N)) (i : Fin N) (hi : i ∉ R) (e : ℕ) :
    aggConst {j // j ∈ R} (fun j => pw i e j) = 1 / ((R.card - 1).factorial : ℝ) ∧
      aggExp {j // j ∈ R} (fun j => pw i e j) = R.card - 1 := by
  have hf : (fun j : {j // j ∈ R} => pw i e j) = fun _ => 0 := by
    funext j; simp only [pw]; rw [if_neg]; rintro h; exact hi (h ▸ j.2)
  rw [hf, aggConst_zero, aggExp_zero, Fintype.card_coe]; exact ⟨rfl, rfl⟩

theorem agg_pw_compl_mem (R : Finset (Fin N)) (i : Fin N) (hi : i ∉ R) (e : ℕ) :
    aggConst {j // j ∉ R} (fun j => pw i e j) =
        (e.factorial : ℝ) / ((N - R.card + e - 1).factorial : ℝ) ∧
      aggExp {j // j ∉ R} (fun j => pw i e j) = N - R.card + e - 1 := by
  have hf : ∀ j : {j // j ∉ R}, pw i e j = if j = ⟨i, hi⟩ then e else 0 := by
    intro j; simp only [pw, Subtype.ext_iff]
  obtain ⟨-, h2, h3⟩ := single_facts (⟨i, hi⟩ : {j // j ∉ R}) e (fun _ => (0 : ℝ))
  refine ⟨?_, ?_⟩
  · simp only [aggConst, aggExp, hf]; rw [h3, h2, card_compl_subtype]
  · simp only [aggExp, hf]; rw [h2, card_compl_subtype]

theorem agg_pw_compl_notMem (R : Finset (Fin N)) (i : Fin N) (hi : i ∈ R) (e : ℕ) :
    aggConst {j // j ∉ R} (fun j => pw i e j) = 1 / ((N - R.card - 1).factorial : ℝ) ∧
      aggExp {j // j ∉ R} (fun j => pw i e j) = N - R.card - 1 := by
  have hf : (fun j : {j // j ∉ R} => pw i e j) = fun _ => 0 := by
    funext j; simp only [pw]; rw [if_neg]; rintro h; exact j.2 (h ▸ hi)
  rw [hf, aggConst_zero, aggExp_zero, card_compl_subtype]; exact ⟨rfl, rfl⟩

end Single

/-! ## Weighted piece integrals -/

/-- The one-aggregate segment integral `∫_{[0,M]} s^β U(0, s)^m (L − S)^n` (stratum `R = ∅`). -/
theorem seg_integral (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (β m n : ℕ) :
    ∫ s in Set.Icc 0 M, s ^ β * ((endpointAgg g L C 0 k 0 s) ^ m *
        (L - (((0 : ℕ) + k) * g + 0 + s)) ^ n) = seg0Val g L C k M β m n := by
  set h : ℝ → ℝ := fun s => (endpointAgg g L C 0 k 0 s) ^ m * (L - (((0 : ℕ) + k) * g + 0 + s)) ^ n
    with hh
  have hhc : Continuous h := by
    simp only [hh]; have := continuous_endpointAgg g L C 0 k
    exact ((this.comp (continuous_const.prodMk continuous_id)).pow m).mul (by fun_prop)
  show ∫ s in Set.Icc 0 M, s ^ β * h s = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hM]
  set X := max 0 (min (L - k * g - C 1) M) with hX
  have hX0 : 0 ≤ X := le_max_left _ _
  have hXM : X ≤ M := max_le hM (min_le_right _ _)
  have hcont : Continuous fun s => s ^ β * h s := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 X)
    (hcont.intervalIntegrable X M)]
  have hLp : ∀ s : ℝ, L - (((0 : ℕ) + k) * g + 0 + s) = L - k * g - s := fun s => by push_cast; ring
  have a1 : ∫ s in (0 : ℝ)..X, s ^ β * h s =
      ∫ s in (0 : ℝ)..X, C 1 ^ m * ((L - k * g - s) ^ n * s ^ β) := by
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
  have a2 : ∫ s in X..M, s ^ β * h s =
      ∫ s in X..M, (L - k * g - s) ^ (m + n) * s ^ β := by
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
      ((by fun_prop : Continuous fun s : ℝ => (L - k * g - s) ^ (m + n) * s ^ β).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => (L - k * g - s) ^ (m + n) * s ^ β).intervalIntegrable _ _),
    innerVal_eq, innerVal_eq, seg0Val]

/-- **A weighted piece with no rough coordinates** (`R = ∅`), any monomial weight `yᵗ`. -/
theorem piece_r0_w {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) * ((endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n) =
      aggConst (Fin N) t * seg0Val g L C k M (aggExp (Fin N) t) m n := by
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
    (∏ i, y i ^ t i) * h (∑ i, y i)) (fun y _ => by
      simp only [hh, (hagg y).1, (hagg y).2])]
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    hhc.continuousOn
  rw [one_group M t h hhc.measurable Bd (fun s hs => by
    rw [← Real.norm_eq_abs]; exact hBd s hs), seg_integral g L C hC1 k M hM]

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
          cellsVal g L C R.card k c M (R.card - 1) (N - R.card + e - 1) m 0 := by
  have key := piece_block R hR hRc g L C k c M (pw i e) m 0
  simp only [pow_zero, mul_one, prod_pw] at key
  rw [key]
  by_cases hi : i ∈ R
  · rw [if_pos hi, (agg_pw_mem R i hi e).1, (agg_pw_mem R i hi e).2,
      (agg_pw_compl_notMem R i hi e).1, (agg_pw_compl_notMem R i hi e).2]
  · rw [if_neg hi, (agg_pw_notMem R i hi e).1, (agg_pw_notMem R i hi e).2,
      (agg_pw_compl_mem R i hi e).1, (agg_pw_compl_mem R i hi e).2]

theorem agg_pw_univ {N : ℕ} (i : Fin N) (e : ℕ) :
    aggConst (Fin N) (pw i e) = (e.factorial : ℝ) / ((N + e - 1).factorial : ℝ) ∧
      aggExp (Fin N) (pw i e) = N + e - 1 := by
  obtain ⟨-, h2, h3⟩ := single_facts i e (fun _ => (0 : ℝ))
  refine ⟨?_, ?_⟩
  · simp only [aggConst, aggExp, pw]; rw [h3, h2, Fintype.card_fin]
  · simp only [aggExp, pw]; rw [h2, Fintype.card_fin]

/-- Every weighted piece integral is `pieceE` at its cardinalities. -/
theorem piece_single_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (e m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ e * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      if i ∈ R then pieceE N R.card K.card e 0 g L τ C m
      else pieceE N R.card K.card 0 e g L τ C m := by
  by_cases he : C R.card - R.card * g < 0 ∨ τ - (R.card + K.card) * g < 0
  · rw [pieceSet_empty N R _ _ (by rintro ⟨h1, h2⟩; rcases he with h | h <;> linarith),
      Measure.restrict_empty, integral_zero_measure]
    simp only [pieceE, if_pos he]; split_ifs <;> rfl
  have he' := he
  push Not at he'
  by_cases hr : R.card = 0
  · have hR : R = ∅ := Finset.card_eq_zero.mp hr
    subst hR
    have hi : i ∉ (∅ : Finset (Fin N)) := Finset.notMem_empty i
    rw [if_neg hi]
    unfold pieceE
    rw [if_neg he, if_pos Finset.card_empty, show N + e - 1 = N - 1 + e by omega]
    have key := piece_r0_w hN g L C hC1 K.card _ (τ - (0 + K.card) * g) (by simpa using he'.1)
      (by simpa using he'.2) (pw i e) m 0
    simp only [pow_zero, mul_one, prod_pw, Finset.card_empty] at key ⊢
    rw [(agg_pw_univ i e).1, (agg_pw_univ i e).2, show N + e - 1 = N - 1 + e by omega] at key
    convert key using 2
    · push_cast; ring_nf
    · push_cast; ring_nf
  · have hRne : R.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hr)
    have hRc : Rᶜ.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
      subst h
      rw [Finset.card_univ, Fintype.card_fin] at he'
      linarith [he'.1]
    have hlt : R.card < N := by
      obtain ⟨j, hj⟩ := hRc
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ R,
        fun h => by rw [h] at hj; simp at hj⟩)
      simpa using this
    rw [piece_single R hRne hRc g L C K.card _ _ i e m]
    simp only [pieceE, if_neg he, if_neg hr, Nat.factorial_zero, Nat.cast_one, add_zero]
    split_ifs
    · rw [show R.card - 1 + e = R.card + e - 1 by omega]
    · rw [show N - R.card - 1 + e = N - R.card + e - 1 by omega]

/-- **Placing a distinguished coordinate**: a sum over `i` of a function constant on `R`, on `K`
and on the rest is `r·a + k·b + (N − r − k)·c`. -/
theorem sum_place {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → ℝ)
    (a b c : ℝ) (ha : ∀ i ∈ R, f i = a) (hb : ∀ i ∈ K, f i = b) (hc : ∀ i ∉ R ∪ K, f i = c) :
    ∑ i, f i = R.card * a + K.card * b + ((N - R.card - K.card : ℕ) : ℝ) * c := by
  classical
  rw [← Finset.sum_add_sum_compl (R ∪ K), Finset.sum_union hRK,
    Finset.sum_congr rfl ha, Finset.sum_congr rfl hb,
    Finset.sum_congr rfl fun i hi => hc i (Finset.mem_compl.mp hi)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin,
    Finset.card_union_of_disjoint hRK]
  rw [show N - (R.card + K.card) = N - R.card - K.card by omega]

theorem continuous_endpointAgg_agg {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (R : Finset (Fin N)) :
    Continuous fun y : Fin N → ℝ => endpointAgg g L C r k (aggR R y) (aggS R y) :=
  (continuous_endpointAgg g L C r k).comp
    ((by unfold aggR; fun_prop : Continuous fun y : Fin N → ℝ => aggR R y).prodMk
      (by unfold aggS; fun_prop : Continuous fun y : Fin N → ℝ => aggS R y))

/-- **The `P₂` block of a piece**: `∫_{piece} (U P̂₂(y + g·1_{R∪K}) + U³/3) U` in closed form. -/
theorem piece_P2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        ((endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) *
            ∑ i, (y + shiftV g (R ∪ K)) i ^ 2 +
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 3 / 3) *
        endpointAgg g L C R.card K.card (aggR R y) (aggS R y) =
      p2J N R.card K.card g L τ C 2 + pieceJ N R.card K.card g L τ C 4 0 / 3 := by
  classical
  set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
  set U : (Fin N → ℝ) → ℝ := fun y => endpointAgg g L C R.card K.card (aggR R y) (aggS R y)
  have hU : Continuous U := continuous_endpointAgg_agg g L C _ _ R
  have hPc : IsCompact P := (simplexF_isCompact (ι := Fin N) _).of_isClosed_subset
    (by
      have : P = {y : Fin N → ℝ | ∀ i, 0 ≤ y i} ∩ ({y | ∑ i ∈ R, y i ≤ C R.card - R.card * g} ∩
          {y | ∑ i, y i ≤ τ - (R.card + K.card) * g}) := by ext y; simp [P, pieceSet]
      rw [this]
      refine IsClosed.inter ?_ (IsClosed.inter (isClosed_le (by fun_prop) continuous_const)
        (isClosed_le (by fun_prop) continuous_const))
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    (pieceSet_subset_simplexF N R _ _)
  have iP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
    fun φ hφ => hφ.continuousOn.integrableOn_compact hPc
  set s := shiftV g (R ∪ K)
  set i₀ : Fin N := ⟨0, hN⟩
  -- expand the integrand
  have hexp : ∀ y ∈ P, (U y * ∑ i, (y + s) i ^ 2 + U y ^ 3 / 3) * U y =
      (∑ i, (y i ^ 2 * U y ^ 2 + 2 * s i * (y i ^ 1 * U y ^ 2) + s i ^ 2 * (y i ^ 0 * U y ^ 2))) +
        1 / 3 * (y i₀ ^ 0 * U y ^ 4) := by
    intro y _
    simp only [Pi.add_apply, pow_one, pow_zero, one_mul]
    rw [show (U y * ∑ i, (y i + s i) ^ 2 + U y ^ 3 / 3) * U y =
      (∑ i, (y i + s i) ^ 2) * U y ^ 2 + 1 / 3 * U y ^ 4 by ring, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have cw : ∀ (i : Fin N) (e m : ℕ), Continuous fun y : Fin N → ℝ => y i ^ e * U y ^ m :=
    fun i e m => by fun_prop
  have hPm : MeasurableSet P := pieceSet_measurableSet _ _ _ _
  show ∫ y in P, (U y * ∑ i, (y + s) i ^ 2 + U y ^ 3 / 3) * U y = _
  rw [setIntegral_congr_fun hPm hexp, integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
    integral_finsetSum _ fun i _ => iP _ (by fun_prop), integral_const_mul, piece_single_eq hN g L τ C hC1 hCN R K i₀ 0 4, ite_self]
  have hterm : ∀ i, ∫ y in P, (y i ^ 2 * U y ^ 2 + 2 * s i * (y i ^ 1 * U y ^ 2) +
      s i ^ 2 * (y i ^ 0 * U y ^ 2)) =
      (if i ∈ R then pieceE N R.card K.card 2 0 g L τ C 2 else pieceE N R.card K.card 0 2 g L τ C 2) +
        2 * s i * (if i ∈ R then pieceE N R.card K.card 1 0 g L τ C 2
          else pieceE N R.card K.card 0 1 g L τ C 2) +
        s i ^ 2 * pieceE N R.card K.card 0 0 g L τ C 2 := by
    intro i
    rw [integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
      integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
      integral_const_mul, integral_const_mul,
      piece_single_eq hN g L τ C hC1 hCN R K i 2 2,
      piece_single_eq hN g L τ C hC1 hCN R K i 1 2,
      piece_single_eq hN g L τ C hC1 hCN R K i 0 2, ite_self]
  simp_rw [hterm]
  have hs : ∀ i, s i = if i ∈ R ∪ K then g else 0 := fun i => by simp [s, shiftV]
  rw [sum_place R K hRK _
    (pieceE N R.card K.card 2 0 g L τ C 2 + 2 * g * pieceE N R.card K.card 1 0 g L τ C 2 +
      g ^ 2 * pieceE N R.card K.card 0 0 g L τ C 2)
    (pieceE N R.card K.card 0 2 g L τ C 2 + 2 * g * pieceE N R.card K.card 0 1 g L τ C 2 +
      g ^ 2 * pieceE N R.card K.card 0 0 g L τ C 2)
    (pieceE N R.card K.card 0 2 g L τ C 2)
    (fun i hi => by
      rw [hs i, if_pos (Finset.mem_union_left K hi), if_pos hi, if_pos hi])
    (fun i hi => by
      have hiR : i ∉ R := fun h => Finset.disjoint_left.mp hRK h hi
      rw [hs i, if_pos (Finset.mem_union_right R hi), if_neg hiR, if_neg hiR])
    (fun i hi => by
      have hiR : i ∉ R := fun h => hi (Finset.mem_union_left K h)
      rw [hs i, if_neg hi, if_neg hiR, if_neg hiR]; ring)]
  have h4 : pieceE N R.card K.card 0 0 g L τ C 4 = pieceJ N R.card K.card g L τ C 4 0 := by
    simp only [pieceE, pieceJ, Nat.factorial_zero, Nat.cast_one, add_zero, one_div]
  rw [h4, p2J]
  ring

/-! ## `J_T[P₂, 1]` in closed form -/

/-- **`(N + 1) ∫_{T̂} (U P̂₂ + U³/3) U` in closed form** (any `N ≥ 1`, data with `0 ≤ g ≤ C(1)`,
`C(N) < N g`). -/
theorem p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) * endpoint g L C x =
      p2EntryVal N g L τ C := by
  classical
  set Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ := fun R x =>
    (stratumEndpoint g L C R x * ∑ i, x i ^ 2 + stratumEndpoint g L C R x ^ 3 / 3) *
      stratumEndpoint g L C R x with hΦ
  have hΦc : ∀ R, Continuous (Φ R) := fun R => by
    simp only [hΦ]; have := continuous_stratumEndpoint g L C R; fun_prop
  have hfun : ∀ x : Fin N → ℝ, (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) *
      endpoint g L C x = Φ (roughSet g x) x := fun x => by
    simp only [hΦ, endpoint_eq_stratum g L C x (roughSet g x) rfl]
  simp_rw [hfun]
  rw [hatSupport_eq, strat_integral g τ C hg Φ hΦc]
  have hpiece : ∀ R : Finset (Fin N), ∀ K ∈ Rᶜ.powerset,
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        Φ R (y + shiftV g (R ∪ K)) =
      p2J N R.card K.card g L τ C 2 + pieceJ N R.card K.card g L τ C 4 0 / 3 := by
    intro R K hK
    have hRK : Disjoint R K := Finset.disjoint_left.mpr fun i hiR hiK =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR
    rw [← piece_P2 hN g L τ C hC1 hCN R K hRK]
    refine setIntegral_congr_fun (pieceSet_measurableSet _ _ _ _) fun y _ => ?_
    simp only [hΦ, stratumEndpoint_shift g L C R K hRK y]
  rw [Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun K hK => by rw [hpiece R K hK],
    count_by_card N (fun r k => p2J N r k g L τ C 2 + pieceJ N r k g L τ C 4 0 / 3)]
  simp only [p2EntryVal, p2Sum, p2Row, jtSum, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## Rational values -/

theorem pieceE_cast (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceE N r k eR eS g L τ C m : ℚ) : ℝ) =
      pieceE N r k eR eS (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  unfold pieceE
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

theorem p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2EntryVal N g L τ C : ℚ) : ℝ) = p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) := by
  simp [p2EntryVal, p2Sum, p2Row, p2J, pieceE_cast, jtSum_cast]

/-! ## Table 3: the marginal Gram entry `J_T[P₂, 1]` -/

/-- **`J_T[P₂, 1]` at Table 3** (computational certificate `p2EntryVal_table3`): the bilinear
`J_T` entry of the generators `gen 0 {2} = P₂` and `gen 0 ∅ = 1` of `B₂₁`,
`45 ∫_{T̂} (U P̂₂ + U³/3) U ≈ 4.99944 × 10⁻⁵⁷`, is an explicit rational. -/
theorem jT_P2_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := table3_hyps
  unfold jTbil
  simp_rw [inner_P2, inner_one]
  rw [p2Entry_eq (N := 44) (by norm_num) g3 L3 τ3 C3 h0 h1 h2,
    show p2EntryVal 44 g3 L3 τ3 C3 = ((p2EntryVal 44 BGP212.Params.g BGP212.Params.L
      BGP212.Params.τ BGP212.Params.C : ℚ) : ℝ) from (p2EntryVal_cast 44 _ _ _ _).symm,
    p2EntryVal_table3]

/-- The entry is symmetric: `J_T[1, P₂] = J_T[P₂, 1]`. -/
theorem jT_one_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [jTbil_comm, jT_P2_one_table3]

/-- Consistency with V2f: the diagonal entry `J_T[1, 1]` of the bilinear form is V2f's `J_T(1)`. -/
theorem jTbil_one_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) :=
  jTbil_self _ _ _ _ _ _

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem jTbil_self (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F F = jT n g L τ C F := by
  apply BGP212.V2e.jTbil_self <;> assumption

theorem jTbil_comm (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F G : (Fin (n + 1) → ℝ) → ℝ) :
    jTbil n g L τ C F G = jTbil n g L τ C G F := by
  apply BGP212.V2e.jTbil_comm <;> assumption

theorem eval_gen_P2 (y : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (BGP212.Var.gen 0 {2}) = ∑ i, y i ^ 2 := by
  apply BGP212.V2e.eval_gen_P2 <;> assumption

theorem inner_P2 (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 {2}) = U * ∑ i, x i ^ 2 + U ^ 3 / 3 := by
  apply BGP212.V2e.inner_P2 <;> assumption

theorem inner_one (x : Fin 44 → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.snoc x u : Fin 45 → ℝ)
        (BGP212.Var.gen 0 0) = U := by
  apply BGP212.V2e.inner_one <;> assumption

theorem strat_integral {N : ℕ} (g τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ) (hΦ : ∀ R, Continuous (Φ R)) :
    ∫ x in supportT N g τ C, Φ (roughSet g x) x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          Φ R (y + shiftV g (R ∪ K)) := by
  apply BGP212.V2e.strat_integral <;> assumption

theorem seg_integral (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (β m n : ℕ) :
    ∫ s in Set.Icc 0 M, s ^ β * ((endpointAgg g L C 0 k 0 s) ^ m *
        (L - (((0 : ℕ) + k) * g + 0 + s)) ^ n) = seg0Val g L C k M β m n := by
  apply BGP212.V2e.seg_integral <;> assumption

theorem piece_r0_w {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1) (k : ℕ)
    (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) * ((endpointAgg g L C 0 k (aggR ∅ y) (aggS ∅ y)) ^ m *
        (L - (((0 : ℕ) + k) * g + aggR ∅ y + aggS ∅ y)) ^ n) =
      aggConst (Fin N) t * seg0Val g L C k M (aggExp (Fin N) t) m n := by
  apply BGP212.V2e.piece_r0_w <;> assumption

theorem piece_single {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (i : Fin N) (e m : ℕ) :
    ∫ y in pieceSet N R c M, y i ^ e * (endpointAgg g L C R.card k (aggR R y) (aggS R y)) ^ m =
      if i ∈ R then (e.factorial : ℝ) / ((R.card + e - 1).factorial : ℝ) *
          (1 / ((N - R.card - 1).factorial : ℝ)) *
          cellsVal g L C R.card k c M (R.card + e - 1) (N - R.card - 1) m 0
      else 1 / ((R.card - 1).factorial : ℝ) *
          ((e.factorial : ℝ) / ((N - R.card + e - 1).factorial : ℝ)) *
          cellsVal g L C R.card k c M (R.card - 1) (N - R.card + e - 1) m 0 := by
  apply BGP212.V2e.piece_single <;> assumption

theorem piece_single_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (e m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ e * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      if i ∈ R then pieceE N R.card K.card e 0 g L τ C m
      else pieceE N R.card K.card 0 e g L τ C m := by
  apply BGP212.V2e.piece_single_eq <;> assumption

theorem sum_place {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → ℝ)
    (a b c : ℝ) (ha : ∀ i ∈ R, f i = a) (hb : ∀ i ∈ K, f i = b) (hc : ∀ i ∉ R ∪ K, f i = c) :
    ∑ i, f i = R.card * a + K.card * b + ((N - R.card - K.card : ℕ) : ℝ) * c := by
  apply BGP212.V2e.sum_place <;> assumption

theorem piece_P2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        ((endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) *
            ∑ i, (y + shiftV g (R ∪ K)) i ^ 2 +
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ 3 / 3) *
        endpointAgg g L C R.card K.card (aggR R y) (aggS R y) =
      p2J N R.card K.card g L τ C 2 + pieceJ N R.card K.card g L τ C 4 0 / 3 := by
  apply BGP212.V2e.piece_P2 <;> assumption

theorem p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) * endpoint g L C x =
      p2EntryVal N g L τ C := by
  apply BGP212.V2e.p2Entry_eq <;> assumption

theorem pieceE_cast (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceE N r k eR eS g L τ C m : ℚ) : ℝ) =
      pieceE N r k eR eS (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  apply BGP212.V2e.pieceE_cast <;> assumption

theorem p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2EntryVal N g L τ C : ℚ) : ℝ) = p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) := by
  apply BGP212.V2e.p2EntryVal_cast <;> assumption

theorem cond_tail (r k : ℕ) (h : 16 ≤ r + k) : C r - r * g < 0 ∨ τ - (r + k) * g < 0 := by
  apply BGP212.V2e.cond_tail <;> assumption

theorem cond_high (r k : ℕ) (h : 14 ≤ r) : C r - r * g < 0 ∨ τ - (r + k) * g < 0 := by
  apply BGP212.V2e.cond_high <;> assumption

theorem p2EntryVal_table3 : p2EntryVal 44 g L τ C = (1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.p2EntryVal_table3 <;> assumption

theorem jT_P2_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P2_one_table3 <;> assumption

theorem jT_one_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((1104358822986966410704354182689648221498493168782115682829421927126277953718756564709620289245978967427176687508450637788075179802115707831812467680353 / 220896518807348573964872193894024577538769622919527803455975308652911717277947389881376238918164744973182678222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_one_P2_table3 <;> assumption

theorem jTbil_one_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) := by
  apply BGP212.V2e.jTbil_one_one_table3 <;> assumption

end BGP212.Challenge
