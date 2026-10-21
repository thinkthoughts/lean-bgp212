/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.PowerSumPlace
import Solution.PowerSumEntry
import Solution.PowerSumSquareCertSum

/-! # V2h: the marginal Gram entry `J_T[P₂, P₂]` (proofs)

* `piece_mono`: every monomial weight `yᵗ` on a piece integrates to `(∏ tᵢ!) · pieceM … a b`
  with `a`, `b` the degrees in the rough and the smooth group;
* `piece_w1`, `piece_w2`: one and two distinguished coordinates, through their classes `cls`;
* `sum_place2`: placing an ordered pair of coordinates (V2c's `Sig` placements, collapsed by
  symmetry to the classes `R`, `K`, neither; the diagonal `i = j` separately);
* `piece_P2sq`, `piece_P2m`, `piece_pow`: the three blocks of `(U P̂₂ + U³/3)²` on a piece;
* `p2p2Entry_eq`: `J_T[P₂, P₂]` in closed form; `jT_P2_P2_table3`: at Table 3. -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## Monomial weights on a piece -/

section Mono


theorem agg_mem_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∈ R} (fun j => t j) =
        (∏ i ∈ R, ((t i).factorial : ℝ)) / ((R.card + ∑ i ∈ R, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∈ R} (fun j => t j) = R.card + ∑ i ∈ R, t i - 1 := by
  have h1 : aggExp {j // j ∈ R} (fun j => t j) = R.card + ∑ i ∈ R, t i - 1 := by
    simp only [aggExp, Fintype.card_coe]
    rw [Finset.sum_coe_sort R t]
  refine ⟨?_, h1⟩
  simp only [aggConst]
  rw [h1, Finset.prod_coe_sort R (fun i => ((t i).factorial : ℝ))]

theorem agg_compl_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∉ R} (fun j => t j) =
        (∏ i ∈ Rᶜ, ((t i).factorial : ℝ)) / ((N - R.card + ∑ i ∈ Rᶜ, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∉ R} (fun j => t j) = N - R.card + ∑ i ∈ Rᶜ, t i - 1 := by
  have hs : ∑ i ∈ Rᶜ, t i = ∑ i : {j // j ∉ R}, t i :=
    Finset.sum_subtype Rᶜ (fun x => Finset.mem_compl) t
  have hp : ∏ i ∈ Rᶜ, ((t i).factorial : ℝ) = ∏ i : {j // j ∉ R}, ((t i).factorial : ℝ) :=
    Finset.prod_subtype Rᶜ (fun x => Finset.mem_compl) _
  have h1 : aggExp {j // j ∉ R} (fun j => t j) = N - R.card + ∑ i ∈ Rᶜ, t i - 1 := by
    simp only [aggExp]
    rw [hs, card_compl_subtype]
  refine ⟨?_, h1⟩
  simp only [aggConst]
  rw [h1, hp]

/-- **A monomial weight on a piece**: `∫_{piece} yᵗ U^m = (∏ tᵢ!) · pieceM N r k a b … m` with
`a = Σ_{i ∈ R} tᵢ` and `b = Σ_{i ∉ R} tᵢ`. -/
theorem piece_mono {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceM N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m := by
  by_cases he : C R.card - R.card * g < 0 ∨ τ - (R.card + K.card) * g < 0
  · rw [pieceSet_empty N R _ _ (by rintro ⟨h1, h2⟩; rcases he with h | h <;> linarith),
      Measure.restrict_empty, integral_zero_measure]
    simp only [pieceM, if_pos he, mul_zero]
  have he' := he
  push Not at he'
  by_cases hr : R.card = 0
  · have hR : R = ∅ := Finset.card_eq_zero.mp hr
    subst hR
    have key := piece_r0_w hN g L C hC1 K.card _ (τ - (0 + K.card) * g) (by simpa using he'.1)
      (by simpa using he'.2) t m 0
    unfold pieceM
    rw [if_neg he, if_pos Finset.card_empty]
    simp only [pow_zero, mul_one, Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero,
      zero_add] at key ⊢
    rw [key]
    simp only [aggConst, aggExp, Fintype.card_fin, Finset.compl_empty]
    rw [show N - 1 + ∑ i, t i = N + ∑ i, t i - 1 by omega]
    ring_nf
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
    have key := piece_block R hRne hRc g L C K.card (C R.card - R.card * g)
      (τ - (R.card + K.card) * g) t m 0
    simp only [pow_zero, mul_one] at key
    rw [key, (agg_mem_facts R t).1, (agg_mem_facts R t).2, (agg_compl_facts R t).1,
      (agg_compl_facts R t).2, ← Finset.prod_mul_prod_compl R]
    unfold pieceM
    rw [if_neg he, if_neg hr, show R.card + ∑ i ∈ R, t i - 1 = R.card - 1 + ∑ i ∈ R, t i by
      have : 1 ≤ R.card := Nat.pos_of_ne_zero hr
      omega, show N - R.card + ∑ i ∈ Rᶜ, t i - 1 = N - R.card - 1 + ∑ i ∈ Rᶜ, t i by omega]
    ring

end Mono

/-! ## Classes of coordinates and one or two distinguished coordinates -/

section Classes


theorem roughPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    roughPart (cls R K i) a = if i ∈ R then a else 0 := by
  unfold roughPart cls; split_ifs <;> simp_all

theorem smoothPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    smoothPart (cls R K i) a = if i ∈ Rᶜ then a else 0 := by
  unfold smoothPart cls; split_ifs <;> simp_all

theorem shift_cls {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (i : Fin N) :
    shiftV g (R ∪ K) i = clsShift g (cls R K i) := by
  unfold clsShift cls
  by_cases hR : i ∈ R
  · simp [shiftV, hR]
  · by_cases hK : i ∈ K
    · simp [shiftV, hR, hK]
    · simp [shiftV, hR, hK]

theorem sum_pw {N : ℕ} (S : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    ∑ l ∈ S, pw i a l = if i ∈ S then a else 0 := by
  simp [pw, Finset.sum_ite_eq']

theorem fact_pw {N : ℕ} (i : Fin N) (a : ℕ) :
    ∏ l, ((pw i a l).factorial : ℝ) = (a.factorial : ℝ) := by
  have := (single_facts i a (fun _ => (0 : ℝ))).2.2
  simpa [pw] using this

theorem fact_pw2 {N : ℕ} (i j : Fin N) (hij : i ≠ j) (a b : ℕ) :
    ∏ l, (((pw i a + pw j b) l).factorial : ℝ) = (a.factorial : ℝ) * (b.factorial : ℝ) := by
  have h : ∀ l, (((pw i a + pw j b) l).factorial : ℝ) =
      ((pw i a l).factorial : ℝ) * ((pw j b l).factorial : ℝ) := by
    intro l
    by_cases hl : l = i
    · subst hl; simp [pw, hij]
    · simp [pw, hl]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, fact_pw, fact_pw]

theorem prod_pw2 {N : ℕ} (i j : Fin N) (a b : ℕ) (y : Fin N → ℝ) :
    ∏ l, y l ^ (pw i a + pw j b) l = y i ^ a * y j ^ b := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pw]

/-- **One distinguished coordinate**: `∫_{piece} yᵢ^a U^m = a! · pieceM` at the class of `i`. -/
theorem piece_w1 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (a m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (a.factorial : ℝ) * pieceM N R.card K.card (roughPart (cls R K i) a)
        (smoothPart (cls R K i) a) g L τ C m := by
  have key := piece_mono hN g L τ C hC1 hCN R K (pw i a) m
  simp only [prod_pw, fact_pw, sum_pw] at key
  rw [key, roughPart_cls, smoothPart_cls]

/-- **Two distinct distinguished coordinates**: `∫_{piece} yᵢ^a yⱼ^b U^m = a! b! · pieceM` at
the classes of `i` and `j` (their degrees add within a group). -/
theorem piece_w2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i j : Fin N) (hij : i ≠ j) (a b m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * y j ^ b * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      ((a.factorial : ℝ) * (b.factorial : ℝ)) *
        pieceM N R.card K.card (roughPart (cls R K i) a + roughPart (cls R K j) b)
          (smoothPart (cls R K i) a + smoothPart (cls R K j) b) g L τ C m := by
  have key := piece_mono hN g L τ C hC1 hCN R K (pw i a + pw j b) m
  simp only [prod_pw2, fact_pw2 i j hij] at key
  rw [key, roughPart_cls, smoothPart_cls, roughPart_cls, smoothPart_cls]
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_pw]

/-- Summing a class function over the coordinates. -/
theorem sum_cls {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (h : Fin 3 → ℝ) :
    ∑ i, h (cls R K i) = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * h c := by
  classical
  rw [sum_place R K hRK _ (h 0) (h 1) (h 2)
    (fun i hi => by simp [cls, hi])
    (fun i hi => by
      have hiR : i ∉ R := fun h' => Finset.disjoint_left.mp hRK h' hi
      simp [cls, hiR, hi])
    (fun i hi => by
      have hiR : i ∉ R := fun h' => hi (Finset.mem_union_left K h')
      have hiK : i ∉ K := fun h' => hi (Finset.mem_union_right R h')
      simp [cls, hiR, hiK])]
  simp [Fin.sum_univ_three, clsCount]

/-- **Placing an ordered pair of distinguished coordinates** (V2c's placements collapsed by the
symmetry within each class): off the diagonal the pair of classes `(c, d)` occurs
`n_c n_d − [c = d] n_c` times, on the diagonal `i = j` the class `c` occurs `n_c` times. -/
theorem sum_place2 {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → Fin N → ℝ)
    (φ : Fin 3 → Fin 3 → ℝ) (ψ : Fin 3 → ℝ)
    (hoff : ∀ i j, i ≠ j → f i j = φ (cls R K i) (cls R K j))
    (hdiag : ∀ i, f i i = ψ (cls R K i)) :
    ∑ i, ∑ j, f i j = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * ψ c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N R.card K.card c d * φ c d := by
  classical
  have h1 : ∀ i j, f i j = φ (cls R K i) (cls R K j) +
      if i = j then ψ (cls R K i) - φ (cls R K i) (cls R K i) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hdiag]
    · simp [h, hoff i j h]
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_congr rfl (fun i _ => sum_cls R K hRK (φ (cls R K i))),
    sum_cls R K hRK (fun c' => ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * φ c' c),
    sum_cls R K hRK (fun c => ψ c - φ c c)]
  simp only [Fin.sum_univ_three, pairCount]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  ring

end Classes

/-! ## The algebra of the moment coefficients -/

/-- **Collecting by moments**: the placement sum is `q2J`. -/
theorem q2J_expand (N r k : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (m : ℕ) :
    q2J N r k g L τ C m = ∑ c : Fin 3, (clsCount N r k c : ℝ) * diagT N r k g L τ C m c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N r k c d * pairT N r k g L τ C m c d := by
  simp only [q2J, q2Coef, diagT, pairT, Fin.sum_univ_three, Finset.sum_range_succ,
    Finset.sum_range_zero, roughPart, smoothPart, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    Nat.reduceSub, Nat.reduceAdd, zero_add, add_zero]
  norm_num
  ring

/-! ## The three blocks on a piece -/

section Blocks


theorem pieceSet_integrableOn {N : ℕ} (R : Finset (Fin N)) (c M : ℝ) (φ : (Fin N → ℝ) → ℝ)
    (hφ : Continuous φ) : IntegrableOn φ (pieceSet N R c M) :=
  integrableOn_pieceSet N R c M φ hφ

/-- **`∫_{piece} U^m P̂₂(y + g·1_{R∪K})²` in closed form** (two distinguished coordinates). -/
theorem piece_P2sq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) ^ 2 *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      q2J N R.card K.card g L τ C m := by
  classical
  set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
  set U : (Fin N → ℝ) → ℝ := fun y => endpointAgg g L C R.card K.card (aggR R y) (aggS R y)
  have hU : Continuous U := continuous_endpointAgg_agg g L C _ _ R
  set s := shiftV g (R ∪ K)
  have iP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
    fun φ hφ => pieceSet_integrableOn R _ _ φ hφ
  have hexp : ∀ y : Fin N → ℝ, (∑ i, (y + s) i ^ 2) ^ 2 * U y ^ m =
      ∑ i, ∑ j, (y i + s i) ^ 2 * (y j + s j) ^ 2 * U y ^ m := by
    intro y
    simp only [Pi.add_apply]
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  show ∫ y in P, (∑ i, (y + s) i ^ 2) ^ 2 * U y ^ m = _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    iP (fun y => (y i + s i) ^ 2 * (y j + s j) ^ 2 * U y ^ m) (by fun_prop)]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
    iP (fun y => (y i + s i) ^ 2 * (y j + s j) ^ 2 * U y ^ m) (by fun_prop)]
  rw [q2J_expand]
  refine sum_place2 R K hRK _ (pairT N R.card K.card g L τ C m) (diagT N R.card K.card g L τ C m)
    ?_ ?_
  · -- two distinct coordinates
    intro i j hij
    have hpt : ∀ y : Fin N → ℝ, (y i + s i) ^ 2 * (y j + s j) ^ 2 * U y ^ m =
        ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, (((Nat.choose 2 a : ℕ) : ℝ) *
          ((Nat.choose 2 b : ℕ) : ℝ) * s i ^ (2 - a) * s j ^ (2 - b)) *
            (y i ^ a * y j ^ b * U y ^ m) := by
      intro y
      rw [add_pow, add_pow, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (iP (fun y => y i ^ a * y j ^ b * U y ^ m) (by fun_prop)).const_mul _]
    rw [Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ =>
      (iP (fun y => y i ^ a * y j ^ b * U y ^ m) (by fun_prop)).const_mul _]
    simp_rw [integral_const_mul]
    unfold pairT
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [piece_w2 hN g L τ C hC1 hCN R K i j hij a b m,
      show s i = clsShift g (cls R K i) from shift_cls g R K i,
      show s j = clsShift g (cls R K j) from shift_cls g R K j]
    ring
  · -- the diagonal
    intro i
    have hpt : ∀ y : Fin N → ℝ, (y i + s i) ^ 2 * (y i + s i) ^ 2 * U y ^ m =
        ∑ a ∈ Finset.range 5,
          (((Nat.choose 4 a : ℕ) : ℝ) * s i ^ (4 - a)) * (y i ^ a * U y ^ m) := by
      intro y
      rw [← pow_add, show 2 + 2 = 4 from rfl, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => (iP _ (by fun_prop)).const_mul _]
    simp_rw [integral_const_mul]
    unfold diagT
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [piece_w1 hN g L τ C hC1 hCN R K i a m,
      show s i = clsShift g (cls R K i) from shift_cls g R K i]
    ring

/-- **`∫_{piece} U^m P̂₂(y + g·1_{R∪K})`** for any power `m` (V2g's `p2J`). -/
theorem piece_P2m {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      p2J N R.card K.card g L τ C m := by
  classical
  set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
  set U : (Fin N → ℝ) → ℝ := fun y => endpointAgg g L C R.card K.card (aggR R y) (aggS R y)
  have hU : Continuous U := continuous_endpointAgg_agg g L C _ _ R
  set s := shiftV g (R ∪ K)
  have iP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
    fun φ hφ => pieceSet_integrableOn R _ _ φ hφ
  have hexp : ∀ y : Fin N → ℝ, (∑ i, (y + s) i ^ 2) * U y ^ m =
      ∑ i, (y i ^ 2 * U y ^ m + 2 * s i * (y i ^ 1 * U y ^ m) + s i ^ 2 * (y i ^ 0 * U y ^ m)) := by
    intro y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  show ∫ y in P, (∑ i, (y + s) i ^ 2) * U y ^ m = _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => iP _ (by fun_prop)]
  have hterm : ∀ i, ∫ y in P, (y i ^ 2 * U y ^ m + 2 * s i * (y i ^ 1 * U y ^ m) +
      s i ^ 2 * (y i ^ 0 * U y ^ m)) =
      (if i ∈ R then pieceE N R.card K.card 2 0 g L τ C m
        else pieceE N R.card K.card 0 2 g L τ C m) +
        2 * s i * (if i ∈ R then pieceE N R.card K.card 1 0 g L τ C m
          else pieceE N R.card K.card 0 1 g L τ C m) +
        s i ^ 2 * pieceE N R.card K.card 0 0 g L τ C m := by
    intro i
    rw [integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
      integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
      integral_const_mul, integral_const_mul,
      piece_single_eq hN g L τ C hC1 hCN R K i 2 m,
      piece_single_eq hN g L τ C hC1 hCN R K i 1 m,
      piece_single_eq hN g L τ C hC1 hCN R K i 0 m, ite_self]
  simp_rw [hterm]
  have hs : ∀ i, s i = if i ∈ R ∪ K then g else 0 := fun i => by simp [s, shiftV]
  rw [sum_place R K hRK _
    (pieceE N R.card K.card 2 0 g L τ C m + 2 * g * pieceE N R.card K.card 1 0 g L τ C m +
      g ^ 2 * pieceE N R.card K.card 0 0 g L τ C m)
    (pieceE N R.card K.card 0 2 g L τ C m + 2 * g * pieceE N R.card K.card 0 1 g L τ C m +
      g ^ 2 * pieceE N R.card K.card 0 0 g L τ C m)
    (pieceE N R.card K.card 0 2 g L τ C m)
    (fun i hi => by
      rw [hs i, if_pos (Finset.mem_union_left K hi), if_pos hi, if_pos hi])
    (fun i hi => by
      have hiR : i ∉ R := fun h => Finset.disjoint_left.mp hRK h hi
      rw [hs i, if_pos (Finset.mem_union_right R hi), if_neg hiR, if_neg hiR])
    (fun i hi => by
      have hiR : i ∉ R := fun h => hi (Finset.mem_union_left K h)
      rw [hs i, if_neg hi, if_neg hiR, if_neg hiR]; ring)]
  rw [p2J]
  ring

/-- **`∫_{piece} U^m`** for any power `m` (V2f's `pieceJ … m 0`). -/
theorem piece_pow {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      pieceJ N R.card K.card g L τ C m 0 := by
  have key := piece_mono hN g L τ C hC1 hCN R K (fun _ => 0) m
  simp only [pow_zero, Finset.prod_const_one, one_mul, Nat.factorial_zero, Nat.cast_one,
    Finset.sum_const_zero] at key
  rw [key]
  simp only [pieceM, pieceJ, add_zero]

end Blocks

/-! ## `J_T[P₂, P₂]` in closed form -/

/-- **`(N + 1) ∫_{T̂} (U P̂₂ + U³/3)²` in closed form** (any `N ≥ 1`, data with `0 ≤ g ≤ C(1)`,
`C(N) < N g`). -/
theorem p2p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) *
          (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) =
      p2p2EntryVal N g L τ C := by
  classical
  set Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ := fun R x =>
    (stratumEndpoint g L C R x * ∑ i, x i ^ 2 + stratumEndpoint g L C R x ^ 3 / 3) *
      (stratumEndpoint g L C R x * ∑ i, x i ^ 2 + stratumEndpoint g L C R x ^ 3 / 3) with hΦ
  have hΦc : ∀ R, Continuous (Φ R) := fun R => by
    simp only [hΦ]; have := continuous_stratumEndpoint g L C R; fun_prop
  have hfun : ∀ x : Fin N → ℝ, (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) *
      (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) = Φ (roughSet g x) x :=
    fun x => by simp only [hΦ, endpoint_eq_stratum g L C x (roughSet g x) rfl]
  simp_rw [hfun]
  rw [hatSupport_eq, strat_integral g τ C hg Φ hΦc]
  have hpiece : ∀ R : Finset (Fin N), ∀ K ∈ Rᶜ.powerset,
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        Φ R (y + shiftV g (R ∪ K)) =
      q2J N R.card K.card g L τ C 2 + 2 / 3 * p2J N R.card K.card g L τ C 4 +
        pieceJ N R.card K.card g L τ C 6 0 / 9 := by
    intro R K hK
    have hRK : Disjoint R K := Finset.disjoint_left.mpr fun i hiR hiK =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR
    set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
    set U : (Fin N → ℝ) → ℝ := fun y => endpointAgg g L C R.card K.card (aggR R y) (aggS R y)
    have hU : Continuous U := continuous_endpointAgg_agg g L C _ _ R
    set s := shiftV g (R ∪ K)
    have iP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
      fun φ hφ => pieceSet_integrableOn R _ _ φ hφ
    have hpt : ∀ y : Fin N → ℝ, Φ R (y + s) =
        (∑ i, (y + s) i ^ 2) ^ 2 * U y ^ 2 + 2 / 3 * ((∑ i, (y + s) i ^ 2) * U y ^ 4) +
          U y ^ 6 / 9 := by
      intro y
      simp only [hΦ, U, s, stratumEndpoint_shift g L C R K hRK y]
      ring
    have hc : Continuous fun y : Fin N → ℝ => ∑ i, (y + s) i ^ 2 := by
      simp only [Pi.add_apply]; fun_prop
    simp_rw [hpt]
    rw [integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)),
      integral_add (iP _ (by fun_prop)) (iP _ (by fun_prop)), integral_const_mul,
      integral_div, piece_P2sq hN g L τ C hC1 hCN R K hRK 2,
      piece_P2m hN g L τ C hC1 hCN R K hRK 4, piece_pow hN g L τ C hC1 hCN R K 6]
  rw [Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun K hK => by rw [hpiece R K hK],
    count_by_card N (fun r k => q2J N r k g L τ C 2 + 2 / 3 * p2J N r k g L τ C 4 +
      pieceJ N r k g L τ C 6 0 / 9)]
  simp only [p2p2EntryVal, q2Sum, q2Row, p2Sum, p2Row, jtSum, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_div]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
    ring

/-! ## Rational values -/

theorem pieceM_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceM N r k a b g L τ C m : ℚ) : ℝ) =
      pieceM N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  unfold pieceM
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

theorem clsShift_cast (g : ℚ) (c : Fin 3) : ((clsShift g c : ℚ) : ℝ) = clsShift (g : ℝ) c := by
  unfold clsShift; split_ifs <;> simp

theorem q2Coef_cast (N r k : ℕ) (g : ℚ) (A B : ℕ) :
    ((q2Coef N r k g A B : ℚ) : ℝ) = q2Coef N r k (g : ℝ) A B := by
  simp only [q2Coef, pairCount, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_sub, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, Rat.cast_pow, clsShift_cast]

theorem q2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((q2Sum N g L τ C m : ℚ) : ℝ) = q2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  simp only [q2Sum, q2Row, q2J, Rat.cast_mul, Rat.cast_sum, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, q2Coef_cast, pieceM_cast]

theorem p2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((p2Sum N g L τ C m : ℚ) : ℝ) = p2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  simp only [p2Sum, p2Row, p2J, Rat.cast_mul, Rat.cast_sum, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, pieceE_cast]

theorem p2p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2p2EntryVal N g L τ C : ℚ) : ℝ) =
      p2p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) := by
  simp only [p2p2EntryVal, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    q2Sum_cast, p2Sum_cast, jtSum_cast]

/-! ## Table 3: the marginal Gram entry `J_T[P₂, P₂]` -/

/-- **`J_T[P₂, P₂]` at Table 3** (computational certificate `p2p2EntryVal_table3`): the diagonal
bilinear `J_T` entry of the generator `gen 0 {2} = P₂` of `B₂₁`,
`45 ∫_{T̂} (U P̂₂ + U³/3)² ≈ 2.27107 × 10⁻⁵⁸`, is an explicit rational. -/
theorem jT_P2_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := table3_hyps
  unfold jTbil
  simp_rw [inner_P2]
  rw [p2p2Entry_eq (N := 44) (by norm_num) g3 L3 τ3 C3 h0 h1 h2,
    show p2p2EntryVal 44 g3 L3 τ3 C3 = ((p2p2EntryVal 44 BGP212.Params.g BGP212.Params.L
      BGP212.Params.τ BGP212.Params.C : ℚ) : ℝ) from (p2p2EntryVal_cast 44 _ _ _ _).symm,
    p2p2EntryVal_table3]

/-- The diagonal entry is `J_T(P₂)` of §9.4 (`jTbil_self`). -/
theorem jT_P2_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [← jTbil_self, jT_P2_P2_table3]

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem agg_mem_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∈ R} (fun j => t j) =
        (∏ i ∈ R, ((t i).factorial : ℝ)) / ((R.card + ∑ i ∈ R, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∈ R} (fun j => t j) = R.card + ∑ i ∈ R, t i - 1 := by
  apply BGP212.V2e.agg_mem_facts <;> assumption

theorem agg_compl_facts {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    aggConst {j // j ∉ R} (fun j => t j) =
        (∏ i ∈ Rᶜ, ((t i).factorial : ℝ)) / ((N - R.card + ∑ i ∈ Rᶜ, t i - 1).factorial : ℝ) ∧
      aggExp {j // j ∉ R} (fun j => t j) = N - R.card + ∑ i ∈ Rᶜ, t i - 1 := by
  apply BGP212.V2e.agg_compl_facts <;> assumption

theorem piece_mono {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceM N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m := by
  apply BGP212.V2e.piece_mono <;> assumption

theorem roughPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    roughPart (cls R K i) a = if i ∈ R then a else 0 := by
  apply BGP212.V2e.roughPart_cls <;> assumption

theorem smoothPart_cls {N : ℕ} (R K : Finset (Fin N)) (i : Fin N) (a : ℕ) :
    smoothPart (cls R K i) a = if i ∈ Rᶜ then a else 0 := by
  apply BGP212.V2e.smoothPart_cls <;> assumption

theorem shift_cls {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (i : Fin N) :
    shiftV g (R ∪ K) i = clsShift g (cls R K i) := by
  apply BGP212.V2e.shift_cls <;> assumption

theorem piece_w1 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i : Fin N) (a m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      (a.factorial : ℝ) * pieceM N R.card K.card (roughPart (cls R K i) a)
        (smoothPart (cls R K i) a) g L τ C m := by
  apply BGP212.V2e.piece_w1 <;> assumption

theorem piece_w2 {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (i j : Fin N) (hij : i ≠ j) (a b m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        y i ^ a * y j ^ b * (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      ((a.factorial : ℝ) * (b.factorial : ℝ)) *
        pieceM N R.card K.card (roughPart (cls R K i) a + roughPart (cls R K j) b)
          (smoothPart (cls R K i) a + smoothPart (cls R K j) b) g L τ C m := by
  apply BGP212.V2e.piece_w2 <;> assumption

theorem sum_cls {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (h : Fin 3 → ℝ) :
    ∑ i, h (cls R K i) = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * h c := by
  apply BGP212.V2e.sum_cls <;> assumption

theorem sum_place2 {N : ℕ} (R K : Finset (Fin N)) (hRK : Disjoint R K) (f : Fin N → Fin N → ℝ)
    (φ : Fin 3 → Fin 3 → ℝ) (ψ : Fin 3 → ℝ)
    (hoff : ∀ i j, i ≠ j → f i j = φ (cls R K i) (cls R K j))
    (hdiag : ∀ i, f i i = ψ (cls R K i)) :
    ∑ i, ∑ j, f i j = ∑ c : Fin 3, (clsCount N R.card K.card c : ℝ) * ψ c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N R.card K.card c d * φ c d := by
  apply BGP212.V2e.sum_place2 <;> assumption

theorem q2J_expand (N r k : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (m : ℕ) :
    q2J N r k g L τ C m = ∑ c : Fin 3, (clsCount N r k c : ℝ) * diagT N r k g L τ C m c +
      ∑ c : Fin 3, ∑ d : Fin 3, pairCount N r k c d * pairT N r k g L τ C m c d := by
  apply BGP212.V2e.q2J_expand <;> assumption

theorem piece_P2sq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) ^ 2 *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      q2J N R.card K.card g L τ C m := by
  apply BGP212.V2e.piece_P2sq <;> assumption

theorem piece_P2m {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∑ i, (y + shiftV g (R ∪ K)) i ^ 2) *
          (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      p2J N R.card K.card g L τ C m := by
  apply BGP212.V2e.piece_P2m <;> assumption

theorem piece_pow {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (m : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (endpointAgg g L C R.card K.card (aggR R y) (aggS R y)) ^ m =
      pieceJ N R.card K.card g L τ C m 0 := by
  apply BGP212.V2e.piece_pow <;> assumption

theorem p2p2Entry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) :
    (N + 1 : ℝ) * ∫ x in hatSupport N g τ C,
        (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) *
          (endpoint g L C x * ∑ i, x i ^ 2 + endpoint g L C x ^ 3 / 3) =
      p2p2EntryVal N g L τ C := by
  apply BGP212.V2e.p2p2Entry_eq <;> assumption

theorem pieceM_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((pieceM N r k a b g L τ C m : ℚ) : ℝ) =
      pieceM N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  apply BGP212.V2e.pieceM_cast <;> assumption

theorem clsShift_cast (g : ℚ) (c : Fin 3) : ((clsShift g c : ℚ) : ℝ) = clsShift (g : ℝ) c := by
  apply BGP212.V2e.clsShift_cast <;> assumption

theorem q2Coef_cast (N r k : ℕ) (g : ℚ) (A B : ℕ) :
    ((q2Coef N r k g A B : ℚ) : ℝ) = q2Coef N r k (g : ℝ) A B := by
  apply BGP212.V2e.q2Coef_cast <;> assumption

theorem q2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((q2Sum N g L τ C m : ℚ) : ℝ) = q2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  apply BGP212.V2e.q2Sum_cast <;> assumption

theorem p2Sum_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) :
    ((p2Sum N g L τ C m : ℚ) : ℝ) = p2Sum N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m := by
  apply BGP212.V2e.p2Sum_cast <;> assumption

theorem p2p2EntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) :
    ((p2p2EntryVal N g L τ C : ℚ) : ℝ) =
      p2p2EntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) := by
  apply BGP212.V2e.p2p2EntryVal_cast <;> assumption

theorem q2Sum_table3 : q2Sum 44 g L τ C 2 = (3721212168331028519748308970328951038185792337510810540226343119085005100382118243388939929073974240705194256627670803250493222973048404504729378100815164851 / 19218624683167755902483553801149155361150055971336758468293306328111992447832780724764623059286350326146930456161499023437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.q2Sum_table3 <;> assumption

theorem p2Sum4_table3 : p2Sum 44 g L τ C 4 = (1054922107983414915906906937769327296716403318132917952691051050531767556339980615191742253819953865176715501384481084502270708223994744906216464469200181833 / 22421728797029048552897479434674014588008398633226218213008857382797324522471577512225393569167408713838085532188415527343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.p2Sum4_table3 <;> assumption

theorem jtSum6_table3 : jtSum 44 g L τ C 6 0 = (1252155086603792447152587540484619879680414957541407403502562097249654124935188516248764747333977754631495416814468563894505101186320460294467373088090599993 / 65770404471285209088499273008377109458157969324130240091492648322872151932583294035861154469557732227258384227752685546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.jtSum6_table3 <;> assumption

theorem p2p2EntryVal_table3 : p2p2EntryVal 44 g L τ C = (7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.p2p2EntryVal_table3 <;> assumption

theorem jT_P2_P2_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P2_P2_table3 <;> assumption

theorem jT_P2_table3 :
    jT 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P2_table3 <;> assumption

end BGP212.Challenge
