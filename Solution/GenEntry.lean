/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.GenEntryBlock
import Solution.PowerSumSquare
import Solution.GenEntryCertSum

/-! # V2i: general polynomial marginal Gram entries (proofs)

* `piece_mono_n`: every monomial weight against `U^m (L − S)^n` on a piece is a moment `pieceMn`;
* `lpEval_*`: coefficient-list polynomials; `coord_integral`: one open coordinate;
* `piece_state`: any number of open coordinates with polynomial weights (`stateVal`);
* `piece_place`: products of class-dependent power sums (`placeVal`: merge or open);
* `inner_genFun`: `∫₀^U G_{a,λ}` as `innerTerms`;
* `genEntry_eq`: `J_T[G_{a₁,l₁}, G_{a₂,l₂}] = genEntryVal` for every `N ≥ 1` and admissible data. -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## Monomials against `U^m (L − S)^n` -/

theorem continuous_blk {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R : Finset (Fin N)) (k m n : ℕ) :
    Continuous (blk g L C R k m n) := by
  have hU := continuous_endpointAgg_agg g L C R.card k R
  have h1 : Continuous fun y : Fin N → ℝ => aggR R y := by unfold aggR; fun_prop
  have h2 : Continuous fun y : Fin N → ℝ => aggS R y := by unfold aggS; fun_prop
  unfold blk; fun_prop

/-- **A monomial weight against `U^m (L − S)^n`**: `∫_{piece} yᵗ U^m (L − S)^n =
(∏ tᵢ!) · pieceMn N r k a b … m n`, `a = Σ_{i ∈ R} tᵢ`, `b = Σ_{i ∉ R} tᵢ`. -/
theorem piece_mono_n {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * blk g L C R K.card m n y =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceMn N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m n := by
  unfold blk
  by_cases he : C R.card - R.card * g < 0 ∨ τ - (R.card + K.card) * g < 0
  · rw [pieceSet_empty N R _ _ (by rintro ⟨h1, h2⟩; rcases he with h | h <;> linarith),
      Measure.restrict_empty, integral_zero_measure]
    simp only [pieceMn, if_pos he, mul_zero]
  have he' := he
  push Not at he'
  by_cases hr : R.card = 0
  · have hR : R = ∅ := Finset.card_eq_zero.mp hr
    subst hR
    have key := piece_r0_w hN g L C hC1 K.card _ (τ - (0 + K.card) * g) (by simpa using he'.1)
      (by simpa using he'.2) t m n
    unfold pieceMn
    rw [if_neg he, if_pos Finset.card_empty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero, zero_add] at key ⊢
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
      (τ - (R.card + K.card) * g) t m n
    rw [key, (agg_mem_facts R t).1, (agg_mem_facts R t).2, (agg_compl_facts R t).1,
      (agg_compl_facts R t).2, ← Finset.prod_mul_prod_compl R]
    unfold pieceMn
    rw [if_neg he, if_neg hr, show R.card + ∑ i ∈ R, t i - 1 = R.card - 1 + ∑ i ∈ R, t i by
      have : 1 ≤ R.card := Nat.pos_of_ne_zero hr
      omega, show N - R.card + ∑ i ∈ Rᶜ, t i - 1 = N - R.card - 1 + ∑ i ∈ Rᶜ, t i by omega]
    ring

/-! ## Coefficient-list polynomials -/

section LP

@[simp] theorem lpEval_nil {K : Type*} [Field K] (y : K) : lpEval ([] : List K) y = 0 := rfl

@[simp] theorem lpEval_cons {K : Type*} [Field K] (c : K) (f : List K) (y : K) :
    lpEval (c :: f) y = c + y * lpEval f y := rfl

theorem lpEval_add {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpAdd f g) y = lpEval f y + lpEval g y := by
  induction f generalizing g with
  | nil => simp [lpAdd]
  | cons a f ih =>
    cases g with
    | nil => simp [lpAdd]
    | cons b g => simp only [lpAdd, lpEval_cons, ih]; ring

theorem lpEval_map_mul {K : Type*} [Field K] (a : K) (g : List K) (y : K) :
    lpEval (g.map (a * ·)) y = a * lpEval g y := by
  induction g with
  | nil => simp
  | cons b g ih => simp only [List.map_cons, lpEval_cons, ih]; ring

theorem lpEval_mul {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpMul f g) y = lpEval f y * lpEval g y := by
  induction f with
  | nil => simp [lpMul]
  | cons a f ih => simp only [lpMul, lpEval_add, lpEval_map_mul, lpEval_cons, ih]; ring

theorem lpEval_append {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (f ++ g) y = lpEval f y + y ^ f.length * lpEval g y := by
  induction f with
  | nil => simp
  | cons a f ih => simp only [List.cons_append, lpEval_cons, ih, List.length_cons]; ring

theorem lpEval_range {K : Type*} [Field K] (h : ℕ → K) (q : ℕ) (y : K) :
    lpEval ((List.range q).map h) y = ∑ a ∈ Finset.range q, h a * y ^ a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, lpEval_append, ih, Finset.sum_range_succ]
    simp [mul_comm]

theorem lpEval_shiftPow {K : Type*} [Field K] (s : K) (q : ℕ) (y : K) :
    lpEval (lpShiftPow s q) y = (y + s) ^ q := by
  rw [lpShiftPow, lpEval_range, add_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end LP

/-! ## One open coordinate -/

theorem coordSum_congr {K : Type*} [Field K] (b b' : ℕ → K) (hb : ∀ e, b e = b' e) (f : List K)
    (e : ℕ) : coordSum b f e = coordSum b' f e := by
  induction f generalizing e with
  | nil => rfl
  | cons c f ih => simp only [coordSum, hb, ih]

theorem coordSum_mul {K : Type*} [Field K] (a : K) (b : ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => a * b e) f e = a * coordSum b f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp only [coordSum, ih]; ring

theorem continuous_lpEval (f : List ℝ) : Continuous fun y : ℝ => lpEval f y := by
  induction f with
  | nil => simpa using continuous_const
  | cons b f ih => simp only [lpEval_cons]; fun_prop

/-- **One open coordinate**: `∫ yᵢ^e f(yᵢ) W = Σ_j f_j ∫ yᵢ^{e+j} W`. -/
theorem coord_integral {N : ℕ} (P : Set (Fin N → ℝ))
    (hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P) (i : Fin N)
    (W : (Fin N → ℝ) → ℝ) (hW : Continuous W) (f : List ℝ) (e : ℕ) :
    ∫ y in P, y i ^ e * lpEval f (y i) * W y =
      coordSum (fun e' => ∫ y in P, y i ^ e' * W y) f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih =>
    have hpt : ∀ y : Fin N → ℝ, y i ^ e * lpEval (c :: f) (y i) * W y =
        c * (y i ^ e * W y) + y i ^ (e + 1) * lpEval f (y i) * W y := by
      intro y; simp only [lpEval_cons]; ring
    have hc : Continuous fun y : Fin N → ℝ => lpEval f (y i) :=
      (continuous_lpEval f).comp (continuous_apply i)
    simp_rw [hpt]
    rw [integral_add ((hP _ (by fun_prop)).const_mul _) (hP _ (by fun_prop)), integral_const_mul,
      ih (e + 1), coordSum]

/-! ## Several open coordinates -/

/-- **Open coordinates with polynomial weights** (distinct coordinates `is`, classes
`cls R K ∘ is`): `∫ yᵗ ∏_j f_j(y_{is j}) U^m (L − S)^n = (∏ tᵢ!) · stateVal`, for `t` vanishing
at the open coordinates. -/
theorem piece_state {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (m n : ℕ) :
    ∀ (d : ℕ) (is : Fin d → Fin N), Function.Injective is → ∀ (fs : Fin d → List ℝ)
      (t : Fin N → ℕ), (∀ j, t (is j) = 0) →
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          (∏ i, y i ^ t i) * (∏ j, lpEval (fs j) (y (is j))) * blk g L C R K.card m n y =
        (∏ i, ((t i).factorial : ℝ)) *
          stateVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) d (fun j => cls R K (is j))
            fs (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) := by
  classical
  set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
  have hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
    fun φ hφ => integrableOn_pieceSet N R _ _ φ hφ
  have hB := continuous_blk g L C R K.card m n
  intro d
  induction d with
  | zero =>
    intro is _ fs t _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, stateVal]
    exact piece_mono_n hN g L τ C hC1 hCN R K t m n
  | succ d ih =>
    intro is his fs t ht
    set i₀ := is 0
    have hW : Continuous fun y : Fin N → ℝ => (∏ i, y i ^ t i) *
        (∏ j : Fin d, lpEval (fs j.succ) (y (is j.succ))) * blk g L C R K.card m n y := by
      have := fun j : Fin d => ((continuous_lpEval (fs j.succ)).comp (continuous_apply (is j.succ)) :
        Continuous fun y : Fin N → ℝ => lpEval (fs j.succ) (y (is j.succ)))
      refine Continuous.mul (Continuous.mul (by fun_prop) ?_) hB
      exact continuous_finset_prod _ fun j _ => this j
    have hpt : ∀ y : Fin N → ℝ, (∏ i, y i ^ t i) * (∏ j, lpEval (fs j) (y (is j))) *
        blk g L C R K.card m n y = y i₀ ^ 0 * lpEval (fs 0) (y i₀) *
          ((∏ i, y i ^ t i) * (∏ j : Fin d, lpEval (fs j.succ) (y (is j.succ))) *
            blk g L C R K.card m n y) := by
      intro y; rw [Fin.prod_univ_succ]; ring
    simp_rw [hpt]
    rw [coord_integral P hP i₀ _ hW (fs 0) 0, stateVal]
    rw [← coordSum_mul]
    refine coordSum_congr _ _ (fun e => ?_) (fs 0) 0
    beta_reduce
    -- the weight `t + e·δ_{i₀}`
    have hpt2 : ∀ y : Fin N → ℝ, y i₀ ^ e * ((∏ i, y i ^ t i) *
        (∏ j : Fin d, lpEval (fs j.succ) (y (is j.succ))) * blk g L C R K.card m n y) =
        (∏ i, y i ^ (t + pw i₀ e) i) * (∏ j : Fin d, lpEval (fs j.succ) (y (is j.succ))) *
          blk g L C R K.card m n y := by
      intro y
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pw]
      ring
    refine (congrArg (fun F : (Fin N → ℝ) → ℝ => ∫ y in P, F y) (funext hpt2)).trans ?_
    beta_reduce
    have hinj : Function.Injective fun j : Fin d => is j.succ :=
      his.comp (Fin.succ_injective d)
    have ht' : ∀ j : Fin d, (t + pw i₀ e) (is j.succ) = 0 := by
      intro j
      have hne : is j.succ ≠ i₀ := fun h => Fin.succ_ne_zero j (his h)
      simp [Pi.add_apply, ht, pw, hne]
    rw [ih _ hinj _ _ ht']
    have hfact : ∏ i, (((t + pw i₀ e) i).factorial : ℝ) =
        (e.factorial : ℝ) * ∏ i, ((t i).factorial : ℝ) := by
      have h1 : ∀ i, (((t + pw i₀ e) i).factorial : ℝ) =
          (if i = i₀ then (e.factorial : ℝ) else 1) * ((t i).factorial : ℝ) := by
        intro i
        by_cases h : i = i₀
        · rw [h]; simp [pw, i₀, ht 0]
        · simp [pw, h]
      simp_rw [h1]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    rw [hfact]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_pw]
    rw [roughPart_cls, smoothPart_cls]
    ring

/-! ## Products of class-dependent power sums: placements -/

theorem cls_cons {N d : ℕ} (R K : Finset (Fin N)) (i : Fin N) (is : Fin d → Fin N) :
    (fun j => cls R K ((Fin.cons i is : Fin (d + 1) → Fin N) j)) =
      Fin.cons (cls R K i) (fun j => cls R K (is j)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

theorem prod_update_lpMul {N d : ℕ} (is : Fin d → Fin N) (fs : Fin d → List ℝ) (j : Fin d)
    (ψ : List ℝ) (y : Fin N → ℝ) :
    ∏ j', lpEval (Function.update fs j (lpMul (fs j) ψ) j') (y (is j')) =
      (∏ j', lpEval (fs j') (y (is j'))) * lpEval ψ (y (is j)) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (fun j' => lpEval (fs j') _)]
  rw [Function.update_self, lpEval_mul]
  have : ∏ j' ∈ ({j}ᶜ : Finset (Fin d)), lpEval (Function.update fs j (lpMul (fs j) ψ) j') (y (is j')) =
      ∏ j' ∈ ({j}ᶜ : Finset (Fin d)), lpEval (fs j') (y (is j')) :=
    Finset.prod_congr rfl fun j' hj' => by
      rw [Function.update_of_ne (by simpa using hj')]
  rw [this]; ring

theorem continuous_prod_lp {N d : ℕ} (is : Fin d → Fin N) (fs : Fin d → List ℝ) :
    Continuous fun y : Fin N → ℝ => ∏ j, lpEval (fs j) (y (is j)) :=
  continuous_finset_prod _ fun j _ => (continuous_lpEval (fs j)).comp (continuous_apply (is j))

theorem continuous_prod_factors {N : ℕ} (R K : Finset (Fin N)) (fac : List (Fin 3 → List ℝ)) :
    Continuous fun y : Fin N → ℝ => (fac.map fun φ => ∑ i, lpEval (φ (cls R K i)) (y i)).prod := by
  induction fac with
  | nil => simpa using continuous_const
  | cons φ fac ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Continuous.mul ?_ ih
    exact continuous_finset_sum _ fun i _ =>
      (continuous_lpEval (φ (cls R K i))).comp (continuous_apply i)

/-- **Placements of a product of class-dependent power sums**: with open coordinates `is`
(polynomials `fs`), `∫ ∏_j f_j(y_{is j}) ∏_{φ} Σᵢ φ(cls i)(yᵢ) U^m (L − S)^n = placeVal`; each
factor merges into an open coordinate or opens a new one, `n_c − #(open in c)` times. -/
theorem piece_place {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m n : ℕ) :
    ∀ (fac : List (Fin 3 → List ℝ)) (d : ℕ) (is : Fin d → Fin N), Function.Injective is →
      ∀ fs : Fin d → List ℝ,
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          (∏ j, lpEval (fs j) (y (is j))) *
            (fac.map fun φ => ∑ i, lpEval (φ (cls R K i)) (y i)).prod * blk g L C R K.card m n y =
        placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) (clsCount N R.card K.card) d
          (fun j => cls R K (is j)) fs fac := by
  classical
  set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
  have hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
    fun φ hφ => integrableOn_pieceSet N R _ _ φ hφ
  have hB := continuous_blk g L C R K.card m n
  intro fac
  induction fac with
  | nil =>
    intro d is his fs
    have key := piece_state hN g L τ C hC1 hCN R K m n d is his fs (fun _ => 0) (fun _ => rfl)
    simp only [pow_zero, Finset.prod_const_one, one_mul, Nat.factorial_zero, Nat.cast_one,
      Finset.sum_const_zero] at key
    simp only [List.map_nil, List.prod_nil, mul_one, placeVal]
    exact key
  | cons φ rest ih =>
    intro d is his fs
    have hcr := continuous_prod_factors R K rest
    have hcp := continuous_prod_lp is fs
    have hci : ∀ i, Continuous fun y : Fin N → ℝ => lpEval (φ (cls R K i)) (y i) :=
      fun i => (continuous_lpEval _).comp (continuous_apply i)
    set F : Fin N → (Fin N → ℝ) → ℝ := fun i y => (∏ j, lpEval (fs j) (y (is j))) *
      lpEval (φ (cls R K i)) (y i) * (rest.map fun φ => ∑ i, lpEval (φ (cls R K i)) (y i)).prod *
        blk g L C R K.card m n y with hF
    have hFc : ∀ i, Continuous (F i) := fun i => by
      simp only [hF]; exact ((hcp.mul (hci i)).mul hcr).mul hB
    have hpt : ∀ y : Fin N → ℝ, (∏ j, lpEval (fs j) (y (is j))) *
        ((φ :: rest).map fun φ => ∑ i, lpEval (φ (cls R K i)) (y i)).prod *
          blk g L C R K.card m n y = ∑ i, F i y := by
      intro y
      simp only [hF, List.map_cons, List.prod_cons, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    refine (congrArg (fun G : (Fin N → ℝ) → ℝ => ∫ y in P, G y) (funext hpt)).trans ?_
    beta_reduce
    rw [integral_finsetSum _ fun i _ => hP _ (hFc i)]
    set D : Finset (Fin N) := Finset.univ.image is
    rw [← Finset.sum_add_sum_compl D, Finset.sum_image fun a _ b _ h => his h, placeVal]
    congr 1
    · -- merging into an open coordinate
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ih d is his]
      refine setIntegral_congr_fun (pieceSet_measurableSet _ _ _ _) fun y _ => ?_
      simp only [hF, prod_update_lpMul]
    · -- opening a new coordinate
      set H : Fin 3 → ℝ := fun c' => placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n)
        (clsCount N R.card K.card) (d + 1) (Fin.cons c' fun j => cls R K (is j))
        (Fin.cons (φ c') fs) rest with hH
      have hnew : ∀ i ∈ Dᶜ, ∫ y in P, F i y = H (cls R K i) := by
        intro i hi
        have hiD : i ∉ Set.range is := by
          rintro ⟨j, rfl⟩; exact (Finset.mem_compl.mp hi) (Finset.mem_image_of_mem is (Finset.mem_univ j))
        have hinj : Function.Injective (Fin.cons i is : Fin (d + 1) → Fin N) :=
          Fin.cons_injective_iff.mpr ⟨hiD, his⟩
        have key := ih (d + 1) (Fin.cons i is) hinj (Fin.cons (φ (cls R K i)) fs)
        rw [cls_cons] at key
        rw [hH]
        beta_reduce
        rw [← key]
        refine setIntegral_congr_fun (pieceSet_measurableSet _ _ _ _) fun y _ => ?_
        simp only [hF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring
      rw [Finset.sum_congr rfl hnew]
      have hall := sum_cls R K hRK H
      have hD : ∑ i ∈ D, H (cls R K i) = ∑ c' : Fin 3,
          (((Finset.univ.filter fun j => cls R K (is j) = c').card : ℕ) : ℝ) * H c' := by
        rw [Finset.sum_image fun a _ b _ h => his h]
        rw [← Finset.sum_fiberwise Finset.univ (fun j => cls R K (is j))]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2], Finset.sum_const,
          nsmul_eq_mul]
      have hsplit := Finset.sum_add_sum_compl D (fun i => H (cls R K i))
      rw [hall, hD] at hsplit
      rw [eq_sub_of_add_eq' hsplit, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring

/-! ## Power sums on a translated piece -/

theorem psum_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (q : ℕ) (y : Fin N → ℝ) :
    ∑ i, (y + shiftV g (R ∪ K)) i ^ q =
      ∑ i, lpEval (lpShiftPow (clsShift g (cls R K i)) q) (y i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpEval_shiftPow, ← shift_cls g R K i]
  rfl

/-- **A product of power sums on a piece**: `∫ ∏_{q ∈ Q} P̂_q(y + g·1_{R∪K}) U^m (L − S)^n` is
the placement value with no open coordinate. -/
theorem piece_psum {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m n : ℕ) (Q : List ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (Q.map fun q => ∑ i, (y + shiftV g (R ∪ K)) i ^ q).prod * blk g L C R K.card m n y =
      placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) (clsCount N R.card K.card) 0
        Fin.elim0 Fin.elim0 (Q.map fun q c => lpShiftPow (clsShift g c) q) := by
  have key := piece_place hN g L τ C hC1 hCN R K hRK m n (Q.map fun q c => lpShiftPow (clsShift g c) q)
    0 Fin.elim0 (fun a => a.elim0) Fin.elim0
  have hc : (fun j : Fin 0 => cls R K (Fin.elim0 j : Fin N)) = Fin.elim0 := funext fun j => j.elim0
  rw [hc] at key
  rw [← key]
  refine setIntegral_congr_fun (pieceSet_measurableSet _ _ _ _) fun y _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, List.map_map, Function.comp_def,
    psum_shift]

/-! ## The inner integral of a generator -/

theorem list_range_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `∏_{q ∈ l} (X_q + u^q) = Σ_{(K, s)} ∏_{q ∈ K} X_q · u^s`. -/
theorem prod_subsetTerms (X : ℕ → ℝ) (u : ℝ) (l : List ℕ) :
    (l.map fun q => X q + u ^ q).prod = ((subsetTerms l).map fun t => (t.1.map X).prod * u ^ t.2).sum := by
  induction l with
  | nil => simp [subsetTerms]
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons, ih, subsetTerms, List.map_append, List.sum_append,
      List.map_map, List.map_map, add_mul, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    · congr 1; apply List.map_congr_left; intro t _
      simp only [Function.comp_apply, List.map_cons, List.prod_cons]; ring
    · congr 1; apply List.map_congr_left; intro t _
      simp only [Function.comp_apply, pow_add]; ring

theorem continuous_list_sum {ι α : Type*} [TopologicalSpace α] (T : List ι) (f : ι → α → ℝ)
    (hf : ∀ t, Continuous (f t)) : Continuous fun u => (T.map fun t => f t u).sum := by
  induction T with
  | nil => simpa using continuous_const
  | cons t T ih => simp only [List.map_cons, List.sum_cons]; exact (hf t).add ih

theorem intervalIntegral_list_sum {ι : Type*} (T : List ι) (f : ι → ℝ → ℝ)
    (hf : ∀ t, Continuous (f t)) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, (T.map fun t => f t u).sum = (T.map fun t => ∫ u in (0 : ℝ)..U, f t u).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add ((hf t).intervalIntegrable _ _)
      ((continuous_list_sum T f hf).intervalIntegrable _ _), ih]

theorem sum_map_flatMap {α β : Type*} (T : List α) (g : α → List β) (h : β → ℝ) :
    ((T.flatMap g).map h).sum = (T.map fun t => ((g t).map h).sum).sum := by
  induction T with
  | nil => simp
  | cons t T ih => simp [List.flatMap_cons, ih]

/-- `∫₀^U (M − u)^a u^s du = Σ_{j ≤ a} C(a, j) (−1)^j M^{a−j} U^{s+j+1} / (s + j + 1)`. -/
theorem inner_mono (M U : ℝ) (a s : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ a * u ^ s =
      ∑ j ∈ Finset.range (a + 1), ((a.choose j : ℕ) : ℝ) * (-1) ^ j / ((s + j + 1 : ℕ) : ℝ) *
        U ^ (s + j + 1) * M ^ (a - j) := by
  have hpt : ∀ u : ℝ, (M - u) ^ a * u ^ s = ∑ j ∈ Finset.range (a + 1),
      (((a.choose j : ℕ) : ℝ) * (-1) ^ j * M ^ (a - j)) * u ^ (s + j) := by
    intro u
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow, pow_add]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finset_sum fun j _ =>
    ((continuous_pow _).const_mul _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- **The inner integral of a generator**: `∫₀^U G_{a,l}(x̂, u) du` as the `innerTerms`. -/
theorem inner_genFun {N : ℕ} (L : ℝ) (a : ℕ) (l : List ℕ) (x : Fin N → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, genFun L a l (Fin.snoc x u : Fin (N + 1) → ℝ) =
      ((innerTerms (K := ℝ) a l).map fun t => t.2.2.2 * (t.1.map fun q => ∑ i, x i ^ q).prod *
        U ^ t.2.1 * (L - ∑ i, x i) ^ t.2.2.1).sum := by
  set X : ℕ → ℝ := fun q => ∑ i, x i ^ q
  have hpt : ∀ u : ℝ, genFun L a l (Fin.snoc x u : Fin (N + 1) → ℝ) =
      ((subsetTerms l).map fun t => (t.1.map X).prod * ((L - ∑ i, x i - u) ^ a * u ^ t.2)).sum := by
    intro u
    have h1 : ∀ q, ∑ i, (Fin.snoc x u : Fin (N + 1) → ℝ) i ^ q = X q + u ^ q := fun q => by
      rw [Fin.sum_univ_castSucc]; simp [X]
    have h2 : ∑ i, (Fin.snoc x u : Fin (N + 1) → ℝ) i = ∑ i, x i + u := by
      rw [Fin.sum_univ_castSucc]; simp
    unfold genFun
    rw [h2]
    simp_rw [h1]
    rw [prod_subsetTerms, ← List.sum_map_mul_left]
    congr 1; ext t; ring_nf
  simp_rw [hpt]
  rw [intervalIntegral_list_sum _ _ (fun t => by fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, inner_mono]
  unfold innerTerms
  rw [sum_map_flatMap]
  congr 1; apply List.map_congr_left; intro t _
  rw [List.map_map, list_range_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]; ring

/-! ## The entry in closed form -/

theorem continuous_psumProd {N : ℕ} (Q : List ℕ) :
    Continuous fun x : Fin N → ℝ => (Q.map fun q => ∑ i, x i ^ q).prod := by
  induction Q with
  | nil => simpa using continuous_const
  | cons q Q ih => simp only [List.map_cons, List.prod_cons]; exact (by fun_prop : Continuous
      fun x : Fin N → ℝ => ∑ i, x i ^ q).mul ih

theorem setIntegral_list_sum {N : ℕ} {ι : Type*} (P : Set (Fin N → ℝ))
    (hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P) (T : List ι)
    (f : ι → (Fin N → ℝ) → ℝ) (hf : ∀ t, Continuous (f t)) :
    ∫ y in P, (T.map fun t => f t y).sum = (T.map fun t => ∫ y in P, f t y).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hP _ (hf t)) (hP _ (continuous_list_sum T f hf)), ih]

/-- **`J_T[G_{a₁,l₁}, G_{a₂,l₂}]` in closed form** for every `N ≥ 1` and data with
`0 ≤ g ≤ C(1)`, `C(N) < N g`: the bilinear `J_T` of two generators `(L − P₁)^a P_λ` is
`genEntryVal`. -/
theorem genEntry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil N g L τ C (genFun L a₁ l₁) (genFun L a₂ l₂) = genEntryVal N g L τ C a₁ l₁ a₂ l₂ := by
  classical
  set T₁ := innerTerms (K := ℝ) a₁ l₁
  set T₂ := innerTerms (K := ℝ) a₂ l₂
  set PQ : List ℕ → (Fin N → ℝ) → ℝ := fun Q x => (Q.map fun q => ∑ i, x i ^ q).prod with hPQ
  set Φ : Finset (Fin N) → (Fin N → ℝ) → ℝ := fun R x =>
    (T₁.map fun t₁ => (T₂.map fun t₂ => t₁.2.2.2 * t₂.2.2.2 * PQ (t₁.1 ++ t₂.1) x *
      (stratumEndpoint g L C R x ^ (t₁.2.1 + t₂.2.1) * (L - ∑ i, x i) ^ (t₁.2.2.1 + t₂.2.2.1))).sum).sum
    with hΦ
  have hΦc : ∀ R, Continuous (Φ R) := fun R => by
    have hU := continuous_stratumEndpoint g L C R
    refine continuous_list_sum T₁ _ fun t₁ => continuous_list_sum T₂ _ fun t₂ => ?_
    have := continuous_psumProd (N := N) (t₁.1 ++ t₂.1)
    simp only [hPQ]; fun_prop
  have hfun : ∀ x : Fin N → ℝ,
      (∫ u in (0 : ℝ)..(endpoint g L C x), genFun L a₁ l₁ (Fin.snoc x u : Fin (N + 1) → ℝ)) *
        (∫ u in (0 : ℝ)..(endpoint g L C x), genFun L a₂ l₂ (Fin.snoc x u : Fin (N + 1) → ℝ)) =
      Φ (roughSet g x) x := by
    intro x
    rw [inner_genFun, inner_genFun, endpoint_eq_stratum g L C x (roughSet g x) rfl]
    simp only [hΦ, hPQ]
    rw [← List.sum_map_mul_right]
    congr 1; apply List.map_congr_left; intro t₁ _
    rw [← List.sum_map_mul_left]
    congr 1; apply List.map_congr_left; intro t₂ _
    rw [List.map_append, List.prod_append, pow_add, pow_add]; ring
  unfold jTbil
  simp_rw [hfun]
  rw [hatSupport_eq, strat_integral g τ C hg Φ hΦc]
  have hpiece : ∀ R : Finset (Fin N), ∀ K ∈ Rᶜ.powerset,
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        Φ R (y + shiftV g (R ∪ K)) = genPiece N R.card K.card g L τ C a₁ l₁ a₂ l₂ := by
    intro R K hK
    have hRK : Disjoint R K := Finset.disjoint_left.mpr fun i hiR hiK =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR
    set P := pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g)
    have hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P :=
      fun φ hφ => integrableOn_pieceSet N R _ _ φ hφ
    have hpt : ∀ y : Fin N → ℝ, Φ R (y + shiftV g (R ∪ K)) =
        (T₁.map fun t₁ => (T₂.map fun t₂ => t₁.2.2.2 * t₂.2.2.2 *
          ((((t₁.1 ++ t₂.1).map fun q => ∑ i, (y + shiftV g (R ∪ K)) i ^ q).prod) *
            blk g L C R K.card (t₁.2.1 + t₂.2.1) (t₁.2.2.1 + t₂.2.2.1) y)).sum).sum := by
      intro y
      have hS : L - ∑ i, (y + shiftV g (R ∪ K)) i =
          L - ((R.card + K.card) * g + aggR R y + aggS R y) := by
        rw [sum_add_shiftV g R K hRK y, sum_eq_aggR_add_aggS R y]; ring
      simp only [hΦ, hPQ, stratumEndpoint_shift g L C R K hRK y, hS, blk]
      congr 1; apply List.map_congr_left; intro t₁ _
      congr 1; apply List.map_congr_left; intro t₂ _
      ring
    have hcont : ∀ (Q : List ℕ) (m n : ℕ), Continuous fun y : Fin N → ℝ =>
        ((Q.map fun q => ∑ i, (y + shiftV g (R ∪ K)) i ^ q).prod) * blk g L C R K.card m n y := by
      intro Q m n
      have h1 : Continuous fun y : Fin N → ℝ => y + shiftV g (R ∪ K) := by fun_prop
      exact ((continuous_psumProd Q).comp h1).mul (continuous_blk g L C R K.card m n)
    simp_rw [hpt]
    rw [setIntegral_list_sum P hP T₁ _ fun t₁ => continuous_list_sum T₂ _ fun t₂ =>
      (hcont _ _ _).const_mul _]
    unfold genPiece genPieceWith
    congr 1; apply List.map_congr_left; intro t₁ _
    rw [setIntegral_list_sum P hP T₂ _ fun t₂ => (hcont _ _ _).const_mul _]
    congr 1; apply List.map_congr_left; intro t₂ _
    rw [integral_const_mul, piece_psum hN g L τ C hC1 hCN R K hRK]
  rw [Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun K hK => by rw [hpiece R K hK],
    count_by_card N (fun r k => genPiece N r k g L τ C a₁ l₁ a₂ l₂)]
  simp only [genEntryVal, genRow]

/-! ## Rational values -/

theorem pieceMn_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceMn N r k a b g L τ C m n : ℚ) : ℝ) =
      pieceMn N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  unfold pieceMn
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

section Hom

variable {K K' : Type*} [Field K] [Field K'] (φ : K →+* K')

theorem lpAdd_map (f g : List K) : (lpAdd f g).map φ = lpAdd (f.map φ) (g.map φ) := by
  induction f generalizing g with
  | nil => simp [lpAdd]
  | cons a f ih =>
    cases g with
    | nil => simp [lpAdd]
    | cons b g => simp [lpAdd, ih, map_add]

theorem lpMul_map (f g : List K) : (lpMul f g).map φ = lpMul (f.map φ) (g.map φ) := by
  induction f with
  | nil => simp [lpMul]
  | cons a f ih =>
    simp only [lpMul, List.map_cons, lpAdd_map, ih, List.map_map, map_zero]
    congr 2; ext x; simp [Function.comp_def, map_mul]

theorem lpShiftPow_map (s : K) (q : ℕ) : (lpShiftPow s q).map φ = lpShiftPow (φ s) q := by
  simp [lpShiftPow, List.map_map, Function.comp_def, map_mul, map_pow, map_natCast]

theorem coordSum_map (b : ℕ → K) (f : List K) (e : ℕ) :
    φ (coordSum b f e) = coordSum (fun e => φ (b e)) (f.map φ) e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp [coordSum, ih, map_add, map_mul]

theorem stateVal_map (M : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      φ (stateVal M d c fs A B) =
        stateVal (fun A B => φ (M A B)) d c (fun j => (fs j).map φ) A B := by
  intro d
  induction d with
  | zero => intro c fs A B; rfl
  | succ d ih =>
    intro c fs A B
    simp only [stateVal, coordSum_map, map_mul, map_natCast, ih]

theorem placeVal_map (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      φ (placeVal M n d c fs fac) =
        placeVal (fun A B => φ (M A B)) n d c (fun j => (fs j).map φ)
          (fac.map fun ψ c' => (ψ c').map φ) := by
  intro fac
  induction fac with
  | nil => intro d c fs; simp only [placeVal, List.map_nil, stateVal_map]
  | cons ψ rest ih =>
    intro d c fs
    simp only [placeVal, List.map_cons, map_add, map_sum, map_mul, map_sub, map_natCast, ih]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      funext j'
      by_cases h : j' = j
      · subst h; simp [lpMul_map]
      · simp [Function.update_of_ne h]
    · refine Finset.sum_congr rfl fun c' _ => ?_
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem innerTerms_map (a : ℕ) (l : List ℕ) :
    (innerTerms (K := K) a l).map (fun t => (t.1, t.2.1, t.2.2.1, φ t.2.2.2)) =
      innerTerms (K := K') a l := by
  simp [innerTerms, List.map_flatMap, List.map_map, Function.comp_def, map_mul, map_div₀,
    map_pow, map_neg, map_one, map_natCast]

end Hom

theorem genPiece_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genPiece N r k g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genPiece N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ := by
  set φ := Rat.castHom ℝ
  have hφ : ∀ x : ℚ, (x : ℝ) = φ x := fun x => rfl
  unfold genPiece genPieceWith
  rw [← innerTerms_map φ a₁ l₁, ← innerTerms_map φ a₂ l₂]
  simp only [hφ, List.map_map, Function.comp_def, map_list_sum, List.map_map]
  congr 1; apply List.map_congr_left; intro t₁ _
  congr 1; apply List.map_congr_left; intro t₂ _
  rw [map_mul, map_mul, placeVal_map]
  congr 1
  have h0 : (fun j : Fin 0 => (Fin.elim0 j : List ℚ).map φ) = Fin.elim0 := funext fun j => j.elim0
  rw [h0]
  congr 1
  · funext A B; rw [← hφ, pieceMn_cast]; rfl
  · simp only [List.map_map, Function.comp_def, lpShiftPow_map]
    congr 1; funext q c'
    congr 1
    unfold clsShift; split_ifs <;> simp [φ]

theorem genEntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genEntryVal N g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genEntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ := by
  simp only [genEntryVal, genRow, Rat.cast_mul, Rat.cast_sum, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_pow, Rat.cast_neg, genPiece_cast]

/-! ## Table 3: every `B₂₁` entry, and worked values -/

/-- V0's generator is `genFun` with `L = 53/50` (parts of `λ` as a list). -/
theorem eval_gen_list (a : ℕ) (l : List ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑l) = genFun (53 / 50) a l x := by
  rw [← MvPolynomial.coe_eval₂Hom]
  simp only [BGP212.Var.gen, BGP212.Var.Plam, Multiset.map_coe, Multiset.prod_coe, map_mul,
    map_pow, map_sub, map_list_prod, List.map_map, Function.comp_def, BGP212.Var.P,
    MvPolynomial.psum, map_sum]
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    BGP212.Params.L, genFun]
  norm_num

theorem L3_eq : L3 = 53 / 50 := by
  simp only [L3, BGP212.Params.L]; norm_num

/-- **Every marginal Gram entry of `B₂₁` at Table 3 is an explicit rational**: for all
`(a₁, λ₁)`, `(a₂, λ₂)` (parts as lists), `J_T[gen a₁ λ₁, gen a₂ λ₂] = genEntryVal 44 … a₁ λ₁ a₂ λ₂`
over `ℚ`. -/
theorem jT_gen_table3 (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₁ ↑l₁))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₂ ↑l₂)) =
      ((genEntryVal 44 BGP212.Params.g BGP212.Params.L BGP212.Params.τ BGP212.Params.C a₁ l₁ a₂ l₂ :
        ℚ) : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := table3_hyps
  have hf : ∀ (a : ℕ) (l : List ℕ), (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
      (BGP212.Var.gen a ↑l)) = genFun L3 a l := fun a l => by
    funext x; rw [eval_gen_list, L3_eq]
  rw [hf, hf, genEntry_eq (N := 44) (by norm_num) g3 L3 τ3 C3 h0 h1 h2]
  exact (genEntryVal_cast 44 _ _ _ _ a₁ l₁ a₂ l₂).symm

theorem jT_P2_P2_gen_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have := jT_gen_table3 0 [2] 0 [2]
  rw [genEntryPP_table3] at this
  exact this

/-- **`J_T[P₄, 1]` at Table 3** (a degree-4 distinguished coordinate). -/
theorem jT_P4_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {4}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((27146941746034049653011991737523849302835974678539227554371494168379938438711742944681131854870392187261353645054163409711502678639106601137182002258884443591 / 986556067069278136327489095125656641872369539861953601372389724843082278988749410537917317043365983408875763416290283203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have := jT_gen_table3 0 [4] 0 []
  rw [genEntryP4_table3] at this
  exact this

/-- **`J_T[P_{(2,2)}, 1]` at Table 3** (two factors: merged and distinct placements). -/
theorem jT_P22_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2, 2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((3660374136242989387380652323344436977885293224812077133314553468438557932655033514945994325078669043220726153480139763307169322012096626962840970046529550207 / 15998206493015321129634958299334972570903289835599247589822536078536469389006747197912172708811340271495282649993896484375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have := jT_gen_table3 0 [2, 2] 0 []
  rw [genEntryP22_table3] at this
  exact this

/-- **`J_T[L − P₁, 1]` at Table 3** (the factor `(L − P₁)^a`, `a = 1`: moments with `(L − S)`). -/
theorem jT_LP1_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((6512729183781214820113280314392773438904805507600460190719004030691673914761277396184278068946241317308961830318311862437086743937347350312387921 / 1178114766972525727812651700768131080206771322237481618431868312815529158815719412700673274230211973190307617187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have := jT_gen_table3 1 [] 0 []
  rw [genEntryLP_table3] at this
  exact this

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

theorem piece_mono_n {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * blk g L C R K.card m n y =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceMn N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m n := by
  apply BGP212.V2e.piece_mono_n <;> assumption

theorem lpEval_add {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpAdd f g) y = lpEval f y + lpEval g y := by
  apply BGP212.V2e.lpEval_add <;> assumption

theorem lpEval_mul {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpMul f g) y = lpEval f y * lpEval g y := by
  apply BGP212.V2e.lpEval_mul <;> assumption

theorem lpEval_shiftPow {K : Type*} [Field K] (s : K) (q : ℕ) (y : K) :
    lpEval (lpShiftPow s q) y = (y + s) ^ q := by
  apply BGP212.V2e.lpEval_shiftPow <;> assumption

theorem coord_integral {N : ℕ} (P : Set (Fin N → ℝ))
    (hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P) (i : Fin N)
    (W : (Fin N → ℝ) → ℝ) (hW : Continuous W) (f : List ℝ) (e : ℕ) :
    ∫ y in P, y i ^ e * lpEval f (y i) * W y =
      coordSum (fun e' => ∫ y in P, y i ^ e' * W y) f e := by
  apply BGP212.V2e.coord_integral <;> assumption

theorem piece_state {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (m n : ℕ) :
    ∀ (d : ℕ) (is : Fin d → Fin N), Function.Injective is → ∀ (fs : Fin d → List ℝ)
      (t : Fin N → ℕ), (∀ j, t (is j) = 0) →
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          (∏ i, y i ^ t i) * (∏ j, lpEval (fs j) (y (is j))) * blk g L C R K.card m n y =
        (∏ i, ((t i).factorial : ℝ)) *
          stateVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) d (fun j => cls R K (is j))
            fs (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) := by
  apply BGP212.V2e.piece_state <;> assumption

theorem piece_place {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m n : ℕ) :
    ∀ (fac : List (Fin 3 → List ℝ)) (d : ℕ) (is : Fin d → Fin N), Function.Injective is →
      ∀ fs : Fin d → List ℝ,
      ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
          (∏ j, lpEval (fs j) (y (is j))) *
            (fac.map fun φ => ∑ i, lpEval (φ (cls R K i)) (y i)).prod * blk g L C R K.card m n y =
        placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) (clsCount N R.card K.card) d
          (fun j => cls R K (is j)) fs fac := by
  apply BGP212.V2e.piece_place <;> assumption

theorem psum_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (q : ℕ) (y : Fin N → ℝ) :
    ∑ i, (y + shiftV g (R ∪ K)) i ^ q =
      ∑ i, lpEval (lpShiftPow (clsShift g (cls R K i)) q) (y i) := by
  apply BGP212.V2e.psum_shift <;> assumption

theorem piece_psum {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m n : ℕ) (Q : List ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (Q.map fun q => ∑ i, (y + shiftV g (R ∪ K)) i ^ q).prod * blk g L C R K.card m n y =
      placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) (clsCount N R.card K.card) 0
        Fin.elim0 Fin.elim0 (Q.map fun q c => lpShiftPow (clsShift g c) q) := by
  apply BGP212.V2e.piece_psum <;> assumption

theorem prod_subsetTerms (X : ℕ → ℝ) (u : ℝ) (l : List ℕ) :
    (l.map fun q => X q + u ^ q).prod = ((subsetTerms l).map fun t => (t.1.map X).prod * u ^ t.2).sum := by
  apply BGP212.V2e.prod_subsetTerms <;> assumption

theorem inner_mono (M U : ℝ) (a s : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ a * u ^ s =
      ∑ j ∈ Finset.range (a + 1), ((a.choose j : ℕ) : ℝ) * (-1) ^ j / ((s + j + 1 : ℕ) : ℝ) *
        U ^ (s + j + 1) * M ^ (a - j) := by
  apply BGP212.V2e.inner_mono <;> assumption

theorem inner_genFun {N : ℕ} (L : ℝ) (a : ℕ) (l : List ℕ) (x : Fin N → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, genFun L a l (Fin.snoc x u : Fin (N + 1) → ℝ) =
      ((innerTerms (K := ℝ) a l).map fun t => t.2.2.2 * (t.1.map fun q => ∑ i, x i ^ q).prod *
        U ^ t.2.1 * (L - ∑ i, x i) ^ t.2.2.1).sum := by
  apply BGP212.V2e.inner_genFun <;> assumption

theorem genEntry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil N g L τ C (genFun L a₁ l₁) (genFun L a₂ l₂) = genEntryVal N g L τ C a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genEntry_eq <;> assumption

theorem tableFn_eq {K : Type*} [Field K] [LinearOrder K] (keys : List ((ℕ × ℕ × ℕ × ℕ) × K)) (dflt : ℕ → ℕ → ℕ → ℕ → K)
    (h : ∀ p ∈ keys, dflt p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 = p.2) : tableFn keys dflt = dflt := by
  apply BGP212.V2e.tableFn_eq <;> assumption

theorem pieceMn_zero {K : Type*} [Field K] [LinearOrder K] (N r k a b : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceMn N r k a b g L τ C m 0 = pieceM N r k a b g L τ C m := by
  apply BGP212.V2e.pieceMn_zero <;> assumption

theorem pieceMn_zero_zero {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) :
    pieceMn N r k 0 0 g L τ C m n = pieceJ N r k g L τ C m n := by
  apply BGP212.V2e.pieceMn_zero_zero <;> assumption

theorem pieceE_eq_pieceMn {K : Type*} [Field K] [LinearOrder K] (N r k eR eS : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceE N r k eR eS g L τ C m =
      (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : K) *
        pieceMn N r k eR eS g L τ C m 0 := by
  apply BGP212.V2e.pieceE_eq_pieceMn <;> assumption

theorem pieceMn_of_pieceE (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) (v : ℚ)
    (h : pieceE N r k eR eS g L τ C m = v) :
    pieceMn N r k eR eS g L τ C m 0 =
      v / (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : ℚ) := by
  apply BGP212.V2e.pieceMn_of_pieceE <;> assumption

theorem genPiece_empty {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g L τ : K) (C : ℕ → K)
    (h : C r - r * g < 0 ∨ τ - (r + k) * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ = 0 := by
  apply BGP212.V2e.genPiece_empty <;> assumption

theorem pieceMn_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceMn N r k a b g L τ C m n : ℚ) : ℝ) =
      pieceMn N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n := by
  apply BGP212.V2e.pieceMn_cast <;> assumption

theorem genPiece_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genPiece N r k g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genPiece N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genPiece_cast <;> assumption

theorem genEntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genEntryVal N g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genEntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ := by
  apply BGP212.V2e.genEntryVal_cast <;> assumption

theorem eval_gen_list (a : ℕ) (l : List ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑l) = genFun (53 / 50) a l x := by
  apply BGP212.V2e.eval_gen_list <;> assumption

theorem jT_gen_table3 (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₁ ↑l₁))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₂ ↑l₂)) =
      ((genEntryVal 44 BGP212.Params.g BGP212.Params.L BGP212.Params.τ BGP212.Params.C a₁ l₁ a₂ l₂ :
        ℚ) : ℝ) := by
  apply BGP212.V2e.jT_gen_table3 <;> assumption

theorem genEntryPP_table3 : genEntryVal 44 g L τ C 0 [2] 0 [2] = (7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genEntryPP_table3 <;> assumption

theorem genEntryP4_table3 : genEntryVal 44 g L τ C 0 [4] 0 [] = (27146941746034049653011991737523849302835974678539227554371494168379938438711742944681131854870392187261353645054163409711502678639106601137182002258884443591 / 986556067069278136327489095125656641872369539861953601372389724843082278988749410537917317043365983408875763416290283203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genEntryP4_table3 <;> assumption

theorem genEntryP22_table3 : genEntryVal 44 g L τ C 0 [2, 2] 0 [] = (3660374136242989387380652323344436977885293224812077133314553468438557932655033514945994325078669043220726153480139763307169322012096626962840970046529550207 / 15998206493015321129634958299334972570903289835599247589822536078536469389006747197912172708811340271495282649993896484375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genEntryP22_table3 <;> assumption

theorem genEntryLP_table3 : genEntryVal 44 g L τ C 1 [] 0 [] = (6512729183781214820113280314392773438904805507600460190719004030691673914761277396184278068946241317308961830318311862437086743937347350312387921 / 1178114766972525727812651700768131080206771322237481618431868312815529158815719412700673274230211973190307617187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  apply BGP212.V2e.genEntryLP_table3 <;> assumption

theorem genEntryPP_eq_v2h : genEntryVal 44 g L τ C 0 [2] 0 [2] = p2p2EntryVal 44 g L τ C := by
  apply BGP212.V2e.genEntryPP_eq_v2h <;> assumption

theorem jT_P2_P2_gen_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P2_P2_gen_table3 <;> assumption

theorem jT_P4_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {4}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((27146941746034049653011991737523849302835974678539227554371494168379938438711742944681131854870392187261353645054163409711502678639106601137182002258884443591 / 986556067069278136327489095125656641872369539861953601372389724843082278988749410537917317043365983408875763416290283203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P4_one_table3 <;> assumption

theorem jT_P22_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2, 2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((3660374136242989387380652323344436977885293224812077133314553468438557932655033514945994325078669043220726153480139763307169322012096626962840970046529550207 / 15998206493015321129634958299334972570903289835599247589822536078536469389006747197912172708811340271495282649993896484375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_P22_one_table3 <;> assumption

theorem jT_LP1_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((6512729183781214820113280314392773438904805507600460190719004030691673914761277396184278068946241317308961830318311862437086743937347350312387921 / 1178114766972525727812651700768131080206771322237481618431868312815529158815719412700673274230211973190307617187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.jT_LP1_one_table3 <;> assumption

end BGP212.Challenge
