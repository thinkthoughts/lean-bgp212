/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.6 (p. 6), Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41),
Proposition 10.2 (pp. 41–42), §11 (p. 42).
-/
import BGP212.GenEntryBlock
import BGP212.Variational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2i: general polynomial marginal Gram entries `J_T[G_{a,λ}, G_{b,μ}]`

Statements only; proofs live in `Solution/GenEntry.lean` and `Solution/GenEntryTable.lean`, the
computational certificate in `Solution/GenEntryCert0.lean` … `Cert13.lean` and
`Solution/GenEntryCertSum.lean` (reusing V2h's certified moments). Objects are defined in
`BGP212/GenEntry.lean` (`genFun`, `pieceMn`, the coefficient-list polynomials, `stateVal`,
`placeVal`, `innerTerms`, `genPiece`, `genEntryVal`, `tableFn`) and `BGP212/GenEntryBlock.lean`
(`blk`), with V2h's classes and moments, V2g's `jTbil`, `pieceE`, V2f's `cellsVal`, `seg0Val`,
`pieceJ`, V2e-A's aggregates, V2d's `jT`, `endpoint`, V2b's `supportT`, `pieceSet`, `shiftV`, V0's
`gen`. The general statements keep `g`, `L`, `τ`, `C` as parameters; Table 3 enters only through
`BGP212.Params` (`g3`, `L3`, `τ3`, `C3`). -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e BGP212.Params MeasureTheory

/-- **A monomial weight against `U^m (L − S)^n`**: `∫_{piece} yᵗ U^m (L − S)^n =
(∏ tᵢ!) · pieceMn N r k a b … m n`, `a = Σ_{i ∈ R} tᵢ`, `b = Σ_{i ∉ R} tᵢ`. -/
theorem piece_mono_n {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (t : Fin N → ℕ) (m n : ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (∏ i, y i ^ t i) * blk g L C R K.card m n y =
      (∏ i, ((t i).factorial : ℝ)) *
        pieceMn N R.card K.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) g L τ C m n :=
  sorry


theorem lpEval_add {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpAdd f g) y = lpEval f y + lpEval g y :=
  sorry


theorem lpEval_mul {K : Type*} [Field K] (f g : List K) (y : K) :
    lpEval (lpMul f g) y = lpEval f y * lpEval g y :=
  sorry


theorem lpEval_shiftPow {K : Type*} [Field K] (s : K) (q : ℕ) (y : K) :
    lpEval (lpShiftPow s q) y = (y + s) ^ q :=
  sorry

/-- **One open coordinate**: `∫ yᵢ^e f(yᵢ) W = Σ_j f_j ∫ yᵢ^{e+j} W`. -/
theorem coord_integral {N : ℕ} (P : Set (Fin N → ℝ))
    (hP : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → IntegrableOn φ P) (i : Fin N)
    (W : (Fin N → ℝ) → ℝ) (hW : Continuous W) (f : List ℝ) (e : ℕ) :
    ∫ y in P, y i ^ e * lpEval f (y i) * W y =
      coordSum (fun e' => ∫ y in P, y i ^ e' * W y) f e :=
  sorry

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
            fs (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) :=
  sorry

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
          (fun j => cls R K (is j)) fs fac :=
  sorry


theorem psum_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (q : ℕ) (y : Fin N → ℝ) :
    ∑ i, (y + shiftV g (R ∪ K)) i ^ q =
      ∑ i, lpEval (lpShiftPow (clsShift g (cls R K i)) q) (y i) :=
  sorry

/-- **A product of power sums on a piece**: `∫ ∏_{q ∈ Q} P̂_q(y + g·1_{R∪K}) U^m (L − S)^n` is
the placement value with no open coordinate. -/
theorem piece_psum {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (R K : Finset (Fin N)) (hRK : Disjoint R K) (m n : ℕ) (Q : List ℕ) :
    ∫ y in pieceSet N R (C R.card - R.card * g) (τ - (R.card + K.card) * g),
        (Q.map fun q => ∑ i, (y + shiftV g (R ∪ K)) i ^ q).prod * blk g L C R K.card m n y =
      placeVal (fun A B => pieceMn N R.card K.card A B g L τ C m n) (clsCount N R.card K.card) 0
        Fin.elim0 Fin.elim0 (Q.map fun q c => lpShiftPow (clsShift g c) q) :=
  sorry

/-- `∏_{q ∈ l} (X_q + u^q) = Σ_{(K, s)} ∏_{q ∈ K} X_q · u^s`. -/
theorem prod_subsetTerms (X : ℕ → ℝ) (u : ℝ) (l : List ℕ) :
    (l.map fun q => X q + u ^ q).prod = ((subsetTerms l).map fun t => (t.1.map X).prod * u ^ t.2).sum :=
  sorry

/-- `∫₀^U (M − u)^a u^s du = Σ_{j ≤ a} C(a, j) (−1)^j M^{a−j} U^{s+j+1} / (s + j + 1)`. -/
theorem inner_mono (M U : ℝ) (a s : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ a * u ^ s =
      ∑ j ∈ Finset.range (a + 1), ((a.choose j : ℕ) : ℝ) * (-1) ^ j / ((s + j + 1 : ℕ) : ℝ) *
        U ^ (s + j + 1) * M ^ (a - j) :=
  sorry

/-- **The inner integral of a generator**: `∫₀^U G_{a,l}(x̂, u) du` as the `innerTerms`. -/
theorem inner_genFun {N : ℕ} (L : ℝ) (a : ℕ) (l : List ℕ) (x : Fin N → ℝ) (U : ℝ) :
    ∫ u in (0 : ℝ)..U, genFun L a l (Fin.snoc x u : Fin (N + 1) → ℝ) =
      ((innerTerms (K := ℝ) a l).map fun t => t.2.2.2 * (t.1.map fun q => ∑ i, x i ^ q).prod *
        U ^ t.2.1 * (L - ∑ i, x i) ^ t.2.2.1).sum :=
  sorry

/-- **`J_T[G_{a₁,l₁}, G_{a₂,l₂}]` in closed form** for every `N ≥ 1` and data with
`0 ≤ g ≤ C(1)`, `C(N) < N g`: the bilinear `J_T` of two generators `(L − P₁)^a P_λ` is
`genEntryVal`. -/
theorem genEntry_eq {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hC1 : g ≤ C 1)
    (hCN : C N - N * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil N g L τ C (genFun L a₁ l₁) (genFun L a₂ l₂) = genEntryVal N g L τ C a₁ l₁ a₂ l₂ :=
  sorry


theorem tableFn_eq {K : Type*} [Field K] [LinearOrder K] (keys : List ((ℕ × ℕ × ℕ × ℕ) × K)) (dflt : ℕ → ℕ → ℕ → ℕ → K)
    (h : ∀ p ∈ keys, dflt p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 = p.2) : tableFn keys dflt = dflt :=
  sorry

/-- V2h's `pieceM` is `pieceMn` without the `L − S` factor. -/
theorem pieceMn_zero {K : Type*} [Field K] [LinearOrder K] (N r k a b : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceMn N r k a b g L τ C m 0 = pieceM N r k a b g L τ C m :=
  sorry

/-- V2f's `pieceJ` is the moment with no weight. -/
theorem pieceMn_zero_zero {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) :
    pieceMn N r k 0 0 g L τ C m n = pieceJ N r k g L τ C m n :=
  sorry

/-- V2g's `pieceE` in terms of `pieceMn` (for `r = 0` the rough degree is idle). -/
theorem pieceE_eq_pieceMn {K : Type*} [Field K] [LinearOrder K] (N r k eR eS : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceE N r k eR eS g L τ C m =
      (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : K) *
        pieceMn N r k eR eS g L τ C m 0 :=
  sorry

/-- Over `ℚ`: a certified `pieceE` value gives the moment. -/
theorem pieceMn_of_pieceE (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) (v : ℚ)
    (h : pieceE N r k eR eS g L τ C m = v) :
    pieceMn N r k eR eS g L τ C m 0 =
      v / (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : ℚ) :=
  sorry

/-- An empty piece (every moment zero) contributes nothing. -/
theorem genPiece_empty {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g L τ : K) (C : ℕ → K)
    (h : C r - r * g < 0 ∨ τ - (r + k) * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ = 0 :=
  sorry


theorem pieceMn_cast (N r k a b : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m n : ℕ) :
    ((pieceMn N r k a b g L τ C m n : ℚ) : ℝ) =
      pieceMn N r k a b (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) m n :=
  sorry


theorem genPiece_cast (N r k : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genPiece N r k g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genPiece N r k (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ :=
  sorry


theorem genEntryVal_cast (N : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ)
    (l₂ : List ℕ) :
    ((genEntryVal N g L τ C a₁ l₁ a₂ l₂ : ℚ) : ℝ) =
      genEntryVal N (g : ℝ) (L : ℝ) (τ : ℝ) (fun i => (C i : ℝ)) a₁ l₁ a₂ l₂ :=
  sorry

/-- V0's generator is `genFun` with `L = 53/50` (parts of `λ` as a list). -/
theorem eval_gen_list (a : ℕ) (l : List ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑l) = genFun (53 / 50) a l x :=
  sorry

/-- **Every marginal Gram entry of `B₂₁` at Table 3 is an explicit rational**: for all
`(a₁, λ₁)`, `(a₂, λ₂)` (parts as lists), `J_T[gen a₁ λ₁, gen a₂ λ₂] = genEntryVal 44 … a₁ λ₁ a₂ λ₂`
over `ℚ`. -/
theorem jT_gen_table3 (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₁ ↑l₁))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a₂ ↑l₂)) =
      ((genEntryVal 44 BGP212.Params.g BGP212.Params.L BGP212.Params.τ BGP212.Params.C a₁ l₁ a₂ l₂ :
        ℚ) : ℝ) :=
  sorry


theorem genEntryPP_table3 : genEntryVal 44 g L τ C 0 [2] 0 [2] = (7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem genEntryP4_table3 : genEntryVal 44 g L τ C 0 [4] 0 [] = (27146941746034049653011991737523849302835974678539227554371494168379938438711742944681131854870392187261353645054163409711502678639106601137182002258884443591 / 986556067069278136327489095125656641872369539861953601372389724843082278988749410537917317043365983408875763416290283203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem genEntryP22_table3 : genEntryVal 44 g L τ C 0 [2, 2] 0 [] = (3660374136242989387380652323344436977885293224812077133314553468438557932655033514945994325078669043220726153480139763307169322012096626962840970046529550207 / 15998206493015321129634958299334972570903289835599247589822536078536469389006747197912172708811340271495282649993896484375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry


theorem genEntryLP_table3 : genEntryVal 44 g L τ C 1 [] 0 [] = (6512729183781214820113280314392773438904805507600460190719004030691673914761277396184278068946241317308961830318311862437086743937347350312387921 / 1178114766972525727812651700768131080206771322237481618431868312815529158815719412700673274230211973190307617187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- The general closed form reproduces V2h's certified `J_T[P₂, P₂]`. -/
theorem genEntryPP_eq_v2h : genEntryVal 44 g L τ C 0 [2] 0 [2] = p2p2EntryVal 44 g L τ C :=
  sorry


theorem jT_P2_P2_gen_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2})) =
      ((7725983848948711113526555513296348981494914790345616552289449922668213805074028117241538978738136344566762720995034275359175909971179243068364482370754073429 / 34019174726526832287154796383643332478357570340067365564565162925623526861681014156479907484253999427892267704010009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- **`J_T[P₄, 1]` at Table 3** (a degree-4 distinguished coordinate). -/
theorem jT_P4_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {4}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((27146941746034049653011991737523849302835974678539227554371494168379938438711742944681131854870392187261353645054163409711502678639106601137182002258884443591 / 986556067069278136327489095125656641872369539861953601372389724843082278988749410537917317043365983408875763416290283203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- **`J_T[P_{(2,2)}, 1]` at Table 3** (two factors: merged and distinct placements). -/
theorem jT_P22_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2, 2}))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((3660374136242989387380652323344436977885293224812077133314553468438557932655033514945994325078669043220726153480139763307169322012096626962840970046529550207 / 15998206493015321129634958299334972570903289835599247589822536078536469389006747197912172708811340271495282649993896484375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- **`J_T[L − P₁, 1]` at Table 3** (the factor `(L − P₁)^a`, `a = 1`: moments with `(L − S)`). -/
theorem jT_LP1_one_table3 :
    jTbil 44 g3 L3 τ3 C3 (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0))
        (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 0)) =
      ((6512729183781214820113280314392773438904805507600460190719004030691673914761277396184278068946241317308961830318311862437086743937347350312387921 / 1178114766972525727812651700768131080206771322237481618431868312815529158815719412700673274230211973190307617187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

end BGP212.Challenge
