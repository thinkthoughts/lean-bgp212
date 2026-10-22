/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, Lemma 9.2 and the display of `J_T` (p. 41).
-/
import BGP212.GenEntry

/-! # V2i: moment tables (bridges for the certificate)

`tableFn_eq`: a moment oracle given by a table of certified values equals the oracle it tabulates.
The bridges relate `pieceMn` to the moments already certified in V2f–V2h (`pieceM`, `pieceE`,
`pieceJ`), so V2i's certificate reuses them; `genPieceWith_zero` gives the empty pieces. -/

namespace BGP212.V2e

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

theorem tableFn_eq (keys : List ((ℕ × ℕ × ℕ × ℕ) × K)) (dflt : ℕ → ℕ → ℕ → ℕ → K)
    (h : ∀ p ∈ keys, dflt p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 = p.2) : tableFn keys dflt = dflt := by
  funext A B m n
  unfold tableFn
  induction keys with
  | nil => rfl
  | cons p keys ih =>
    rw [List.find?_cons]
    by_cases hp : (p.1 == (A, B, m, n)) = true
    · rw [hp]
      dsimp only
      have he : p.1 = (A, B, m, n) := by simpa using hp
      rw [← h p List.mem_cons_self, he]
    · rw [Bool.not_eq_true] at hp
      rw [hp]
      dsimp only
      exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- V2h's `pieceM` is `pieceMn` without the `L − S` factor. -/
theorem pieceMn_zero (N r k a b : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceMn N r k a b g L τ C m 0 = pieceM N r k a b g L τ C m := rfl

/-- V2f's `pieceJ` is the moment with no weight. -/
theorem pieceMn_zero_zero (N r k : ℕ) (g L τ : K) (C : ℕ → K) (m n : ℕ) :
    pieceMn N r k 0 0 g L τ C m n = pieceJ N r k g L τ C m n := by
  simp only [pieceMn, pieceJ, add_zero]

/-- V2g's `pieceE` in terms of `pieceMn` (for `r = 0` the rough degree is idle). -/
theorem pieceE_eq_pieceMn (N r k eR eS : ℕ) (g L τ : K) (C : ℕ → K) (m : ℕ) :
    pieceE N r k eR eS g L τ C m =
      (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : K) *
        pieceMn N r k eR eS g L τ C m 0 := by
  unfold pieceE pieceMn
  split_ifs with h1 h2 <;> push_cast <;> ring_nf
  all_goals first | rfl | simp [h2]

/-- Over `ℚ`: a certified `pieceE` value gives the moment. -/
theorem pieceMn_of_pieceE (N r k eR eS : ℕ) (g L τ : ℚ) (C : ℕ → ℚ) (m : ℕ) (v : ℚ)
    (h : pieceE N r k eR eS g L τ C m = v) :
    pieceMn N r k eR eS g L τ C m 0 =
      v / (((if r = 0 then 1 else eR.factorial) * eS.factorial : ℕ) : ℚ) := by
  rw [← h, pieceE_eq_pieceMn, mul_div_cancel_left₀]
  have hpos : 0 < (if r = 0 then 1 else eR.factorial) * eS.factorial :=
    Nat.mul_pos (by split_ifs <;> positivity) (Nat.factorial_pos eS)
  exact_mod_cast hpos.ne'

omit [LinearOrder K] in
theorem stateVal_zero : ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
    stateVal (fun _ _ => (0 : K)) d c fs A B = 0 := by
  intro d
  induction d with
  | zero => intro c fs A B; rfl
  | succ d ih =>
    intro c fs A B
    simp only [stateVal, ih, mul_zero]
    generalize fs 0 = f
    generalize 0 = e
    induction f generalizing e with
    | nil => rfl
    | cons x f ihf => simp only [coordSum, mul_zero, zero_add, ihf]

omit [LinearOrder K] in
theorem placeVal_zero (n : Fin 3 → ℕ) : ∀ (fac : List (Fin 3 → List K)) (d : ℕ)
    (c : Fin d → Fin 3) (fs : Fin d → List K), placeVal (fun _ _ => (0 : K)) n d c fs fac = 0 := by
  intro fac
  induction fac with
  | nil => intro d c fs; exact stateVal_zero d c fs 0 0
  | cons φ rest ih => intro d c fs; simp [placeVal, ih]

/-- An empty piece (every moment zero) contributes nothing. -/
theorem genPiece_empty (N r k : ℕ) (g L τ : K) (C : ℕ → K)
    (h : C r - r * g < 0 ∨ τ - (r + k) * g < 0) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ = 0 := by
  have hz : (fun A B m n => pieceMn N r k A B g L τ C m n) = fun _ _ _ _ => (0 : K) := by
    funext A B m n; simp only [pieceMn, if_pos h]
  unfold genPiece genPieceWith
  rw [hz]
  simp [placeVal_zero]

end Formula

end BGP212.V2e
