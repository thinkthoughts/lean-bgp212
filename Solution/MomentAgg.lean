/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import BGP212.MomentAgg
import Solution.GenEntryTable
import Solution.GenEntry

/-! # V2j: shared-moment aggregation (proofs)

* linearity of `stateVal`, `placeVal`, `genPieceWith` in the moment oracle;
* locality: they read the oracle only at `stateKeys`, `placeKeys`, `genKeys`;
* `genPieceWith_eq_keys`: the coefficient collapse over any duplicate-free key list covering the
  queried keys, and `genPieceWith_eq_coeffs` for `genCoeffs`;
* `aggPiece_eq`, `aggEntryVal_eq`: the aggregated value of a weighted list of generator pairs is
  the weighted sum of V2i's `genPieceWith`, `genEntryVal`. All statements are algebraic identities
  about V2i's definitions, over any field. -/

namespace BGP212.V2e

section Lin


/-! ## `coordSum` -/

theorem coordSum_add' {K : Type*} [Field K] (b b' : ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => b e + b' e) f e = coordSum b f e + coordSum b' f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp only [coordSum, ih]; ring

theorem coordSum_mul' {K : Type*} [Field K] (a : K) (b : ℕ → K) (f : List K) (e : ℕ) :
    coordSum (fun e => a * b e) f e = a * coordSum b f e := by
  induction f generalizing e with
  | nil => simp [coordSum]
  | cons c f ih => simp only [coordSum, ih]; ring

theorem coordSum_congr' {K : Type*} [Field K] (b b' : ℕ → K) (f : List K) (e : ℕ)
    (h : ∀ i, i < f.length → b (e + i) = b' (e + i)) : coordSum b f e = coordSum b' f e := by
  induction f generalizing e with
  | nil => rfl
  | cons c f ih =>
    simp only [coordSum]
    rw [show b e = b' e from by simpa using h 0 (by simp)]
    congr 1
    exact ih (e + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      rwa [show e + (i + 1) = e + 1 + i by omega] at this

/-! ## Linearity in the oracle -/

theorem stateVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => M A B + M' A B) d c fs A B =
        stateVal M d c fs A B + stateVal M' d c fs A B := by
  intro d
  induction d with
  | zero => intro c fs A B; rfl
  | succ d ih =>
    intro c fs A B
    simp only [stateVal]
    rw [← coordSum_add']
    exact coordSum_congr' _ _ _ _ fun i _ => by rw [ih]; ring

theorem stateVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      stateVal (fun A B => a * M A B) d c fs A B = a * stateVal M d c fs A B := by
  intro d
  induction d with
  | zero => intro c fs A B; rfl
  | succ d ih =>
    intro c fs A B
    simp only [stateVal]
    rw [← coordSum_mul']
    exact coordSum_congr' _ _ _ _ fun i _ => by rw [ih]; ring

theorem placeVal_add {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => M A B + M' A B) n d c fs fac =
        placeVal M n d c fs fac + placeVal M' n d c fs fac := by
  intro fac
  induction fac with
  | nil => intro d c fs; exact stateVal_add M M' d c fs 0 0
  | cons φ rest ih =>
    intro d c fs
    simp only [placeVal, ih, Finset.sum_add_distrib, mul_add]
    ring

theorem placeVal_smul {K : Type*} [Field K] (a : K) (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      placeVal (fun A B => a * M A B) n d c fs fac = a * placeVal M n d c fs fac := by
  intro fac
  induction fac with
  | nil => intro d c fs; exact stateVal_smul a M d c fs 0 0
  | cons φ rest ih =>
    intro d c fs
    simp only [placeVal, ih]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring

end Lin

section Ord


theorem genPieceWith_add {K : Type*} [Field K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ)
    (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => Mo A B m n + Mo' A B m n) a₁ l₁ a₂ l₂ =
      genPieceWith N r k g Mo a₁ l₁ a₂ l₂ + genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ := by
  unfold genPieceWith
  rw [← List.sum_map_add]
  congr 1; apply List.map_congr_left; intro t₁ _
  rw [← List.sum_map_add]
  congr 1; apply List.map_congr_left; intro t₂ _
  rw [placeVal_add]; ring

theorem genPieceWith_smul {K : Type*} [Field K] (N r k : ℕ) (g : K) (a : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => a * Mo A B m n) a₁ l₁ a₂ l₂ =
      a * genPieceWith N r k g Mo a₁ l₁ a₂ l₂ := by
  unfold genPieceWith
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro t₁ _
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro t₂ _
  rw [placeVal_smul]; ring

theorem placeVal_zero' {K : Type*} [Field K] (n : Fin 3 → ℕ) (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3)
    (fs : Fin d → List K) : placeVal (fun _ _ => (0 : K)) n d c fs fac = 0 :=
  placeVal_zero n fac d c fs

theorem genPieceWith_zero {K : Type*} [Field K] (N r k : ℕ) (g : K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun _ _ _ _ => (0 : K)) a₁ l₁ a₂ l₂ = 0 := by
  unfold genPieceWith
  simp [placeVal_zero']

/-- **Linearity in the oracle**: the value of a finite combination of oracles is the combination
of the values. -/
theorem genPieceWith_listSum {K : Type*} [Field K] [LinearOrder K] {ι : Type*} (N r k : ℕ) (g : K) (S : List ι) (c : ι → K)
    (F : ι → ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g (fun A B m n => (S.map fun t => c t * F t A B m n).sum) a₁ l₁ a₂ l₂ =
      (S.map fun t => c t * genPieceWith N r k g (F t) a₁ l₁ a₂ l₂).sum := by
  induction S with
  | nil => simpa using genPieceWith_zero N r k g a₁ l₁ a₂ l₂
  | cons t S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [genPieceWith_add, genPieceWith_smul, ih]

end Ord

/-! ## Locality: the queried keys -/

section Loc


theorem stateVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) :
    ∀ (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K) (A B : ℕ),
      (∀ p ∈ stateKeys d c fs A B, M p.1 p.2 = M' p.1 p.2) →
        stateVal M d c fs A B = stateVal M' d c fs A B := by
  intro d
  induction d with
  | zero => intro c fs A B h; exact h (A, B) (by simp [stateKeys])
  | succ d ih =>
    intro c fs A B h
    simp only [stateVal]
    refine coordSum_congr' _ _ _ _ fun i hi => ?_
    rw [ih]
    intro p hp
    refine h p ?_
    simp only [stateKeys, List.mem_dedup, List.mem_flatMap, List.mem_range]
    exact ⟨0 + i, by simpa using hi, by simpa using hp⟩

theorem placeVal_congr {K : Type*} [Field K] (M M' : ℕ → ℕ → K) (n : Fin 3 → ℕ) :
    ∀ (fac : List (Fin 3 → List K)) (d : ℕ) (c : Fin d → Fin 3) (fs : Fin d → List K),
      (∀ p ∈ placeKeys d c fs fac, M p.1 p.2 = M' p.1 p.2) →
        placeVal M n d c fs fac = placeVal M' n d c fs fac := by
  intro fac
  induction fac with
  | nil => intro d c fs h; exact stateVal_congr M M' d c fs 0 0 h
  | cons φ rest ih =>
    intro d c fs h
    simp only [placeVal]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ih _ _ _ fun p hp => h p ?_
      simp only [placeKeys, List.mem_dedup, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨j, List.mem_finRange j, hp⟩
    · refine Finset.sum_congr rfl fun c' _ => ?_
      rw [ih _ _ _ fun p hp => h p ?_]
      simp only [placeKeys, List.mem_dedup, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨c', List.mem_finRange c', hp⟩

end Loc

section Ord2


/-- **Locality**: `genPieceWith` reads its oracle only at `genKeys`. -/
theorem genPieceWith_congr {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo Mo' : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (h : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, Mo s.1 s.2.1 s.2.2.1 s.2.2.2 = Mo' s.1 s.2.1 s.2.2.1 s.2.2.2) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = genPieceWith N r k g Mo' a₁ l₁ a₂ l₂ := by
  unfold genPieceWith
  congr 1; apply List.map_congr_left; intro t₁ ht₁
  congr 1; apply List.map_congr_left; intro t₂ ht₂
  congr 1
  refine placeVal_congr _ _ _ _ _ _ _ fun p hp =>
    h (p.1, p.2, t₁.2.1 + t₂.2.1, t₁.2.2.1 + t₂.2.2.1) ?_
  simp only [genKeys, List.mem_dedup, List.mem_flatMap, List.mem_map]
  exact ⟨t₁, ht₁, t₂, ht₂, p, hp, rfl⟩

theorem sum_delta {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (f : MKey → K) (s : MKey) (hs : s ∈ S) :
    (S.map fun t => f t * delta t s.1 s.2.1 s.2.2.1 s.2.2.2).sum = f s := by
  induction S with
  | nil => simp at hs
  | cons t S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hS
    by_cases h : s = t
    · subst h
      have hz : (S.map fun t => f t * delta t s.1 s.2.1 s.2.2.1 s.2.2.2).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
        have : (s.1, s.2.1, s.2.2.1, s.2.2.2) ≠ u := fun h' => hS.1 (by simpa [← h'] using hu)
        simp [delta, this]
      rw [hz, add_zero]
      simp [delta]
    · have hs' : s ∈ S := (List.mem_cons.mp hs).resolve_left h
      have : (s.1, s.2.1, s.2.2.1, s.2.2.2) ≠ t := fun h' => h (by simpa using h')
      simp only [delta, if_neg this, mul_zero, zero_add]
      exact ih hS.2 hs'

/-- **Coefficient collapse**: for any duplicate-free key list `S` containing the queried keys,
`genPieceWith … Mo … = Σ_{s ∈ S} genPieceWith … (delta s) … · Mo s`. -/
theorem genPieceWith_eq_keys {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) (S : List MKey) (hS : S.Nodup)
    (hcov : ∀ s ∈ genKeys g a₁ l₁ a₂ l₂, s ∈ S) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      (S.map fun s => genPieceWith N r k g (delta s) a₁ l₁ a₂ l₂ *
        Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum := by
  rw [genPieceWith_congr N r k g Mo
    (fun A B m n => (S.map fun t => Mo t.1 t.2.1 t.2.2.1 t.2.2.2 * delta t A B m n).sum)
    a₁ l₁ a₂ l₂ fun s hs => (sum_delta S hS (fun t => Mo t.1 t.2.1 t.2.2.1 t.2.2.2) s
      (hcov s hs)).symm,
    genPieceWith_listSum]
  congr 1; apply List.map_congr_left; intro t _; ring

/-- **Coefficient collapse** with V2i's own keys: `genPieceWith = Σ_{(s, c) ∈ genCoeffs} c · Mo s`. -/
theorem genPieceWith_eq_coeffs {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (Mo : ℕ → ℕ → ℕ → ℕ → K) (a₁ : ℕ)
    (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ) :
    genPieceWith N r k g Mo a₁ l₁ a₂ l₂ =
      ((genCoeffs N r k g a₁ l₁ a₂ l₂).map fun p => p.2 * Mo p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2).sum := by
  rw [genPieceWith_eq_keys N r k g Mo a₁ l₁ a₂ l₂ _ (List.nodup_dedup _) fun s hs => hs,
    genCoeffs, List.map_map]
  rfl

theorem list_sum_comm {K : Type*} [Field K] {α β : Type*} (as : List α) (bs : List β) (F : α → β → K) :
    (as.map fun a => (bs.map fun b => F a b).sum).sum = (bs.map fun b => (as.map fun a => F a b).sum).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

/-- **Shared moments across generator pairs**, over a key list `S`: if `S` is duplicate-free and
contains the keys of every pair, the aggregated piece value is the weighted sum of V2i's piece
values. -/
theorem aggPieceOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N r k : ℕ) (g : K) (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S)
    (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPieceOn S N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  have hw : ∀ w ∈ ws, w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 =
      (S.map fun s => w.1 * genPieceWith N r k g (delta s) w.2.1 w.2.2.1 w.2.2.2.1
        w.2.2.2.2 * Mo s.1 s.2.1 s.2.2.1 s.2.2.2).sum := fun w hw' => by
    rw [genPieceWith_eq_keys N r k g Mo _ _ _ _ S hS (hcov w hw'), ← List.sum_map_mul_left]
    congr 1; apply List.map_congr_left; intro s _; ring
  rw [List.map_congr_left hw, list_sum_comm]
  unfold aggPieceOn aggCoeff
  congr 1; apply List.map_congr_left; intro s _
  rw [← List.sum_map_mul_right]

/-- **Shared moments across generator pairs** with the canonical keys `aggKeys`. -/
theorem aggPiece_eq {K : Type*} [Field K] [LinearOrder K] (N r k : ℕ) (g : K) (ws : List (WPair K)) (Mo : ℕ → ℕ → ℕ → ℕ → K) :
    aggPiece N r k g ws Mo =
      (ws.map fun w => w.1 * genPieceWith N r k g Mo w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  aggPieceOn_eq (aggKeys g ws) (List.nodup_dedup _) N r k g ws (fun w hw s hs => by
    simp only [aggKeys, List.mem_dedup, List.mem_flatMap]; exact ⟨w, hw, hs⟩) Mo

theorem list_sum_finset_comm {K : Type*} [Field K] {α β : Type*} (as : List α) (s : Finset β) (F : α → β → K) :
    (as.map fun a => ∑ b ∈ s, F a b).sum = ∑ b ∈ s, (as.map fun a => F a b).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- **The aggregated entry** over a key list `S` (duplicate-free, covering the keys):
`aggEntryValOn S N g L τ C ws = Σ_{(w, a₁, l₁, a₂, l₂) ∈ ws} w · genEntryVal N g L τ C a₁ l₁ a₂ l₂`. -/
theorem aggEntryValOn_eq {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K)
    (ws : List (WPair K))
    (hcov : ∀ w ∈ ws, ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    aggEntryValOn S N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum := by
  unfold aggEntryValOn genEntryVal genRow genPiece
  simp_rw [aggPieceOn_eq S hS _ _ _ g ws hcov]
  have hw : ∀ w : WPair K, w.1 * ((N + 1 : K) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
      ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
        genPieceWith N r k g (fun A B m n => pieceMn N r k A B g L τ C m n) w.2.1 w.2.2.1 w.2.2.2.1
          w.2.2.2.2) =
      (N + 1 : K) * ∑ r ∈ Finset.range (N + 1), (N.choose r : K) *
        ∑ k ∈ Finset.range (N - r + 1), ((N - r).choose k : K) * (-1) ^ k *
          (w.1 * genPieceWith N r k g (fun A B m n => pieceMn N r k A B g L τ C m n) w.2.1 w.2.2.1
            w.2.2.2.1 w.2.2.2.2) := by
    intro w
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [List.map_congr_left fun w _ => hw w]
  symm
  rw [List.sum_map_mul_left, list_sum_finset_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [List.sum_map_mul_left, list_sum_finset_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [List.sum_map_mul_left]

/-- **The aggregated entry**: `aggEntryVal N g L τ C ws = Σ_{(w, a₁, l₁, a₂, l₂) ∈ ws} w ·
genEntryVal N g L τ C a₁ l₁ a₂ l₂`. Each piece evaluates every distinct moment once. -/
theorem aggEntryVal_eq {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L τ : K) (C : ℕ → K) (ws : List (WPair K)) :
    aggEntryVal N g L τ C ws =
      (ws.map fun w => w.1 * genEntryVal N g L τ C w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2).sum :=
  aggEntryValOn_eq (aggKeys g ws) (List.nodup_dedup _) N g L τ C ws fun w hw s hs => by
    simp only [aggKeys, List.mem_dedup, List.mem_flatMap]; exact ⟨w, hw, hs⟩

/-- **One pair as an aggregated piece value** (term-mode bridge for certificates). -/
theorem genPiece_eq_aggPieceOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey) (hS : S.Nodup)
    (N r k : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genPiece N r k g L τ C a₁ l₁ a₂ l₂ =
      aggPieceOn S N r k g [(1, a₁, l₁, a₂, l₂)] (fun A B m n => pieceMn N r k A B g L τ C m n) := by
  rw [aggPieceOn_eq S hS N r k g _ hcov]
  simp [genPiece]

/-- **One pair as an aggregated entry** (term-mode bridge for certificates). -/
theorem genEntryVal_eq_aggEntryValOn {K : Type*} [Field K] [LinearOrder K] (S : List MKey)
    (hS : S.Nodup) (N : ℕ) (g L τ : K) (C : ℕ → K) (a₁ : ℕ) (l₁ : List ℕ) (a₂ : ℕ) (l₂ : List ℕ)
    (hcov : ∀ w ∈ ([(1, a₁, l₁, a₂, l₂)] : List (WPair K)),
      ∀ s ∈ genKeys g w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2, s ∈ S) :
    genEntryVal N g L τ C a₁ l₁ a₂ l₂ = aggEntryValOn S N g L τ C [(1, a₁, l₁, a₂, l₂)] := by
  rw [aggEntryValOn_eq S hS N g L τ C _ hcov]
  simp

end Ord2

/-! ## The integral form -/

open BGP212.Gram BGP212.V2d in
/-- **A weighted sum of marginal Gram entries is the aggregated value**: for every `N ≥ 1`,
admissible data and weighted generator pairs `ws`, `Σ w · J_T[G_{a₁,l₁}, G_{a₂,l₂}] =
aggEntryVal N g L τ C ws` (the shape of `J_T(P⋆) = Σ cᵢ cⱼ J_T[Gᵢ, Gⱼ]`). -/
theorem jT_weighted_eq_agg {N : ℕ} (hN : 0 < N) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (hC1 : g ≤ C 1) (hCN : C N - N * g < 0) (ws : List (WPair ℝ)) :
    (ws.map fun w => w.1 * jTbil N g L τ C (genFun L w.2.1 w.2.2.1) (genFun L w.2.2.2.1 w.2.2.2.2)).sum =
      aggEntryVal N g L τ C ws := by
  rw [aggEntryVal_eq]
  congr 1; apply List.map_congr_left; intro w _
  rw [genEntry_eq hN g L τ C hg hC1 hCN]

end BGP212.V2e
