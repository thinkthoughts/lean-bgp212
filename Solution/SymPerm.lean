/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, the display of `J_T` (p. 41), §11 (B₂₁, p. 42).
-/
import Solution.SymReduce

/-! # V2ℓ: the order of the factors is immaterial (proofs)

V2k's multiset-state value `msVal M n φs S` applies the factors one at a time through the operator
`mOp n φ` (merge into a part, or open a new one). Two such operators commute
(`mOp_comm`): expanding both orders gives six families of terms — two merges into the same part,
merges into two distinct parts, a merge and an opening (either order), an opening followed by a
merge into the new part, and two openings — which match pairwise. Hence `msVal` and V2i's
`placeVal` depend only on the multiset of factors (`msVal_perm`, `placeVal_perm`), and inner-term
pairs with the same multiset of power-sum degrees share one run. -/

namespace BGP212.V2e

section Perm

variable {K : Type*} [Field K]

/-- **Definition.** One factor as an operator on continuations: merge `φ` into a part of `S` or
open a new part, `n_c − #(class c)` times. -/
def mOp (n : Fin 3 → ℕ) (φ : Fin 3 → List K) (G : Multiset SPart → K) (S : Multiset SPart) : K :=
  (S.map fun x => coordSum (fun a => G ((x.1, x.2 + a) ::ₘ S.erase x)) (φ x.1) 0).sum +
    ∑ c : Fin 3, ((n c : K) - (S.countP fun x => x.1 = c : ℕ)) *
      coordSum (fun a => G ((c, a) ::ₘ S)) (φ c) 0

theorem msVal_cons_mOp (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φ : Fin 3 → List K)
    (rest : List (Fin 3 → List K)) (S : Multiset SPart) :
    msVal M n (φ :: rest) S = mOp n φ (msVal M n rest) S := rfl

/-- **Definition.** The open weight `n_c − #(class c in S)`. -/
def wt (n : Fin 3 → ℕ) (S : Multiset SPart) (c : Fin 3) : K :=
  (n c : K) - (S.countP fun x => x.1 = c : ℕ)

theorem coordSum_msum (F : SPart → ℕ → K) (m : Multiset SPart) (f : List K) :
    coordSum (fun a => (m.map fun y => F y a).sum) f 0 = (m.map fun y => coordSum (F y) f 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [coordSum_zero_body]
  | cons z m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [coordSum_add'', ih]

theorem msum_finsum (m : Multiset SPart) (F : SPart → Fin 3 → K) :
    (m.map fun x => ∑ d : Fin 3, F x d).sum = ∑ d : Fin 3, (m.map fun x => F x d).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Finset.sum_add_distrib]

theorem msum_mul_left (m : Multiset SPart) (c : K) (F : SPart → K) :
    (m.map fun x => c * F x).sum = c * (m.map F).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring

theorem mset_congr (m : Multiset SPart) (F F' : SPart → K) (h : ∀ x ∈ m, F x = F' x) :
    (m.map F).sum = (m.map F').sum := by
  rw [Multiset.map_congr rfl h]

/-- Ordered pairs of distinct elements of a multiset, in either order. -/
theorem pairs_symm (S : Multiset SPart) (H : SPart → SPart → Multiset SPart → K) :
    (S.map fun x => ((S.erase x).map fun y => H x y ((S.erase x).erase y)).sum).sum =
      (S.map fun y => ((S.erase y).map fun x => H x y ((S.erase y).erase x)).sum).sum := by
  induction S using Multiset.induction_on generalizing H with
  | empty => simp
  | cons z S ih =>
    have e1 : ∀ x ∈ S, ((z ::ₘ S).erase x) = z ::ₘ S.erase x := fun x hx =>
      Multiset.erase_cons_tail_of_mem hx
    -- left side
    have hL : ((z ::ₘ S).map fun x => (((z ::ₘ S).erase x).map fun y =>
        H x y (((z ::ₘ S).erase x).erase y)).sum).sum =
        (S.map fun y => H z y (S.erase y)).sum + (S.map fun x => H x z (S.erase x)).sum +
          (S.map fun x => ((S.erase x).map fun y => H x y (z ::ₘ (S.erase x).erase y)).sum).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, add_assoc]
      congr 1
      rw [← Multiset.sum_map_add]
      refine mset_congr _ _ _ fun x hx => ?_
      rw [e1 x hx, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
      congr 1
      refine mset_congr _ _ _ fun y hy => ?_
      rw [Multiset.erase_cons_tail_of_mem hy]
    have hR : ((z ::ₘ S).map fun y => (((z ::ₘ S).erase y).map fun x =>
        H x y (((z ::ₘ S).erase y).erase x)).sum).sum =
        (S.map fun x => H x z (S.erase x)).sum + (S.map fun y => H z y (S.erase y)).sum +
          (S.map fun y => ((S.erase y).map fun x => H x y (z ::ₘ (S.erase y).erase x)).sum).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, add_assoc]
      congr 1
      rw [← Multiset.sum_map_add]
      refine mset_congr _ _ _ fun y hy => ?_
      rw [e1 y hy, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
      congr 1
      refine mset_congr _ _ _ fun x hx => ?_
      rw [Multiset.erase_cons_tail_of_mem hx]
    rw [hL, hR, ih (fun x y m => H x y (z ::ₘ m))]
    ring

theorem countP_merge (S : Multiset SPart) (x : SPart) (hx : x ∈ S) (a : ℕ) (d : Fin 3) :
    ((x.1, x.2 + a) ::ₘ S.erase x).countP (fun y => y.1 = d) = S.countP (fun y => y.1 = d) := by
  conv_rhs => rw [← Multiset.cons_erase hx]
  rw [Multiset.countP_cons, Multiset.countP_cons]

theorem wt_open (n : Fin 3 → ℕ) (S : Multiset SPart) (c d : Fin 3) (a : ℕ) :
    wt (K := K) n ((c, a) ::ₘ S) d = wt n S d - if c = d then 1 else 0 := by
  simp only [wt, Multiset.countP_cons]
  split_ifs <;> push_cast <;> ring

/-- The six families of terms of two consecutive factors. -/
theorem mOp_mOp (n : Fin 3 → ℕ) (φ ψ : Fin 3 → List K) (G : Multiset SPart → K)
    (S : Multiset SPart) :
    mOp n φ (mOp n ψ G) S =
      (S.map fun x => coordSum (fun a => coordSum (fun b =>
        G ((x.1, x.2 + a + b) ::ₘ S.erase x)) (ψ x.1) 0) (φ x.1) 0).sum +
      (S.map fun x => ((S.erase x).map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ (S.erase x).erase y)) (ψ y.1) 0) (φ x.1) 0).sum).sum +
      (S.map fun x => ∑ d : Fin 3, wt n S d * coordSum (fun a => coordSum (fun b =>
        G ((d, b) ::ₘ (x.1, x.2 + a) ::ₘ S.erase x)) (ψ d) 0) (φ x.1) 0).sum +
      ∑ c : Fin 3, wt n S c * coordSum (fun a => coordSum (fun b =>
        G ((c, a + b) ::ₘ S)) (ψ c) 0) (φ c) 0 +
      ∑ c : Fin 3, wt n S c * (S.map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (c, a) ::ₘ S.erase y)) (ψ y.1) 0) (φ c) 0).sum +
      ∑ c : Fin 3, ∑ d : Fin 3, wt n S c * (wt n S d - if c = d then 1 else 0) *
        coordSum (fun a => coordSum (fun b => G ((d, b) ::ₘ (c, a) ::ₘ S)) (ψ d) 0) (φ c) 0 := by
  -- the merge part of the outer factor
  have hx : ∀ x ∈ S, coordSum (fun a => mOp n ψ G ((x.1, x.2 + a) ::ₘ S.erase x)) (φ x.1) 0 =
      coordSum (fun a => coordSum (fun b => G ((x.1, x.2 + a + b) ::ₘ S.erase x)) (ψ x.1) 0) (φ x.1) 0 +
      ((S.erase x).map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ (S.erase x).erase y)) (ψ y.1) 0) (φ x.1) 0).sum +
      ∑ d : Fin 3, wt n S d * coordSum (fun a => coordSum (fun b =>
        G ((d, b) ::ₘ (x.1, x.2 + a) ::ₘ S.erase x)) (ψ d) 0) (φ x.1) 0 := by
    intro x hxS
    have hin : ∀ a : ℕ, mOp n ψ G ((x.1, x.2 + a) ::ₘ S.erase x) =
        coordSum (fun b => G ((x.1, x.2 + a + b) ::ₘ S.erase x)) (ψ x.1) 0 +
        ((S.erase x).map fun y => coordSum (fun b =>
          G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ (S.erase x).erase y)) (ψ y.1) 0).sum +
        ∑ d : Fin 3, wt n S d * coordSum (fun b => G ((d, b) ::ₘ (x.1, x.2 + a) ::ₘ S.erase x)) (ψ d) 0 := by
      intro a
      rw [mOp, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
      congr 1
      · congr 1
        refine mset_congr _ _ _ fun y hy => ?_
        rw [Multiset.erase_cons_tail_of_mem hy]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [wt, countP_merge S x hxS a d]
    rw [coordSum_congr'' _ _ hin, coordSum_add'', coordSum_add'', coordSum_msum, coordSum_finsetSum]
    simp only [coordSum_mul'']
  have ho : ∀ c : Fin 3, coordSum (fun a => mOp n ψ G ((c, a) ::ₘ S)) (φ c) 0 =
      coordSum (fun a => coordSum (fun b => G ((c, a + b) ::ₘ S)) (ψ c) 0) (φ c) 0 +
      (S.map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (c, a) ::ₘ S.erase y)) (ψ y.1) 0) (φ c) 0).sum +
      ∑ d : Fin 3, (wt n S d - if c = d then 1 else 0) * coordSum (fun a => coordSum (fun b =>
        G ((d, b) ::ₘ (c, a) ::ₘ S)) (ψ d) 0) (φ c) 0 := by
    intro c
    have hin : ∀ a : ℕ, mOp n ψ G ((c, a) ::ₘ S) =
        coordSum (fun b => G ((c, a + b) ::ₘ S)) (ψ c) 0 +
        (S.map fun y => coordSum (fun b => G ((y.1, y.2 + b) ::ₘ (c, a) ::ₘ S.erase y)) (ψ y.1) 0).sum +
        ∑ d : Fin 3, (wt n S d - if c = d then 1 else 0) *
          coordSum (fun b => G ((d, b) ::ₘ (c, a) ::ₘ S)) (ψ d) 0 := by
      intro a
      rw [mOp, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
      congr 1
      · congr 1
        refine mset_congr _ _ _ fun y hy => ?_
        rw [Multiset.erase_cons_tail_of_mem hy]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [← wt_open n S c d a, wt]
    rw [coordSum_congr'' _ _ hin, coordSum_add'', coordSum_add'', coordSum_msum, coordSum_finsetSum]
    simp only [coordSum_mul'']
  rw [mOp, mset_congr S _ _ hx, Multiset.sum_map_add, Multiset.sum_map_add]
  simp only [ho, mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← msum_mul_left]
  simp only [wt, mul_assoc]
  ring

/-- **Two factors commute.** -/
theorem mOp_comm (n : Fin 3 → ℕ) (φ ψ : Fin 3 → List K) (G : Multiset SPart → K)
    (S : Multiset SPart) : mOp n φ (mOp n ψ G) S = mOp n ψ (mOp n φ G) S := by
  rw [mOp_mOp, mOp_mOp]
  -- same part
  have h1 : (S.map fun x => coordSum (fun a => coordSum (fun b =>
        G ((x.1, x.2 + a + b) ::ₘ S.erase x)) (ψ x.1) 0) (φ x.1) 0).sum =
      (S.map fun x => coordSum (fun a => coordSum (fun b =>
        G ((x.1, x.2 + a + b) ::ₘ S.erase x)) (φ x.1) 0) (ψ x.1) 0).sum := by
    refine mset_congr _ _ _ fun x _ => ?_
    rw [coordSum_comm]
    refine coordSum_congr'' _ _ (fun b => coordSum_congr'' _ _ (fun a => ?_) _ _) _ _
    rw [add_right_comm]
  -- two distinct parts
  have h2 : (S.map fun x => ((S.erase x).map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ (S.erase x).erase y)) (ψ y.1) 0) (φ x.1) 0).sum).sum =
      (S.map fun x => ((S.erase x).map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ (S.erase x).erase y)) (φ y.1) 0) (ψ x.1) 0).sum).sum := by
    rw [pairs_symm S (fun x y m => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (x.1, x.2 + a) ::ₘ m)) (ψ y.1) 0) (φ x.1) 0)]
    refine mset_congr _ _ _ fun y _ => mset_congr _ _ _ fun x _ => ?_
    rw [coordSum_comm, Multiset.erase_comm]
    refine coordSum_congr'' _ _ (fun b => coordSum_congr'' _ _ (fun a => ?_) _ _) _ _
    rw [Multiset.cons_swap, Multiset.erase_comm]
  -- a merge and an opening
  have h3 : ∀ (φ ψ : Fin 3 → List K),
      (S.map fun x => ∑ d : Fin 3, wt n S d * coordSum (fun a => coordSum (fun b =>
        G ((d, b) ::ₘ (x.1, x.2 + a) ::ₘ S.erase x)) (ψ d) 0) (φ x.1) 0).sum =
      ∑ c : Fin 3, wt n S c * (S.map fun y => coordSum (fun a => coordSum (fun b =>
        G ((y.1, y.2 + b) ::ₘ (c, a) ::ₘ S.erase y)) (φ y.1) 0) (ψ c) 0).sum := by
    intro φ ψ
    rw [msum_finsum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [msum_mul_left]
    congr 1
    refine mset_congr _ _ _ fun x _ => ?_
    rw [coordSum_comm]
    refine coordSum_congr'' _ _ (fun b => coordSum_congr'' _ _ (fun a => ?_) _ _) _ _
    rw [Multiset.cons_swap]
  -- opening, then merging into the new part
  have h4 : ∑ c : Fin 3, wt n S c * coordSum (fun a => coordSum (fun b =>
        G ((c, a + b) ::ₘ S)) (ψ c) 0) (φ c) 0 =
      ∑ c : Fin 3, wt n S c * coordSum (fun a => coordSum (fun b =>
        G ((c, a + b) ::ₘ S)) (φ c) 0) (ψ c) 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coordSum_comm]
    congr 1
    refine coordSum_congr'' _ _ (fun b => coordSum_congr'' _ _ (fun a => ?_) _ _) _ _
    rw [add_comm]
  -- two openings
  have h6 : ∑ c : Fin 3, ∑ d : Fin 3, wt n S c * (wt n S d - if c = d then 1 else 0) *
        coordSum (fun a => coordSum (fun b => G ((d, b) ::ₘ (c, a) ::ₘ S)) (ψ d) 0) (φ c) 0 =
      ∑ c : Fin 3, ∑ d : Fin 3, wt n S c * (wt n S d - if c = d then 1 else 0) *
        coordSum (fun a => coordSum (fun b => G ((d, b) ::ₘ (c, a) ::ₘ S)) (φ d) 0) (ψ c) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
    have hw : wt n S c * (wt n S d - if c = d then 1 else 0) =
        wt (K := K) n S d * (wt n S c - if d = c then 1 else 0) := by
      by_cases h : c = d
      · subst h; ring
      · simp only [h, Ne.symm h, ite_false]; ring
    rw [hw, coordSum_comm]
    congr 1
    refine coordSum_congr'' _ _ (fun b => coordSum_congr'' _ _ (fun a => ?_) _ _) _ _
    rw [Multiset.cons_swap]
  rw [h1, h2, h3 φ ψ, h3 ψ φ, h4, h6]
  ring

/-- Two consecutive factors of `msVal` commute. -/
theorem msVal_swap (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) (φ ψ : Fin 3 → List K)
    (rest : List (Fin 3 → List K)) (S : Multiset SPart) :
    msVal M n (φ :: ψ :: rest) S = msVal M n (ψ :: φ :: rest) S := by
  rw [msVal_cons_mOp, msVal_cons_mOp]
  have e1 : msVal M n (ψ :: rest) = mOp n ψ (msVal M n rest) := funext fun T => rfl
  have e2 : msVal M n (φ :: rest) = mOp n φ (msVal M n rest) := funext fun T => rfl
  rw [e1, e2, mOp_comm]

/-- **The multiset-state value depends only on the multiset of factors.** -/
theorem msVal_perm (M : ℕ → ℕ → K) (n : Fin 3 → ℕ) {φs φs' : List (Fin 3 → List K)}
    (h : φs.Perm φs') : ∀ S, msVal M n φs S = msVal M n φs' S := by
  induction h with
  | nil => intro S; rfl
  | cons φ _ ih =>
    intro S
    rw [msVal_cons_mOp, msVal_cons_mOp, show msVal M n _ = msVal M n _ from funext ih]
  | swap φ ψ l => intro S; exact msVal_swap M n ψ φ l S
  | trans _ _ ih₁ ih₂ => intro S; rw [ih₁, ih₂]

end Perm

/-- **V2i's placement value depends only on the multiset of factors.** -/
theorem placeVal_perm {K : Type*} [Field K] (M : ℕ → ℕ → K) (n : Fin 3 → ℕ)
    {φs φs' : List (Fin 3 → List K)} (h : φs.Perm φs') :
    placeVal M n 0 Fin.elim0 Fin.elim0 φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs' := by
  rw [placeVal_eq_msVal, placeVal_eq_msVal, msVal_perm M n h]

end BGP212.V2e

#print axioms BGP212.V2e.placeVal_perm
