# V2k: symmetric-function reduction of the placement recursion (specification)

Status: definitions, general proofs and kernel demonstrations on branch `v2k`, based on V2j
(`8fa2aa5`; the same Lean and Comparator content as the rebased `v2j-main` commit `4e02daf` on
`main` `e20c364`). V2j's VPS verification is reported separately; nothing here assumes it.

## 1. What is replaced

V2i integrates a product of class-dependent power sums over a piece with `placeVal`: each factor
either merges into an open coordinate (its polynomial is multiplied) or opens a new coordinate of
a class `c` with multiplicity `n_c − #(open in c)`. Unrolled, this enumerates the set partitions of the
factors with a class for every block (Bell numbers × `3^blocks`), and each leaf expands its
coordinate polynomials coefficient by coefficient. Oracle calls at the example data
(`n = (3, 2, 4)`, shifted `P̂₂`, `specs/checks/sym_reduce_v2k_model.py`):

| factors | degree | V2i oracle calls | V2k canonical states (after the last factor) |
|---|---|---|---|
| `P̂₂²` | 4 | 96 | 26 |
| `P̂₂³` | 6 | 1 155 | 91 |
| `P̂₂⁴` | 8 | 15 309 | 281 |
| `P̂₂⁵` | 10 | 220 182 | 787 |
| `P̂₃P̂₂²P̂₁³` | 10 | 1 652 811 | 3 755 |

V2k keeps the specification and replaces the evaluation strategy. V2i's and V2j's definitions and
theorems are unchanged.

## 2. Mathematics

**Class power sums.** On a piece, a factor is `Σᵢ φ(cls i)(yᵢ)` with `φ(c) = Σ_a φ(c)_a y^a`, so

```text
Σᵢ φ(cls i)(yᵢ) = Σ_c n_c φ(c)₀ + Σ_c Σ_{a≥1} φ(c)_a p_{c,a},     p_{c,a} = Σ_{cls i = c} yᵢ^a.
```

**Augmented monomial symmetric functions.** For a class `c` and a partition `ν`,
`m̃_ν = Σ_{distinct i₁,…,i_ℓ of class c} ∏_j y_{i_j}^{ν_j} = (∏_v mult_v(ν)!) · m_ν`. A state is a
product `∏_c m̃_{ν_c}`, i.e. a multiset of parts `(c, e)`. The transition from products of class power
sums is the classical rule

```text
p_{c,a} · m̃_ν = Σ_j m̃_{ν + a e_j} + m̃_{ν ∪ (a)}           (parts of class c only),
```

so `p_α = Σ_ν R_{α,ν} m̃_ν` with nonnegative integers `R_{α,ν}` that do not depend on the class
sizes (`psTrans`, `psTrans_indep`); the coefficient of `m_ν` is `R_{α,ν} ∏_v mult_v(ν)!`. A part of
exponent `0` is a scalar: `m̃_{ν ∪ (0)} = (n_c − ℓ(ν)) m̃_ν` (`msVal_zero_part`), so the constant terms
contribute `Σ_c n_c φ(c)₀` without changing the state.

**Dirichlet-weighted moment.** V2i's piece integral of a monomial `yᵗ` is `∏ tᵢ! · M(A, B)` with
`A` the degree on rough coordinates (class `0`) and `B` the degree on the others (V2i's
`piece_state`, the leaves of `stateVal`). All `(n_c)_{ℓ(ν_c)}` monomials of `m̃_{ν_c}` have the same
integral, so

```text
∫ ∏_c m̃_{ν_c} = ∏_c (n_c)_{ℓ(ν_c)} · ∏_{(c,e)} e! · M(|ν₀|, |ν₁| + |ν₂|)      (monoMoment),
∫ ∏_c m_{ν_c}  = ∏_c #monomials(m_{ν_c}) · ∏ e! · M(…),   #monomials(m_ν) = (n)_ℓ / ∏_v mult_v(ν)!.
```

Hence, for any product of class-dependent power sums,

```text
∫ ∏_q (Σᵢ φ_q(cls i)(yᵢ)) = Σ_ν R_ν · monoMoment ν          (symPlaceVal_eq_trans, placeVal_eq_trans),
```

with `R_ν` the coefficients in the augmented monomial basis (`symRun1`). The evaluator itself
applies the weight `n_c − ℓ(ν_c)` when a part opens (`symRun`); `symRun_scale` proves that this is
the unweighted run with each state multiplied by `∏_c (n_c)_{ℓ(ν_c)}`.

## 3. Data representation (`BGP212/SymReduce.lean`)

- `SPart := Fin 3 × ℕ` (class, exponent); `SKey := List SPart`, canonical when sorted by class
  ascending, then exponent descending (`sIns`): one integer partition per class.
- A combination is `List (SKey × K)` with exact coefficients (`ℚ` in certificates).
- `symStep n φ` applies one factor to one state; `normalize` sorts by `keyCmp` and merges equal
  states (`normalizeBy`: balanced merge sort by structural recursion, `O(n log n)` comparisons on
  natural numbers, shallow kernel evaluation); `symRun` applies the factors in order;
  `symFinal M L = Σ κ · ∏ e! · M(A, B)` (balanced summation `bsum`).
- `symPlaceVal M n φs`, `genPieceSym`, `genEntrySym`: V2i's values through the new evaluator.
- `psFactor c a` is `p_{c,a}` (`lpEval_psFactor`); `symStep1`, `symRun1`, `psTrans` are the
  unweighted transition; `fallW`, `monoMoment` the Dirichlet moment.
- `genTable N r k g a₁ l₁ a₂ l₂ : List (MKey × K)`: every moment coefficient of a piece from one
  evaluation (keys `(A, B, m, n)` as in V2j, merged by `mkeyCmp`); `aggTable` for weighted pairs;
  `tableVal T Mo = Σ c · Mo s`.
- The specification side: `msVal M n rest S` on multisets `S` (the order of parts is immaterial by
  construction), `msOf`, `msum` (iterated coefficient sums over open coordinates), `symVal`.

## 4. Theorems (`Solution/SymReduce.lean`, all proved; every ordered field `K`)

| theorem | statement |
|---|---|
| `placeVal_eq_msum` | `placeVal M n d c fs rest = msum d fs (fun e => msVal M n rest (msOf c e))` |
| `placeVal_eq_msVal` | `placeVal M n 0 Fin.elim0 Fin.elim0 φs = msVal M n φs 0` |
| `msVal_zero_part` | `msVal M n rest ((c, 0) ::ₘ S) = msVal M n rest S` |
| `symStep_val` | one step of the evaluator = one factor of `msVal` |
| `normalize_val`, `symRun_val` | normalization preserves the value; `symFinal M (symRun n φs L) = symVal M n φs L` |
| **`symPlaceVal_eq`** | `symPlaceVal M n φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs` (all `M`, `n`, `φs`) |
| `genPieceSym_eq`, `genEntrySym_eq` | `genPieceSym … Mo … = genPieceWith … Mo …`; `genEntrySym = genEntryVal` |
| `jT_eq_genEntrySym` | `J_T[G_{a₁,λ₁}, G_{a₂,λ₂}] = genEntrySym N g L τ C a₁ λ₁ a₂ λ₂` (every `N ≥ 1`, admissible data) |
| `aggCoeff_eq_sym` | V2j's collapsed coefficients through `genPieceSym` |
| `symRun_scale` | `symRun n φs (L.map (scaleQ n)) = (symRun1 n φs L).map (scaleQ n)` |
| `symPlaceVal_eq_trans`, `placeVal_eq_trans` | `Σ_{(ν,R) ∈ symRun1 n φs [([],1)]} R · monoMoment M n ν` |
| `lpEval_psFactor` | `psFactor c a` evaluates to `y^a` on class `c` and `0` elsewhere |
| `psTrans_indep`, `placeVal_psTrans` | `R_{α,ν}` independent of `n` (positive parts); `∫ p_α = Σ_ν R_{α,ν} · monoMoment ν` |
| `genPieceWith_eq_table` | `genPieceWith N r k g Mo a₁ l₁ a₂ l₂ = tableVal (genTable N r k g a₁ l₁ a₂ l₂) Mo` |
| `aggTable_eq` | `Σ_{w ∈ ws} w · genPieceWith … = tableVal (aggTable N r k g ws) Mo` |
| `genEntryVal_eq_table` | `genEntryVal` as the signed sum of `tableVal (genTable …) (pieceMn …)` over pieces |

Acceptance: no `sorry`; axioms `propext`, `Quot.sound`, `Classical.choice`.

**Proof architecture.** (i) `msum` and the coefficient-list algebra (`coordSum_lpMul`: multiplying
coefficient lists composes coefficient sums; exchange and linearity lemmas) turn V2i's polynomial
coordinates into monomial ones (`msum_update_lpMul`, `stateVal_eq_msum`); (ii) induction over the
factors identifies V2i's merge/open recursion with `msVal` on the multiset of parts
(`placeVal_eq_msum`), so permutation invariance is free; (iii) exponent-`0` parts are scalars;
(iv) the canonical evaluator is checked against `msVal` step by step (`picks_sum`: picking a list
element and erasing it from the multiset; `sIns_coe`: sorted insertion is `cons` on multisets), and
normalization by merge sort preserves values and commutes with key-dependent weights.

## 5. Certificate pattern with tables

1. `tab_*`: `genTable … = literal` (or `aggTable`) by one `decide +kernel` — all moment
   coefficients of a piece at once;
2. `mo_*`: each distinct moment once (V2j's lemmas are reused);
3. `tv_*`: `tableVal literal (pieceMn …) = v` by `simp only` with the moment lemmas and `norm_num`;
4. term-mode bridges: `genPieceWith_eq_table` / `aggTable_eq` / `genEntryVal_eq_table`.

## 6. Measurements (build container: 2 cores, 8 GB; `lean` process with Mathlib loaded ≈ 3.1 GB)

Kernel time of single statements (`decide +kernel`, profiler "type checking"; peak memory of the
whole `lean` process):

| statement | V2i (placement recursion) | V2k |
|---|---|---|
| value of `P̂₂²` (degree 4) at the example data | 0.32 s | 0.20 s |
| `P̂₂³` (degree 6) | 3.83 s, 3.50 GB | 1.14 s, 3.22 GB |
| `P̂₂⁴` (degree 8) | 45.1 s, 5.81 GB | 4.98 s, 3.70 GB |
| `P̂₂⁵` (degree 10) | out of memory (5.87 GB at 55 s) | 19.4 s, 5.48 GB |
| Table 3, `J_T[P_(2,2), P_(2,2)]`, piece `(6, 3)`, one coefficient (key `(1, 6, 2, 0)`) | 30.8 s, 5.79 GB (`aggCoeff`) | 5.08 s, 3.71 GB (`genPieceSym`) |
| the same piece, all 85 coefficients | 85 evaluations as above (not run) | 4.91 s, 3.67 GB (`genTable`, one evaluation) |
| Table 3, `J_T[P₂, P₂]`, piece `(6, 3)`, all 19 coefficients | 19 V2j `ck_*` lemmas, each under 0.5 s | 0.13 s (`genTable`) |

Builds (one `lean` process per file, `lake build`): `Solution/SymReduce.lean` 9.5 s, 3.20 GB;
`SymReduceDemo1` 14.9 s, 3.74 GB; `SymReduceDemo2` 17.1 s, 3.98 GB; `SymReduceDemo3` (degree 10)
23.2 s, 5.33 GB; `SymReduceSuite` 12.9 s; `Challenge/SymReduce.lean` 11.2 s. Comparator (36
statements): 296 s, peak 3.21 GB, accepted by the Lean default kernel.

Controls: the statement `symPlaceVal_eq` with `2 * placeVal …` in the Challenge is rejected by
Comparator ("statement do not match"); four kernel controls (`specs/checks/sym_reduce_v2k_controls.py`:
the m-basis coefficient in place of the augmented one, a shifted value, an exponent-`0` part, a
changed table key) are rejected and the positive control is accepted.

Engineering notes. (i) Normalizing by linear insertion (`O(n²)` list comparisons) took 26–32 s for
the degree-8 run; the balanced merge sort takes 5 s. (ii) A left fold of `n` insertions builds a
nested term of depth `n` that the kernel evaluates recursively; at 3 108 entries it stopped
reducing, so runs are merged in balanced rounds (`mergePairs`, `mergeAll`) and sums are taken
in balanced rounds (`bsum`), both by structural recursion. (iii) Comparisons use natural-number
tests (`partCmp`, `keyCmp`, `mkeyCmp`) rather than `DecidableEq` instances on `Fin` and lists.

## 7. Toward `J_T(P⋆) − 4 I_T(P⋆)` (forward plan; not a result)

`J_T(P⋆)` is `aggTable` over `ws = [(cᵢ cⱼ, aᵢ, λᵢ, aⱼ, λⱼ)]` per piece (`aggTable_eq`,
`jT_weighted_eq_agg`). State counts of V2k's evaluator at Table 3's class sizes of piece `(6, 3)`
(`n = (6, 3, 35)`, shifts `(g, g, 0)`, Python model):

| factors | degree | canonical states after the last factor | largest generated list |
|---|---|---|---|
| `P̂₂⁴` | 8 | 281 | 906 |
| `P̂₂⁶` | 12 | 2 052 | 9 537 |
| `P̂₃²P̂₂²P̂₁²` | 12 | 7 556 | 22 589 |
| `P̂₁¹²` | 12 | 18 240 | 101 050 |
| `P̂₄⁴` | 16 | 1 354 | 6 028 |
| `P̂₂⁸` | 16 | 11 807 | 71 103 |
| `P̂₃⁷` | 21 | 19 147 | 131 475 |
| `P̂₂¹⁰` | 20 | 57 559 | 423 441 |

Next steps: (1) collect the 4 317 distinct inner terms of `B₂₁` and the 2 361 multisets `μ` (V2j
§5) as factor lists; (2) aggregate tables across all generator pairs per piece, so each `μ` is run
once and each moment key appears once; (3) evaluate the moments through V2j §6's `boxVal`
collapse; (4) the kernel cost of the largest `μ` (tens of thousands of states) calls for splitting a
run into certified intermediate combinations (`normalize (Lᵢ.flatMap (symStep n φ)) = Lᵢ₊₁` per
factor), which `symRun_val` already supports; (5) `I_T(P⋆)` from V2c's closed form.
