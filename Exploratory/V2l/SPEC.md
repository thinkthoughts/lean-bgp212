# V2ℓ: staged symmetric-function evaluation and reusable coefficient tables (specification)

Status: definitions, general proofs, staged certificates and demonstrations on branch `v2l`, based on
V2k (`8ca723d` on the V2j branch; the same Lean and Comparator content as `bbd5027` on `main`).
V2k's independent verification is reported separately; nothing here assumes it. V2i's, V2j's and
V2k's definitions and statements are unchanged.

## 1. Why staging

V2k's evaluator is proved equal to V2i's placement recursion (`symPlaceVal_eq`), but a single kernel
evaluation of a long run keeps every intermediate result: the degree-12 run (six shifted `P̂₂`,
2 052 canonical states, 9 537 generated entries in the last step) and the degree-12 table of
`J_T[P_(2,2,2), P_(2,2,2)]` on one piece both exhaust memory in one `decide +kernel` (8 GB container;
§6). V2ℓ certifies the same computations one factor, one chunk of states, one merge at a time, each
in its own `lean` process, and proves that the certificates compose to V2k's run and V2i's value.

## 2. Certificates (`BGP212/SymStaged.lean`)

- `symStepAll n φ L = normalize (L.flatMap (symStep n φ))` — one step of `symRun`.
- `StepCert n φ L L'` — `L'` carries the value of `L` continued by `φ`, for every moment oracle and
  every continuation (`∀ M rest, symVal M n rest L' = symVal M n (φ :: rest) L`).
- `ValEq n L L'`, `ChainCert n φs L L'` — value equality and chains of step certificates;
  `StepsOK n φs Ls` — the list-level chain `symStepAll n φᵢ Lᵢ = Lᵢ₊₁`.
- `combBEq` — Boolean equality of combinations with natural-number key comparisons (kernel checks).
- `psFactors g Q` — the factors `P̂_q`, `q ∈ Q`, on a piece.
- Compact data: `decComb`, `decTable`, `decProf` read states, tables and profiles from lists of
  natural numbers (the elaborator reads `ℕ` literals far faster than `ℚ` and `Fin` literals).
- Tables: `pairGroups ws` groups the inner-term pairs of weighted generator pairs by
  `(sorted multiset Q, power of U, power of L − S)`; `stagedTable N r k g R ws` evaluates each
  group from certified runs `R` (or V2k's run if absent); `abProfile L` is the moment profile of a
  run (`Σ κ ∏ e!` collected by `(A, B)`), `ProfCert n g Q P` a certified profile, and
  `profTable N r k g R ws` the table built from certified profiles.

## 3. Theorems (`Solution/SymStaged.lean`, `Solution/SymPerm.lean`, all proved)

| theorem | statement |
|---|---|
| `stepCert_of_eq` | `symStepAll n φ L = L' → StepCert n φ L L'` |
| `stepCert_of_beq` | `combBEq (symStepAll n φ L) L' = true → StepCert n φ L L'` |
| `stepCert_append`, `stepCert_merge` | certified chunks of `L₁ ++ L₂`; a merge `normalize (D₁ ++ D₂) = L'` |
| `stepCert_chunks`, `stepCert_runs` | chunks `Cs` with `List.Forall₂ (StepCert n φ) Cs Ds` and one merge (`normalize Ds.flatten` or the linear `mergeAll keyCmp 64 Ds`) certify `StepCert n φ Cs.flatten L'` |
| `chainCert_append`, `chainCert_snoc` | **prefix reuse**: a chain for `φs₁` composes with any continuation |
| `chainCert_val` | `ChainCert n φs L L' → symVal M n rest L' = symVal M n (φs ++ rest) L` |
| **`chainCert_placeVal`** | `ChainCert n φs [([], 1)] L → placeVal M n 0 Fin.elim0 Fin.elim0 φs = symFinal M L` |
| `chainCert_symPlaceVal`, `chainCert_symRun` | the same for V2k's `symPlaceVal`; V2k's run is a chain |
| **`symRun_of_steps`**, `placeVal_of_steps` | `StepsOK n φs (L :: Ls) → symRun n φs L = (L :: Ls).getLast _`, hence V2i's value |
| `msVal_perm`, **`placeVal_perm`** | `φs.Perm φs' → placeVal M n 0 Fin.elim0 Fin.elim0 φs = placeVal M n 0 Fin.elim0 Fin.elim0 φs'` |
| `stagedTable_eq`, `genPieceWith_eq_stagedTable` | for certified runs `R`: `Σ_{w∈ws} w · genPieceWith … Mo … = tableVal (stagedTable N r k g R ws) Mo` |
| `symFinal_abProfile`, `profCert_of_chain`, `profCert_of_chunks` | profiles from chains, chunk by chunk |
| **`profTable_eq`**, `genPieceWith_eq_profTable` | for certified profiles `R`: the same identity with `profTable` |
| `symFinal_flatten` | the value of a chunked combination is the sum over the chunks |

**Permutation invariance** (`Solution/SymPerm.lean`). With `mOp n φ` the operator of one factor on
continuations, `mOp n φ (mOp n ψ G) = mOp n ψ (mOp n φ G)` (`mOp_comm`): expanding both orders
gives two merges into the same part, merges into two distinct parts (`pairs_symm`: ordered pairs of
distinct elements of a multiset in either order), a merge and an opening, an opening and a merge
into the new part, and two openings, whose weights `w_c (w_d − [c = d])` are symmetric. Hence
`msVal` and V2i's `placeVal` depend only on the multiset of factors, and `pairGroups` sorts the
degrees of each inner-term pair.

Acceptance: no `sorry`; axioms `propext`, `Quot.sound`, `Classical.choice`.

## 4. Certificate pattern

For a run of factors `φ₁ … φ_K` from the empty state:

1. small steps: `StepCert n φᵢ Lᵢ₋₁ Lᵢ := stepCert_of_beq … (by decide +kernel)`;
2. a large step: the input `Lᵢ₋₁` is stored in chunks `[C₀, …].flatten` (data module); each chunk's step
   `StepCert n φᵢ Cⱼ Dⱼ` is one file; one merge file checks `combBEq (mergeAll keyCmp 64 [D₀, …]) Lᵢ`
   and concludes `StepCert n φᵢ Lᵢ₋₁ Lᵢ` (`stepCert_runs`);
3. chains: `chainCert_snoc` after each step; every prefix chain is itself a certified run;
4. values: `chainCert_placeVal`, with `symFinal` of a chunked combination as the sum of chunk
   values (`symFinal_flatten`), or through certified moment profiles (`profCert_of_chunks`);
5. tables: `stagedTable` / `profTable` against a list of certified runs or profiles, one kernel
   evaluation per piece, then V2j's moments.

Data modules (`…D`) contain no proofs and depend only on the definitions, so they build in parallel;
each certificate imports only the data it reads.

## 5. Demonstrations

- `SymStagedDemo1`: the list-level steps of `P̂₂³` on V2k's example data (`StepsOK`), giving
  V2k's `demo_place_222` and, through the prefix chain, `demo_place_22` (`rfl`); `perm_42`
  (`placeVal_perm`) with both orders evaluated by the kernel.
- Runs `Dm` (example data) and `T3` (Table 3, piece `(6, 3)`, `n = (6, 3, 35)`, shift `g`) of `P̂₂^k`,
  `k ≤ 6`, in `Solution/SymStagedCert/` (22 modules per run, with the value and profile files 52): factors 1–4 in one file; factor 5 in 4 chunk
  files and a merge; factor 6 in 12 chunk files and a merge.
- `SymStagedDemo2`: degree 10 on the example data, V2k's `demo_place_22222` (`rfl`).
- `SymStagedDemo3`: **degree 12** on the example data (`demo_place_222222_staged`), from the chain and
  three files of chunk values.
- `SymStagedDemo4`, `Demo5`: at Table 3, `stagedTable` with the certified runs `T3_R` reproduces
  V2k's tables of `J_T[P₂, P₂]` (19 keys) and `J_T[P_(2,2), P_(2,2)]` (85 keys); with V2j's moments the
  first is V2i's `gpPP_6_3` (`rfl`), the second V2k's `genPieceP22_6_3_expansion` (`rfl`).
- `SymStagedDemo6`: **degree 12 at Table 3**: piece `(6, 3)` of `J_T[P_(2,2,2), P_(2,2,2)]` as an
  explicit combination of 231 moments, from the certified profiles `T3_P` (64 inner-term pairs,
  7 groups `(Q, m, n)`, profiles of at most 85 entries).

## 6. Measurements

Build container: 2 cores, 8 GB. Peak = maximum resident set of the build (`lake` and `lean`), of which
about 3.0–3.4 GB are memory-mapped Mathlib and project `.olean` files shared between processes;
anonymous = peak heap memory of the process tree. Each module below is one `lean` process
(`specs/checks/sym_staged_v2l_build.sh` order).

| modules | count | time per module | peak | anonymous |
|---|---|---|---|---|
| chunk certificates (`…Run5C*`, `…Run6C*`) | 32 | 7.2–11.0 s | 3.50–3.78 GB | 0.78–1.07 GB |
| merges and chains (`…Run5`, `…Run6`) | 4 | 5.1–9.5 s | 3.29–3.95 GB | 0.58–1.20 GB |
| data (`…Run4D`, `…Run5D`, `…Run6D`) | 6 | 4.1–13.7 s | 2.98–3.32 GB | 0.41–0.75 GB |
| factors 1–4 (`…Run1`) | 2 | 8.0–8.4 s | 3.58 GB | 0.88 GB |
| values, profiles, runs, demonstrations | 16 | 3.5–8.6 s | 3.14–3.52 GB | 0.38–0.78 GB |
| suite (`SymStagedSuite`) | 1 | 7.2 s | 3.21 GB | 0.43 GB |

In all: 61 modules, 479 s, every module under 4 GB (largest 3.95 GB). Proof modules:
`Solution/SymStaged.lean` 3.0 s, `Solution/SymPerm.lean` 3.1 s. Comparator (35 statements): 358 s,
peak 3.18 GB, accepted by the Lean default kernel.

Single evaluations for comparison (one `decide +kernel`):

| computation | V2i | V2k, one evaluation | V2ℓ, staged |
|---|---|---|---|
| `P̂₂⁵` (degree 10), example data | out of memory | 23.2 s, 5.33 GB | 8 certificate files, each ≤ 3.68 GB |
| `P̂₂⁶` (degree 12), example data | — | out of memory at 42 s | 22 certificate files + 3 value files, each ≤ 3.88 GB |
| `J_T[P_(2,2,2), P_(2,2,2)]`, piece `(6, 3)` table (231 keys) | — | out of memory at 156 s | run `T3` + 5 profile files + 5.5 s table, each ≤ 3.95 GB |

Engineering notes. (i) Certificate data are lists of natural numbers (`decComb`, `decTable`,
`decProf`): literal rational lists of 281 states exceeded the elaborator's heartbeat limit, and a
2 052-entry literal its recursion depth. (ii) Merging the chunk results with the linear
`mergeAll keyCmp 64` (no re-sorting) and keeping the data in a module separate from the merge lowered
the degree-12 merge from 2.35 GB to 1.1–1.2 GB anonymous memory. (iii) Moment profiles (at most 85
entries per run here) replace per-state table entries, so the degree-12 table is checked in 5.5 s.
(iv) `lake build` runs modules in parallel; on a 4 GB machine build the staged modules with
`specs/checks/sym_staged_v2l_build.sh`, one `lean` process at a time.

Controls: `chainCert_placeVal` with `2 * symFinal M L` in the Challenge is rejected by Comparator;
five kernel controls (`specs/checks/sym_staged_v2l_controls.py`: a changed step coefficient, a changed
chunk state, a merge missing a state, a changed profile coefficient, equal values claimed for different
multisets of degrees) are rejected, and the positive controls are accepted.

## 7. Toward `J_T(P⋆)` (exploratory counts, not theorems)

Over all 846 generators of `B₂₁` (Python, `specs/checks/sym_staged_v2l_counts.py`): 139 distinct
ordered kept-part lists; their pairs give 17 381 distinct ordered factor lists but only **2 361
multisets** (`placeVal_perm`), so one run per multiset per piece suffices. The 2 361 multisets,
sorted, are closed under prefixes: one chain step per multiset, **2 360 certified steps per
piece** cover all of them, against 16 389 steps without prefix sharing; the longest has 20
factors. The weights `n_c − ℓ` depend on the piece, so runs are per piece; profiles are shared by
all pairs and all powers of `U` and `L − S` of a piece.

Next steps: (1) certificates for the 2 360-step prefix trie of one piece, chunked by the measured
states per step; (2) aggregated profile tables for `J_T(P⋆) = Σ cᵢ cⱼ J_T[Gᵢ, Gⱼ]` per piece
(`profTable_eq` with weights); (3) moments by V2j §6's `boxVal` collapse; (4) sharing runs across
pieces through polynomial coefficients in `(n₀, n₁, n₂)` (the unweighted transition is independent
of the class sizes, V2k's `psTrans_indep`, while the constant terms `Σ n_c φ(c)₀` are not).
