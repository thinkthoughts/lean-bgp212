# V2m: certified prefix-trie evaluation for B₂₁ (specification)

Status: definitions, general proofs, a certified subtree at Table 3, piece `(6, 3)`, and
demonstrations on branch `v2m`, based on V2ℓ (`5e8feaa`; the same Lean and Comparator content as
`a02c40e` on `main`). V2ℓ's independent verification is reported separately; nothing here assumes it.
V2i–V2ℓ definitions and statements are unchanged.

## 1. Three layers

| layer | what it is | where |
|---|---|---|
| general theorems | trie evaluation is correct for every certified trie, every reordering of a node's degrees, every moment oracle | `Solution/SymTrie.lean` |
| kernel-certified results | the nodes of one subtree at piece `(6, 3)`, their moment profiles, coverage of two enumerated blocks, four coefficient tables | `Solution/SymTrieCert/`, `SymTrieProfData*.lean`, `SymTrieNodes.lean`, `SymTrieKept.lean`, `SymTrieTab*.lean`, `SymTrieDemo1–6.lean` |
| exploratory enumeration | the 2 361 multisets of `B₂₁`, the 2 360-step trie, state counts of the remaining nodes | `specs/checks/sym_staged_v2l_counts.py`, §6 |

Tables are coefficient representations: `tableVal T Mo = Σ c · Mo s`. The rational moments `pieceMn`
are evaluated separately (V2f–V2j), and V2m evaluates none of them.

## 2. Definitions (`BGP212/SymTrie.lean`)

- `stepFactor g q` — the factor `P̂_q` on a piece with class shift `g`.
- `TrieOK n g T` — every node `(Q, L)` of `T` has `ChainCert n (psFactors g Q) [([], 1)] L`.
- `ProfOK n g R` — every entry `(Q, P)` of `R` is a certified moment profile (`ProfCert`, V2ℓ).
- `sortDesc`, `isSortedDesc`, `natListMem`, `prefixClosed`, `trieShapeOK` — the canonical order of a
  multiset of degrees and the shape of a trie.
- `partsList`, `b21Lambdas`, `b21Kept`, `keptUpTo s`, `blockMultisets s`, `shortMultisetsOf kept k`,
  `shortMultisets k`, `b21Multisets` — enumeration from the definition of `B₂₁` (even parts, `|λ| ≤ 21`) and V2i's
  `subsetTerms`: the partitions, the kept-part lists of the inner integrals, and the sorted factor
  multisets of inner-term pairs (of the block `|λ| ≤ s`, with at most `k` factors, of all of `B₂₁`).

## 3. Theorems (`Solution/SymTrie.lean`, all proved)

| theorem | statement |
|---|---|
| `trieOK_root` | `TrieOK n g [([], [([], 1)])]` |
| `trieOK_cons` | `TrieOK n g T → (Q, L) ∈ T → StepCert n (stepFactor g q) L L' → TrieOK n g ((Q ++ [q], L') :: T)` |
| `trieOK_cons_chain` | adding a node with its own chain |
| **`trieOK_placeVal`** | `TrieOK n g T → (Q, L) ∈ T → Q'.Perm Q → placeVal M n 0 Fin.elim0 Fin.elim0 (psFactors g Q') = symFinal M L` |
| `profOK_nil`, `profOK_cons` | building certified profile lists |
| `profCert_perm` | `ProfCert n g Q P → Q'.Perm Q → ProfCert n g Q' P` |
| `profCert_of_trie` | the profile of a trie node |
| `profCert_of_step` | a child's profile from its stored parent: `ChainCert … Q … L → abProfile (symStepAll n (stepFactor g q) L) = P → ProfCert n g (Q ++ [q]) P` |
| `profCert_of_step_chunks` | the same with the parent in chunks and one merge of the chunk profiles |
| **`trieProf_table_eq`** | `ProfOK (clsCount N r k) g R → Σ_{w ∈ ws} w · genPieceWith N r k g Mo … = tableVal (profTable N r k g R ws) Mo` |
| `table_parts_merge` | if each part `wsᵢ` of the pairs has `Σ_{w ∈ wsᵢ} … = tableVal Tᵢ Mo` and `mergeAll mkeyCmp 64 [T₁, …] = T`, then `Σ_{w ∈ ws} … = tableVal T Mo` (`ws` the concatenation of the parts); applied repeatedly, parts merge in a tree |
| `trieProf_table_parts` | the same with each part certified by `profTable … wsᵢ = Tᵢ` |

The certificates of particular nodes are separate: each is a `StepCert` (stored nodes) or a
`ProfCert` (all nodes) proved by `decide +kernel` in its own module (the profile data itself lives in
`SymTrieProfData0–4.lean`, so table checks import data without the certificates), assembled into
`Tt_trie_ok : TrieOK (clsCount 44 6 3) g Tt_trie` and `Tt_prof_ok : ProfOK (clsCount 44 6 3) g Tt_prof`.

## 4. The certified subtree at piece `(6, 3)` (`clsCount 44 6 3 = (6, 3, 35)`, shift `g = 41/625`)

Nodes: the multisets of the block `|λ| ≤ 6` (`blockMultisets 6`, 22 with the root: up to six factors,
degree 12) and the multisets of `B₂₁` with at most two factors (`shortMultisets 2`, 66 with the root:
degrees up to 40) — 77 nodes besides the root.

- **Stored nodes** (22): nodes with children in the subtree; their canonical states are certificate
  data, reached from the parent by one certified step (chunks and a linear merge when the step
  generates more than 900 entries).
- **Leaves** (55): only the moment profile is certified, from the stored parent (chunked when large),
  so their states are never stored.
- **Profiles**: 78 (with the root), indexed by `(A, B)`; `Tt_prof_ok`.
- **Coverage (kernel)**: `Tt_covers` — every multiset of `blockMultisets 6` and of `shortMultisets 2`
  has a certified profile; `block6_shape`, `short2_shape` — the two sets are sorted and prefix-closed
  (22 and 66 elements); `b21_counts` — 139 partitions, 139 kept-part lists. The kept-part lists are
  certified once (`b21Kept_eq`, `SymTrieKept.lean`) and reused through `shortMultisetsOf`.

## 5. Tables (demonstrations)

Each kernel table check is its own module (`SymTrieTab*.lean`, importing only the profile data); a
table whose single check would exceed 4 GB is split into parts by the size of the profiles it looks
up, each part certified by `profTable … = Tᵢ`, and the parts are merged by `decide +kernel` checks of
`mergeAll mkeyCmp 64` in a tree of 4-way merges, composed by `table_parts_merge`. The statements carry
one merged table.

- `genPieceP222_6_3_trie_expansion`: V2ℓ's degree-12 statement from the trie profiles (`rfl`).
- `block6_6_3_expansion`: `Σ_{i,j} cᵢ cⱼ J_T[P_{λᵢ}, P_{λⱼ}]` on piece `(6, 3)` for the seven
  generators `P_λ`, `|λ| ≤ 6`, `c = 1, …, 7` — 49 pairs, one table of 231 keys (4 parts, one merge).
- `onepart_6_3_expansion`: `Σ_{i,j} J_T[P_{2i}, P_{2j}]`, `1 ≤ i, j ≤ 10` — 100 pairs, 901 keys,
  factor degrees up to 40 (23 parts; merges 23 → 6 → 2 → 1).
- `genPieceP20_6_3_trie_expansion`: piece `(6, 3)` of `J_T[P_20, P_20]` (degree 40), 523 moments.

## 6. Measurements

All modules were built one `lean` process at a time in the order of `specs/checks/sym_trie_v2m_build.sh`
(8 GB, 2-core container; peak = maximum resident memory of `lake` + `lean`, of which about 3.0–3.4 GB is
memory-mapped Mathlib and project `.olean` files; anon = heap).

| progress measure | value |
|---|---|
| trie nodes certified at piece `(6, 3)` | 77 (+ root): 22 stored, 55 profile-only leaves |
| maximum factor length / degree | 6 factors (`[2]^6`, degree 12); degree 40 (`[20, 20]`, two factors) |
| distinct certified moment profiles | 78 (`Tt_prof`) |
| generated entries checked by the kernel (steps and leaf profiles) | 79 553 |
| coefficient tables | 4 (231, 231, 901 and 523 keys) |

| modules | count | time | peak | anon |
|---|---|---|---|---|
| `BGP212/SymTrie`, `Solution/SymTrie` | 2 | 3.4 s, 3.8 s | 2.94, 3.10 GB | 0.38, 0.40 GB |
| profile data (`SymTrieProfData0–4`, aggregate) | 6 | 3.5–13.5 s | 2.98–3.38 GB | 0.38–0.82 GB |
| node states (`D_*`) | 22 | 3.2–6.6 s | 2.93–3.05 GB | 0.36–0.49 GB |
| steps to stored nodes (`S_*`; chunk steps `S_*_C*`) | 22 + 9 | 3.4–10.1 s | 3.09–3.75 GB | 0.37–1.04 GB |
| stored-node profiles (`P_*`) | 22 | 3.4–6.5 s | 3.11–3.20 GB | 0.40–0.48 GB |
| leaf profiles (`G_*`; chunks `L_*_C*`; merges `L_*`) | 22 + 85 + 26 | 3.6–9.7 s | 3.12–3.91 GB | 0.42–1.21 GB |
| assembly (`SymTrieNodes`) | 1 | 3.8 s | 3.22 GB | 0.40 GB |
| kept-part lists (`SymTrieKept`), Demo1, Demo2 | 3 | 9.0, 4.6, 5.2 s | 3.90, 3.10, 3.23 GB | 1.34, 0.54, 0.65 GB |
| table parts (`SymTrieTab*_R*`, `Tab3`, `Tab6`) | 29 | 4.8–11.0 s | 3.11–3.92 GB | 0.55–1.34 GB |
| table merges (`SymTrieTab*_M*`, `Tab4`, `Tab5`) | 10 | 5.5–12.4 s | 3.16–3.79 GB | 0.58–1.17 GB |
| Demo3–6, `SymTrieSuite`, `Challenge/SymTrie` | 6 | 5.0–12.6 s | 3.24–3.49 GB | 0.41–0.60 GB |
| **all V2m modules** | **265** | **1 691 s (28.2 min)** | **≤ 3.92 GB** | **≤ 1.34 GB** |

Comparator (`Comparator/sym_trie_v2m.json`, 20 statements): accepted by the Lean default kernel,
745 s, peak 3.36 GB. Engineering notes: the first single-module versions of the tables exceeded the
limit (one-part table: out of memory at 8 GB; block table 4.03 GB; all profile data in one module
4.31 GB; the degree-40 table hit the default `maxRecDepth` of its 523-entry literal), and the
enumeration of the multisets with at most two factors reached 4.07 GB when it recomputed
`b21Kept`; certifying `b21Kept` once, splitting data and tables, and merging table parts in a tree
brought every module under 4 GB. The kernel count of all 2 361 multisets (`b21Multisets`) exceeds
8 GB and stays exploratory.

## 7. Remaining (exploratory, not certified)

Exploratory counts (V2ℓ, `specs/checks/sym_staged_v2l_counts.py`): 2 361 multisets, a 2 360-step
trie per piece, longest 20 factors (degree 40). V2m certifies 77 of the 2 360 nodes of piece `(6, 3)`.
State counts grow with the degrees of the factors (each `P̂_q` has `q + 1` terms): at piece `(6, 3)`,
the 150 three-factor nodes generate 1 309 843 entries in all (largest 29 635, up to 9 878 states),
against 46 035 for the 55 two-factor nodes; the block `|λ| ≤ 8` (52 multisets, degree 16) generates
447 116, with 11 807 states at `[2]^8`. At the measured rate (about 900 generated entries per
certificate module of 4–10 s and at most about 1.1 GB of heap) the three-factor layer is about 1 500
modules. Next steps: (1) the three-factor layer and the block `|λ| ≤ 8`; (2) moment profiles
computed directly from a parent without canonicalizing the last step; (3) the same subtree for the
other pieces; (4) the moments, through V2j §6's `boxVal` collapse.
