# V2n: direct certified moment-profile transitions (specification)

Status: definitions, general proofs, the obstruction, and a kernel-certified extension of V2m's subtree to
the block `|λ| ≤ 8` at Table 3, piece `(6, 3)`, on branch `v2n` from V2m (`3e6ae72`; the same Lean and
Comparator content as `a6f3220` on `v2m-main`). V2m's independent verification is reported separately;
nothing here assumes it. V2i–V2m definitions, statements and certificates are unchanged.

## 1. The question and the answer

V2ℓ's moment profile of a combination `L` of states keeps, for each pair `(A, B)` of rough and smooth
degrees, only `Σ κ ∏ e!`. Can the profile of a child (`L` multiplied by a shifted power sum `P̂_q`) be
computed from the profile of the parent?

**No (Lean-checked).** Multiplying by a factor sends a part `(c, e)` to `(c, e + a)`, which multiplies
`∏ e!` by `(e + a)!/e!`, a weight depending on the individual exponent `e`; a new part `(c, a)` carries
the weight `n_c − ℓ_c`, depending on the number of parts of class `c`. Both are forgotten by the
profile.

- `profile_insufficient`: there is no map from parent profiles to child values. The states `{(0, 2)}`
  (coefficient 1) and `{(0, 1), (0, 1)}` (coefficient 2) have equal profiles, and their children under
  `P̂₂` at piece `(6, 3)` take the values 44 and 40 at the oracle `M(A, B) = [A = 4 ∧ B = 0]`.
- `classProfile_insufficient`: adding the class counts (`Σ κ ∏ e! · ℓ_c` by `(A, B, c)`) is still not
  enough: `{(0, 3), (0, 1)}` (2) and `{(0, 2), (0, 2)}` (3) agree on both and their children differ.

**A sufficient augmented state: marked profiles.** For a state `k` let `dtup t k` be the ordered
`t`-tuples of distinct parts (positions) of `k`. The marked profile of order `≤ T` is

  `markProfile T L = Σ_{(k, κ) ∈ L} Σ_{t ≤ T} Σ_{u ∈ dtup t k} ((A k, B k, u), κ ∏ e!)`,

merged by key; order 0 is the moment profile. **One factor maps the marked profile of order `≤ T + 1`
of the parent to the marked profile of order `≤ T` of the child, entry by entry** (`markStep`,
`markTerms`), without forming any state of the child:

- the constant terms keep the key;
- the first mark `(c, e)` absorbs `a` (`φ(c)_a ≠ 0`): released with weight `(e + a)!/e! − a!`, or kept
  as `(c, e + a)` (weight `(e + a)!/e!`) or `(c, a)` (weight `−a!`) at any position;
- a new part `(c, a)` opens with weight `(n_c − #marks of class c) · a!`, unmarked or marked.

The `− a!` terms and the mark count correct `n_c − ℓ_c`: the unmarked parts of class `c` are exactly
the next order of marks. Each step consumes one order of marks, so a node with a marked profile of
order `T` serves every descendant up to `T` levels below it, and a parent's marked profile of order
`≤ 1` is exactly the information needed for its children's profiles (`profCert_of_markStep`).
Order 1 is minimal in the sense of the counterexamples: order 0 (the profile) and order 0 with class
counts are insufficient, and the states of the first counterexample are separated already at order 1
(`pos_marks_separate`).

## 2. Definitions (`BGP212/SymProfile.lean`)

`MarkKey` (`ℕ × ℕ × List SPart`), `dtup`, `tupsLe`, `insAt`, `markCmp`, `nat3Cmp`, `markProfile`,
`constSum`, `markTerms`, `markStep`, `MarkOK n g Q T P` (`P` has, against every test function on marked
keys, the value of `markProfile T L` for some `L` reached from the empty state by certified steps for
the factors `P̂_q`, `q ∈ Q`), `classProfile`, `markToProf`, `decMEntry`, `decMark`.

## 3. Theorems (`Solution/SymProfile.lean`, all proved, for arbitrary class sizes, shifts, factors, orders and test functions)

| theorem | statement |
|---|---|
| **`markProfile_step`** | `Σ_{markProfile T (symStepAll n φ L)} c · F = Σ_{markStep n φ T (markProfile (T + 1) L)} c · F` |
| `markOK_of_chain`, `markOK_of_chunks`, `markOK_of_tree` | marked profiles of certified states (in chunks, merged once or in a tree) |
| `markOK_of_trie` | every node of a V2m `TrieOK` trie has marked profiles of every order |
| `markOK_step`, `markOK_step_chunks`, `markOK_step_tree` | the direct transition certifies the child's marked profile (parent in chunks, results merged in a tree, parent of higher order restricted) |
| `markOK_mono` | lower orders by filtering |
| `profCert_of_markOK`, `profCert_of_markStep` | to V2m's `ProfCert` (order 0; a child's profile from a parent's order-1 marked profile) |
| `markOK_congr` (`Solution/SymProfileSplit.lean`) | a certified marked profile can be replaced by any list of the same value against every test function |
| `profOK_append` | V2m's `ProfOK` lists concatenate, so V2n's profiles join V2m's in `trieProf_table_eq` |
| `profile_insufficient`, `classProfile_insufficient` | the obstruction (§1) |

The proof works on multisets: the marked value of a state is a sum over tuples of distinct elements
(`dtupM`); a new part splits the tuples (`dtupM_cons_sum`), and the parts outside a tuple are counted
by the next order (`dtupM_compl`), which is where `n_c − ℓ_c` becomes `n_c − #marks` minus one more
order of marks.

## 4. The certified extension at piece `(6, 3)` (`clsCount 44 6 3 = (6, 3, 35)`, shift `g = 41/625`)

The block `|λ| ≤ 8` (`blockMultisets 8`) has 52 factor multisets; 27 have V2m profiles, **25 are new**
(degree up to 16, up to 8 factors). Every prefix of a new multiset outside V2m's stored nodes is a
**direct node** (34: 25 new multisets and 9 prefixes that V2m certified by staged states). Each direct
node gets a marked profile of order = its height in the direct subtree (orders 0–3) from its parent's
by `markStep`; **no state of a direct node is formed in any certificate**. The parents at the top are 8
of V2m's stored nodes (*sources*): their already-certified states give marked profiles of order 3–4
(`markOK_of_tree`, chunk by chunk). Leaves (13) certify only their moment profile; internal nodes (21)
store marked profiles as data.

- `Tn_prof_ok : ProfOK (clsCount 44 6 3) g Tn_prof` (34 profiles) and
  `Tn_all_ok : ProfOK … (Tn_prof ++ Tt_prof)` (with V2m's 78).
- `Tn_same_as_v2m`: the 9 direct nodes that V2m also certified by staged states get exactly V2m's
  profiles (kernel).
- `Tn_covers`: every multiset of `blockMultisets 8` has a certified profile; `block8_shape`: 52, sorted
  and prefix-closed.
- `profile_2x8_direct`: the moment profile of `[2]^8` (degree 16; 11 807 states, never formed).
- Tables (coefficient representations; the moments `pieceMn` are evaluated separately):
  `genPieceP2222_6_3_direct_expansion` (piece `(6, 3)` of `J_T[P_(2,2,2,2), P_(2,2,2,2)]`, degree 16,
  489 moments) and `block8_6_3_expansion` (`Σ cᵢ cⱼ J_T[P_{λᵢ}, P_{λⱼ}]` over the twelve generators with
  `|λ| ≤ 8`, `c = 1, …, 12`: 144 pairs in 38 certified parts merged in a tree, 489 keys).

Certificate modules (`Solution/SymProfileCert/`, 674): `Q_*` marked profiles of slices of the 8 sources'
certified states (59), `S_*` direct-step chunks (333, each at most 1 100 emitted entries), `P_*_d*` marked-
profile data parts (46) and `P_*` their lists (29), `M_*` key-range merges of internal nodes (117), `R_*`
and `F_*` group and final merges of leaves (14 and 13), `A_*` assembled `MarkOK`/`ProfCert` (42), `G_*`
order-0 profiles of internal nodes (21).

**Merging by key ranges.** A merge of all chunk results of a node with thousands of marked entries
exceeds 4 GB in one kernel check. Each chunk result is therefore certified as the concatenation of its
slices on ranges of the rank `1024 A + B` (results are sorted by key, so the slices are contiguous); the
slices of one range are merged in one check (`M_*`, at most 1 200 input entries); the node's marked
profile is the concatenation of the range merges, certified by `markOK_congr` from the value of the
chunk results, the equality of values being commutativity of the sum (`linear_combination` over the
slices' values). No merge of all results of a node is evaluated.

## 5. Cost comparison with V2m's staged route (same 34 nodes)

| | direct (V2n) | staged (V2m route) |
|---|---|---|
| entries emitted / generated by kernel checks for the 34 nodes | 290 252 | 437 831 |
| data stored for the 34 nodes | 38 402 marked entries | 99 989 states |
| leaves (13): emitted vs generated | 30 137 | 314 670 |
| order-1 nodes (11) | 103 777 | 95 468 |
| order-2 nodes (9) | 155 780 | 27 552 |
| sources (8): marked entries vs states | 17 470 | 2 308 |

Marks compress when a node has many small parts (`[2]^8`: 11 807 states, 145 marked entries of order 0;
`[2]^7`: 5 042 states, 1 268 of order 1) and expand at high order (`[2]^6`: 2 052 states, 4 690 marked
entries of order 2). The efficient use is therefore **one level**: stored states (V2m) for internal
nodes and a direct order-0 transition from each stored parent's order-1 marks for the leaves.
Exploratory projection for the three-factor layer (150 nodes; `specs/checks/sym_profile_v2n_projection.py`):
1 011 793 emitted entries (order-1 marks for the 54 two-factor parents, 126 012; leaves, 885 781) against
1 309 843 staged — a 23 % reduction, smaller than in the block because those multisets have few, large
parts.

## 6. Measurements

All 737 V2n modules were built one `lean` process at a time from a clean state, in the order of
`specs/checks/sym_profile_v2n_build.sh` (8 GB, 2-core container; V2m's certificates already built; peak =
maximum resident memory of `lake` + `lean`, of which about 3.0–3.4 GB is memory-mapped `.olean` files
shared between processes; anon = heap).

| progress measure | value |
|---|---|
| new multisets with certified profiles at piece `(6, 3)` | 25 (block `|λ| ≤ 8`; with V2m, all 52 of the block) |
| direct nodes (no state formed) | 34: 13 leaves, 21 internal (marked orders 1–3) |
| longest multiset / degree | 8 factors (`[2]^8`), degree 16 |
| distinct certified profiles | 34 direct + 78 V2m = 112 (`Tn_all`) |
| entries emitted by direct-step checks | 290 252 (each check at most 1 100) |
| (state, tuple) pairs read from V2m's states at the 8 sources | 48 309 |

| modules | count | time | peak | anon |
|---|---|---|---|---|
| `BGP212/SymProfile`, `Solution/SymProfile`, `Solution/SymProfileSplit` | 3 | 5.5–11.7 s | 2.94–3.21 GB | 0.38–0.50 GB |
| profile data `SymProfileProfData` | 1 | 23.4 s | 3.40 GB | 0.83 GB |
| source marked profiles `Q_*` | 59 | 4.4–16.6 s | 2.95–3.75 GB | 0.38–1.18 GB |
| direct steps `S_*` | 333 | 4.0–14.4 s | 3.10–3.92 GB | 0.38–1.21 GB |
| data `P_*_d*`, `P_*` | 46 + 29 | 3.7–15.8 s | 2.93–3.29 GB | 0.36–0.73 GB |
| range merges `M_*` | 117 | 4.1–7.5 s | 3.10–3.45 GB | 0.39–0.73 GB |
| leaf merges `R_*`, `F_*` | 14 + 13 | 4.4–6.0 s | 3.13–3.17 GB | 0.41–0.46 GB |
| assemblies `A_*`, order-0 profiles `G_*` | 42 + 21 | 3.8–7.5 s | 3.10–3.58 GB | 0.37–0.72 GB |
| certificate modules in all | **674** | **5 820 s** | **≤ 3.92 GB** | **≤ 1.21 GB** |
| tables `SymProfileTab*` | 53 | 6.1–14.7 s | 3.11–3.98 GB | 0.55–1.40 GB |
| `SymProfileNodes`, Demo1, Demo2, Challenge | 4 | 5.7–11.6 s | 3.09–3.93 GB | 0.50–0.55 GB |
| Demo4, `SymProfileSuite` | 2 | 16.1, 12.8 s | 4.10, 4.05 GB | 0.63, 0.58 GB |
| **all V2n modules** | **737** | **6 431 s (107 min)** | 735 modules ≤ 3.98 GB | **≤ 1.40 GB** |

The two modules above 4 GB resident are compositions that import every certificate (the 1.6 GB of
`SymProfileCert` `.olean` files plus V2m's); their heap is at most 0.63 GB and the remainder is
read-only memory-mapped data, which the operating system can page out. They are expected to build on
the 3.8 GiB VPS; that is part of the independent verification.

Comparator (`Comparator/sym_profile_v2n.json`, 19 statements): accepted by the Lean default kernel,
3 176 s, peak 4.05 GB (1.68 GB heap).

Comparison with V2m's staged route: §5. V2m certified 77 nodes with 265 modules in 1 691 s; V2n
certifies 34 nodes (25 new multisets, of degree up to 16 and up to 8 factors) with 737 modules in 6 431 s.
The staged route for the same 34 nodes would generate 437 831 entries and store 99 989 states; at V2m's
measured rate (about 900 generated entries per certificate module) that is about 490 step and profile
checks plus their merges. The direct route stores 38 402 marked entries for the 34 nodes and emits
290 252, but its sources carry marks of order 3–4 (17 470 marked entries against 2 308 states), which
is why the module count is higher here: the orders were chosen to demonstrate multi-level transitions
(up to three levels without states), not to minimize cost. The measured per-order costs (§5) favour
order ≤ 1: one level of direct transitions below stored states.

Engineering notes: one-piece merges of the largest marked profiles (6 486 entries) reached 4.29 GB, and
range merges that filtered all chunk results 4.4 GB; slicing each chunk result by key range and merging
one range per check (`markOK_congr`) lowered the merges to at most 3.45 GB. Data modules hold at most
2 000 marked entries (one module of 6 486 reached 4.08 GB). Tables import only the profile data
(`SymProfileProfData`), not the certificates (importing the certificates added about 0.9 GB of mapped
files).

## 7. Remaining

The other 2 258 multisets of `B₂₁` at piece `(6, 3)` (2 361 minus the 103 with certified profiles: V2m's
78 with the root and V2n's 25 new), the other pieces, the
moment values (V2j §6), the 846 × 846 matrices, `P⋆` and the variational certificate. A sharper
transition for leaves (marks restricted to what the next factor reads: the first mark and the class
counts of the remaining marks) is the natural next refinement.

## 8. Reproduction

On the V2n commit (patch applied on V2m `a6f3220`), with Lean `v4.34.0-rc2` and Mathlib `85e3a25`
(`lake exe cache get`), on a machine with about 4 GB of memory, build one module at a time:

```text
bash specs/checks/sym_trie_v2m_build.sh        # V2m's certificates (V2n starts from them)
bash specs/checks/sym_profile_v2n_build.sh     # V2n: 737 modules, then the suite and the challenge
lake env lean Solution/SymProfile.lean         # the general theorems; prints the axioms
```

Comparator (`Comparator/sym_profile_v2n.json`, 19 statements), as for the other pairs:

```text
COMPARATOR_LANDRUN=... COMPARATOR_LEAN4EXPORT=... lake env "$COMPARATOR_BIN" Comparator/sym_profile_v2n.json
./verify.sh                                     # builds the project and runs every config, V2n included
```

Generators and checks (Python 3, standard library):

```text
mkdir -p /tmp/v2n && python3 -I specs/checks/sym_profile_v2n_demo.py /tmp/v2n
for f in $(cd /tmp/v2n && find Solution specs -type f); do cmp "/tmp/v2n/$f" "$f"; done
python3 -I specs/checks/sym_profile_v2n_model.py
python3 -I specs/checks/sym_profile_v2n_projection.py
python3 -I specs/checks/sym_profile_v2n_controls.py /tmp/v2n_ctl
for f in /tmp/v2n_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

Expected: the generator reproduces all 733 generated files; `neg_*` rejected, `pos_*` accepted.
The statement-level control: change `markProfile_step` in `Challenge/SymProfile.lean` (right-hand side doubled) and run
Comparator with a configuration naming only `BGP212.Challenge.markProfile_step`.
