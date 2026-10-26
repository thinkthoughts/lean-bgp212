# V2o: minimal marked-profile certificates for one-level trie extensions (specification)

Status: definitions, general proofs (sufficiency, minimality, degree gap), and one-level certificates
for the three-factor nodes of total degree ≤ 26 at Table 3, piece `(6, 3)`, on branch `v2o` from V2n
(`b5b1e20`; the same Lean and Comparator content as `acab402` on `v2n-main`). V2n's independent
verification is reported separately; nothing here assumes it. V2i–V2n definitions, statements and
certificates are unchanged; README, THEOREMS.md and the manuscript are unchanged.

## 1. The question and the answer

V2n showed that the moment profile is insufficient for one factor and that the marked profile of
order ≤ 1 suffices. **What does one factor actually read from those marks?**

For a leaf, V2n's transition at order 0 reads the profile `P(A, B)` and, for each mark `(c, e)` at
`(A, B)` with weight `v`, the terms `φ(c)_a · ((e + a)!/e! − a!)`. Since
`(e + a)!/e! − a! = a! (C(e + a, a) − 1)`, a factor of degree ≤ d reads the marks only through the
**binomial read summary**

  `δ_a(A, B, c) = Σ_{marks (c, e) at (A, B)} v · (C(e + a, a) − 1)`,   `1 ≤ a ≤ d`.

The class counts `β₀ = Σ v` enter only through these differences (`C(e + a, a) − 1 = β_a − β₀` per
mark), never on their own; the individual exponents enter only through the binomial moments.

**Proved in Lean (for arbitrary class sizes, factors, combinations and moment oracles):**

| theorem | statement |
|---|---|
| **`readStep_sufficient`** | for every factor `φ` of degree ≤ `d`: `symFinal M (symStepAll n φ L) = Σ_{readStep n φ (abProfile L) (readSummary d (markProfile 1 L))} c · M` |
| `monomial_reads` | the monomial factor `x^a` in class `c` reads exactly the profile (weight `n_c a!`) and the summary coordinates `(·, ·, c, a)` (weight `a!`) at the keys shifted by `a` in class `c` |
| `monomial_reads_at` | at the indicator oracle of one shifted key, the child under `x^a` has the value `a! (n_c P(A, B) + δ_a(A, B, c))` |
| **`summary_determined`** (minimality) | over a field of characteristic 0: for combinations with the same profile, if the children under all monomial factors of degree ≤ `d` agree for every oracle, every summary coordinate `δ_a(A, B, c)`, `1 ≤ a ≤ d`, agrees |
| **`summary_degree_gap`** | V2n's two states `{(0, 2)}` (1) and `{(0, 1), (0, 1)}` (2) have equal profiles and equal summaries of degree 1, so their children agree under **every** factor of degree ≤ 1 for all class sizes and oracles; their summaries of degree 2 differ, and their children under `P̂₂` at Table 3 differ |

Together: **`(P, δ₁, …, δ_d)` is exactly the information that factors of degree ≤ d read** —
sufficient by `readStep_sufficient`, necessary coordinate by coordinate by `summary_determined`, and
the required degree cannot be lowered (`summary_degree_gap`). Counterexamples identifying necessary
information: the profile alone and the profile with class counts are insufficient (V2n's
`profile_insufficient`, `classProfile_insufficient`); the degree-1 summary is insufficient for degree-2
factors (`summary_degree_gap`).

**Minimal size (exploratory, `specs/checks/sym_read_v2o_cost.py`).** Per group `(A, B, c)` with
exponent set `E` (all `e ≥ 1`), the functionals `e ↦ C(e + a, a) − 1`, `1 ≤ a ≤ d`, span the
polynomials of degree ≤ d vanishing at 0; restricted to `E` their rank is `min(|E|, d)`. Order-1 marks
store `|E|` numbers, the summary `d`: the minimum is the smaller. On the three-factor layer of piece
`(6, 3)` (54 parents, `d` = the largest child degree): 87.5 % of the 21 024 groups have `|E| = 1`;

| representation of the parents' extra information | stored numbers |
|---|---|
| order-1 marks (V2n) | 38 253 |
| binomial summary (degree `d`) | 128 800 |
| minimum `Σ min(|E|, d)` | 30 495 |

so marks are within 25 % of the minimum here and the summary does not pay; with the cost of computing
it, the summary route (880 546 kernel operations for all 150 leaves) equals the marks route (885 781).
The summary is the better representation where exponent sets are larger than the factor degrees
(many small parts and low-degree children).

## 2. Definitions (`BGP212/SymRead.lean`)

`ReadKey` (`ℕ × ℕ × Fin 3 × ℕ`), `readCmp`, `readTerms`, `readSummary d P` (the summary of an
order-≤ 1 marked profile), `pull0`, `pull1`, `readStep n φ R0 Rd` (the child's profile from a profile
and a summary), `degLe d φ`, `monoF c a` (the monomial `x^a` in class `c`), `profAt`, `readAt`.

## 3. Certificate architecture (one level)

- **Internal nodes** (the two-factor parents) use certified canonical states: 5 are V2m's stored
  nodes, 30 are staged here from V2m's stored one-factor nodes (`stepCert_runs`, chunks, one merge,
  `chainCert_snoc`).
- **Parents' marks**: the order-≤ 1 marked profile of each parent is read from its certified states
  (`markOK_of_tree`), each chunk result certified as key-range slices and merged per range
  (`markOK_congr`, V2n).
- **Leaves** (three-factor multisets): one direct order-0 transition from the parent's marks
  (`markOK_step_tree`, `profCert_of_markOK`), chunked by emitted entries and merged; **no state of a
  leaf is formed** (the Python generator forms them only to cross-check every profile).
- **Literal factors**: each check uses `To_f_q`, the coefficients of `P̂_q` as literal rationals, and
  the bridge `To_fe_q : stepFactor g q = To_f_q` (proved once per `q`). Measured on one leaf check of
  1 091 emitted entries at `q = 10`: **215.4 s with `stepFactor g 10`, 7.4 s with the literal**
  (same memory, 0.83 GB heap): the kernel otherwise re-expands `(x + g)^q` for every entry.
- `To_prof_ok : ProfOK (clsCount 44 6 3) g To_prof` and `To_all_ok` (with V2m's profiles) feed
  V2m's `trieProf_table_eq`.

## 4. Coverage at piece `(6, 3)` (`clsCount 44 6 3 = (6, 3, 35)`, `g = 41/625`)

- **66 of the 150 three-factor multisets of `B₂₁`: all of total degree ≤ 26** (`To_covers`,
  `three_counts`: 150 three-factor multisets, 66 of degree ≤ 26), under 35 two-factor parents.
- Agreement: the 5 of them that V2m certified by staged states and the 8 that V2n certified by
  multi-level transitions get identical profiles (`To_same_v2m_*`, `To_same_v2n_*`, kernel).
- `profile_10_8_8_direct`: the profile of `[10, 8, 8]` (degree 26).
- Table: piece `(6, 3)` of `J_T[P_10, P_(8,8)]` (574 moments) from the one-level profile of
  `[10, 8, 8]` and V2m's profiles (`genPieceP10_P88_6_3_expansion`). Tables are coefficient
  representations; the moments `pieceMn` are evaluated separately.

## 5. Cost comparison for the same 66 leaves (exact counts from the generator)

| route | internal nodes | leaves | child states formed |
|---|---|---|---|
| V2m staged | 14 822 generated (30 staged parents) | 242 920 generated | 106 661 |
| V2n multi-level (order-2 marks of the one-factor nodes) | 43 980 emitted | 159 340 emitted | 0 |
| **V2o one level** | 14 822 generated + 25 006 (state, tuple) reads | **159 340 emitted** | **0** |

V2o's kernel work for the layer is 199 168 entries against V2m's 257 742 (−23 %), with no leaf state,
and each check runs on literal factors. The leaf work is dominated by the parents' profiles: a leaf
of degree `q` costs about `|P|·(2q + 2) + Σ_marks q` entries, the new-part openings of every profile
entry in two classes plus one absorption per mark.

## 6. Measurements

All 632 V2o modules were built one `lean` process at a time from a clean state, in the order of
`specs/checks/sym_read_v2o_build.sh` (8 GB, 2-core container; V2m's certificates and V2n's
`SymProfileSplit`/`SymProfileProfData` built; peak = maximum resident memory of `lake` + `lean`,
about 3.0–3.4 GB of which is memory-mapped `.olean` data; anon = heap).

| modules | count | time | peak | anon |
|---|---|---|---|---|
| `BGP212/SymRead`, `Solution/SymRead`, `SymReadFactors` | 3 | 4.7–7.6 s | 2.94–3.15 GB | 0.38–0.46 GB |
| profile data `SymReadProfData0–3`, aggregate | 5 | 4.6–22.7 s | 3.00–3.44 GB | 0.39–0.89 GB |
| staged parents: step chunks `T_*_*`, states `D_*`, chains `T_*` | 55 + 30 + 30 | 4.1–8.7 s | 2.95–3.54 GB | 0.39–0.84 GB |
| parents' marks `Q_*`, data `P_*_d*`/`P_*`, range merges `M_*`, `A_*` (35) | 42 + 70 + 35 + 35 | 3.5–14.3 s | 2.93–3.74 GB | 0.36–1.17 GB |
| leaf steps `S_*` | 145 | 4.0–10.3 s | 2.95–3.67 GB | 0.39–1.11 GB |
| leaf merges `R_*`, profile checks `F_*`, `A_*` (66) | 44 + 66 + 66 | 3.6–6.3 s | 2.97–3.21 GB | 0.37–0.54 GB |
| certificate modules in all | **618** | **3 634 s** | **≤ 3.74 GB** | **≤ 1.17 GB** |
| `SymReadNodes`, Demo1, Tab2, Demo2, Suite, Challenge | 6 | 6.0–9.4 s | 3.01–3.68 GB | 0.45–0.78 GB |
| **all V2o modules** | **632** | **3 772 s (63 min)** | **≤ 3.74 GB** | **≤ 1.17 GB** |

Every module, including the compositions that import all certificates, is below 4 GB resident.

Comparator (`Comparator/sym_read_v2o.json`, 8 statements): accepted by the Lean default kernel, 1 621 s,
peak 3.68 GB (1.61 GB heap).

Engineering notes: the leaf profile data in one module reached 4.65 GB (degree-26 profiles carry
large rationals) and is split into parts of at most 250 KB; a demonstration importing the
certificates for a coverage check reached 4.01 GB and the coverage check now imports only the data.

## 7. Remaining

The other 84 three-factor nodes of piece `(6, 3)` (degree 28–40): 726 441 leaf entries by this
route (exploratory), about 4.6 times the work certified here, so roughly 1 000 more modules at the
measured rates, under the same 4 GB bound per module. With V2m, V2n and V2o, 157 of the 2 361
multisets of `B₂₁` have certified profiles at this piece; the other 2 204 are these 84 and 2 120 with
four or more factors (where internal nodes need their own states or marks). Beyond that: the other pieces,
the moment values (V2j §6), the 846 × 846 matrices, `P⋆` and the variational certificate.

## 8. Reproduction

On the V2o commit (patch applied on V2n `acab402`), with Lean `v4.34.0-rc2` and Mathlib `85e3a25`,
one module at a time:

```text
bash specs/checks/sym_trie_v2m_build.sh     # V2m's certificates (the parents' states)
lake build Solution.SymProfileSplit Solution.SymProfileProfData   # V2n pieces V2o uses
bash specs/checks/sym_read_v2o_build.sh     # V2o: 628 modules, then the suite and the challenge
lake env lean Solution/SymRead.lean         # the general theorems; prints the axioms
./verify.sh                                 # all Comparator configs, Comparator/sym_read_v2o.json included
```

Generators and checks (Python 3):

```text
mkdir -p /tmp/v2o && python3 -I specs/checks/sym_read_v2o_demo.py /tmp/v2o
for f in $(cd /tmp/v2o && find Solution specs -type f); do cmp "/tmp/v2o/$f" "$f"; done
python3 -I specs/checks/sym_read_v2o_cost.py
python3 -I specs/checks/sym_read_v2o_controls.py /tmp/v2o_ctl
for f in /tmp/v2o_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

Expected: 629 generated files reproduced; `neg_*` rejected, `pos_*` accepted. Statement-level control:
in `Challenge/SymRead.lean`, state `readStep_sufficient` with `readSummary (d - 1)` (one degree too
few) and run Comparator with a configuration naming only `BGP212.Challenge.readStep_sufficient`.
