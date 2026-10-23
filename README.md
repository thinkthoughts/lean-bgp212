# BGP212

**[translatepi.ai](https://translatepi.ai/paper/)** · The reading point. PiπΠ.

Independent mathematical specifications, exact certificates, and Lean 4 verification.

This repository develops formal proofs for the exact and combinatorial parts of Axiom Math's *A New Bound for Small Gaps Between Primes* (H₁ ≤ 212, preliminary draft of September 3, 2026).

## Mathematical theorem inventory

**[Exact Rational Integration over Constrained Simplices — Theorem Inventory](specs/paper/THEOREMS.md)**

The theorem inventory documents exact simplex moments, the 846-dimensional
polynomial space, general constrained integrals, rational Gram representations,
marginal-fibre identities, and successive V2f–V2j certificates. Each result
is linked to its Lean declarations, hypotheses, and verification scope.

**Verification milestones:** V2i's complete VPS regression accepted **21/21
Comparator configurations** (including its 33-statement suite; `verify.sh`
exited with status 0). V2j's **24-statement shared-moment aggregation suite**
was separately accepted on both Linux VPS and macOS, at source commit
[`a9a8af9`](https://github.com/thinkthoughts/lean-bgp212/commit/a9a8af9).
The macOS check used a development replacement for Linux `landrun`; the VPS
used Linux isolation. These independent V2j suite acceptances do **not**
constitute a separately recorded complete 22-suite regression.

**Next development:** V2k's symmetric-function evaluator and its general
equality with V2i have been reported in a development container; independent
Mac/VPS reproduction and integration into `main` are pending.

The unconditional H₁ ≤ 212 argument remains outside the completed formalization.

## Scope

This repository verifies the exact and combinatorial layer of the H₁ ≤ 212 deduction.
The analytic estimates (Type I/II/III, Bombieri–Vinogradov, the Harman decomposition)
and the variational certificate stay imported as hypotheses, matching the boundary of
Axiom's own Lean certificate. The priorities are kernel verification and exact
theorem-to-source correspondence.

## Two tracks

- **Track A — specification audit.** `specs/A0_parameters.yaml` fixes Table 3 as the
  specification of record and records three source inconsistencies verbatim (SI-1, SI-2, SI-3)
  plus one editorial note (ED-1). Lean statements are formalized against A0.
- **Track B — multi-shift GDT.** `specs/B0_multishift_gdt.yaml` extends the General
  Divisor Theorem (github.com/thinkthoughts/general-divisor-theorem, v1.0.0) from one
  shift to a tuple H, with absolute density (1/m)·∏_{p | R}(1 − ν_p(H)/p).

The tracks join at Lemma 12.1: admissibility of H₄₅ equals positivity of every local factor.

## Formal Challenge

The first Challenge/Solution pair is Lemma 12.1 (`Challenge/Lemma12_1.lean`,
`Solution/Lemma12_1.lean`), in core Lean with no Mathlib dependency. Five statements:

1. `h45_card` — 45 distinct elements
2. `h45_diameter` — minimum 0, maximum 212
3. `h45_omitted_table` — the source's listed omitted classes for p ≤ 43
4. `h45_admissible` — an omitted class modulo every prime
5. `lemma_12_1` — the packaged lemma

The second pair is the Table 3 parameter layer and Appendix B (`Challenge/AppendixB.lean`,
`Solution/AppendixB.lean`, data in `BGP212/Params.lean` and `BGP212/Ledger.lean`). Its
central statement, `table6_derivation`, equates every printed left and right entry of
Table 6 with its formula in the Table 3 parameters. That check found a third source
inconsistency (SI-3, Proposition 7.8 (II) versus Table 6 row 14), recorded in
`specs/A0_parameters.yaml`.

The third pair is A2, the combinatorial layer (`Challenge/A2Combinatorial.lean`,
`Solution/A2Combinatorial.lean`): Lemma 4.2, the §7.2 smooth-insertion mechanism,
the factor-extraction Lemmas 7.5–7.7 in log-size form, Table 2, Lemma 8.2 and
Lemma 9.2. Scope notes and the source hypotheses the proofs leave unused are in
`specs/results/A2_combinatorial.yaml`.

The fourth pair is B1, the multi-shift GDT counting theorem (`Challenge/MultiShift.lean`,
`Solution/MultiShift.lean`). It counts `n ≡ a (mod m)` with `gcd(n + h, N) = 1` for every
shift `h ∈ H`: each period `Tmin = mR` holds exactly `∏_{p | R} (p − ν_p(H))` such
values, absolute density `(1/m)·∏_{p | R}(1 − ν_p(H)/p)`. With `H = {0}` it re-derives GDT
v1.0.0's `gdt_count_per_period`, statement for statement (Gate B). It uses Mathlib and
vendors GDT v1.0.0's definitions and lemmas in `BGP212/GDTv1Basic.lean` and
`BGP212/GDTv1.lean`, with provenance hashes in their headers.

The fifth pair is B2 (`Challenge/MultiShiftB2.lean`, `Solution/MultiShiftB2.lean`):
relative density; local positivity (the accepted set is nonempty exactly when every local
factor is positive); a minimal-period theorem extending GDT v1.0.0's to every nonempty shift
set, with kernel-checked counterexamples showing both of its extra hypotheses are needed;
and the W-trick of Definition 4.5. Through `admissible_iff_local_factors`, Lemma 12.1 gives
a residue `b` with `gcd(b + h, W) = 1` for all `h ∈ H₄₅` and every `W`; at
`W = 2·3·…·23` that residue is unique, `b = 74549147`.

The sixth pair is A3a (`Challenge/Packing.lean`, `Solution/Packing.lean`), the first part
of Lemma 7.10's factor packing: a generic greedy packing lemma and 296 of the 455 packing
roots, each proved for every rough profile in its domain (the settled condition-(D) root
uniformly over its full (γ, ω₀) box). Certificates are in
`specs/certificates/packing_a3a.json`; the kernel re-checks every inequality. The other 159
roots are listed in `openRoots` and stay outside the proved scope until A3b.

The seventh pair is A3b (`Challenge/PackingB.lean`, `Solution/PackingB.lean`), a verified
certificate checker for Lemma 7.10 (Farkas certificates over subdivision trees of sorted
cells, `Solution/PackingCert.lean`) and 116 further roots: all remaining (A), (C), (E) roots
and 47 of the 90 (D) roots, uniformly over the (γ, ω₀) box. With A3a, **412 of the 455
roots** are proved; the 43 (D) roots left after A3b are listed in `openRootsB`.

The eighth pair is A3c (`Challenge/PackingC.lean`, `Solution/PackingC.lean`), which proves
those 43 roots and closes the ledger: **Lemma 7.10 holds for all 455 roots**, stated as
`lemma_7_10 : ∀ c m m', 1 ≤ m → m ≤ m' → m' ≤ 13 → Root c m m'`. The checker extension
(`Solution/PackingCertC.lean`) cuts along any integer hyperplane in profile and box
coordinates, certifies empty cells by exact Farkas infeasibility (`emptyB_sound`), and
checks large trees piece by piece (`checkTree2_split_path`). `checkTree2_sound` holds for any
capacity data, so the framework applies to other exact rational packing problems.

The ninth pair is A4 (`Challenge/Theorem711.lean`, `Solution/Theorem711.lean`, objects in
`BGP212/Theorem711.lean`): the deduction from Lemma 7.10 to **Theorem 7.11**. It proves, at
Table 3, every combinatorial hypothesis the proof of Theorem 7.11 uses:

- Definition 4.1 and Proposition 7.8 (I)–(III);
- Proposition 7.8 (A)–(E), quantified as printed (all `m, m′ ≤ ⌊1/δ⌋ = 60`, both orders,
  `m + m′ > 0`), from the 455 roots by `lemma_7_10_case_split`;
- the permissible triples of Lemmas 5.3–5.7 at the proof's widths `δ*(γ)` over every
  `γ`-range, the Type II ranges covering `[ξ₂ − ϵ, 1/2]`;
- the six containments `Q ⊆ D_X` (Type I in two ranges, IIa, IIb, IIc, III), each the
  verified packing composed with A2's extraction Lemmas 7.5–7.7.

`theorem_7_11` then holds relative to `AnalyticInputs`, whose fields name Lemmas 5.3–5.7, the
assembly step of Proposition 7.8, and Theorem 8.3. The record
`specs/results/A4_theorem_7_11.yaml` carries the exact signatures, the dependency graph, and
six findings, among them a Type III width that the printed `δ*` misses by exactly `ϵ`
(`type_III_printed_gap`, repaired within the printed conditions).

```text
lemma_7_10 (455 roots) ─► lemma_7_10_case_split ─► prop_7_8_A_E_table3
(A)–(E) + Lemmas 7.5–7.7 (A2) + perm_type_* ─► containment_{I_low, I_high, IIa, IIb, IIc, III}
Table 3 ─► definition_4_1_table3, prop_7_8_I_III_table3
all of the above ─► theorem_7_11_core ─► theorem_7_11 (H : AnalyticInputs)
```

The tenth pair is B3 (`Challenge/Gap.lean`, `Solution/Gap.lean`, objects in
`BGP212/Gap.lean`): **the final deduction**.

- `dhl_45_implies_gap : DHL 45 2 → H1Le 212`, from the general `dhl_implies_gap` (any
  admissible `k`-tuple of diameter `D`) and Lemma 12.1; `h1_liminf` reads `H1Le D` as
  `liminf (p_{n+1} − p_n) ≤ D`.
- Lemma 4.9's W-trick step (`wtrick_coprime`, prime-factor form `wtrick_coprime_of_primes`,
  squarefree combined modulus), connected to B2's `h45_wtrick_exists` by `h45_wtrick_coprime`.
  For `H₄₅` every prime dividing a difference is at most 103, so `w ≥ 103` suffices, and 103
  is sharp (`h45_wtrick_sharp`).
- Theorem 4.10 as an interface (`SieveInputs`): the sieve criterion, Theorem 11.1, and the
  bridge from Theorem 7.11's two conclusions to Definition 4.4 at Table 3, each a named field.
- `final_deduction (A : AnalyticInputs) (S : SieveInputs A) : DHL 45 2 ∧ H1Le 212`.

```text
Lemma 12.1 + §2 ─► dhl_implies_gap ─► dhl_45_implies_gap
B2 h45_wtrick_exists + wtrick_coprime_of_primes + h45_diff_primes ─► h45_wtrick_coprime
A4 theorem_7_11 (A) ─► S.equidistributed_of_coverage ─┐
S.theorem_11_1 ───────────────────────────────────────┼─► S.theorem_4_10 ─► DHL 45 2 ─► H1Le 212
table3_valid ─────────────────────────────────────────┘
```

**Scope.** The paper proves `H₁ ≤ 212` unconditionally. Here, `DHL[45, 2] ⇒ H₁ ≤ 212` and every
combinatorial ingredient are proved outright; `H₁ ≤ 212` itself is proved relative to the
named fields of `AnalyticInputs` and `SieveInputs` (`specs/results/B3_final_deduction.yaml`).

The eleventh pair is V0 (`Challenge/Variational.lean`, `Solution/Variational.lean`, objects
in `BGP212/Variational.lean`): **the variational space `B₂₁` of §11 has dimension exactly 846**.

- `B21 = span_ℚ {(L − P₁)^a P_λ : λⱼ ∈ 2ℤ_{>0}, a + |λ| ≤ 21}` over the 45 rescaled coordinates,
  with `P_j` Mathlib's power sums and `λ` a multiset of parts.
- `dimension_identity : Σ_{j ≤ 10} p(j)(22 − 2j) = 846`, with `p` Mathlib's partition count
  (computed through a verified enumeration `partsLE`).
- `B21Idx`, an explicit index type of 846 elements; `toPair_injective` and `toPair_range` show
  it lists each printed pair `(a, λ)` exactly once.
- `power_sums_algebraically_independent` (Newton's identities, the fundamental theorem of
  symmetric polynomials, and Noetherianity) gives `genIdx_linearIndependent` and
  `finrank_B21 : Module.finrank ℚ B21 = 846`.
- For V1: `simplexMoment` (the right side of (10.1)) with its `m = 0`, `m = 1` and Fubini-step
  identities.

The twelfth pair is V1 (`Challenge/SimplexMoment.lean`, `Solution/SimplexMoment.lean`, objects
in `BGP212/SimplexMoment.lean`): **the simplex moment identity (10.1) as a Lebesgue integral**.

- `beta_integral : ∫₀^R x^u (R − x)^v dx = R^{u+v+1} u! v! / (u+v+1)!` for every real `R`.
- `simplex_integral : ∫_{z ≥ 0, Σ zᵢ ≤ R} ∏ zᵢ^{eᵢ} dz = R^{m+Σeᵢ} ∏ eᵢ! / (m+Σeᵢ)!` for `R ≥ 0`,
  by Fubini and induction on the dimension; boundary cases `m = 0`, `R = 0`, `R < 0`, and the
  volume `R^m/m!`.
- `simplex_integral_rat`: at rational `R` the integral is V0's rational `simplexMoment`; V0
  proved the algebra of that formula, V1 proves it is the integral.
- `poly_integral` (Lemma 10.1 on the simplex): a rational polynomial integrates to the explicit
  rational `polyIntegralQ R G`, the step Proposition 10.2's Gram matrices build on (V2).

The thirteenth pair is V2b (`Challenge/GramEntry.lean`, `Solution/GramEntry.lean`,
`Solution/GramEntryCert.lean`, objects in `BGP212/GramEntry.lean`): **the first Gram entry as a
Lebesgue integral**, `I_T[(1, ∅), (0, (2))] = ∫_{T̃} (L − P₁) P₂ dx`.

- `integral_supportT`: for every dimension `N`, `g ≥ 0`, `L`, **cap function `C`** and coordinate
  `a`, `∫_{T̃} (L − Σ x)^p x_a^e` equals the closed form `gramFormula` (Proposition 10.2 made
  explicit): pointwise stratification and inclusion–exclusion (`indicator_supportT`), translation
  with null faces (`integral_Qset`), two-group Dirichlet integrals from V1 by Fubini
  (`piece_integral_mem`, `piece_integral_notMem`), and binomial counting (`count_pieces`).
- Boundary cases: `R = ∅`, `R = univ`, `N = 0`, empty index types.
- `gramEntryQ_eq` (computational certificate): the closed form at Table 3, evaluated over `ℚ` by
  the kernel row by row; it equals V2a's exploratory value exactly.
- `gram_entry_integral`, `gram_entry_B21`: the Table 3 entry, in V0's generators `gen 1 ∅`,
  `gen 0 {2}`, equals `gramEntryQ ≈ 1.18854 × 10⁻⁵⁸`.

The fourteenth pair is V2c (`Challenge/GramGeneral.lean`, `Solution/GramGeneral.lean`,
`Solution/GramGeneralCert.lean`, objects in `BGP212/GramGeneral.lean`): **the general monomial
integral bridge**.

- `integral_supportT_gen`: for every dimension `N`, `g ≥ 0`, `L`, **cap function `C`**, exponent
  vector `e` and weight `p`, `∫_{T̃} (L − Σ x)^p ∏ xᵢ^{eᵢ} = gramGen N g L C e p`. V2b's
  stratification, translation and Fubini steps are reused; the new counting places each
  distinguished coordinate in the rough set, the inclusion–exclusion set, or neither
  (`sig_insert`, `sig_union`, `sig_card`).
- `gramGen_extend`: the closed form transports to `gramFin`, indexed by the `d` distinguished
  coordinates only (loops of size `d`, not `N`); `gramGen_single` recovers V2b.
- `gram_entry_gen_list`, `gram_entry_B21_rat`: every `I_T` Gram entry of `B₂₁` generators
  `(L − P₁)^a P_λ` is a sum over placements of the parts, and at Table 3 an explicit rational.
- `gram_entry_example` (two distinguished coordinates): `I_T[(1, (2)), (0, (2))] =
  ∫_{T̃} (L − P₁) P₂² = gramExampleQ ≈ 5.45081 × 10⁻⁶⁰`, its value certified cell by cell.

The fifteenth pair is V2d (`Challenge/Fibre.lean`, `Solution/Fibre.lean`, objects in
`BGP212/Fibre.lean`): **the `J_T` fibre theorem, Lemma 9.2**. With `x̂ ∈ ℝⁿ`, `S = Σ x̂ᵢ`,
`s` the rough count and `ρ₁` the rough mass, `T̂ = {x̂ ≥ 0 : S ≤ τ, ρ₁ ≤ C(s)}` and
`U(x̂) = min{L − S, max{g, C(s+1) − ρ₁}}`:

- `roughSet_snoc`, `roughCount_snoc`, `roughMass_snoc`: appending `u` adds the new coordinate to
  the rough set exactly when `u > g`.
- `fibre_equiv`: for `x̂ ∈ T̂`, `(x̂, u) ∈ T̃ ⇔ 0 ≤ u ≤ U(x̂)` (any cap function, `0 ≤ g`, `τ ≤ L`).
- `empty_fibre_neg`, `empty_fibre_cap`: the fibre is empty when a coordinate is negative, or when
  `ρ₁ > C(s)`; the latter uses the cap step `C(m+1) ≤ C(m) + g` **for `m ≥ 1`** and `0 ≤ C(0)`.
  At Table 3 the step from `m = 0` fails (`C(1) = 777/1250 > g`; `capStep_zero_fails_table3`),
  and both hypotheses as stated hold (`capStep_table3`, `C_zero_table3`).
- `fibre_integral`, `marginal_agrees`: for continuous `P`, Definition 4.6's marginal of
  `1_{T̃} P` equals `J_T(P) = k ∫_{T̂} (∫₀^{U} P du)²`.
- `inner_integral`: `∫₀^U (M − u)^p u^t du` in closed form, the first block of the `J_T` bridge.
- `v2d_spec_discharged`: all seven specification statements, including the Table 3 instances.

The sixteenth pair is V2e-A (`Challenge/Aggregate.lean`, `Solution/Aggregate.lean`, objects in
`BGP212/Aggregate.lean`): **two-aggregate Dirichlet integration**. With
`aggExp ι e = |ι| + Σ eᵢ − 1` and `aggConst ι e = ∏ eᵢ! / (aggExp ι e)!`:

- `one_group`: `∫_{z ≥ 0, Σ z ≤ R} zᵉ h(Σ z) = aggConst ι e · ∫_{[0, R]} s^{aggExp ι e} h(s)` for a
  nonempty group and `h` measurable and bounded on `[0, R]` (shear `s = Σ z`, Fubini, V2b's
  weighted simplex moment on each slice).
- `two_group`, `two_group_fin`: two groups with sums `u₁`, `u₂` reduce to the triangle
  `{u₁, u₂ ≥ 0, u₁ + u₂ ≤ R}` with weight `u₁^{aggExp I a} u₂^{aggExp J b}`; on `Fin N` the groups
  are a rough set `R` and its complement (`u₁ = aggR R y`, `u₂ = aggS R y`).
- Boundary cases (empty groups, zero exponents, `R < 0`), rational polynomial specializations
  (`tri_poly`, `two_group_poly`, via V1's Lemma 10.1) and consistency with (10.1) (`two_group_const`).
- `stratumEndpoint_shift`: on V2b's piece `x = y + g·1_{R ∪ K}` the endpoint of Lemma 9.2 (cap index
  from the stratum `R`) is `endpointAgg` at `(u₁, u₂)`: rough mass `|R| g + u₁`, remaining mass
  `|K| g + u₂`.
- `example_value`: `∫_{y ∈ ℝ³, y ≥ 0, Σ y ≤ 1} y₀ y₂² 1[y₀ ≤ 1/2] = 19/7680` through the theorem.

The seventeenth pair is V2e-B (`Challenge/CapCell.lean`, `Solution/CapCell.lean`, objects in
`BGP212/CapCell.lean`): **polygon cells of the cap branch**. On a piece `(R, K)`, `r = |R|`,
`k = |K|`, the endpoint takes the cap value `U = C(r+1) − r g − u₁` exactly on
`u₁ ≤ C(r+1) − (r+1) g`, `u₂ ≤ L − k g − C(r+1)`; with the piece constraints this is the cell
`capCell = {0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ M}`.

- `box_monomial`, `box_capPow`, `box_poly`: exact values of monomial, cap-power and rational
  polynomial integrals over such cells (`boxVal`, computable over `ℚ`); boundary cases
  `boxVal_empty`, `boxVal_nonpos`, `boxVal_rect`.
- `endpointAgg_cap`, `endpointAgg_gBranch`, `endpointAgg_LBranch_cap`, `endpointAgg_LBranch_g`:
  the three branches of `U` in the aggregates; `cap_total_le`: on the cap branch `S ≤ L − g`, so
  the τ constraint is inactive when `L − g ≤ τ` (Table 3: `capCell_rect_table3`, every cap cell is
  a rectangle).
- `cap_branch_piece`, `cap_branch_r0`: `∫_{piece} yᵗ 1_cap U^m` in closed form.
- `capPieceT3_value` (computational certificate): the cap-branch part of `J_T(1)` on the Table 3
  piece `({0}, ∅)` of `T̂` is `(L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!) ≈ 1.0464 × 10⁻⁷⁰`.

The eighteenth pair is V2f (`Challenge/MarginalEntry.lean`, `Solution/MarginalEntry.lean`,
`Solution/MarginalEntryCert.lean`, objects in `BGP212/MarginalEntry.lean`): **all three endpoint
branches and the first marginal Gram entry `J_T[1, 1]`**.

- `cells_integral`: on a piece region the block `u₁^α u₂^β U^m (L − S)^n` integrates exactly over
  the four branch cells (cap; `L − S` on the cap side; `g`; `L − S` on the `g` side), each a signed
  combination of V2e-B's `boxTri` cells (`box_twoPow`, `cellsVal`).
- `piece_block`, `piece_r0`: every piece integral in closed form (two aggregates; one aggregate for
  the stratum `R = ∅`).
- `indicator_supportT_strat`, `jT_one_pieces`: V2b's inclusion–exclusion with a stratum-dependent
  integrand, so the rough-set-dependent endpoint of Lemma 9.2 is integrated exactly.
- `jT_one_eq`: `J_T(1) = jtSum N g L τ C 2 0` for every `N ≥ 1` and data with `0 ≤ g ≤ C(1)`,
  `C(N) < N g`; the count over pieces is binomial (`count_by_card`).
- `jT_gram_gen00_table3` (computational certificate `jtSum_table3`, 133 kernel-evaluated pieces):
  at Table 3 the marginal Gram entry of the generator `gen 0 ∅ = 1` is
  `J_T[1, 1] = 45 ∫_{T̂} U(x̂)² dx̂ ≈ 1.11935 × 10⁻⁵⁵`, an explicit rational, in V2d's `J_T` form and
  in Definition 4.6's marginal form.

The nineteenth pair is V2g (`Challenge/PowerSumEntry.lean`, `Solution/PowerSumEntry.lean`,
`Solution/PowerSumEntryCert.lean`, objects in `BGP212/PowerSumEntry.lean`): **a marginal Gram entry
with a power sum, `J_T[P₂, 1]`**.

- `jTbil`: the bilinear form `J_T[F, G] = (n + 1) ∫_{T̂} (∫₀^U F)(∫₀^U G)` (`jTbil_self`,
  `jTbil_comm`); `inner_P2`: `∫₀^U P₂ = U P̂₂ + U³/3` for `P₂ = gen 0 {2}`.
- `strat_integral`: V2b's stratified decomposition for any stratum-dependent continuous integrand.
- `piece_single`, `piece_r0_w`, `piece_single_eq`: a single-coordinate weight `yᵢ^e` raises the
  Dirichlet exponent of the group containing `i` by `e` (`pieceE`); `sum_place` places the
  distinguished coordinate in `R`, in `K` or in neither (multiplicities `r`, `k`, `N − r − k`).
- `piece_P2`, `p2Entry_eq`: `(N + 1) ∫_{T̂} (U P̂₂ + U³/3) U = p2EntryVal N g L τ C` for every
  `N ≥ 1` and data with `0 ≤ g ≤ C(1)`, `C(N) < N g`, after expanding `P̂₂(y + g·1_{R∪K})`.
- `jT_P2_one_table3` (computational certificate `p2EntryVal_table3`, 266 kernel-evaluated piece
  lemmas): `J_T[P₂, 1] = 45 ∫_{T̂} (U² P̂₂ + U⁴/3) ≈ 4.99944 × 10⁻⁵⁷` at Table 3, an explicit rational.

The twentieth pair is V2h (`Challenge/PowerSumSquare.lean`, `Solution/PowerSumSquare.lean`, the
certificate `Solution/PowerSumSquareCert0.lean` … `Cert13.lean` (one per row) and
`Solution/PowerSumSquareCertSum.lean`,
objects in `BGP212/PowerSumSquare.lean` and `BGP212/PowerSumPlace.lean`): **the marginal Gram entry
`J_T[P₂, P₂]`, with two distinguished coordinates**.

- `piece_mono`: every monomial weight `yᵗ` on a piece integrates to `(∏ tᵢ!) · pieceM N r k a b … m`,
  where `a` and `b` are the degrees landing in the rough and the smooth group; `piece_w1`,
  `piece_w2` specialize to one coordinate and to two distinct coordinates through their classes
  `cls R K i` (rough, in `K`, neither).
- `sum_place2`: V2c's placements of two distinguished coordinates, collapsed by symmetry to
  classes: an ordered pair of classes `(c, d)` occurs `n_c n_d − [c = d] n_c` times off the
  diagonal, and the diagonal `i = j` occurs `n_c` times with weight `(yᵢ + sᵢ)⁴`.
- `q2J_expand`, `piece_P2sq`: `∫_{piece} U^m P̂₂(y + g·1_{R∪K})²` as 15 moments (`A + B ≤ 4`) with
  explicit coefficients `q2Coef`; `piece_P2m` (`P̂₂` at any power of `U`) and `piece_pow`.
- `p2p2Entry_eq`: `(N + 1) ∫_{T̂} (U P̂₂ + U³/3)² = p2p2EntryVal N g L τ C` for every `N ≥ 1` and
  data with `0 ≤ g ≤ C(1)`, `C(N) < N g`.
- `jT_P2_P2_table3`, `jT_P2_table3` (computational certificate `p2p2EntryVal_table3`: a moment
  table of 1 995 kernel-evaluated moments plus 1 064 further piece lemmas):
  `J_T[P₂, P₂] = J_T(P₂) ≈ 2.27107 × 10⁻⁵⁸` at Table 3, an explicit rational.

The twenty-first pair is V2i (`Challenge/GenEntry.lean`, `Solution/GenEntry.lean`,
`Solution/GenEntryTable.lean`, the certificate `Solution/GenEntryCert0.lean` … `Cert13.lean` and
`Solution/GenEntryCertSum.lean`, objects in `BGP212/GenEntry.lean` and `BGP212/GenEntryBlock.lean`):
**general polynomial marginal Gram entries `J_T[G_{a,λ}, G_{b,μ}]`, `G_{a,λ} = (L − P₁)^a P_λ`**.

- `inner_genFun`: `∫₀^U G_{a,λ}` as a sum over sub-multisets `T ⊆ λ` and powers of `L − Ŝ`, so every
  entry is a combination of power-sum products against `U^m (L − S)^n`; `piece_mono_n` makes every
  monomial weight against that block a moment `pieceMn`.
- `piece_state`, `piece_place`: products of power sums on a piece, by an induction over the
  factors (each merges into an open coordinate or opens one of class `c`, `n_c − #open` times);
  unrolled this is the set-partition placement with falling-factorial class counts.
- `genEntry_eq`: `J_T[G_{a₁,λ₁}, G_{a₂,λ₂}] = genEntryVal N g L τ C a₁ λ₁ a₂ λ₂` for every `N ≥ 1`
  and data with `0 ≤ g ≤ C(1)`, `C(N) < N g`; `jT_gen_table3`: every `B₂₁` entry at Table 3 is the
  rational `genEntryVal 44 …`.
- Evaluated by the kernel (moment tables shared with V2h through `tableFn_eq`): `J_T[P₄, 1]`,
  `J_T[P_{(2,2)}, 1]`, `J_T[L − P₁, 1]`, and `J_T[P₂, P₂]` recomputed through the general form
  (`genEntryPP_eq_v2h`).

The twenty-second pair is V2j (`Challenge/MomentAgg.lean`, `Solution/MomentAgg.lean`, the demonstration
`Solution/MomentAggDemo1.lean` … `Demo4.lean`, wrappers in `Solution/MomentAggSuite.lean`, objects in
`BGP212/MomentAgg.lean`, specification `Exploratory/V2j/SPEC.md`): **shared-moment aggregation**.

- `genPieceWith_listSum`, `genPieceWith_congr`: V2i's piece value is linear in the moment oracle and
  reads it only at `genKeys` (the queried keys, listed without duplicates).
- `genPieceWith_eq_keys`: the coefficient collapse `Σ_{s ∈ S} genPieceWith (delta s) · Mo s`.
- `aggEntryVal_eq`, `jT_weighted_eq_agg`: for a weighted list of generator pairs (the shape of
  `J_T(P⋆)`), coefficients collected per key across all pairs and each distinct moment evaluated once
  per piece give `Σ w · J_T[G_{a₁,λ₁}, G_{a₂,λ₂}]`.
- Demonstration: V2i's certified piece value `gpPP_6_3` recomputed from 19 moments (115 oracle
  queries), V2i's four entries on that piece from 21 shared keys, and `J_T[P₂, P₂]` on synthetic data.

## What is proved, imported, and external

- **Proved here, kernel-checked:** Lemma 12.1; the Table 3 parameter layer and every
  Appendix B row as a formula in those parameters; the A2 combinatorial lemmas; the
  multi-shift GDT counting theorem (B1); density, positivity, minimal period and the
  W-trick for H₄₅ (B2); Lemma 7.10, all 455 packing roots (A3a, A3b, A3c); every
  combinatorial hypothesis of Theorem 7.11 at Table 3 (A4); DHL[45, 2] ⇒ H₁ ≤ 212 and the
  W-trick step of Lemma 4.9 (B3); `dim B₂₁ = 846` (V0); the simplex moment identity (10.1) (V1); the Gram entry
  `I_T[(1, ∅), (0, (2))]` as a Lebesgue integral over Table 3's support (V2b); every monomial
  integral over the support in closed form, and every `I_T` entry of `B₂₁` as an explicit rational
  (V2c); the `J_T` fibre theorem of Lemma 9.2 and the marginal identity `J_T(1_{T̃} P) = J_T(P)` (V2d);
  two-aggregate Dirichlet integration and the aggregate form of Lemma 9.2's endpoint (V2e-A);
  exact polygon-cell integrals of the cap branch and one Table 3 cap-branch certificate (V2e-B);
  all three endpoint branches and the marginal Gram entry `J_T[1, 1]` at Table 3 (V2f); the bilinear
  `J_T` form, single-coordinate placement, and the power-sum entry `J_T[P₂, 1]` at Table 3 (V2g);
  two-coordinate placement and the entry `J_T[P₂, P₂]` at Table 3 (V2h); every `J_T` entry of
  `B₂₁` generators in closed form, with four Table 3 entries evaluated (V2i); shared-moment
  aggregation of weighted sums of entries, proved equal to V2i's closed form (V2j).
- **Imported analytic hypotheses (taken as hypotheses in Axiom's certificate too):** the
  Type I/II/III equidistribution estimates (Lemmas 5.3–5.7), bilinear Bombieri–Vinogradov
  (Lemma 8.1), and the Harman decomposition (Proposition 7.2). In A4 these are the named
  fields of `AnalyticInputs`, together with Proposition 7.8's assembly step and Theorem 8.3.
- **Covered by Axiom's own Lean certificate, outside this repository:** the sieve
  criterion (Theorem 4.10) and the deduction of Theorem 1.1.
- **Open, outside the proved scope:** the exact variational certificate of Theorem 11.1.

## Current mathematical scope

V2i proves an exact rational representation of every marginal Gram entry
for the 846-dimensional `B₂₁` polynomial space. V2j proves that aggregation
of repeated rational-moment keys preserves those expressions, including
weighted combinations of generator pairs. Selected Table 3 entries have exact
kernel-checked certificates. The complete evaluated `846 × 846` matrices,
optimized polynomial `P⋆`, the variational sign certificate, and an
unconditional proof of `H₁ ≤ 212` remain outstanding.

See [`Exploratory/V2j/SPEC.md`](Exploratory/V2j/SPEC.md),
[`Comparator/moment_agg_v2j.json`](Comparator/moment_agg_v2j.json), and
[`specs/results/V2j_moment_agg.yaml`](specs/results/V2j_moment_agg.yaml).

## Comparator Verification

Track B uses Mathlib, so fetch its build cache first:

```text
lake exe cache get
```

Then

```text
./verify.sh
```

The A3c kernel checks need about 2.6 GB of memory at peak.

To regenerate and cross-check the A3a certificate data (exploratory, outside the kernel):

```text
python3 -I specs/checks/packing_ledger.py specs/certificates/packing_a3a.json
python3 -I specs/checks/packing_certificates_match.py
```

For A3b (the generator needs SciPy; it proposes candidates only):

```text
python3 -I specs/checks/packing_a3b_generate.py specs/certificates/packing_a3a.json /tmp/a3b.json
cmp /tmp/a3b.json specs/certificates/packing_a3b.json
python3 -I specs/checks/packing_a3b_emit.py specs/certificates/packing_a3b.json . --check
```

For A3c (the generator needs SciPy; it proposes cuts, assignments and dual supports only):

```text
python3 -I specs/checks/packing_a3c_generate.py /tmp/a3c.json --jobs 2
cmp /tmp/a3c.json specs/certificates/packing_a3c.json
python3 -I specs/checks/packing_a3c_emit.py specs/certificates/packing_a3c.json . --check
python3 -I specs/checks/packing_a3c_negative_controls.py /tmp/a3c_neg
for f in /tmp/a3c_neg/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For A4's negative controls:

```text
python3 -I specs/checks/theorem_7_11_negative_controls.py /tmp/a4_neg
for f in /tmp/a4_neg/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For B3's negative controls:

```text
python3 -I specs/checks/final_deduction_negative_controls.py /tmp/b3_neg
for f in /tmp/b3_neg/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V0's negative controls:

```text
python3 -I specs/checks/variational_v0_negative_controls.py /tmp/v0_neg
for f in /tmp/v0_neg/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V1's controls:

```text
python3 -I specs/checks/simplex_moment_v1_controls.py /tmp/v1_ctl
for f in /tmp/v1_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2b's controls:

```text
python3 -I specs/checks/gram_entry_v2b_controls.py /tmp/v2b_ctl
for f in /tmp/v2b_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2c's controls:

```text
python3 -I specs/checks/gram_general_v2c_controls.py /tmp/v2c_ctl
for f in /tmp/v2c_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2d's controls:

```text
python3 -I specs/checks/fibre_v2d_controls.py /tmp/v2d_ctl
for f in /tmp/v2d_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2e-A's controls:

```text
python3 -I specs/checks/aggregate_v2e_controls.py /tmp/v2e_ctl
for f in /tmp/v2e_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2e-B's controls:

```text
python3 -I specs/checks/capcell_v2eb_controls.py /tmp/v2eb_ctl
for f in /tmp/v2eb_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2f's certificate and controls:

```text
python3 -I specs/checks/marginal_entry_v2f_emit.py /tmp/MarginalEntryCert.lean
cmp /tmp/MarginalEntryCert.lean Solution/MarginalEntryCert.lean
python3 -I specs/checks/marginal_entry_v2f_controls.py /tmp/v2f_ctl
for f in /tmp/v2f_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2g's certificate and controls:

```text
python3 -I specs/checks/power_sum_entry_v2g_emit.py /tmp/PowerSumEntryCert.lean
cmp /tmp/PowerSumEntryCert.lean Solution/PowerSumEntryCert.lean
python3 -I specs/checks/power_sum_entry_v2g_controls.py /tmp/v2g_ctl
for f in /tmp/v2g_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2h's certificate and controls:

```text
mkdir -p /tmp/v2h_cert && python3 -I specs/checks/power_sq_entry_v2h_emit.py /tmp/v2h_cert
for f in /tmp/v2h_cert/*.lean; do cmp "$f" "Solution/$(basename "$f")"; done
python3 -I specs/checks/power_sq_entry_v2h_controls.py /tmp/v2h_ctl
for f in /tmp/v2h_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

For V2i's certificate and controls:

```text
mkdir -p /tmp/v2i_cert && python3 -I specs/checks/gen_entry_v2i_emit.py /tmp/v2i_cert
for f in /tmp/v2i_cert/*.lean; do cmp "$f" "Solution/$(basename "$f")"; done
python3 -I specs/checks/gen_entry_v2i_controls.py /tmp/v2i_ctl
for f in /tmp/v2i_ctl/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
```

`./verify.sh` builds the project and runs Lean Comparator on each config in `Comparator/`.
A successful run ends with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Axioms used: `propext` and `Quot.sound` for Lemma 12.1; `propext`, `Quot.sound` and
`Classical.choice` for the other pairs (all within the permitted set). Each pair's
run, sandbox provenance and negative controls are recorded in `specs/results/`.

## Source

Place Axiom Math's PDF at `Source/bgp212.pdf` (kept outside version control). sha256 `2b307ae26046dffd2153fe7466e5a9a302976dc3ba5142151a8a8104a37b3d80`.
