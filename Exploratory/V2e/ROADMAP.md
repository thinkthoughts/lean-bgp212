# V2e roadmap: from the aggregate Dirichlet theorem to `J_T` Gram entries

Status:
- **V2e-A is proved** (sixteenth pair, `Solution/Aggregate.lean`).
- **V2e-B is proved** (seventeenth pair, `Solution/CapCell.lean`): the cap branch, see §3.
- **V2f is proved** (eighteenth pair, `Solution/MarginalEntry.lean`): all branches and the first marginal Gram entry `J_T[1, 1]`, see §4.
- **V2g is proved** (nineteenth pair, `Solution/PowerSumEntry.lean`): the bilinear `J_T` form, single-coordinate placement, and the power-sum entry `J_T[P₂, 1]`, see §6.
- **V2h is proved** (twentieth pair, `Solution/PowerSumSquare.lean`): monomial weights as moments, two-coordinate placement, and the entry `J_T[P₂, P₂]`, see §8.
- This file is the plan for the remaining `J_T` entries and certificates (§7, §9).
- Statements marked *exploratory* were checked numerically, not in the kernel.

## 1. What V2e-A provides (kernel-checked)

**Dirichlet exponent and constant.**
- `aggExp ι e = |ι| + Σ e − 1`.
- `aggConst ι e = ∏ eᵢ! / (aggExp ι e)!`.

**The two-aggregate identity, `two_group_fin`.** For a rough set `R` with `R` and `Rᶜ` nonempty, and `h` measurable and bounded on the triangle:

```text
∫_{y ≥ 0, Σ y ≤ M} yᵗ h(u₁, u₂) dy = aggConst R t · aggConst Rᶜ t · ∫_{tri M} u₁^{aggExp R t} u₂^{aggExp Rᶜ t} h(u₁, u₂)
```

Here `u₁ = Σ_R y`, `u₂ = Σ_{Rᶜ} y`, and `tri M = {u₁, u₂ ≥ 0, u₁ + u₂ ≤ M}`.

**Boundary cases.**
- A single group: `one_group`.
- An empty group: `one_group_empty`, `two_group_left_empty`, `two_group_right_empty` and `two_group_both_empty`.
- Zero exponents.
- `R < 0`.

**Rational specializations.**
- `tri_poly` and `two_group_poly` give the rational value for polynomial `h`, via V1's Lemma 10.1.
- `two_group_const` shows consistency with (10.1).

**The endpoint as a function of the aggregates.**
- On V2b's translated piece `x = y + g·1_{R ∪ K}`, with `r = |R|` and `k = |K|`:
  - rough mass `ρ₁ = r g + u₁` (`aggR_shift`);
  - remaining mass `S − ρ₁ = k g + u₂` (`aggS_shift`).
- `stratumEndpoint_shift` then gives `U = endpointAgg g L C r k u₁ u₂ = min(L − (r+k)g − u₁ − u₂, max(g, C(r+1) − r g − u₁))`.
- The cap index is `r + 1`, taken from the stratum `R`.
  - The translated point's own rough set is `R ∪ K`, since the `K` coordinates are also shifted by `g`.
  - Using it gives a different endpoint. The control `nc_union` records this: 461/1250 instead of 587/1250 at Table 3.
  - `endpoint_eq_stratum` identifies the two on the stratum itself.

**Prototype of a branch integral.**
- `tri_cut` integrates `u₁^α u₂^β` over the triangle cut by `u₁ ≤ c`.
- It is closed-form, via V2d's `inner_integral`.

## 2. The cells of one piece (kernel-checked in V2e-B; first verified exactly at 20 000 random points)

Fix a piece `(R, K)` with `r = |R|` and `k = |K|`. The branches of `U` switch along three lines in the `(u₁, u₂)` plane:

| switch | line | type |
|---|---|---|
| `max`: `g` vs `C(r+1) − ρ₁` | `u₁ = c₁ := C(r+1) − (r+1) g` | vertical |
| `min`, cap side (`u₁ ≤ c₁`): `L − S` vs `C(r+1) − ρ₁` | `u₂ = c₂ := L − k g − C(r+1)` | horizontal (`u₁` cancels) |
| `min`, `g` side (`u₁ ≥ c₁`): `L − S` vs `g` | `u₁ + u₂ = c₃ := L − (r+k+1) g` | anti-diagonal |

The four branch lemmas `endpointAgg_cap`, `endpointAgg_gBranch`, `endpointAgg_LBranch_cap` and `endpointAgg_LBranch_g` (V2e-B) prove this classification.

On each cell `U` is affine, with three possible values:
- `L − (r+k) g − u₁ − u₂`;
- `C(r+1) − r g − u₁`;
- `g`.

The support constraints of `T̂ = supportT 44 g τ C` (V2d's `hatSupport_eq`) on the piece are:
- `u₁ + u₂ ≤ τ − (r+k) g`;
- `u₁ ≤ C(r) − r g`.

These lines are of the same three types. So every cell is a polygon bounded by vertical, horizontal and anti-diagonal lines with rational offsets.

Every cell integral is therefore an iterated one-variable polynomial integral with rational limits, the shape of `tri_cut`.

## 3. V2e-B: the cap branch (done)

**Cells.** `boxTri A B D = {0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ D}`.
- `box_monomial` gives `∫_{boxTri} u₁^α u₂^β = boxVal A B D α β` exactly.
  - `boxVal` splits `[0, A]` at `E = max 0 (min A (D − B))` and `F = max 0 (min A D)`.
  - It is computable over `ℚ`, and `boxVal_cast` transports it to `ℝ`.
- `box_capPow` handles the cap power `(a − u₁)^m`, and `box_poly` any `P ∈ ℚ[u₁, u₂]`.
- Boundary cases:
  - `boxVal_empty`: `A < 0` or `B < 0`;
  - `boxVal_nonpos`: `D ≤ 0`;
  - `boxVal_rect`: `A + B ≤ D`.
- Independent check: polygon clipping, at 300 random cells and in the controls.

**The cap cell.** `capCell = boxTri (min c c₁) c₂ M`, where `c` and `M` are the piece cap and total.
- `endpointAgg_on_capCell`: on it, `U = C(r+1) − r g − u₁`.
- `cap_inner`: the inner integral `∫₀^U (L − S − u)^p u^t du` there is an explicit polynomial in `(u₁, u₂)`.

**Piece integrals.**
- `cap_branch_piece`: `∫_{piece} yᵗ 1_cap U^m` in closed form, through `two_group_fin`.
- `cap_branch_r0`: the stratum with no rough coordinates, through `one_group`.
- `piece_cap_eq`: the piece constraints are automatic on the cell.

**Findings.**
- **The τ constraint is inactive on the cap branch.**
  - There `g ≤ U ≤ L − S`, so `S ≤ L − g` (`cap_total_le`).
  - At Table 3, `τ − (L − g) = 1/625 > 0` (`tau_ge_table3`).
  - So every Table 3 cap cell is a rectangle `[0, A] × [0, B]` (`capCell_rect_table3`).
- **Few nonempty cap cells (exploratory, exact enumeration).** At Table 3, the cap cell is nonempty only for 59 cardinality classes `(r, k)`:
  - `r ≤ 12`;
  - `k ≤ 6`, with `k ≤ 2` once `r ≥ 9`.

  For `r = 1` it is empty from `k = 7` on (`capCell_empty_table3`).
- **Certificate.** `capPieceT3_value` gives the cap-branch part of `J_T(1)` on the piece `({0}, ∅)` as:

  ```text
  (L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!) ≈ 1.0464 × 10⁻⁷⁰
  ```

  It is kernel-checked, and a direct 3-dimensional grid integration of the analogous `N = 3` piece agrees.

## 4. V2f: all branches and `J_T[1, 1]` (done)

**All four cells as signed `boxTri` cells** (`cells_integral`, kernel-checked). On the piece region `P = boxTri c M M`, with `A₁ = min c c₁` and `M₃ = min M (L' − g)`:

| cell | set | `U` |
|---|---|---|
| `Z₁` | `boxTri A₁ c₂ M` | `C(r+1) − r g − u₁` |
| `Z₂` | `boxTri A₁ M M \ Z₁` | `L' − u₁ − u₂` |
| `Z₃` | `boxTri c M M₃ \ boxTri A₁ M M₃` | `g` |
| `Z₄` | `(P \ boxTri A₁ M M) \ Z₃` | `L' − u₁ − u₂` |

Each set difference is an exact `setIntegral_sdiff`.
- The clamping of the roadmap's §4.1 is built in, through `min c c₁` and `min M (L' − g)`.
- `box_twoPow` integrates `u₁^α u₂^β (p − u₁)^{m₁} (L' − u₁ − u₂)^{m₂}` over any cell.
- So `cellsVal` covers every block `U^m (L − S)^n` that a `J_T` Gram entry needs.

**The stratum-dependent decomposition.** The integrand of `J_T` depends on the rough set of `x̂`.
- `indicator_supportT_strat` is V2b's inclusion–exclusion with an integrand `G R` that depends on the stratum.
- `jT_one_pieces` writes `J_T(1)` as `(N+1) Σ_R Σ_{K ⊆ Rᶜ} (−1)^{|K|} ∫_{piece} U²`, using:
  - `integral_Qset` (translation);
  - `stratumEndpoint_shift` (aggregates).
- `piece_block` and `piece_r0` evaluate each piece (two aggregates, or one aggregate for `R = ∅`).
- `piece_eq_pieceJ` shows the value depends only on `(|R|, |K|)`.
- `count_by_card` gives `jT_one_eq`. It holds for any `N ≥ 1` and any data with `0 ≤ g ≤ C(1)` and `C(N) < N g`.

**Certificate.** At Table 3:
- 133 pieces are nonempty (`r ≤ 13`, `r + k ≤ 15`); each is one `decide +kernel` lemma.
- Every other piece vanishes by linear arithmetic (`pieceJ_tail`, `pieceJ_high`).
- `jT_one_table3`: `J_T[1, 1] = 45 ∫_{T̂} U² ≈ 1.11935 × 10⁻⁵⁵`, an exact rational with a 145-digit numerator and a 200-digit denominator.
- It also holds in Definition 4.6's marginal form, for the generator `gen 0 ∅` (`jT_gram_gen00_table3`, via V2d's `marginal_agrees`).

**Independent checks (exploratory).**
- Monte Carlo at `N = 44`: within 0.42 and 0.15 standard errors in two runs.
- Polygon clipping of piece `(1, 0)`: exact agreement.
- Synthetic data at `N = 3`: grid integration with the true rough-set endpoint agrees to 0.4%.

**A planning correction.** The V2c placement counting is not needed for symmetric integrands. A piece value depends only on `(|R|, |K|)`, so the count is binomial (`count_by_card`). Placements return only for entries whose generators have distinguished coordinates (§6).

## 5. Costs observed in V2e-A and V2e-B

- **Elaboration:** `Solution/Aggregate.lean` elaborates in about 6 s, with a 3.15 GB peak, which is mostly the import baseline.
- **New Mathlib modules:** none.
- **Kernel arithmetic:** none beyond the worked example's small constants (`decide +kernel` on four `ℚ`/`ℕ` values).
- **V2e-B:**
  - `Solution/CapCell.lean` elaborates in about 5 s, peaking at 3.19 GB.
  - The Comparator suite takes about 115 s, peaking at 3.16 GB.
  - Kernel arithmetic is only the certificate's `capPowVal` and a few small constants.
- **V2f:**
  - `Solution/MarginalEntry.lean` elaborates in seconds.
  - The certificate `Solution/MarginalEntryCert.lean` (133 piece lemmas) is described in `specs/results/V2f_marginal_entry.yaml`.

## 6. V2g: the power-sum entry `J_T[P₂, 1]` (done)

**The bilinear form.** `jTbil` is `J_T[F, G] = (n + 1) ∫_{T̂} (∫₀^U F)(∫₀^U G)`.
- `jTbil_self`: `J_T(F) = J_T[F, F]`.
- `jTbil_comm`: the form is symmetric.
- For `P₂ = gen 0 {2}`, `∫₀^U P₂ = U P̂₂ + U³/3` (`inner_P2`), so `J_T[P₂, 1] = 45 ∫_{T̂} (U² P̂₂ + U⁴/3)`.

**Power sums after the translation.** On a piece:

```text
P̂₂(y + g·1_{R∪K}) = Σᵢ yᵢ² + 2 g Σ_{i ∈ R∪K} yᵢ + g² |R ∪ K|
```

- **Single-coordinate weights.** A weight `yᵢ^e` raises the Dirichlet exponent of the group containing `i` by `e`, and multiplies that group's constant by `e!` (`piece_single`, `piece_r0_w`, `pieceE`).
- **Placement.** Summing over `i` places the distinguished coordinate in `R`, in `K` or in neither, with multiplicities `r`, `k` and `N − r − k` (`sum_place`). This is V2b's `count_pieces` pattern, for one distinguished coordinate.
- **Closed form.** `p2Entry_eq` gives the result for any `N ≥ 1` and admissible data.

**Certificate.**
- 266 piece lemmas (`p2J` and `pieceJ … 4 0` for each of the 133 pieces).
- The build takes 2 286 s, peaking at 5.22 GB.
- `J_T[P₂, 1] ≈ 4.99944 × 10⁻⁵⁷`.

**Independent checks (exploratory).**
- Monte Carlo at `N = 44`: z = −0.29 and 0.27 in two runs.
- Synthetic `N = 3` grid: 0.54%.

**Finding (exploratory).** The shift terms nearly cancel:
- the `R`-shift contributes +35.8%;
- the `K`-shift contributes −35.8%;
- their sum is −1.7 × 10⁻¹² of the entry.

The inclusion–exclusion therefore carries cancellation to about twelve digits, so certificates must stay in exact arithmetic. Whether an exact identity lies behind the near-cancellation is open.

## 7. Cost of the full marginal Gram computation (exploratory model, calibrated)

**Measured.**
- `J_T[1, 1]` costs one `cellsVal` per piece: about 2.4 s; 324 s in total.
- `J_T[P₂, 1]` costs six `cellsVal` per piece: about 17 s; 2 286 s in total.
- `J_T[P₂, P₂]` costs 21 `cellsVal`-sized evaluations per piece (15 moments at `m = 2`, five at `m = 4`, one at `m = 6`): 37–101 s per piece; 10 681 s in total (§8). The cost per moment grows with the power of `U`: about 3 s at `m = 2`, 7.7 s at `m = 4`, 14 s at `m = 6`.
- A single `boxVal` with exponents up to about 90 costs 0.4–0.9 s of kernel time above the import baseline.

**Why the cost is driven by moments.** Every `J_T` entry, after the power-sum expansion and the placement of coordinates, is a rational combination of per-piece moments `cellsVal(α + A, β + B, m, n)`. Here:
- `A` and `B` are the coordinate degrees landing in the rough and the smooth group;
- `m` and `n` are the powers of `U` and `L − S`.

For `B₂₁` (`a + |λ| ≤ 21`), the moments satisfy `A + B ≤ 40`, `m ≥ 2` and `A + B + m + n ≤ 44`. That gives up to 163 016 distinct moments per piece.

**Entry by entry.** All 846 × 847 / 2 entries need about 2.2 × 10⁷ moment certificates. That is 250–600 kernel-days: not a practical route.

**`J_T(P⋆)` directly.** On each cell `U` is affine, so the whole weighted integrand `Σ cᵢ cⱼ (∫Fᵢ)(∫Fⱼ)` collapses to one bivariate polynomial in `(u₁, u₂)`:
- its extra degree is at most 44, so at most 1 035 monomials;
- there are 5 distinct `boxTri` cells per piece, so about 5 175 `boxVal` evaluations per piece;
- over 133 pieces that is about 6.9 × 10⁵ evaluations, about 4–7 kernel-days single-threaded.

The pieces are independent lemmas, so the work parallelizes on the VPS.

**What that route still needs, besides the arithmetic.**
1. A general placement theorem for products of power sums. This means V2c's set partitions of the parts, each block placed in `R`, `K` or the rest, with falling-factorial multiplicities.
2. A kernel-computed reduction from `P⋆`'s 846 coefficients to the per-cell polynomial coefficients.

## 8. V2h: the entry `J_T[P₂, P₂]` (done)

`J_T[P₂, P₂] = 45 ∫_{T̂} (U P̂₂ + U³/3)² = 45 ∫ (U² P̂₂² + (2/3) U⁴ P̂₂ + U⁶/9)`. The last two blocks
are V2g's `p2J … 4` (proved for every power of `U`, `piece_P2m`) and V2f's `pieceJ … 6 0`
(`piece_pow`). The new block carries `P̂₂(y + s)² = Σᵢ Σⱼ (yᵢ + sᵢ)² (yⱼ + sⱼ)²`.

**Moments instead of exponent bookkeeping.** `piece_mono`: for any exponent vector `t`,

```text
∫_{piece} yᵗ U^m = (∏ tᵢ!) · pieceM N r k a b … m,   a = Σ_{i ∈ R} tᵢ,  b = Σ_{i ∉ R} tᵢ
```

so a weight matters only through the degrees `(a, b)` landing in the rough and the smooth group.
This replaces V2g's case analysis on the position of one coordinate and applies to any number of
distinguished coordinates.

**Two distinguished coordinates.** Each coordinate has a class `cls R K i ∈ {rough, K, neither}`
with counts `n = (r, k, N − r − k)` and shift `σ = (g, g, 0)`.
- `sum_place2`: off the diagonal, the ordered pair of classes `(c, d)` occurs `n_c n_d − [c = d] n_c`
  times; on the diagonal `i = j`, the class `c` occurs `n_c` times. This is V2c's `Sig` placement
  (`sig_union` splits off the distinguished set `D`, every `a ∈ D` placed in `R`, in `K` or in
  neither) after the symmetry within each class collapses the `3^|D|` placements to class counts;
  for `|D| = 2` the coincidence `i = j` is the only set partition beyond the trivial one.
- `piece_w2`: for `i ≠ j` the degrees add within a group (`yᵢ^a yⱼ^b` with both rough contributes
  `a + b` to the rough group, factor `a! b!`).
- `q2J_expand`: collecting the binomial expansion by `(A, B)` gives 15 moments (`A + B ≤ 4`) with
  explicit coefficients `q2Coef`, polynomial in `g`, `r`, `k`, `N`.

**Certificate (moment table).**
- Per nonempty piece: the 15 moments at `m = 2` (about 3 s each), the five `pieceE … 4` (about 7.7 s
  each), `pieceJ … 6 0` (about 14 s); assembling `q2J` and `p2J … 4` from the moment numerals takes
  under 0.1 s, since the kernel then evaluates only the coefficients.
- 3 059 piece lemmas in fourteen files, one per row `r`, so a restarted build resumes
  at the last finished row, and an assembly file for rows and totals.
- Splitting `p2J … 4` into its five `pieceE` lemmas lowered the peak from 5.88 GB to 4.71 GB.
- Build: 10 681 s (2 h 58 min) in the build container, rows from 1 509 s (`r = 1`, 15 pieces) down to
  121 s (`r = 13`); peak 5.18 GB.
- `J_T[P₂, P₂] ≈ 2.27107 × 10⁻⁵⁸`.

**Independent checks (exploratory).**
- Monte Carlo at `N = 44`: 2.27512 ± 0.0034 and 2.27075 ± 0.0034 (× 10⁻⁵⁸; z = 1.18, −0.09) with
  200 000 samples each; three vectorized runs of 4 000 000 samples pooled to 2.27054 ± 0.00044
  (z = −1.21). The integrand is heavy-tailed: a 100 000-sample run gave z = 3.17.
- Synthetic `N = 3`: the closed form 0.00136761 against midpoint grids 0.00137584 (200³),
  0.00136013 (400³), 0.00136800 (800³), 0.00136658 (1600³): relative errors +0.60%, −0.55%,
  +0.03%, −0.08%. Counting the diagonal twice gives 0.00092516.

**Finding (exploratory): the `{1, P₂}` block is nearly singular.** With V2f's `J_T[1, 1]` and V2g's
`J_T[P₂, 1]`, `J[P₂,1]² / (J[1,1] J[P₂,P₂]) = 0.98321`: in the `J_T` inner product `P₂` is
nearly parallel to `1`. If the same holds across `B₂₁`, the `J_T` Gram matrix is badly conditioned
and the certificate for `J_T(P⋆) − 4 I_T(P⋆)` must stay exact, as the twelve-digit cancellation in
V2g already indicated (an expectation, not checked beyond this 2 × 2 block).

## 9. After V2h

1. **The general generator `(L − P₁)^a P_λ`.** `piece_mono` already integrates every monomial; what
   remains is the expansion of `∏ (P̂_q + u^q)` with `|λ|` distinguished coordinates, their set
   partitions (`i = j` merges blocks, as the diagonal did here), and placement of each block in a
   class with falling-factorial multiplicities `n_c (n_c − 1) ⋯`, generalizing `sum_place2`.
2. **Moment sharing.** All entries with the same powers `(m, n)` of `U` and `L − S` share the
   moment table `pieceM … A B m`; only the coefficients differ, and they cost the kernel almost
   nothing. A table-driven certificate for many entries at once costs one moment table per
   `(m, n)`, not one per entry (calibration in §7: about 3 s per moment at `m = 2`, rising with
   `m`).
3. **The collapsed per-cell certificate for `J_T(P⋆) − 4 I_T(P⋆)`**, following §7.
