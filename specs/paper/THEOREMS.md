# Theorem Inventory

**Working paper:** *Exact Rational Integration over Constrained Simplices*
**Project:** [translatepi.ai](https://translatepi.ai/) · [Lean repository](https://github.com/thinkthoughts/lean-bgp212)
**Baseline:** V2j, [implementation commit `a9a8af9`](https://github.com/thinkthoughts/lean-bgp212/commit/a9a8af9), building on V2i [proof commit `a994d73`](https://github.com/thinkthoughts/lean-bgp212/commit/a994d73) and [VPS verification/provenance commit `486cf85`](https://github.com/thinkthoughts/lean-bgp212/commit/486cf85).
**Verification:** V2i completed the full **21/21 VPS Comparator regression**, including its **33-statement** Challenge/Solution suite. The final suite reported `Lean default kernel accepts the solution` and `Your solution is okay!`; `verify.sh` finished with **exit status 0**. The VPS run was logged to `/tmp/bgp212-v2i-full.log`. V2j additionally compiled on the MacBook Pro and its 24-statement Comparator configuration was accepted on both the MacBook Pro and Linux VPS. The Mac used a development substitute for Linux `landrun`, whereas the VPS used its native Linux verification setup. Earlier verification results remain documented below.
**Purpose:** Inventory the central mathematical statements for the paper, with source locations and explicit scope. These are independent formalization results motivated by the bounded-prime-gap argument; the unconditional bound is not claimed here.

## 1. Exact simplex moments

**Lean:** `simplex_integral` — `Solution/SimplexMoment.lean:160`
**Definitions:** `simplex`, `momentR` — `BGP212/SimplexMoment.lean`

For `m : ℕ`, `R : ℝ`, `e : Fin m → ℕ`, and `0 ≤ R`, the simplex

$$
\Delta_m(R)=\{x\in\mathbb R^m:x_i\ge0,\ \sum_i x_i\le R\}
$$

satisfies

$$
\int_{\Delta_m(R)}\prod_{i=1}^m x_i^{e_i}\,dx
=\frac{R^{m+\sum_i e_i}\prod_i e_i!}{(m+\sum_i e_i)!}.
$$

The Lean statement identifies the integral with `momentR m R e`; the displayed closed form follows from that definition. The development includes dimension-zero, negative-radius, zero-radius, volume, and rational-polynomial cases (`poly_integral`, `Solution/SimplexMoment.lean:237`).

## 2. The polynomial basis B₂₁

**Lean:** `genIdx_linearIndependent`, `finrank_B21` — `Solution/Variational.lean:398,410`
**Definitions:** `gen`, `genIdx`, `B21`, `B21Idx` — `BGP212/Variational.lean`

The indexed generators `genIdx : B21Idx → Poly` are linearly independent over `ℚ`, and

$$
\dim_{\mathbb Q}(B_{21})=846.
$$

The proof combines an injective exponent encoding, independence of distinct monomials, and injectivity of polynomial transformations. The rank theorem uses `B21_eq_span` and `card_B21Idx`. **Scope:** dimension of the specified rational polynomial subspace, not a claim about every polynomial on 45 variables.

## 3. General monomial integration over constrained support

**Lean:** `integral_supportT_gen` — `Solution/GramGeneral.lean:344`
**Definitions:** `supportT` — `BGP212/GramEntry.lean`; `gramGen` — `BGP212/GramGeneral.lean`

For arbitrary `N : ℕ`, `g L : ℝ`, `C : ℕ → ℝ`, `e : Fin N → ℕ`, `p : ℕ`, and **`0 ≤ g`**,

$$
\int_{\mathrm{supportT}(N,g,L,C)}
 (L-\sum_i x_i)^p\prod_i x_i^{e_i}\,dx
=\mathrm{gramGen}(N,g,L,C,e,p).
$$

The right side is an explicit finite closed-form expression defined in Lean. It uses rough-set decomposition, inclusion–exclusion, group integrals, and the placement-counting identities `sig_insert`, `sig_union`, and `sig_card`. No specific Table 3 cap function is required for the general theorem.

**Related:** `gramGen_extend` (`Solution/GramGeneral.lean:667`) reduces evaluation to the coordinates with nonzero exponents. This reduction is proved; it does not assert that computing all Gram entries is inexpensive.

## 4. Explicit rational Gram representation

**Lean:** `gram_entry_B21_rat` — `Solution/GramGeneral.lean:522`
**Related:** `gram_entry_gen_list`, `gram_entry_example`, `gram_entry_example_value` — `Solution/GramGeneral.lean:496,753,821`

For all `i j : BGP212.Var.B21Idx`, the integral of the product of the corresponding polynomial generators over the **Table 3, 45-coordinate** constrained support equals the real cast of an explicit finite sum of rational `gramGen` expressions:

$$
\int_{T} \mathrm{eval}(\mathrm{genIdx}(i))
\mathrm{eval}(\mathrm{genIdx}(j))\,dx
=\left(\sum_{\varphi}\mathrm{gramGen}_{\mathbb Q}(\mathrm{expo}(\varphi),i.a+j.a)\right)_{\mathbb R}.
$$

The sum runs over placements of the combined power-sum parts into the 45 coordinates, as specified by the Lean theorem. This is **an exact rational representation for each entry**, not a generated or certified full 846 × 846 matrix. A worked example has an exact rational certificate.

## 5. Marginal-fibre equivalence

**Lean:** `fibre_equiv` — `Solution/Fibre.lean:115`
**Definitions:** `hatSupport`, `endpoint`, `roughCount`, `roughMass` — `BGP212/Fibre.lean`

For `n : ℕ`, `g L τ : ℝ`, `C : ℕ → ℝ`, **`0 ≤ g`**, **`τ ≤ L`**, `x ∈ hatSupport n g τ C`, and any `u : ℝ`,

$$
\mathrm{Fin.snoc}(x,u)\in\mathrm{supportT}(n+1,g,L,C)
\iff 0\le u\le U(x),
$$

where

$$
U(x)=\min\bigl(L-\sum_i x_i,\ \max(g,C(s+1)-\rho_1)\bigr),
$$

with `s = roughCount g x` and `ρ₁ = roughMass g x`.

**Related:** `empty_fibre_neg` and `empty_fibre_cap` (`Solution/Fibre.lean:136,151`) address empty fibres. The cap-violation case additionally requires `CapStep g C` for indices `m ≥ 1` and `0 ≤ C 0`. The Table 3 cap-step facts are separately proved; no zero-to-one cap-step assumption is introduced.

## 6. Marginal identity and inner polynomial integral

**Lean:** `marginal_agrees`, `inner_integral` — `Solution/Fibre.lean:217,240`
**Definitions:** `marginalJ`, `jT` — `BGP212/Fibre.lean`

For `0 ≤ g`, `τ ≤ L`, `CapStep g C`, `0 ≤ C 0`, and continuous `P : (Fin (n+1) → ℝ) → ℝ`, Lean proves

$$
\mathrm{marginalJ}(n,g,L,\tau,C,P)=jT(n,g,L,\tau,C,P).
$$

For arbitrary `U M : ℝ` and `p t : ℕ`, Lean also proves the interval-integral identity

$$
\int_0^U(M-u)^p u^t\,du
=\sum_{j=0}^{p}\binom pj M^{p-j}(-1)^j\frac{U^{t+j+1}}{t+j+1}.
$$

This proves the geometry-to-marginal bridge and the inner polynomial integration step. V2f certifies `J_T[1,1]`, V2g certifies `J_T[P₂,1]`, and V2h certifies `J_T[P₂,P₂]`.

## 7. Two-aggregate Dirichlet integration (V2e-A)

**Lean:** `two_group`, `two_group_fin`, `two_group_poly` — `Solution/Aggregate.lean`
**Related:** `one_group`, `tri_cut`, `aggR_shift`, `aggS_shift`, `stratumEndpoint_shift` — `Solution/Aggregate.lean`
**Definitions:** `aggExp`, `aggConst`, `endpointAgg` — `BGP212/Aggregate.lean`

Partition the `N` coordinates into a nonempty group `R` and a nonempty complement `Rᶜ`. For an exponent vector `t : Fin N → ℕ`, define

$$
\alpha_R=|R|+\sum_{i\in R}t_i-1,\qquad
A_R=\frac{\prod_{i\in R}t_i!}{\alpha_R!}.
$$

with analogous definitions for `Rᶜ`. Let `u₁ = ∑_{i ∈ R} yᵢ` and `u₂ = ∑_{i ∈ Rᶜ} yᵢ`. For a measurable function `h : ℝ × ℝ → ℝ` bounded in absolute value on the aggregate triangle, `two_group_fin` establishes

$$
\int_{\Delta_N(M)}\left(\prod_i y_i^{t_i}\right)h(u_1,u_2)\,dy
=A_R A_{R^c}\int_{\Delta_2(M)}
v_1^{\alpha_R}v_2^{\alpha_{R^c}}h(v_1,v_2)\,dv_1\,dv_2.
$$

Here `v₁, v₂` are integration variables on the two-dimensional triangle; `M` is the real simplex radius. The proof uses Fubini and the one-group weighted simplex identity. **Scope:** both groups must be nonempty for this main identity; separately proved boundary theorems handle one or both groups empty, while `tri_eq_empty` and `quad_eq_empty` address negative radii.

**Exact rational specialization:** `tri_poly` and `two_group_poly` evaluate polynomial aggregate weights in rational arithmetic. `two_group_const` recovers the simplex-moment formula when `h = 1`.

**Worked certificate:** `example_value` evaluates the integral of `y₀ y₂²` over the three-coordinate simplex of radius `1`, restricted by `y₀ ≤ 1/2`, as **`19/7680`**. The controls independently compare that value with the uncut integral `1/360` and reject the incorrect aggregate exponent obtained by dropping the `−1`.

**Endpoint bridge:** On a translated stratum `x = y + g·1_{R∪K}`, the proven shifts express rough mass and remaining mass in terms of `u₁,u₂`. The theorem `stratumEndpoint_shift` expresses the fibre endpoint as

$$
U=\min\bigl(L-(r+k)g-u_1-u_2,\ \max(g,C(r+1)-rg-u_1)\bigr),
$$

where `r = |R|` and `k = |K|`. The cap index comes from the **stratum `R`**, rather than the translated point's rough set `R ∪ K`. A Table 3 control distinguishes the correct stratum endpoint `587/1250` from the union-based value `461/1250`.

`tri_cut` supplies an exact closed form for an aggregate triangle cut by one coordinate threshold. This underlies V2e-B’s polygon cells, V2f’s constant-generator certificate, and V2g’s power-sum entry. V2h extends the calculation to the square of the second power sum; general generators and variational positivity remain future targets.

## 8. Exact polygon-cell integration and the cap branch (V2e-B)

**Lean:** `box_monomial`, `box_capPow`, `box_poly`, `cap_branch_piece`, `cap_branch_r0` — `Solution/CapCell.lean`
**Geometry and endpoint:** `endpointAgg_cap`, `endpointAgg_on_capCell`, `cap_inner`, `capCell_rect_table3` — `Solution/CapCell.lean`
**Definitions:** `boxTri`, `boxVal`, `capPowVal`, `capCell` — `BGP212/CapCell.lean`

For real cell parameters `A`, `B`, `D`, define the capped triangle

$$
\mathrm{boxTri}(A,B,D)=\{(u_1,u_2):0\le u_1\le A,\ 0\le u_2\le B,\ u_1+u_2\le D\}.
$$

For natural exponents `α`, `β`, the Lean theorem `box_monomial` identifies its Lebesgue monomial integral with the finite closed form `boxVal`:

$$
\int_{\mathrm{boxTri}(A,B,D)}u_1^\alpha u_2^\beta\,du_1\,du_2
=\mathrm{boxVal}(A,B,D,\alpha,\beta).
$$

The formula splits the first-coordinate interval at

$$
E=\max(0,\min(A,D-B)),\qquad F=\max(0,\min(A,D)),
$$

and evaluates the resulting polynomial integrals explicitly; its rational specialization is computable over `ℚ`. Related theorems cover rational bivariate polynomials (`box_poly`), powers `(a-u₁)^m` (`box_capPow`), empty or degenerate cells (`boxVal_empty`, `boxVal_nonpos`), and the rectangle case (`boxVal_rect`).

**Cap-branch geometry.** On V2e-A's translated piece, let `r = |R|`, `k = |K|`, and let `u₁,u₂` denote the two aggregate coordinate sums. The cap branch of the fibre endpoint is

$$
U=C(r+1)-rg-u_1
$$

on the cell specified by the vertical and horizontal inequalities

$$
u_1\le C(r+1)-(r+1)g,\qquad u_2\le L-kg-C(r+1),
$$

together with the translated piece constraints. Theorems `endpointAgg_on_capCell`, `cap_inner` and `cap_branch_piece` give the endpoint identity, polynomial inner integral and the exact weighted piece integral via `two_group_fin`. `cap_branch_r0` treats the empty-rough-stratum case.

**Table 3 simplification.** On the cap branch, `S ≤ L-g`; at Table 3, `τ-(L-g)=1/625 > 0`. Consequently the total-mass cut is inactive there, and `capCell_rect_table3` proves that each Table 3 cap cell is a rectangle. The fact that only **59** `(r,k)` cardinality classes contribute is an *exploratory exact enumeration*, not a general kernel-checked count. The particular emptiness result for `r=1`, `k≥7` is kernel-checked.

**Worked rational certificate.** `capPieceT3_value` proves that the cap-branch contribution from the single Table 3 piece `(R,K)=({0},∅)` to the squared-fibre integrand for `J_T(1)` equals

$$
\frac{(L-C(2))^{43}\bigl((C(2)-g)^3-g^3\bigr)}{3\cdot43!}
\approx1.0464\times10^{-70}.
$$

This is **one piece** of the inclusion–exclusion decomposition. V2f assembles the full constant-generator marginal Gram entry across all endpoint branches, and V2g certifies the cross entry `J_T[P₂,1]`, and V2h certifies the power-sum diagonal `J_T[P₂,P₂]`.

## 9. All endpoint branches and the first marginal Gram entry (V2f)

**Lean:** `box_twoPow`, `cells_integral`, `piece_block`, `piece_r0`, `indicator_supportT_strat`, `jT_one_eq`, `jtSum_table3`, `jT_gram_gen00_table3` — `Solution/MarginalEntry.lean`, `Solution/MarginalEntryCert.lean`
**Definitions:** `cellsVal`, `pieceJ`, `jtSum` — `BGP212/MarginalEntry.lean`
**Certificate generator:** `specs/checks/marginal_entry_v2f_emit.py`

**Polygon-cell formula.** V2f partitions each two-aggregate piece into four cells, on which the fibre endpoint `U` equals respectively the cap value `C(r+1)-rg-u₁`, the remaining-mass value `L-(r+k)g-u₁-u₂` on the cap side, the threshold `g`, or the remaining-mass value on the threshold side. The cells are expressed as signed differences of V2e-B `boxTri` regions with clamped boundaries. `box_twoPow` and `cells_integral` establish rational closed forms for polynomial blocks of the form

$$
u_1^\alpha u_2^\beta (p-u_1)^{m_1}(L'-u_1-u_2)^{m_2},$$

and hence for the needed powers of `U` and `L-S`. The one-group boundary stratum is handled by `piece_r0`.

**Stratum-dependent assembly.** `indicator_supportT_strat` extends the inclusion–exclusion decomposition to integrands depending on the rough-coordinate stratum. With the two-aggregate reduction and cardinality counting, `jT_one_eq` proves, for `N ≥ 1`, `0 ≤ g ≤ C(1)`, and `C(N) < N g`, an exact finite expression:

$$
J_T(1)=(N+1)\int_{\widehat T} U(\widehat x)^2\,d\widehat x
=\operatorname{jtSum}(N,g,L,\tau,C,2,0).
$$

Here `J_T(1)` denotes the marginal quadratic form for the constant generator, not all possible polynomial inputs.

**Table 3 rational certificate.** At `N=44`, the constant generator `gen 0 ∅ = 1` has the exact certified diagonal entry

$$
J_T[1,1]=45\int_{\widehat T}U(\widehat x)^2\,d\widehat x
=\frac{196405301342598493830210603911544843582810204587055080769623409436245894353192939488221872912132381844932553462651053065161718578698716871038141}{1754639014639931935040119554335514374776042394821781133834697487172064704619156572107385727576911449432373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}
\approx 1.1193487646\times10^{-55}.
$$

The exact numerator and denominator above are intentionally retained as the Lean certificate’s rational value. `jtSum_table3` evaluates **133 nonempty cardinality-class pieces** with individual kernel-checked lemmas; `pieceJ_tail` and `pieceJ_high` establish vanishing of the others. `jT_gram_gen00_table3` connects the result to the marginal form using `marginal_agrees`. The generator-specific result establishes one diagonal entry. V2g adds the bilinear form and the cross entry `J_T[P₂,1]`; V2h adds the power-sum diagonal; further generator pairs and variational positivity remain targets.

**Verification:** The new eighteenth Comparator suite was accepted by the Lean kernel on the VPS, and the whole regression reported **18/18 accepted**. Four positive and five negative Lean-file controls gave their expected outcomes; the separate altered-Challenge statement was rejected by Comparator in Claude’s fresh-clone test. The 133-piece certificate regenerated byte-identically on the VPS. Monte Carlo, polygon clipping, and low-dimensional grid checks are additional exploratory checks, rather than Lean proofs.

## 10. Bilinear marginal form and a power-sum Gram entry (V2g)

**Lean:** `jTbil_self`, `jTbil_comm`, `inner_P2`, `sum_place`, `piece_P2`, `p2Entry_eq`, `p2EntryVal_table3`, `jT_P2_one_table3` — `Solution/PowerSumEntry.lean`, `Solution/PowerSumEntryCert.lean`
**Definitions:** `jTbil`, `pieceE`, `p2J`, `p2EntryVal` — `BGP212/PowerSumEntry.lean`
**Certificate generator:** `specs/checks/power_sum_entry_v2g_emit.py`

**Bilinear marginal form.** For suitable input functions `F` and `G`, V2g introduces

$$
J_T[F,G]=(N+1)\int_{\widehat T}
\left(\int_0^{U(\widehat x)}F(\widehat x,u)\,du\right)
\left(\int_0^{U(\widehat x)}G(\widehat x,u)\,du\right)\,d\widehat x.
$$

The declarations `jTbil_self` and `jTbil_comm` identify the existing quadratic form with the diagonal and establish symmetry. For the nonconstant generator $P_2=\sum_{i=1}^{45}x_i^2$ paired with $1$, `inner_P2` proves

$$
\int_0^U P_2(\widehat x,u)\,du
=U\widehat P_2+\frac{U^3}{3},
\qquad
J_T[P_2,1]=45\int_{\widehat T}
\left(U^2\widehat P_2+\frac{U^4}{3}\right)\,d\widehat x.
$$

**Translated-coordinate placement.** On a translated piece $x=y+g\mathbf1_{R\cup K}$, the square power sum expands as

$$
\widehat P_2(x)=\sum_i y_i^2+2g\sum_{i\in R\cup K}y_i+g^2|R\cup K|.
$$

The single distinguished coordinate belongs to $R$, $K$, or their complement, with respective multiplicities $r$, $k$, and $N-r-k$. `piece_single`, `sum_place`, and `piece_P2` combine this placement calculation with V2f’s exact rational piece integrals. `p2Entry_eq` supplies a closed form under the hypotheses $N\ge1$, $0\le g\le C(1)$, and $C(N)<Ng$.

**Table 3 certificate.** The Lean theorem `p2EntryVal_table3` evaluates the exact rational entry

$$
J_T[P_2,1]\approx 4.999439687639965\times10^{-57}.
$$

The exact numerator and denominator are preserved in `specs/results/V2g_power_sum_entry.yaml` and the Lean certificate. The certificate contains **266 individually kernel-checked piece lemmas**, two for each of 133 contributing cardinality classes. `jT_one_P2_table3` certifies the symmetric entry, and `jTbil_one_one_table3` checks consistency with V2f's constant entry.

**Verification:** The nineteenth Comparator suite passed the Lean kernel on the VPS, and the full regression produced **19/19 acceptances**. The certificate regenerated byte-identically. Two positive controls were accepted and four intentionally incorrect controls were rejected. The separate altered-Challenge statement-mismatch test was reported rejected in Claude's development environment. Monte Carlo and low-dimensional grid comparisons are exploratory checks. The reported trusted axioms are `propext`, `Quot.sound`, and `Classical.choice`.

**Scope:** V2g uses one distinguished coordinate. V2h extends the placement argument to two distinguished coordinates and their diagonal, as detailed next. General generators, exact coefficients for $P^\star$, and direct variational positivity remain further work.

## 11. Two-coordinate placement and the power-sum-square Gram entry (V2h)

**Lean:** `Solution/PowerSumSquare.lean`, `Solution/PowerSumSquareCert0.lean` through `Solution/PowerSumSquareCert13.lean`, `Solution/PowerSumSquareCertSum.lean`
**Definitions and placement machinery:** `BGP212/PowerSumPlace.lean`, `BGP212/PowerSumSquare.lean`
**Challenge and Comparator:** `Challenge/PowerSumSquare.lean`, `Comparator/power_sum_square_v2h.json`
**Certificate generator and controls:** `specs/checks/power_sq_entry_v2h_emit.py`, `specs/checks/power_sq_entry_v2h_controls.py`
**Result record:** `specs/results/V2h_power_sum_square.yaml`

**Second diagonal entry of the marginal Gram form.** With $P_2=\sum_{i=1}^{45}x_i^2$, $\widehat P_2=\sum_{i=1}^{44}\widehat x_i^2$, and the fibre endpoint $U$, the squared inner polynomial integral expands as

$$
\begin{aligned}
J_T[P_2,P_2]
 &=45\int_{\widehat T}\left(U\widehat P_2+\frac{U^3}{3}\right)^2\,d\widehat x\\
 &=45\int_{\widehat T}\left(U^2\widehat P_2^{\,2}
 +\frac23 U^4\widehat P_2+\frac19 U^6\right)d\widehat x.
\end{aligned}
$$

The new term is $\widehat P_2^{\,2}=\sum_i\sum_j x_i^2x_j^2$. V2h separates the **diagonal** contributions $i=j$, involving $(y_i+s_i)^4$, from the **ordered distinct-coordinate** contributions $i\ne j$, involving $(y_i+s_i)^2(y_j+s_j)^2$, on translated strata. Distinguished coordinates are placed in the three classes $R$, $K$, and the remaining coordinates. For classes of sizes $n_c,n_d$, the ordered distinct placements have multiplicities $n_cn_d$ for $c\ne d$ and $n_c(n_c-1)$ for $c=d$; diagonal placements have multiplicity $n_c$.

**Reusable exact moment table.** For a monomial weight $y^t$ on a piece, the reduction expresses its weighted integral as $(\prod_i t_i!)$ times a shared moment depending on the degrees assigned to rough and smooth groups. The expansion of $\widehat P_2^{\,2}$ needs the moment pairs with total assigned degree at most four: $15$ such pairs per piece. A moment is calculated once and reused across coordinate placements. The certificate is divided into **14 row files** plus an assembly file to control kernel computation and permit resumable builds.

**Table 3 result.** The full V2h Comparator's Lean default-kernel acceptance certifies the rational Table 3 entry recorded in the V2h result YAML:

$$
\boxed{J_T[P_2,P_2]\approx 2.27107\times10^{-58}.}
$$

Together with the V2f and V2g certificates, this gives the symmetric two-generator marginal Gram block for $\{1,P_2\}$:

$$
G_J(1,P_2)=
\begin{pmatrix}
J_T[1,1] & J_T[1,P_2]\\
J_T[P_2,1] & J_T[P_2,P_2]
\end{pmatrix}
\approx
\begin{pmatrix}
1.1193487646\times10^{-55}&4.9994396876\times10^{-57}\\
4.9994396876\times10^{-57}&2.27107\times10^{-58}
\end{pmatrix}.
$$

The numerical Cauchy–Schwarz ratio $J_T[P_2,1]^2/(J_T[1,1]J_T[P_2,P_2])$ is about $0.984$, indicating near-dependence of these two marginal functions. This ratio is a numerical observation; an exact determinant or positivity theorem should be identified separately before being described as kernel certified.

**Verification and computational scope:** The full **27-statement V2h Comparator suite** ended with `Lean default kernel accepts the solution` and `Your solution is okay!` on the VPS. The preceding 19/19 regression was separately documented for V2g; a saved cumulative count for V2h's full 20-suite run was unavailable. The result record documents approximately 10,681 seconds for the certificate build in the development container, a peak of 5.18 GB, and exploratory synthetic-grid and Monte Carlo checks. The numerical controls support the calculation independently of the kernel proof. V2h proves this selected Gram block; the general $846\times846$ marginal matrix and the final variational certificate remain further mathematical targets.

## 12. General polynomial marginal Gram entries (V2i)

**Lean:** `Solution/GenEntry.lean`, `Solution/GenEntryTable.lean`, `Solution/GenEntryCert0.lean` through `Solution/GenEntryCert13.lean`, `Solution/GenEntryCertSum.lean`
**Definitions:** `BGP212/GenEntry.lean`, `BGP212/GenEntryBlock.lean`
**Challenge and Comparator:** `Challenge/GenEntry.lean`, `Comparator/gen_entry_v2i.json`
**Certificate generator, exact model and controls:** `specs/checks/gen_entry_v2i_emit.py`, `specs/checks/gen_entry_v2i_model.py`, `specs/checks/gen_entry_v2i_controls.py`, `specs/checks/gen_entry_v2i_grid.py`
**Result record:** `specs/results/V2i_gen_entry.yaml`

**Every generator pair.** For $G_{a,\lambda}=(L-P_1)^aP_\lambda$ and $M=L-\sum_i\widehat x_i$,

$$
\int_0^U G_{a,\lambda}(\widehat x,u)\,du=\sum_{T\subseteq\lambda}\widehat P_{\lambda\setminus T}\sum_{j=0}^{a}\binom aj(-1)^j\,\frac{M^{a-j}\,U^{s_T+j+1}}{s_T+j+1},\qquad s_T=\sum_{q\in T}q .
$$

After the translation of a piece, $M$ is the $L-S$ factor already integrated by V2f's cells, so $J_T[G_{a_1,\lambda_1},G_{a_2,\lambda_2}]$ is a finite rational combination of integrals $\int_{\text{piece}}\widehat P_Q(y+s)\,U^m(L-S)^n$.

**Placements by induction.** On a piece, $\widehat P_q(y+s)=\sum_i\varphi_q(y_i,\operatorname{cls}i)$ with $\varphi_q(y,c)=(y+\sigma_c)^q$. `piece_place` integrates a product of such sums by induction over the factors: a factor either merges into an already open coordinate (its polynomial is multiplied) or opens a coordinate of class $c\in\{R,K,\text{rest}\}$, with multiplicity $n_c-\#\{\text{open coordinates of class }c\}$. Unrolled, this is the sum over set partitions of the factors with falling-factorial class counts. Every monomial weight against $U^m(L-S)^n$ is a moment $(\prod_it_i!)\,\texttt{pieceMn}(A,B,m,n)$, with $A,B$ the degrees in the rough and smooth groups (`piece_mono_n`).

**General theorem.** `genEntry_eq`: for every $N\ge1$, admissible data and all $(a_1,\lambda_1),(a_2,\lambda_2)$,

$$
J_T[G_{a_1,\lambda_1},G_{a_2,\lambda_2}]=\texttt{genEntryVal}\,N\,g\,L\,\tau\,C\,a_1\,\lambda_1\,a_2\,\lambda_2 ,
$$

and `jT_gen_table3` states that every $B_{21}$ entry at Table 3 is the corresponding rational. The value is linear in the moment oracle, so certificates certify moments once (`tableFn_eq`) and the kernel evaluates only coefficients and placements.

**Evaluated Table 3 entries (kernel-certified rationals).**

| entry | value | moments |
|---|---|---|
| $J_T[P_2,P_2]$, via the general form (`genEntryPP_eq_v2h`) | $2.27107\times10^{-58}$ | V2h's table |
| $J_T[P_4,1]$ | $2.75169\times10^{-59}$ | V2h's table |
| $J_T[P_{(2,2)},1]$ | $2.28799\times10^{-58}$ | V2h's table |
| $J_T[L-P_1,1]$ | $5.52809\times10^{-57}$ | two new moments per piece |

The general closed form reproduces V2h's separately certified $J_T[P_2,P_2]$ exactly. Also exactly, $J_T[P_{(2,2)},1]-J_T[P_2,P_2]=(\tfrac15-\tfrac19)\cdot45\int_{\widehat T}U^6$.

**Verification and computational scope:** The full **33-statement V2i Comparator suite** was accepted by the Lean default kernel on the VPS. The entire `verify.sh` regression recorded **21/21** `Your solution is okay!` acceptances and **exit status 0**; the final V2i suite explicitly reported `Lean default kernel accepts the solution`. The independently verified proof is pinned at commit [`a994d73`](https://github.com/thinkthoughts/lean-bgp212/commit/a994d73), with verification provenance at [`486cf85`](https://github.com/thinkthoughts/lean-bgp212/commit/486cf85). In the development container, the V2i suite took 13,997 s (including replay of V2h moments); the statement-level negative control (`genEntry_eq` with a doubled right side) was rejected, and four positive and four negative Lean controls yielded their expected outcomes. Monte Carlo checks at $N=44$ used $z=0.52$, $0.38$, and $1.06$; these checks are exploratory, not kernel proofs. The development-container certificate build took 1,543 s (peak 3.89 GB). V2i proves the exact representation of every $B_{21}$ entry; evaluating further entries requires their moment tables. The full $846\times846$ numerical matrices, $P^\star$, and the variational certificate remain targets.

## 13. Shared-moment aggregation of Gram entries (V2j)

**Lean:** `Solution/MomentAgg.lean`, `Solution/MomentAggDemo1.lean` through `Solution/MomentAggDemo4.lean`, `Solution/MomentAggSuite.lean`  
**Definitions:** `BGP212/MomentAgg.lean`  
**Challenge and Comparator:** `Challenge/MomentAgg.lean`, `Comparator/moment_agg_v2j.json`  
**Specification and exploratory checks:** `Exploratory/V2j/SPEC.md`, `specs/checks/moment_agg_v2j_demo.py`  
**Result record:** `specs/results/V2j_moment_agg.yaml`

**Shared-moment evaluation.** V2j adds an exact evaluation layer to V2i's general rational marginal Gram-entry representation. Rather than treating each occurrence of a moment independently, it identifies the finite moment keys used by the selected piece and aggregates their rational coefficients. The construction retains V2i's underlying definitions and mathematical scope.

**Formal correctness.** The Lean development proves linearity of `genPieceWith` in its moment oracle, locality with respect to the relevant moment-key set (`genPieceWith_congr`), and agreement between the aggregated coefficient representation and the original weighted Gram-entry expression. In particular, `aggEntryVal_eq` and `jT_weighted_eq_agg` identify the shared-moment calculation with the V2i formulation. These are exact identities, not numerical approximations.

**Exact demonstrations.** Four staged Lean demonstration modules and `MomentAggSuite` build successfully. The exploratory generator records fewer distinct moment keys than the number of repeated calls: for example, the $J_T[P_2,P_2]$ example uses 19 distinct keys across 115 occurrences, while a $J_T[P_{(2,2)},P_{(2,2)}]$ example records 85 distinct keys across 20,542 occurrences. These counts illustrate computational reuse; they do not constitute a claimed bound for every Gram entry.

**Verification.** V2j implementation commit [`a9a8af9`](https://github.com/thinkthoughts/lean-bgp212/commit/a9a8af9) was merged into `main`. On the MacBook Pro, the definitions, central proofs, four demonstration modules, and combined suite compiled successfully. The **24-statement V2j Comparator** independently returned `Your solution is okay!` on both the MacBook Pro and Linux VPS. On macOS, Comparator used `fake-landrun.sh` without Linux sandbox isolation; the VPS supplied the Linux verification environment. The matching Lean 4.34.0-rc2 `lean4export` was built separately from Comparator's Lean 4.35.0 toolchain.

**Scope.** V2j proves correctness of moment reuse and coefficient aggregation for the specified representation. It does not yet evaluate the full $846\times846$ marginal Gram matrix, determine the optimized polynomial $P^\star$, establish the final variational positivity certificate, or yield an unconditional proof of $H_1\le212$.

## Formal verification and provenance

- **Source:** [`thinkthoughts/lean-bgp212`](https://github.com/thinkthoughts/lean-bgp212)
- **V2d:** proof commit `52fd36a`; provenance commit `90055db`.
- **V2e-A:** [proof commit `01644e6`](https://github.com/thinkthoughts/lean-bgp212/commit/01644e6); [VPS provenance commit `38606c0`](https://github.com/thinkthoughts/lean-bgp212/commit/38606c0).
- **V2e-B:** [proof commit `6a21780`](https://github.com/thinkthoughts/lean-bgp212/commit/6a21780); [VPS provenance commit `25a7376`](https://github.com/thinkthoughts/lean-bgp212/commit/25a7376).
- **V2f:** [proof commit `8c50fb6`](https://github.com/thinkthoughts/lean-bgp212/commit/8c50fb6); [VPS provenance commit `da0c3fd`](https://github.com/thinkthoughts/lean-bgp212/commit/da0c3fd).
- **V2g:** [proof commit `ad70abb`](https://github.com/thinkthoughts/lean-bgp212/commit/ad70abb); [VPS provenance commit `12f8b16`](https://github.com/thinkthoughts/lean-bgp212/commit/12f8b16).
- **V2h:** [proof commit `6cef1f4`](https://github.com/thinkthoughts/lean-bgp212/commit/6cef1f4); [VPS provenance commit `a9b0e0c`](https://github.com/thinkthoughts/lean-bgp212/commit/a9b0e0c).
- **V2i:** [proof commit `a994d73`](https://github.com/thinkthoughts/lean-bgp212/commit/a994d73); [VPS provenance commit `486cf85`](https://github.com/thinkthoughts/lean-bgp212/commit/486cf85).
- **V2j:** [implementation commit `a9a8af9`](https://github.com/thinkthoughts/lean-bgp212/commit/a9a8af9); 24-statement Comparator configuration accepted on MacBook Pro and Linux VPS.
- **Toolchain:** Lean `v4.34.0-rc2`; mathlib pinned at `85e3a25` (see repository result YAML files).
- **VPS:** V2g regression: 19/19 Comparator suites accepted; V2h full 27-statement Comparator: default-kernel accepted; cumulative 20/20 count not saved. V2i full 33-statement Comparator: default-kernel accepted on VPS, with 21/21 cumulative acceptances and `verify.sh` exit status 0. V2d: four positive/four negative controls; V2e-A: five positive/four negative; V2e-B: five positive/five negative; V2f: four positive/five negative; V2g: two positive/four negative Lean-file controls. Additional V2f/V2g statement-mismatch tests were reported rejected in Claude’s development environment.
- **Trusted axioms reported for V2d, V2e-A, V2e-B, V2f and V2g:** `propext`, `Quot.sound`, `Classical.choice`.
- **Result records:** [`specs/results`](https://github.com/thinkthoughts/lean-bgp212/tree/main/specs/results).

## Beyond the current theorems

The following are **outstanding**, not conclusions of this inventory:

1. Evaluating further `J_T` Gram entries: V2i proves the exact representation of every $B_{21}$ entry and evaluates four; V2j aggregates shared moment keys, but the remaining entries still need exact moment tables and scalable evaluation.
2. Exact optimized polynomial coefficient data and direct positivity certificates.
3. Remaining analytic/variational hypotheses needed for `DHL[45,2]`.

The project has formally verified the **conditional implication** `DHL[45,2] → H₁ ≤ 212`; it does **not** yet furnish an unconditional Lean proof of `H₁ ≤ 212`.

---

*Admissible generalizations trail leading specifications. · PiπΠ*
