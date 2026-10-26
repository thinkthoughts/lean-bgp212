#!/usr/bin/env python3
"""Emit V2o's one-level certificates for the three-factor nodes of B₂₁ of total degree ≤ DEG_MAX at
Table 3, piece (6, 3) (class sizes (6, 3, 35), shift g = 41/625).

Route (one level). Internal nodes are the two-factor parents: their canonical states are certified
by V2m (5 stored nodes) or staged here from V2m's stored one-factor nodes (StepCert, chunked, with
a literal factor). Each parent's marked profile of order ≤ 1 is read from its certified states
(`markOK_of_tree`, key-range merges, `markOK_congr`). Each leaf (a three-factor multiset) gets its
moment profile by one direct order-0 transition from its parent's marked profile
(`markOK_step_tree`, `profCert_of_markOK`); no state of a leaf is formed.

Literal factors. `markStep`/`symStep` checks use `To_f_q` (the coefficients of P̂_q as literal
rationals) and the bridge `To_fe_q : stepFactor g q = To_f_q`: the kernel then never re-expands
(x + g)^q per entry (a measured 29× saving at q = 10).

Files: Solution/SymReadFactors.lean (literal factors and bridges); Solution/SymReadCert/:
  D_<p>_d<k>, D_<p>        states of a staged parent (data);
  T_<p>_<j>, T_<p>         staged step chunks and the chain of the parent;
  Q_<p>_<j>_<k>            marked profile (order ≤ 1) of a slice of the parent's states, as key-range slices;
  P_<p>_d<k>, P_<p>        the parent's marked profile (data, chunked within key ranges);
  M_<p>_<r>, A_<p>         key-range merges and MarkOK of the parent;
  S_<m>_<j>                one direct order-0 step of the leaf m over consecutive parent chunks;
  R_<m>_<g>, F_<m>, A_<m>  leaf merges, the leaf's moment profile check, ProfCert of the leaf;
Solution/SymReadProfData.lean (profiles, data only), Solution/SymReadNodes.lean (ProfOK and
agreement with V2m and V2n), Solution/SymReadTab*.lean, Solution/SymReadDemo1–2.lean, and
specs/checks/sym_read_v2o_build.sh.

Usage: python3 -I specs/checks/sym_read_v2o_demo.py [root]
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_entry_v2i_model as Q  # noqa: E402
import sym_profile_v2n_demo as N  # noqa: E402
import sym_profile_v2n_model as M  # noqa: E402
import sym_reduce_v2k_model as S  # noqa: E402
import sym_staged_v2l_demo as V  # noqa: E402
import sym_trie_v2m_demo as D  # noqa: E402

HDR = V.HDR
DEG_MAX = 26         # three-factor multisets of total degree ≤ DEG_MAX
GEN_B = 900          # generated states per staged step check (as V2m)
STAT_B = 1100        # (state, tuple) pairs per marked-profile check
EMIT_B = 1500        # emitted entries per direct-step check (literal factor)
DATA_B = 1500        # marked entries per data chunk
DMOD_B = 2000        # marked entries per data module
RANGE_B = 1200       # input entries per key-range merge
MERGE_K = 4          # results per leaf merge check
N3 = "(clsCount 44 6 3)"
OPEN = "open BGP212.Params\n\nset_option maxRecDepth 20000\n\n"
PDATA = "Solution.SymReadProfData"
PDATA_B = 250000     # bytes of profile literals per data module
FACT = "Solution.SymReadFactors"
ident, qlist, menc, merge, split_by, f2, fac = N.ident, N.qlist, N.menc, N.merge, N.split_by, N.f2, N.fac


def three_multisets():
    kall = D.kept(lambda l: True)
    return sorted({tuple(sorted(x + y, reverse=True)) for x in kall for y in kall if len(x) + len(y) == 3})


def ql(l):
    return "[" + ", ".join(f"(({x.numerator} : ℚ) / {x.denominator})" for x in l) + "]"


def rank(e):
    return e[0][0] * 1024 + e[0][1]


def in_rng(e, lo, hi):
    return rank(e) >= lo and (hi is None or rank(e) < hi)


class Plan:
    def __init__(self):
        self.T = D.Trie()
        T = self.T
        self.all3 = three_multisets()
        self.leaves = [m for m in self.all3 if sum(m) <= DEG_MAX]
        self.parents = sorted({m[:2] for m in self.leaves}, key=lambda m: (sum(m), m))
        self.v2m_stored = set(T.stored)
        for p in self.parents:
            assert p[:1] in self.v2m_stored and p in T.L
        self.P1 = {p: M.aug_lean(1, T.L[p]) for p in self.parents}
        self.kids = {p: [m for m in self.leaves if m[:2] == p] for p in self.parents}
        self.prof = {}
        for m in self.leaves:
            P0 = M.step_lean(0, N.NCLS, fac(m[2]), self.P1[m[:2]])
            self.prof[m] = M.to_prof(P0)
            Lm = S.normalize(T.step_entries(T.L[m[:2]], m[2]))          # Python check only
            assert self.prof[m] == V.prof(Lm), m
        self.qs = sorted({m[2] for m in self.leaves} | {p[1] for p in self.parents if p not in self.v2m_stored})


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    pl = Plan()
    T = pl.T
    d = os.path.join(root, "Solution", "SymReadCert")
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))
    order = []
    stats = dict(staged_gen=0, staged_states=0, tuples=0, emitted=0, max_emit=0)
    mod = lambda s: f"Solution.SymReadCert.{s}"  # noqa: E731
    base = ["BGP212.SymRead"]

    def write(name, imports, doc, body):
        txt = (HDR + "".join(f"import {i}\n" for i in dict.fromkeys(imports)) + "\n" +
               f"/-! # V2o: {doc} (generated by `specs/checks/sym_read_v2o_demo.py`) -/\n\n"
               "namespace BGP212.V2e\n\n" + OPEN + "\n".join(body) + "\nend BGP212.V2e\n")
        open(os.path.join(d, f"{name}.lean"), "w").write(txt)
        order.append(mod(name))
        return mod(name)

    # literal factors and bridges
    fl = [HDR + "import BGP212.SymRead\n\n/-! # V2o: the factors P̂_q at Table 3 as literal coefficient lists, and the\n"
          "bridges `stepFactor g q = To_f_q` (generated by `specs/checks/sym_read_v2o_demo.py`) -/\n\n"
          "namespace BGP212.V2e\n\n" + OPEN]
    for q in pl.qs:
        f = fac(q)
        fl.append(f"/-- The coefficients of `P̂_{q}` in the three classes. -/\n"
                  f"def To_f_{q} : Fin 3 → List ℚ := ![{ql(f(0))},\n  {ql(f(1))},\n  {ql(f(2))}]\n")
        fl.append(f"theorem To_fe_{q} : stepFactor g {q} = To_f_{q} := by\n  funext c; fin_cases c <;> decide +kernel\n")
    open(os.path.join(root, "Solution", "SymReadFactors.lean"), "w").write("\n".join(fl) + "\nend BGP212.V2e\n")
    order.append(FACT)
    # leaf profile data (light), split into parts by size
    parts, cur, size = [], [], 0
    for m in pl.leaves:
        dfn = f"def To_R_{ident(m)} : List ((ℕ × ℕ) × ℚ) := {V.penc(pl.prof[m])}\n"
        if cur and size + len(dfn) > PDATA_B:
            parts.append(cur)
            cur, size = [], 0
        cur.append(dfn)
        size += len(dfn)
    parts.append(cur)
    for j, part in enumerate(parts):
        open(os.path.join(root, "Solution", f"SymReadProfData{j}.lean"), "w").write(
            HDR + "import BGP212.SymRead\n\n/-! # V2o: moment profiles of the three-factor leaves, data part "
            f"{j} (generated by `specs/checks/sym_read_v2o_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN +
            "\n".join(part) + "\nend BGP212.V2e\n")
        order.append(f"{PDATA}{j}")
    plit = "[" + ", ".join(f"({qlist(m)}, To_R_{ident(m)})" for m in reversed(pl.leaves)) + "]"
    open(os.path.join(root, "Solution", "SymReadProfData.lean"), "w").write(
        HDR + "".join(f"import {PDATA}{j}\n" for j in range(len(parts))) + "import Solution.SymTrieProfData\n\n"
        "/-! # V2o: the moment profiles of the three-factor leaves (data; certified in `Solution/SymReadCert/`,\n"
        "assembled in `Solution/SymReadNodes.lean`) (generated by `specs/checks/sym_read_v2o_demo.py`) -/\n\n"
        "namespace BGP212.V2e\n\n" + OPEN +
        "/-- **Definition (one-level profiles).** The moment profiles of the three-factor multisets of degree\n"
        f"`≤ {DEG_MAX}`, certified by one direct transition each (`To_prof_ok`). -/\n"
        f"def To_prof : List (List ℕ × List ((ℕ × ℕ) × ℚ)) :=\n  {plit}\n\n"
        "/-- **Definition.** V2o's profiles together with V2m's (`To_all_ok`). -/\n"
        "def To_all : List (List ℕ × List ((ℕ × ℕ) × ℚ)) := To_prof ++ Tt_prof\n\nend BGP212.V2e\n")
    order.append(PDATA)

    chain = {}      # parent -> (states chunk names with data, chain theorem, modules)
    # staged parents
    for p in pl.parents:
        i, x, y = ident(p), p[:1], p[1]
        if p in pl.v2m_stored:
            chain[p] = ([(T.lname(p, j), c, f"Solution.SymTrieCert.D_{i}") for j, c in enumerate(T.chunks[p])],
                        f"Tt_c_{i}", [f"Solution.SymTrieCert.S_{i}"], T.lname(p))
            continue
        Lp = T.L[p]
        stats["staged_states"] += len(Lp)
        Ds, smods = [], []
        for j, (cn, cd) in enumerate(zip(T.pchunks(x), T.pchunk_data(x))):
            gen = T.step_entries(cd, y)
            stats["staged_gen"] += len(gen)
            assert len(gen) <= GEN_B * 1.5, (p, len(gen))
            Dj = S.normalize(gen)
            Ds.append(Dj)
            smods.append(write(f"T_{i}_{j}", [f"Solution.SymTrieCert.D_{ident(x)}", FACT, "Solution.SymStaged"] + base,
                               f"staged step to {qlist(p)}, chunk {j}",
                               [f"def To_D_{i}_{j} : List (SKey × ℚ) :=\n  {V.enc(Dj)}\n",
                                f"theorem To_t_{i}_{j} : StepCert {N3} To_f_{y} {cn} To_D_{i}_{j} :=\n"
                                "  stepCert_of_beq _ _ _ _ (by decide +kernel)\n"]))
        assert V.merge_all(Ds) == Lp
        cs = V.split(Lp, 600)
        dnames = [f"To_L_{i}_c{j}" for j in range(len(cs))]
        dm = write(f"D_{i}", base, f"the states of the staged parent {qlist(p)}",
                   [f"def {dnames[j]} : List (SKey × ℚ) :=\n  {V.enc(c)}\n" for j, c in enumerate(cs)] +
                   [f"def To_L_{i} : List (SKey × ℚ) :=\n  [{', '.join(dnames)}].flatten\n"])
        k = len(Ds)
        body = [f"/-- The canonical states of the internal node `{qlist(p)}`, staged from V2m's `{qlist(x)}`. -/\n"
                f"theorem To_c_{i} : ChainCert {N3} (psFactors g {qlist(p)}) [([], 1)] To_L_{i} :=\n"
                f"  chainCert_snoc {N3} g {qlist(x)} {y} _ _ _ Tt_c_{ident(x)} (by\n"
                f"    show StepCert {N3} (stepFactor g {y}) _ _\n    rw [To_fe_{y}]\n"
                f"    exact stepCert_runs {N3} To_f_{y} [{', '.join(T.pchunks(x))}]\n"
                f"      [{', '.join(f'To_D_{i}_{j}' for j in range(k))}] To_L_{i}\n"
                f"      {f2([f'To_t_{i}_{j}' for j in range(k)])}\n      (by decide +kernel))\n"]
        cm = write(f"T_{i}", smods + [dm, f"Solution.SymTrieCert.S_{ident(x)}"], f"the chain of the staged parent {qlist(p)}", body)
        chain[p] = ([(dnames[j], cs[j], dm) for j in range(len(cs))], f"To_c_{i}", [cm], f"To_L_{i}")

    pnames, markmod = {}, {}
    # parents: marked profiles of order ≤ 1 from their certified states
    for p in pl.parents:
        i = ident(p)
        schunks, cthm, cmods, lname = chain[p]
        Ls, items = [], []
        tup = lambda st: 1 + len(st[0])  # noqa: E731
        for cj, (cn, c, cmod_) in enumerate(schunks):
            for sj, sub in enumerate(split_by(list(range(len(c))), lambda k_: tup(c[k_]), STAT_B)):
                a0, a1 = sub[0], sub[-1] + 1
                expr = cn if (a0 == 0 and a1 == len(c)) else f"((({cn}).drop {a0}).take {a1 - a0})"
                part = c[a0:a1]
                stats["tuples"] += sum(tup(st) for st in part)
                Ls.append(expr)
                items.append((f"To_Q_{i}_{cj}_{sj}", M.aug_lean(1, part), f"{cj}_{sj}", expr, cmod_))
        P1 = pl.P1[p]
        assert merge([it[1] for it in items]) == P1
        cnt = {}
        for it in items:
            for e in it[1]:
                cnt[rank(e)] = cnt.get(rank(e), 0) + 1
        bs, cur = [], 0
        for r in sorted(cnt):
            if cur and cur + cnt[r] > RANGE_B:
                bs.append(r)
                cur = 0
            cur += cnt[r]
        rng = list(zip([0] + bs, bs + [None]))
        # data, chunked within ranges so that every child's step on a chunk emits ≤ EMIT_B
        kids = pl.kids[p]
        cost = lambda e: max(len(M.emit(0, N.NCLS, fac(m[2]), [e])) for m in kids)  # noqa: E731
        chunks, per_range = [], []
        for lo, hi in rng:
            sl = [e for e in P1 if in_rng(e, lo, hi)]
            js = []
            for part in split_by(sl, cost, EMIT_B):
                for k_ in range(0, len(part), DATA_B):
                    js.append(len(chunks))
                    chunks.append(part[k_:k_ + DATA_B])
            per_range.append(js)
        names = [f"To_P_{i}_c{j}" for j in range(len(chunks))]
        dmods, cmod = [], {}
        for grp in split_by(list(range(len(chunks))), lambda j: len(chunks[j]), DMOD_B):
            m_ = write(f"P_{i}_d{len(dmods)}", base, f"the marked profile of {qlist(p)}, order ≤ 1 (data part {len(dmods)})",
                       [f"def {names[j]} : List (MarkKey × ℚ) :=\n  {menc(chunks[j])}\n" for j in grp])
            dmods.append(m_)
            for j in grp:
                cmod[j] = m_
        pm = write(f"P_{i}", dmods, f"the marked profile of {qlist(p)}, order ≤ 1 (data)",
                   [f"def To_P_{i} : List (MarkKey × ℚ) :=\n  [{', '.join(names)}].flatten\n"])
        pnames[p] = [(names[j], chunks[j], cmod[j]) for j in range(len(chunks))]
        # Q modules with range slices
        results, snames = [], []
        for nm, Qd, tag, expr, cmod_ in items:
            sl = [[e for e in Qd if in_rng(e, lo, hi)] for lo, hi in rng]
            sn = {r: f"{nm}_r{r}" for r, x_ in enumerate(sl) if x_}
            body = [f"def {sn[r]} : List (MarkKey × ℚ) :=\n  {menc(x_)}\n" for r, x_ in enumerate(sl) if x_]
            body.append(f"def {nm} : List (MarkKey × ℚ) :=\n  [{', '.join(sn[r] for r in sorted(sn))}].flatten\n")
            body.append(f"theorem To_q_{i}_{tag} : markProfile 1 {expr} = {nm} := by\n  decide +kernel\n")
            results.append((nm, Qd, write(f"Q_{i}_{tag}", [cmod_] + base, f"marked profile of a slice of the states of {qlist(p)}", body)))
            snames.append(sn)
        kms, kthms = [], []
        for r, ((lo, hi), js) in enumerate(zip(rng, per_range)):
            srcs = [(snames[j][r], results[j][2]) for j in range(len(results)) if r in snames[j]]
            assert merge([[e for e in results[j][1] if in_rng(e, lo, hi)] for j in range(len(results))]) == \
                [e for j in js for e in chunks[j]]
            kms.append(write(f"M_{i}_{r}", [s_[1] for s_ in srcs] + [cmod[j] for j in js] + ["Solution.SymProfileSplit"],
                             f"merge of the range-{r} slices of the marked profile of {qlist(p)}",
                             [f"theorem To_k_{i}_{r} : mergeAll markCmp 64 [{', '.join(s_[0] for s_ in srcs)}] =\n"
                              f"    [{', '.join(names[j] for j in js)}].flatten := by\n  decide +kernel\n"]))
            kthms.append(f"To_k_{i}_{r}")
        qn = [r_[0] for r_ in results]
        hL = "rfl" if Ls == [s_[0] for s_ in schunks] else "(by decide +kernel)"
        inner = (f"markOK_of_tree _ g {qlist(p)} 1 {lname}\n"
                 f"    [{', '.join(Ls)}]\n    [{', '.join(qn)}]\n"
                 f"    [{', '.join('[' + x_ + ']' for x_ in qn)}]\n"
                 f"    [{', '.join(qn)}] (mergeAll markCmp 64 [{', '.join(qn)}])\n"
                 f"    {cthm} {hL}\n    {f2(['To_q_' + i + '_' + it[2] for it in items])}\n    rfl\n"
                 f"    {f2(['rfl'] * len(qn))}\n    rfl")
        hs = "\n".join(f"  have e{r} := merge_slices_val _ _ {k_} F" for r, k_ in enumerate(kthms))
        es = " ".join(f"e{r}" for r in range(len(kthms)))
        body = [f"/-- The marked profile of order `≤ 1` of the internal node `{qlist(p)}`, from its certified states. -/\n"
                f"theorem To_m_{i} : MarkOK {N3} g {qlist(p)} 1 To_P_{i} := by\n"
                f"  refine markOK_congr _ g {qlist(p)} 1 _ _\n    ({inner}) fun F => ?_\n{hs}\n"
                f"  simp only [mergeAll_markVal, To_P_{i}, {', '.join(qn)}, sum_flatten_val, List.map_cons,\n"
                f"    List.map_nil, List.sum_cons, List.sum_nil] at {es} ⊢\n"
                f"  linear_combination {' + '.join(f'e{r}' for r in range(len(kthms)))}\n"]
        markmod[p] = write(f"A_{i}", kms + [pm] + cmods + ["Solution.SymProfileSplit"] + [r_[2] for r_ in results],
                           f"MarkOK of the internal node {qlist(p)}", body)

    # leaves: one direct order-0 transition each
    for m in pl.leaves:
        i, p, q = ident(m), m[:2], m[2]
        pch = pnames[p]
        groups, cur, tot = [], [], 0
        for j, (cn, cd, cm) in enumerate(pch):
            em = len(M.emit(0, N.NCLS, fac(q), cd))
            if cur and tot + em > EMIT_B:
                groups.append(cur)
                cur, tot = [], 0
            cur.append(j)
            tot += em
        groups.append(cur)
        results, Cs = [], []
        for gj, js in enumerate(groups):
            CC = [e for j in js for e in pch[j][1]]
            em = len(M.emit(0, N.NCLS, fac(q), CC))
            stats["emitted"] += em
            stats["max_emit"] = max(stats["max_emit"], em)
            Dd = M.step_lean(0, N.NCLS, fac(q), CC)
            cexpr = f"([{', '.join(pch[j][0] for j in js)}].flatten)"
            Cs.append(cexpr)
            results.append((f"To_D_{i}_{gj}", Dd,
                            write(f"S_{i}_{gj}", [pch[j][2] for j in js] + [FACT] + base,
                                  f"direct step to {qlist(m)}, parent chunks {js[0]}–{js[-1]}",
                                  [f"def To_D_{i}_{gj} : List (MarkKey × ℚ) :=\n  {menc(Dd)}\n",
                                   f"theorem To_s_{i}_{gj} : markStep {N3} To_f_{q} 0\n"
                                   f"    ({cexpr}.filter fun e => decide (e.1.2.2.length ≤ 1)) = To_D_{i}_{gj} := by\n"
                                   "  decide +kernel\n"])))
        # merges
        grs = V.split(results, MERGE_K)
        Rs = []
        for gi, grp in enumerate(grs):
            if len(grp) == 1:
                Rs.append((grp[0][0], grp[0][1], grp[0][2], "rfl"))
                continue
            Rg = merge([r_[1] for r_ in grp])
            nm = f"To_G_{i}_{gi}"
            Rs.append((nm, Rg, write(f"R_{i}_{gi}", [r_[2] for r_ in grp] + base, f"merge {gi} of the steps to {qlist(m)}",
                                     [f"def {nm} : List (MarkKey × ℚ) :=\n  {menc(Rg)}\n",
                                      f"theorem To_g_{i}_{gi} : mergeAll markCmp 64 [{', '.join(r_[0] for r_ in grp)}] = {nm} := by\n"
                                      "  decide +kernel\n"]), f"To_g_{i}_{gi}"))
        assert M.to_prof(merge([r_[1] for r_ in Rs])) == pl.prof[m]
        fm = write(f"F_{i}", [r_[2] for r_ in Rs] + [PDATA] + base, f"the moment profile of {qlist(m)}",
                   [f"theorem To_fin_{i} : markToProf (mergeAll markCmp 64 [{', '.join(r_[0] for r_ in Rs)}]) = To_R_{i} := by\n"
                    "  decide +kernel\n"])
        hP = f"(by simp only [To_P_{ident(p)}, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil])"
        steps = [f"(by rw [To_fe_{q}]; exact To_s_{i}_{gj})" for gj in range(len(results))]
        mk = (f"markOK_step_tree _ g {qlist(p)} {q} 0 1 (by decide) To_P_{ident(p)}\n"
              f"    [{', '.join(Cs)}]\n    [{', '.join(r_[0] for r_ in results)}]\n"
              f"    [{', '.join('[' + ', '.join(r_[0] for r_ in grp) + ']' for grp in grs)}]\n"
              f"    [{', '.join(r_[0] for r_ in Rs)}] (mergeAll markCmp 64 [{', '.join(r_[0] for r_ in Rs)}])\n"
              f"    To_m_{ident(p)} {hP}\n    {f2(steps)}\n    rfl\n    {f2([r_[3] for r_ in Rs])}\n    rfl")
        body = [f"/-- The moment profile of the leaf `{qlist(m)}` by one direct transition from `{qlist(p)}`. -/\n"
                f"theorem To_pc_{i} : ProfCert {N3} g {qlist(m)} To_R_{i} :=\n"
                f"  To_fin_{i} ▸ profCert_of_markOK _ g {qlist(m)} _\n  ({mk})\n"]
        markmod[m] = write(f"A_{i}", [fm, markmod[p], FACT, "Solution.SymProfileSplit"] + [r_[2] for r_ in results],
                           f"the certificate of the leaf {qlist(m)}", body)
    # assembly
    ppf = "(profOK_nil _ g)"
    for m in pl.leaves:
        ppf = f"(profOK_cons _ g _ {qlist(m)} _ To_pc_{ident(m)}\n    {ppf})"
    same2 = [m for m in pl.leaves if m in T.L and m in set(T.nodes)]
    import sym_profile_v2n_demo as NN
    o = [HDR + "import Solution.SymTrieNodes\nimport Solution.SymProfileProfData\n" + f"import {PDATA}\n" +
         "".join(f"import {markmod[m]}\n" for m in pl.leaves) + "\n"
         f"/-! # V2o: the one-level certificates of the three-factor nodes of degree ≤ {DEG_MAX} at Table 3, piece (6, 3)\n\n"
         "(generated by `specs/checks/sym_read_v2o_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN,
         f"theorem To_prof_ok : ProfOK {N3} g To_prof :=\n  {ppf}\n",
         f"theorem To_all_ok : ProfOK {N3} g To_all := profOK_append _ g _ _ To_prof_ok Tt_prof_ok\n"]
    v2m_same = [m for m in pl.leaves if m in set(T.nodes)]
    pln = NN.Plan()
    v2n_same = [m for m in pl.leaves if m in pln.aug]
    for m in v2m_same:
        assert pl.prof[m] == V.prof(T.L[m])
    for m in v2n_same:
        assert pl.prof[m] == pln.prof[m]
    o.append("/-! **Agreement with V2m and V2n.** The one-level profiles of the three-factor nodes that V2m\n"
             "(staged states) or V2n (multi-level direct transitions) also certified are identical. -/\n")
    for m in v2m_same:
        o.append(f"theorem To_same_v2m_{ident(m)} : To_R_{ident(m)} = Tt_P_{ident(m)} := by\n  decide +kernel\n")
    for m in v2n_same:
        o.append(f"theorem To_same_v2n_{ident(m)} : To_R_{ident(m)} = Tn_R_{ident(m)} := by\n  decide +kernel\n")
    o.append("end BGP212.V2e\n")
    open(os.path.join(root, "Solution", "SymReadNodes.lean"), "w").write("\n".join(o))
    demos = write_demos(root, pl)
    order_all = order + ["Solution.SymReadNodes"] + demos
    sh = ["#!/usr/bin/env bash",
          "# V2o: build the one-level certificates one `lean` process at a time (for a 3.8 GiB machine",
          "# without swap). Requires V2m's certificates (specs/checks/sym_trie_v2m_build.sh) and V2n's profile",
          "# data (Solution.SymProfileProfData, built by specs/checks/sym_profile_v2n_build.sh or alone).",
          "set -euo pipefail",
          "lake build Solution.SymRead Solution.SymProfileSplit Solution.SymProfileProfData",
          "for m in \\"] + [f"  {x} \\" for x in order_all] + ["  ; do", "  echo \"== $m\"", "  lake build \"$m\"", "done",
                                                          "lake build Solution.SymReadSuite Challenge.SymRead", ""]
    os.makedirs(os.path.join(root, "specs", "checks"), exist_ok=True)
    bp = os.path.join(root, "specs", "checks", "sym_read_v2o_build.sh")
    open(bp, "w").write("\n".join(sh))
    os.chmod(bp, 0o755)
    print("leaves", len(pl.leaves), "parents", len(pl.parents), "staged", len([p for p in pl.parents if p not in pl.v2m_stored]),
          "modules", len(order), "v2m_same", len(v2m_same), "v2n_same", len(v2n_same), stats)


PIECE = "(fun A B m n => pieceMn 44 6 3 A B g L τ C m n)"


def ws_lit(ws):
    return "[" + ", ".join(f"(({V.rlit(w)} : ℚ), {a1}, {qlist(l1)}, {a2}, {qlist(l2)})" for (w, a1, l1, a2, l2) in ws) + "]"


def write_demos(root, pl):
    T = pl.T
    hd = lambda imps, doc: (HDR + "".join(f"import {i}\n" for i in imps) + "\n" +  # noqa: E731
                            f"/-! # V2o: {doc}\n\nCOMPUTATIONAL DEMONSTRATION (generated by "
                            "`specs/checks/sym_read_v2o_demo.py`). Tables are coefficient representations;\n"
                            "the rational moments `pieceMn` are evaluated separately. -/\n\nnamespace BGP212.V2e\n\n" + OPEN)
    out = lambda name, parts: open(os.path.join(root, "Solution", f"{name}.lean"), "w").write("\n".join(parts + ["end BGP212.V2e\n"]))  # noqa: E731
    mods = []
    m0 = (10, 8, 8)
    assert m0 in pl.leaves
    out("SymReadDemo1", [hd([PDATA, "Solution.SymTrieKept"], f"coverage of the three-factor nodes of degree ≤ {DEG_MAX}"),
         f"/-- **Coverage.** Every multiset of `B₂₁` with three factors and total degree `≤ {DEG_MAX}` has a\n"
         "profile certified by one direct transition (`To_prof_ok`). -/\n"
         f"theorem To_covers : ((shortMultisets 3).filter fun Q => Q.length = 3 ∧ Q.sum ≤ {DEG_MAX}).all\n"
         "    (fun Q => natListMem Q (To_prof.map Prod.fst)) = true := by\n"
         "  rw [shortMultisets, b21Kept_eq]; decide +kernel\n",
         f"/-- The three-factor multisets of degree `≤ {DEG_MAX}`: {len(pl.leaves)} of the {len(pl.all3)} with three factors. -/\n"
         f"theorem three_counts : ((shortMultisets 3).filter fun Q => Q.length = 3).length = {len(pl.all3)} ∧\n"
         f"    ((shortMultisets 3).filter fun Q => Q.length = 3 ∧ Q.sum ≤ {DEG_MAX}).length = {len(pl.leaves)} := by\n"
         "  rw [shortMultisets, b21Kept_eq]; decide +kernel\n",
])
    mods.append("Solution.SymReadDemo1")
    ws = [(Fr(1), 0, (10,), 0, (8, 8))]
    Tb = D.prof_table(T, ws) if False else None
    groups = {}
    for (w, a1, l1, a2, l2) in ws:
        for (K1, p1, q1, c1) in Q.innerTerms(a1, l1):
            for (K2, p2, q2, c2) in Q.innerTerms(a2, l2):
                key = (tuple(sorted(K1 + K2, reverse=True)), p1 + p2, q1 + q2)
                groups[key] = groups.get(key, Fr(0)) + w * c1 * c2
    acc = {}
    for (Qd, mm, nn), c in sorted(groups.items()):
        P = pl.prof[Qd] if Qd in pl.prof else V.prof(T.L[Qd])
        for (A, B), v in P:
            acc[(A, B, mm, nn)] = acc.get((A, B, mm, nn), Fr(0)) + c * v
    Tb = sorted(acc.items())
    assert Tb == S.gen_table(6, 3, 0, [10], 0, [8, 8])
    out("SymReadTab2", [hd([PDATA], "J_T[P_10, P_(8,8)] at piece (6, 3) (the table)"),
         f"theorem tabO_P10_P88_6_3 : profTable 44 6 3 g To_all {ws_lit(ws)} =\n    ({V.tenc(Tb)}) := by\n  decide +kernel\n"])
    mods.append("Solution.SymReadTab2")
    out("SymReadDemo2", [hd(["Solution.SymReadNodes", "Solution.SymReadTab2"], "J_T[P_10, P_(8,8)] at piece (6, 3)"),
         f"/-- **A leaf by one direct transition.** The moment profile of `{qlist(m0)}` (degree {sum(m0)}), from the\n"
         f"marked profile of order `≤ 1` of `{qlist(m0[:2])}`; no state of `{qlist(m0)}` is formed. -/\n"
         f"theorem profile_10_8_8_direct : ProfCert {N3} g {qlist(m0)}\n    ({V.penc(pl.prof[m0])}) :=\n"
         f"  To_pc_{ident(m0)}\n",
         "/-- **Degree 26.** Piece `(6, 3)` of `J_T[P_10, P_(8,8)]` as an explicit combination of moments, from\n"
         "the one-level profile of `[10, 8, 8]` and V2m's profiles. -/\n"
         "theorem genPieceP10_P88_6_3_expansion : genPiece 44 6 3 g L τ C 0 [10] 0 [8, 8] =\n"
         f"    tableVal ({V.tenc(Tb)})\n      {PIECE} :=\n"
         "  (genPieceWith_eq_profTable 44 6 3 g To_all To_all_ok _ 0 [10] 0 [8, 8]).trans\n"
         f"    (congrArg (fun T => tableVal T {PIECE}) tabO_P10_P88_6_3)\n"])
    mods.append("Solution.SymReadDemo2")
    print("table J_T[P_10, P_(8,8)]:", len(Tb), "keys")
    return mods


if __name__ == "__main__":
    main()
