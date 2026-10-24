#!/usr/bin/env python3
"""Emit V2n's direct moment-profile certificates for the block |λ| ≤ 8 of B₂₁ at Table 3, piece (6, 3).

Route. The 52 multisets of the block |λ| ≤ 8 (`blockMultisets 8`): 27 have V2m profiles, 25 are new.
Every prefix of a new multiset that is not a V2m stored node is a *direct node* (34): its marked
profile of order = (its height in the direct subtree) is obtained from its parent's by `markStep`,
never forming states. The parents at the top are V2m stored nodes (*sources*, 8): their certified
states give marked profiles directly (`markProfile`, chunk by chunk). Each direct node's order-0
part is its moment profile (`profCert_of_markOK`); the 9 direct nodes that V2m also certified are
checked against V2m's staged profiles.

Files (Solution/SymProfileCert/):
  Q_<s>_<j>_<k>  marked profile of a slice of the states of a source s (V2m's certified states), as the
                 concatenation of its key-range slices (data and check);
  S_<x>_<j>      one direct step: a chunk of the parent's marked profile to a chunk result of x (for
                 internal nodes, as the concatenation of its key-range slices);
  P_<x>_d<k>     the marked profile of an internal node x, data part k (chunks within key ranges);
  P_<x>          the marked profile of x as the list of its chunks (data only);
  M_<x>_<r>      the merge of the range-r slices of the chunk results of x (check: equals the chunks of
                 x in range r) — only the slices of one range enter each check;
  R_<x>_<g>, F_<x>  group merges and the final moment-profile check of a leaf x;
  A_<x>          MarkOK of x (internal: by `markOK_congr`, regrouping the range merges with
                 `linear_combination`) or ProfCert of x (leaves);
  G_<x>          the moment profile of an internal node x (order 0 of its marked profile).
Then Solution/SymProfileNodes.lean, Solution/SymProfileTab*.lean, Solution/SymProfileDemo1, 2, 4.lean
and specs/checks/sym_profile_v2n_build.sh (sequential build).

Usage: python3 -I specs/checks/sym_profile_v2n_demo.py [root]
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_entry_v2i_model as Q  # noqa: E402
import sym_profile_v2n_model as M  # noqa: E402
import sym_reduce_v2k_model as S  # noqa: E402
import sym_staged_v2l_demo as V  # noqa: E402
import sym_trie_v2m_demo as D  # noqa: E402

HDR = V.HDR
PDATA2 = "Solution.SymProfileProfData"
EMIT_B = 1100        # emitted entries per direct-step check
STAT_B = 1100        # (state, tuple) pairs per marked-profile check of a source chunk
DATA_B = 1500        # entries per data chunk
MERGE_K = 4          # results per merge check (leaves)
RANGE_B = 1200       # input entries per range-merge check (internal nodes)
DMOD_B = 2000        # marked entries per data module
PART_B = 120000      # bytes of looked-up profiles per table part (as V2m)
N3 = "(clsCount 44 6 3)"
OPEN = "open BGP212.Params\n\nset_option maxRecDepth 20000\n\n"
G = Fr(41, 625)
SIG = [G, G, Fr(0)]
NCLS = [6, 3, 35]


def fac(q):
    return lambda c: Q.shiftPow(SIG[c], q)


def ident(m):
    return "_".join(map(str, m)) if m else "root"


def qlist(m):
    return "[" + ", ".join(map(str, m)) + "]"


def menc(P):
    out = []
    for (A, B, u), v in P:
        v = Fr(v)
        out.append("[" + ", ".join(map(str, [A, B, 0 if v >= 0 else 1, abs(v.numerator), v.denominator] +
                                       [x for ce in u for x in ce])) + "]")
    return "decMark [" + ",\n    ".join(out) + "]"


def merge(Ps):
    acc = {}
    for P in Ps:
        for k, v in P:
            acc[k] = acc.get(k, Fr(0)) + v
    return M.lean_sorted(acc)


def split_by(items, cost, budget):
    out, cur, tot = [], [], 0
    for x in items:
        c = cost(x)
        if cur and tot + c > budget:
            out.append(cur)
            cur, tot = [], 0
        cur.append(x)
        tot += c
    out.append(cur)
    return out


def f2(names):
    return "".join(f"(List.Forall₂.cons {x} " for x in names) + "List.Forall₂.nil" + ")" * len(names)


class Plan:
    def __init__(self):
        self.T = D.Trie()
        T = self.T
        self.v2m = set(T.nodes)
        self.stored = set(T.stored) | {()}
        k8 = D.kept(lambda l: sum(l) <= 8)
        self.b8 = sorted({tuple(sorted(x + y, reverse=True)) for x in k8 for y in k8}, key=lambda m: (len(m), m))
        self.new = [m for m in self.b8 if m not in self.v2m]
        aug = set()
        for m in self.new:
            for i in range(len(m) + 1):
                if m[:i] not in self.stored:
                    aug.add(m[:i])
        self.aug = sorted(aug, key=lambda m: (len(m), m))
        self.children = {}
        for a in self.aug:
            self.children.setdefault(a[:-1], []).append(a)
        self.order = {}
        for a in sorted(self.aug, key=len, reverse=True):
            ch = self.children.get(a, [])
            self.order[a] = 0 if not ch else 1 + max(self.order[c] for c in ch)
        self.src = sorted({a[:-1] for a in self.aug if a[:-1] in self.stored}, key=lambda m: (len(m), m))
        for s in self.src:
            self.order[s] = 1 + max(self.order[c] for c in self.children[s])
        # states (Python only, for the checks against V2k and V2m)
        for m in self.b8:
            if m not in T.L:
                T.L[m] = S.normalize(T.step_entries(T.L[m[:-1]], m[-1]))
        self.P = {}
        for s in self.src:
            self.P[s] = M.aug_lean(self.order[s], T.L[s])
        for a in self.aug:
            p = a[:-1]
            PP = [e for e in self.P[p] if len(e[0][2]) <= self.order[a] + 1]
            self.P[a] = M.step_lean(self.order[a], NCLS, fac(a[-1]), PP)
            assert {k: v for k, v in self.P[a] if v != 0} == M.aug(self.order[a], T.L[a])
        self.prof = {a: M.to_prof([e for e in self.P[a] if len(e[0][2]) == 0]) for a in self.aug}
        for a in self.aug:
            if a in self.v2m:
                assert self.prof[a] == V.prof(T.L[a]), a


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    pl = Plan()
    T = pl.T
    d = os.path.join(root, "Solution", "SymProfileCert")
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))
    order = []
    mod = lambda s: f"Solution.SymProfileCert.{s}"  # noqa: E731
    stats = dict(stat_mods=0, step_mods=0, merge_mods=0, data_mods=0, final_mods=0, asm_mods=0,
                 emitted=0, tuples=0, max_emit=0)

    def write(name, imports, doc, body):
        txt = (HDR + "".join(f"import {i}\n" for i in dict.fromkeys(imports)) + "\n" +
               f"/-! # V2n: {doc} (generated by `specs/checks/sym_profile_v2n_demo.py`) -/\n\n"
               "namespace BGP212.V2e\n\n" + OPEN + "\n".join(body) + "\nend BGP212.V2e\n")
        open(os.path.join(d, f"{name}.lean"), "w").write(txt)
        order.append(mod(name))
        return mod(name)

    base = ["BGP212.SymProfile"]
    plit = "[" + ", ".join(f"({qlist(a)}, Tn_R_{ident(a)})" for a in reversed(pl.aug)) + "]"
    open(os.path.join(root, "Solution", "SymProfileProfData.lean"), "w").write(
        HDR + "import BGP212.SymProfile\nimport Solution.SymTrieProfData\n\n"
        "/-! # V2n: the moment profiles of the direct nodes (data; certified in `Solution/SymProfileCert/`,\n"
        "assembled in `Solution/SymProfileNodes.lean`)\n\n(generated by `specs/checks/sym_profile_v2n_demo.py`) -/\n\n"
        "namespace BGP212.V2e\n\n" + OPEN +
        "".join(f"def Tn_R_{ident(a)} : List ((ℕ × ℕ) × ℚ) := {V.penc(pl.prof[a])}\n\n" for a in pl.aug) +
        "/-- **Definition (direct profiles).** The moment profiles of the direct nodes, certified by\n"
        "direct transitions from V2m's stored nodes (`Tn_prof_ok`; no state of a direct node is formed). -/\n"
        f"def Tn_prof : List (List ℕ × List ((ℕ × ℕ) × ℚ)) :=\n  {plit}\n\n"
        "/-- **Definition.** V2n's direct profiles together with V2m's profiles (`Tn_all_ok`). -/\n"
        "def Tn_all : List (List ℕ × List ((ℕ × ℕ) × ℚ)) := Tn_prof ++ Tt_prof\n\nend BGP212.V2e\n")
    order.append(PDATA2)
    pnames = {}      # node -> (data module, chunk names, chunk data)
    markmod = {}     # node -> module proving Tn_m_<id>
    # data chunking of every node with children: each chunk's emission for every child ≤ EMIT_B
    def rank(e):
        return e[0][0] * 1024 + e[0][1]

    def ranges_of(Ds):
        """Bounds b₁ < b₂ < … (ranks) so that each range holds at most RANGE_B input entries."""
        cnt = {}
        for D_ in Ds:
            for e in D_:
                cnt[rank(e)] = cnt.get(rank(e), 0) + 1
        bs, cur = [], 0
        for r in sorted(cnt):
            if cur and cur + cnt[r] > RANGE_B:
                bs.append(r)
                cur = 0
            cur += cnt[r]
        return list(zip([0] + bs, bs + [None]))

    def in_rng(e, lo, hi):
        return rank(e) >= lo and (hi is None or rank(e) < hi)

    def slices(D_, rng):
        out = [[e for e in D_ if in_rng(e, lo, hi)] for lo, hi in rng]
        assert [e for sl in out for e in sl] == D_
        return out

    def result_body(nm, D_, rng):
        """Definitions of a chunk result as the concatenation of its nonempty range slices."""
        sl = slices(D_, rng)
        names = {r: f"{nm}_r{r}" for r, x_ in enumerate(sl) if x_}
        body = [f"def {names[r]} : List (MarkKey × ℚ) :=\n  {menc(x_)}\n" for r, x_ in enumerate(sl) if x_]
        body.append(f"def {nm} : List (MarkKey × ℚ) :=\n  [{', '.join(names[r] for r in sorted(names))}].flatten\n")
        return body, names

    def write_internal_data(x, rng):
        """Data of the internal node x, chunked within the key ranges and split over data modules."""
        i = ident(x)
        P = pl.P[x]
        kids = pl.children.get(x, [])
        cost = lambda e: max([len(M.emit(pl.order[c], NCLS, fac(c[-1]), [e])) if len(e[0][2]) <= pl.order[c] + 1 else 1
                              for c in kids] + [1])  # noqa: E731
        chunks, per_range = [], []
        for lo, hi in rng:
            sl = [e for e in P if in_rng(e, lo, hi)]
            js = []
            for part in split_by(sl, cost, EMIT_B):
                for k in range(0, len(part), DATA_B):
                    js.append(len(chunks))
                    chunks.append(part[k:k + DATA_B])
            per_range.append(js)
        assert [e for c_ in chunks for e in c_] == P
        names = [f"Tn_P_{i}_c{j}" for j in range(len(chunks))]
        dmods, cmod = [], {}
        for grp in split_by(list(range(len(chunks))), lambda j: len(chunks[j]), DMOD_B):
            m_ = write(f"P_{i}_d{len(dmods)}", base, f"the marked profile of {qlist(x)}, order ≤ {pl.order[x]} (data part {len(dmods)})",
                       [f"def {names[j]} : List (MarkKey × ℚ) :=\n  {menc(chunks[j])}\n" for j in grp])
            stats["data_mods"] += 1
            dmods.append(m_)
            for j in grp:
                cmod[j] = m_
        pm = write(f"P_{i}", dmods, f"the marked profile of {qlist(x)}, order ≤ {pl.order[x]} (data)",
                   [f"def Tn_P_{i} : List (MarkKey × ℚ) :=\n  [{', '.join(names)}].flatten\n"])
        pnames[x] = [(names[j], chunks[j], cmod[j]) for j in range(len(chunks))]
        return pm, names, per_range, cmod

    def write_ranges(x, rng, results, snames, names, per_range, cmod):
        """One kernel merge per key range, over the slices of that range only."""
        i = ident(x)
        kms, kthms = [], []
        for r, ((lo, hi), js) in enumerate(zip(rng, per_range)):
            srcs = [(results[j][0], snames[j][r], results[j][2]) for j in range(len(results)) if r in snames[j]]
            Dm = merge([[e for e in results[j][1] if in_rng(e, lo, hi)] for j in range(len(results))])
            assert Dm == [e for j in js for e in pnames[x][j][1]]
            nm = f"Tn_k_{i}_{r}"
            m_ = write(f"M_{i}_{r}", [s_[2] for s_ in srcs] + [cmod[j] for j in js] + ["Solution.SymProfileSplit"],
                       f"merge of the range slices of {qlist(x)} on the ranks [{lo}, {hi if hi is not None else '∞'})",
                       [f"theorem {nm} : mergeAll markCmp 64 [{', '.join(s_[1] for s_ in srcs)}] =\n"
                        f"    [{', '.join(names[j] for j in js)}].flatten := by\n  decide +kernel\n"])
            stats["merge_mods"] += 1
            kms.append(m_)
            kthms.append(nm)
        return kms, kthms

    def regroup_proof(x, inner, dn, kthms):
        i = ident(x)
        hs = "\n".join(f"  have e{r} := merge_slices_val _ _ {k} F" for r, k in enumerate(kthms))
        es = " ".join(f"e{r}" for r in range(len(kthms)))
        return (f"by\n  refine markOK_congr _ g {qlist(x)} {pl.order[x]} _ _\n    ({inner}) fun F => ?_\n{hs}\n"
                f"  simp only [mergeAll_markVal, Tn_P_{i}, {', '.join(dn)}, sum_flatten_val, List.map_cons,\n"
                f"    List.map_nil, List.sum_cons, List.sum_nil] at {es} ⊢\n"
                f"  linear_combination {' + '.join(f'e{r}' for r in range(len(kthms)))}")

    def merges(x, results, final_rhs, final_name, final_imports, final_doc, leaf):
        """results: list of (name, data, module). Writes group merges and the final merge module."""
        i = ident(x)
        groups = V.split(results, MERGE_K)
        Rs = []
        for gi, grp in enumerate(groups):
            if len(grp) == 1:
                Rs.append((grp[0][0], grp[0][1], grp[0][2], "rfl"))
                continue
            Rg = merge([r[1] for r in grp])
            nm = f"Tn_R_{i}_{gi}"
            m_ = write(f"R_{i}_{gi}", [r[2] for r in grp] + base, f"merge {gi} of {qlist(x)}",
                       [f"def {nm} : List (MarkKey × ℚ) :=\n  {menc(Rg)}\n",
                        f"theorem Tn_r_{i}_{gi} : mergeAll markCmp 64 [{', '.join(r[0] for r in grp)}] = {nm} := by\n"
                        "  decide +kernel\n"])
            stats["merge_mods"] += 1
            Rs.append((nm, Rg, m_, f"Tn_r_{i}_{gi}"))
        Pm = merge([r[1] for r in Rs])
        if leaf:
            assert M.to_prof(Pm) == pl.prof[x]
            body = [f"theorem {final_name} : markToProf (mergeAll markCmp 64 [{', '.join(r[0] for r in Rs)}]) = Tn_R_{i} := by\n"
                    "  decide +kernel\n"]
        else:
            assert Pm == pl.P[x], x
            body = [f"theorem {final_name} : mergeAll markCmp 64 [{', '.join(r[0] for r in Rs)}] = {final_rhs} := by\n"
                    "  decide +kernel\n"]
        fm = write(f"F_{i}", [r[2] for r in Rs] + final_imports + base, final_doc, body)
        stats["final_mods"] += 1
        return groups, Rs, fm

    # sources: marked profiles of V2m's stored states
    for s_ in pl.src:
        i, Ts = ident(s_), pl.order[s_]
        Ls, items = [], []
        for cj, c in enumerate(T.chunks[s_]):
            cn = T.lname(s_, cj)
            tup = lambda st: sum(len(M.dtup(t, list(st[0]))) for t in range(Ts + 1))  # noqa: E731
            subs = split_by(list(range(len(c))), lambda k: tup(c[k]), STAT_B)
            for sj, sub in enumerate(subs):
                a0, a1 = sub[0], sub[-1] + 1
                expr = cn if (a0 == 0 and a1 == len(c)) else f"((({cn}).drop {a0}).take {a1 - a0})"
                part = c[a0:a1]
                stats["tuples"] += sum(tup(st) for st in part)
                Ls.append(expr)
                items.append((f"Tn_Q_{i}_{cj}_{sj}", M.aug_lean(Ts, part), f"{cj}_{sj}", expr))
        rng = ranges_of([it[1] for it in items])
        pm, names, per_range, cmod = write_internal_data(s_, rng)
        results, snames = [], []
        for nm, Qd, tag, expr in items:
            body, sn = result_body(nm, Qd, rng)
            body.append(f"theorem Tn_q_{i}_{tag} : markProfile {Ts} {expr} = {nm} := by\n  decide +kernel\n")
            m_ = write(f"Q_{i}_{tag}", [f"Solution.SymTrieCert.D_{i}"] + base,
                       f"marked profile of a chunk of the states of {qlist(s_)}", body)
            stats["stat_mods"] += 1
            results.append((nm, Qd, m_))
            snames.append(sn)
        kms, kthms = write_ranges(s_, rng, results, snames, names, per_range, cmod)
        hL = "rfl" if all(" " not in e for e in Ls) and Ls == [T.lname(s_, j) for j in range(len(T.chunks[s_]))] else \
            "(by decide +kernel)"
        qn = [r[0] for r in results]
        inner = (f"markOK_of_tree _ g {qlist(s_)} {Ts} {T.lname(s_)}\n"
                 f"    [{', '.join(Ls)}]\n    [{', '.join(qn)}]\n"
                 f"    [{', '.join('[' + x_ + ']' for x_ in qn)}]\n"
                 f"    [{', '.join(qn)}] (mergeAll markCmp 64 [{', '.join(qn)}])\n"
                 f"    Tt_c_{i} {hL}\n    {f2(['Tn_q_' + i + '_' + it[2] for it in items])}\n    rfl\n"
                 f"    {f2(['rfl'] * len(qn))}\n    rfl")
        body = [f"/-- The marked profile of order `≤ {Ts}` of the V2m stored node `{qlist(s_)}`. -/\n"
                f"theorem Tn_m_{i} : MarkOK {N3} g {qlist(s_)} {Ts} Tn_P_{i} := {regroup_proof(s_, inner, qn, kthms)}\n"]
        markmod[s_] = write(f"A_{i}", kms + [pm, f"Solution.SymTrieCert.S_{i}", "Solution.SymProfileSplit"] +
                            [r[2] for r in results], f"MarkOK of the source {qlist(s_)}", body)
        stats["asm_mods"] += 1
    # direct nodes
    for a in pl.aug:
        i, p, q, Ta = ident(a), a[:-1], a[-1], pl.order[a]
        Tp = pl.order[p]
        leaf = Ta == 0
        pchunks = pnames[p]
        items = []
        for j, (cn, cd, cm) in enumerate(pchunks):
            CC = [e for e in cd if len(e[0][2]) <= Ta + 1]
            em = len(M.emit(Ta, NCLS, fac(q), CC))
            stats["emitted"] += em
            stats["max_emit"] = max(stats["max_emit"], em)
            items.append((f"Tn_D_{i}_{j}", M.step_lean(Ta, NCLS, fac(q), CC), j, cn, cm))
        rng = None if leaf else ranges_of([it[1] for it in items])
        if not leaf:
            pm, names, per_range, cmod = write_internal_data(a, rng)
        results, snames = [], []
        for nm, Dd, j, cn, cm in items:
            if leaf:
                body, sn = [f"def {nm} : List (MarkKey × ℚ) :=\n  {menc(Dd)}\n"], {}
            else:
                body, sn = result_body(nm, Dd, rng)
            body.append(f"theorem Tn_s_{i}_{j} : markStep {N3} (stepFactor g {q}) {Ta}\n"
                        f"    ({cn}.filter fun e => decide (e.1.2.2.length ≤ {Ta + 1})) = {nm} := by\n  decide +kernel\n")
            m_ = write(f"S_{i}_{j}", [cm, "Solution.SymTrie"] + base, f"direct step to {qlist(a)}, parent chunk {j}", body)
            stats["step_mods"] += 1
            results.append((nm, Dd, m_))
            snames.append(sn)
        pexpr = f"Tn_P_{ident(p)}"
        dn = [r[0] for r in results]
        if leaf:
            fin = f"Tn_f_{i}"
            groups, Rs, fm = merges(a, results, None, fin, [PDATA2], f"the final merge of {qlist(a)}", True)
            mk = (f"markOK_step_tree _ g {qlist(p)} {q} {Ta} {Tp} (by decide) {pexpr}\n"
                  f"    [{', '.join(x_[0] for x_ in pchunks)}]\n    [{', '.join(dn)}]\n"
                  f"    [{', '.join('[' + ', '.join(r[0] for r in grp) + ']' for grp in groups)}]\n"
                  f"    [{', '.join(r[0] for r in Rs)}] (mergeAll markCmp 64 [{', '.join(r[0] for r in Rs)}])\n"
                  f"    Tn_m_{ident(p)} rfl\n    {f2([f'Tn_s_{i}_{j}' for j in range(len(results))])}\n    rfl\n"
                  f"    {f2([r[3] for r in Rs])}\n    rfl")
            body = [f"/-- The moment profile of `{qlist(a)}` by direct transitions. -/\n"
                    f"theorem Tn_pc_{i} : ProfCert {N3} g {qlist(a)} Tn_R_{i} :=\n"
                    f"  {fin} ▸ profCert_of_markOK _ g {qlist(a)} _\n  ({mk})\n"]
            imps = [fm]
        else:
            kms, kthms = write_ranges(a, rng, results, snames, names, per_range, cmod)
            inner = (f"markOK_step_tree _ g {qlist(p)} {q} {Ta} {Tp} (by decide) {pexpr}\n"
                     f"    [{', '.join(x_[0] for x_ in pchunks)}]\n    [{', '.join(dn)}]\n"
                     f"    [{', '.join('[' + x_ + ']' for x_ in dn)}]\n"
                     f"    [{', '.join(dn)}] (mergeAll markCmp 64 [{', '.join(dn)}])\n"
                     f"    Tn_m_{ident(p)} rfl\n    {f2([f'Tn_s_{i}_{j}' for j in range(len(results))])}\n    rfl\n"
                     f"    {f2(['rfl'] * len(dn))}\n    rfl")
            body = [f"/-- The marked profile of order `≤ {Ta}` of `{qlist(a)}` by direct transitions. -/\n"
                    f"theorem Tn_m_{i} : MarkOK {N3} g {qlist(a)} {Ta} Tn_P_{i} := {regroup_proof(a, inner, dn, kthms)}\n"]
            imps = kms + [pm]
        markmod[a] = write(f"A_{i}", imps + [markmod[p], "Solution.SymProfileSplit"] + [r[2] for r in results],
                           f"the direct certificate of {qlist(a)}", body)
        stats["asm_mods"] += 1
    # moment profiles of the internal direct nodes (order-0 part), in their own modules
    for a in pl.aug:
        if pl.order[a] == 0:
            continue
        i = ident(a)
        body = [f"theorem Tn_g_{i} : markToProf (Tn_P_{i}.filter fun e => decide (e.1.2.2.length ≤ 0)) = Tn_R_{i} := by\n"
                "  decide +kernel\n",
                f"/-- The moment profile of `{qlist(a)}` (order `0` of its marked profile). -/\n"
                f"theorem Tn_pc_{i} : ProfCert {N3} g {qlist(a)} Tn_R_{i} :=\n"
                f"  Tn_g_{i} ▸ profCert_of_markOK _ g {qlist(a)} _ (markOK_mono _ g {qlist(a)} {pl.order[a]} 0 (by decide) _ Tn_m_{i})\n"]
        markmod[("prof", a)] = write(f"G_{i}", [markmod[a], PDATA2], f"the moment profile of {qlist(a)}", body)
    # assembly
    nodes = pl.aug
    ppf = "(profOK_nil _ g)"
    for a in nodes:
        ppf = f"(profOK_cons _ g _ {qlist(a)} _ Tn_pc_{ident(a)}\n    {ppf})"
    imps = sorted({markmod[a] for a in nodes if pl.order[a] == 0} | {markmod[("prof", a)] for a in nodes if pl.order[a] > 0})
    same = [a for a in nodes if a in pl.v2m]
    o = [HDR + "import Solution.SymTrieNodes\n" + f"import {PDATA2}\n" + "".join(f"import {x}\n" for x in imps) + "\n"
         "/-! # V2n: the direct moment profiles of the block |λ| ≤ 8 at Table 3, piece (6, 3)\n\n"
         "(generated by `specs/checks/sym_profile_v2n_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN,
         f"theorem Tn_prof_ok : ProfOK {N3} g Tn_prof :=\n  {ppf}\n",
         f"theorem Tn_all_ok : ProfOK {N3} g Tn_all := profOK_append _ g _ _ Tn_prof_ok Tt_prof_ok\n",
         "/-- **Agreement with V2m.** The direct profiles of the nodes V2m certified by staged states equal\n"
         "V2m's profiles. -/\n"
         "theorem Tn_same_as_v2m : " + " ∧\n    ".join(f"Tn_R_{ident(a)} = Tt_P_{ident(a)}" for a in same) +
         " := by\n  decide +kernel\n",
         "end BGP212.V2e\n"]
    open(os.path.join(root, "Solution", "SymProfileNodes.lean"), "w").write("\n".join(o))
    demos = write_demos(root, pl)
    order_all = order + ["Solution.SymProfileNodes"] + demos
    sh = ["#!/usr/bin/env bash",
          "# V2n: build the direct-profile certificates one `lean` process at a time (for a 3.8 GiB machine",
          "# without swap): each `lake build` below finds its dependencies already built and runs one `lean`.",
          "# Requires V2m's certificates (specs/checks/sym_trie_v2m_build.sh) first.",
          "set -euo pipefail",
          "lake build Solution.SymProfile Solution.SymProfileSplit",
          "for m in \\"] + [f"  {m} \\" for m in order_all] + ["  ; do", "  echo \"== $m\"", "  lake build \"$m\"", "done",
                                                            "lake build Solution.SymProfileSuite Challenge.SymProfile", ""]
    os.makedirs(os.path.join(root, "specs", "checks"), exist_ok=True)
    bp = os.path.join(root, "specs", "checks", "sym_profile_v2n_build.sh")
    open(bp, "w").write("\n".join(sh))
    os.chmod(bp, 0o755)
    print("block8", len(pl.b8), "new", len(pl.new), "direct nodes", len(pl.aug), "sources", len(pl.src),
          "same as V2m", len(same), "modules", len(order), stats)
    print("orders", {ident(s): pl.order[s] for s in pl.src})


PIECE = "(fun A B m n => pieceMn 44 6 3 A B g L τ C m n)"


def ws_lit(ws):
    return "[" + ", ".join(f"(({V.rlit(w)} : ℚ), {a1}, {qlist(l1)}, {a2}, {qlist(l2)})" for (w, a1, l1, a2, l2) in ws) + "]"


def write_demos(root, pl):
    T = pl.T
    hd = lambda imps, doc: (HDR + "".join(f"import {i}\n" for i in imps) + "\n" +  # noqa: E731
                            f"/-! # V2n: {doc}\n\nCOMPUTATIONAL DEMONSTRATION (generated by "
                            "`specs/checks/sym_profile_v2n_demo.py`). Tables are coefficient representations;\n"
                            "the rational moments `pieceMn` are evaluated separately. -/\n\nnamespace BGP212.V2e\n\n" + OPEN)
    sol = lambda name: os.path.join(root, "Solution", f"{name}.lean")  # noqa: E731
    out = lambda name, parts: open(sol(name), "w").write("\n".join(parts + ["end BGP212.V2e\n"]))  # noqa: E731
    mods = []
    out("SymProfileDemo1", [hd([PDATA2], "the block |λ| ≤ 8: shape and coverage"),
         "/-- The block `|λ| ≤ 8`: 52 factor multisets, sorted and prefix-closed. -/\n"
         "theorem block8_shape : (blockMultisets 8).length = 52 ∧ trieShapeOK (blockMultisets 8) = true := by\n"
         "  decide +kernel\n",
         "/-- **Coverage.** Every multiset of the block `|λ| ≤ 8` has a certified moment profile at piece\n"
         "`(6, 3)`, from V2m's staged certificates or V2n's direct transitions (`Tn_all_ok`). -/\n"
         "theorem Tn_covers : (blockMultisets 8).all (fun Q => natListMem Q (Tn_all.map Prod.fst)) = true := by\n"
         "  decide +kernel\n"])
    mods.append("Solution.SymProfileDemo1")
    # tables
    def cost(w):
        c_ = 0
        for (K1, *_r) in Q.innerTerms(w[1], w[2]):
            for (K2, *_r2) in Q.innerTerms(w[3], w[4]):
                c_ += len(V.penc(V.prof(T.L[tuple(sorted(K1 + K2, reverse=True))])))
        return c_

    def ptab(ws):
        return D.prof_table(T, ws)

    def parted(k, tag, doc, ws, docstring, stmt):
        wss = split_by(ws, cost, PART_B)
        Ts = [ptab(w) for w in wss]
        Tb = V.merge_profiles(Ts)
        assert Tb == ptab(ws)
        level = []
        for r, (w, Tr) in enumerate(zip(wss, Ts)):
            out(f"SymProfileTab{k}_R{r}", [hd([PDATA2], f"{doc}, part {r}"),
                 f"def Tn_T{k}_{r} : List (MKey × ℚ) :=\n  {V.tenc(Tr)}\n",
                 f"theorem tabN_{tag}_{r} : profTable 44 6 3 g Tn_all {ws_lit(w)} = Tn_T{k}_{r} := by\n  decide +kernel\n"])
            mods.append(f"Solution.SymProfileTab{k}_R{r}")
            pf = (f"((trieProf_table_eq 44 6 3 g Tn_all Tn_all_ok {ws_lit(w)} {PIECE}).trans\n"
                  f"      (congrArg (fun T => tableVal T {PIECE}) tabN_{tag}_{r}))")
            level.append((f"Tn_T{k}_{r}", w, Tr, pf, f"Solution.SymProfileTab{k}_R{r}"))
        depth = 0
        while len(level) > 1:
            depth += 1
            groups = V.split(level, MERGE_K)
            final = len(groups) == 1
            nxt = []
            for gi, grp in enumerate(groups):
                if len(grp) == 1:
                    nxt.append(grp[0])
                    continue
                Tm = V.merge_profiles([x[2] for x in grp])
                wm = [w for x in grp for w in x[1]]
                name, thm = f"Tn_T{k}_M{depth}_{gi}", f"tabN_{tag}_M{depth}_{gi}"
                rhs = f"({V.tenc(Tm)})" if final else name
                body = [] if final else [f"def {name} : List (MKey × ℚ) :=\n  {V.tenc(Tm)}\n"]
                body.append(f"theorem {thm} : mergeAll mkeyCmp 64 [{', '.join(x[0] for x in grp)}] =\n"
                            f"    {rhs} := by\n  decide +kernel\n")
                mname = f"SymProfileTab{k}_M{depth}_{gi}" if not final else f"SymProfileTab{k}"
                out(mname, [hd([x[4] for x in grp], f"{doc}, merge {depth}.{gi}")] + body)
                mods.append(f"Solution.{mname}")
                pf = (f"(table_parts_merge 44 6 3 g {PIECE}\n    [{', '.join(ws_lit(x[1]) for x in grp)}]\n"
                      f"    {ws_lit(wm)} rfl _\n    {f2([x[3] for x in grp])}\n    _ {thm})")
                nxt.append((name, wm, Tm, pf, f"Solution.{mname}"))
            level = nxt
        wsum = (f"(List.map (fun w : WPair ℚ => w.1 * genPieceWith 44 6 3 g\n    {PIECE} w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)\n"
                f"    {ws_lit(ws)}).sum")
        if depth == 0:
            proof = level[0][3]
            imps = ["Solution.SymProfileNodes", level[0][4]]
        else:
            proof = level[0][3]
            imps = ["Solution.SymProfileNodes", f"Solution.SymProfileTab{k}"]
        out(f"SymProfileDemo{k}", [hd(imps, doc), docstring.replace("PARTS", str(len(wss))) +
             f"theorem {stmt} : {wsum} =\n    tableVal ({V.tenc(Tb)})\n      {PIECE} :=\n  {proof}\n"])
        mods.append(f"Solution.SymProfileDemo{k}")
        return Tb, len(wss)

    # Demo 2: J_T[P_(2,2,2,2), P_(2,2,2,2)] (degree 16) at piece (6, 3)
    ws = [(Fr(1), 0, (2, 2, 2, 2), 0, (2, 2, 2, 2))]
    Tb = ptab(ws)
    assert Tb == S.gen_table(6, 3, 0, [2, 2, 2, 2], 0, [2, 2, 2, 2])
    out("SymProfileTab2", [hd([PDATA2], "degree 16: J_T[P_(2,2,2,2), P_(2,2,2,2)] (the table)"),
         f"theorem tabN_P2222_6_3 : profTable 44 6 3 g Tn_all {ws_lit(ws)} =\n    ({V.tenc(Tb)}) := by\n  decide +kernel\n"])
    mods.append("Solution.SymProfileTab2")
    m28 = (2,) * 8
    assert m28 in pl.aug and pl.order[m28] == 0 and m28 not in pl.v2m
    out("SymProfileDemo2", [hd(["Solution.SymProfileNodes", "Solution.SymProfileTab2"],
                               "degree 16: J_T[P_(2,2,2,2), P_(2,2,2,2)] at piece (6, 3)"),
         "/-- **A new node by direct transitions.** The moment profile of `[2]^8` (degree 16, outside V2m's\n"
         "subtree), certified by direct transitions from V2m's stored node `[2]^5`: no state of `[2]^6`,\n"
         "`[2]^7` or `[2]^8` is formed in the certificate. -/\n"
         f"theorem profile_2x8_direct : ProfCert {N3} g {qlist(m28)}\n    ({V.penc(pl.prof[m28])}) :=\n"
         f"  Tn_pc_{ident(m28)}\n",
         "/-- **Degree 16.** Piece `(6, 3)` of `J_T[P_(2,2,2,2), P_(2,2,2,2)]` as an explicit combination of\n"
         "moments, from profiles certified by direct transitions (`[2]^7`, `[2]^8`) and by V2m. -/\n"
         "theorem genPieceP2222_6_3_direct_expansion : genPiece 44 6 3 g L τ C 0 [2, 2, 2, 2] 0 [2, 2, 2, 2] =\n"
         f"    tableVal ({V.tenc(Tb)})\n      {PIECE} :=\n"
         "  (genPieceWith_eq_profTable 44 6 3 g Tn_all Tn_all_ok _ 0 [2, 2, 2, 2] 0 [2, 2, 2, 2]).trans\n"
         f"    (congrArg (fun T => tableVal T {PIECE}) tabN_P2222_6_3)\n"])
    mods.append("Solution.SymProfileDemo2")
    # Demo 4: the block |λ| ≤ 8, 144 pairs, weights c_i c_j, c = 1, …, 12
    lams = sorted({l for l in D.LAMBDAS if sum(l) <= 8}, key=lambda l: (sum(l), l))
    c = {l: Fr(i + 1) for i, l in enumerate(lams)}
    ws = [(c[x] * c[y], 0, x, 0, y) for x in lams for y in lams]
    gen_check = {}
    for (w, a1, l1, a2, l2) in ws:
        for s_, v in S.gen_table(6, 3, a1, list(l1), a2, list(l2)):
            gen_check[s_] = gen_check.get(s_, Fr(0)) + w * v
    Tb4, parts = parted(4, "block8", "the block |λ| ≤ 8 of B₂₁ at piece (6, 3)", ws,
                        "/-- **The block `|λ| ≤ 8`.** `Σ_{i,j} cᵢ cⱼ J_T[P_{λᵢ}, P_{λⱼ}]` on piece `(6, 3)` for the twelve\n"
                        "generators `P_λ`, `|λ| ≤ 8`, with `c = 1, …, 12`: 144 pairs (PARTS certified parts merged by\n"
                        "`table_parts_merge`), from V2m's and V2n's certified profiles. -/\n", "block8_6_3_expansion")
    assert {s_: v for s_, v in Tb4 if v != 0} == {s_: v for s_, v in gen_check.items() if v != 0}
    print("tables: P2222", len(Tb), "block8", len(Tb4), "keys in", parts, "parts")
    return mods


if __name__ == "__main__":
    main()
