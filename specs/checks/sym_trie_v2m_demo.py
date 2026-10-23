#!/usr/bin/env python3
"""Emit V2m's certified prefix-trie subtree at Table 3, piece (6, 3) (class sizes (6, 3, 35), shift g).

Nodes: the factor multisets (degrees in decreasing order) of
  * the block |λ| ≤ 6 of B₂₁ (`blockMultisets 6`, 22 multisets, up to six factors, degree 12), and
  * all multisets of B₂₁ with at most two factors (`shortMultisets 2`, 66 multisets, degree up to 40),
78 in all with the root. A node with children in the set is *stored*: its canonical states are
certificate data, reached from its parent by one certified step (chunked with a merge when the step
generates more than GEN_B entries). Every other node is a *leaf*: only its moment profile is
certified, computed from the stored parent (chunked when large), so its states are never stored.

Files (Solution/SymTrieCert/):
  D_<id>        states of a stored node, in chunks (data only);
  S_<id>        the step to a stored node and its chain (S_<id>_C<j>: chunk steps);
  P_<id>        the moment profile of a stored node;
  G_<pid>_<k>   moment profiles of small leaves of the parent <pid>;
  L_<id>        the moment profile of a large leaf (L_<id>_C<j>: chunk profiles);
Before them Solution/SymTrieProfData.lean (the profile data); then Solution/SymTrieNodes.lean (the
trie and profile lists with TrieOK / ProfOK), Solution/SymTrieKept.lean, the tables
Solution/SymTrieTab*.lean (each kernel table check in its own module, the one-part table in parts
and one merge), Solution/SymTrieDemo1.lean … Demo6.lean, and specs/checks/sym_trie_v2m_build.sh
(sequential build).

Usage: python3 -I specs/checks/sym_trie_v2m_demo.py [root]
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_entry_v2i_model as Q  # noqa: E402
import sym_reduce_v2k_model as S  # noqa: E402
import sym_staged_v2l_demo as V  # noqa: E402

HDR = V.HDR
PDATA = "Solution.SymTrieProfData"
PDATA_B = 250000     # bytes of profile literals per data module
GEN_B = 900          # generated entries per kernel step check
PROF_B = 800         # states per kernel profile check
N3 = "(clsCount 44 6 3)"
OPEN = "open BGP212.Params\n\n"


def parts(j, k):
    if j == 0:
        yield ()
        return
    for p in range(min(j, k), 0, -1):
        for r in parts(j - p, p):
            yield (p,) + r


def subsets(l):
    if not l:
        return [((), 0)]
    q, rest = l[0], l[1:]
    st = subsets(rest)
    return [((q,) + K, s) for K, s in st] + [(K, s + q) for K, s in st]


LAMBDAS = [tuple(2 * x for x in lam) for j in range(11) for lam in parts(j, j)]


def kept(pred):
    out = set()
    for l in LAMBDAS:
        if pred(l):
            for K, _ in subsets(l):
                out.add(K)
    return out


def multisets():
    k6 = kept(lambda l: sum(l) <= 6)
    kall = kept(lambda l: True)
    s1 = {tuple(sorted(x + y, reverse=True)) for x in k6 for y in k6}
    s2 = {tuple(sorted(x + y, reverse=True)) for x in kall for y in kall if len(x) + len(y) <= 2}
    return s1, s2


def ident(m):
    return "_".join(map(str, m)) if m else "root"


def qlist(m):
    return "[" + ", ".join(map(str, m)) + "]"


def prof(L):
    return V.prof(L)


class Trie:
    def __init__(self):
        self.s1, self.s2 = multisets()
        self.nodes = sorted(self.s1 | self.s2, key=lambda m: (len(m), m))
        g = Fr(41, 625)
        self.sig = [g, g, Fr(0)]
        self.n = [6, 3, 35]
        self.L = {(): [((), Fr(1))]}
        self.gen = {}
        for m in self.nodes:
            if not m:
                continue
            L = self.L[m[:-1]]
            gen = self.step_entries(L, m[-1])
            self.L[m] = S.normalize(gen)
            self.gen[m] = len(gen)
        self.stored = [m for m in self.nodes if any(c and c[:-1] == m for c in self.nodes)]
        self.children = {p: [c for c in self.nodes if c and c[:-1] == p] for p in self.stored}
        # chunk size of each stored node: every child step generates at most GEN_B entries per chunk
        self.csize = {}
        for p in self.stored:
            per = max(self.gen[c] / max(1, len(self.L[p])) for c in self.children[p])
            self.csize[p] = max(1, int(GEN_B / per))
        self.chunks = {p: V.split(self.L[p], self.csize[p]) for p in self.stored}

    def step_entries(self, L, q):
        fac = lambda c: Q.shiftPow(self.sig[c], q)  # noqa: E731
        return [e for (k, kap) in L for e in S.step(self.n, fac, k, kap)]

    def lname(self, m, j=None):
        return "[([], 1)]" if not m else (f"Tt_L_{ident(m)}" + ("" if j is None else f"_c{j}"))

    def chain(self, m):
        return f"(chainCert_nil {N3} [([], 1)])" if not m else f"Tt_c_{ident(m)}"

    def pchunks(self, p):
        """Parent chunk names (the root is one chunk)."""
        if not p:
            return ["[([], 1)]"]
        return [self.lname(p, j) for j in range(len(self.chunks[p]))]

    def pchunk_data(self, p):
        return [[((), Fr(1))]] if not p else self.chunks[p]

    def emit(self, root):
        d = os.path.join(root, "Solution", "SymTrieCert")
        os.makedirs(d, exist_ok=True)
        for f in os.listdir(d):
            os.remove(os.path.join(d, f))
        self.order = []          # modules in build order
        self.profmods = []       # modules providing profile certificates
        self.chainmod = {(): None}
        self.datamod = {(): None}
        mod = lambda s: f"Solution.SymTrieCert.{s}"  # noqa: E731

        def head(imports, doc):
            return (HDR + "".join(f"import {i}\n" for i in imports) + "\n" +
                    f"/-! # V2m: {doc} (generated by `specs/checks/sym_trie_v2m_demo.py`) -/\n\n"
                    "namespace BGP212.V2e\n\n" + OPEN)

        def write(name, imports, doc, body):
            open(os.path.join(d, f"{name}.lean"), "w").write(head(imports, doc) + "\n".join(body) + "\nend BGP212.V2e\n")
            self.order.append(mod(name))
            return mod(name)

        parts, cur, size = [], [], 0
        for m in self.nodes:
            dfn = f"def Tt_P_{ident(m)} : List ((ℕ × ℕ) × ℚ) := {V.penc(prof(self.L[m]))}\n"
            if cur and size + len(dfn) > PDATA_B:
                parts.append(cur)
                cur, size = [], 0
            cur.append(dfn)
            size += len(dfn)
        parts.append(cur)
        for j, part in enumerate(parts):
            open(os.path.join(root, "Solution", f"SymTrieProfData{j}.lean"), "w").write(
                HDR + "import BGP212.SymTrie\n\n/-! # V2m: moment profiles of the certified subtree, data part "
                f"{j} (generated by `specs/checks/sym_trie_v2m_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN +
                "\n".join(part) + "\nend BGP212.V2e\n")
            self.order.append(f"{PDATA}{j}")
        pd = [HDR + "".join(f"import {PDATA}{j}\n" for j in range(len(parts))) +
              "\n/-! # V2m: the moment profiles of the certified subtree (data; certified in\n"
              "`Solution/SymTrieCert/`, assembled in `Solution/SymTrieNodes.lean`)\n\n"
              "(generated by `specs/checks/sym_trie_v2m_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN]
        nodes = [m for m in self.nodes if m]
        pd.append("/-- **Definition (profiles of the subtree).** The moment profiles of all nodes of the subtree,\n"
                  "indexed by the multiset of degrees (certified by `Tt_prof_ok`). -/\n"
                  "def Tt_prof : List (List ℕ × List ((ℕ × ℕ) × ℚ)) :=\n  [" +
                  ", ".join(f"({qlist(m)}, Tt_P_{ident(m)})" for m in reversed(nodes)) + ", ([], Tt_P_root)]\n")
        open(os.path.join(root, "Solution", "SymTrieProfData.lean"), "w").write("\n".join(pd) + "\nend BGP212.V2e\n")
        self.order.append(PDATA)
        base = "Solution.SymTrie"
        for m in self.nodes:
            if not m:
                continue
            p, q, i = m[:-1], m[-1], ident(m)
            pimports = [x for x in (self.datamod[p], self.chainmod[p]) if x] or [base]
            if m in self.stored:
                # data
                cs = self.chunks[m]
                body = [f"def {self.lname(m, j)} : List (SKey × ℚ) :=\n  {V.enc(c)}\n" for j, c in enumerate(cs)]
                body.append(f"def {self.lname(m)} : List (SKey × ℚ) :=\n  [{', '.join(self.lname(m, j) for j in range(len(cs)))}].flatten\n")
                self.datamod[m] = write(f"D_{i}", ["BGP212.SymStaged"], f"states of the node {qlist(m)}", body)
                # step
                if self.gen[m] <= GEN_B:
                    body = [f"theorem Tt_s_{i} : StepCert {N3} (stepFactor g {q}) {self.lname(p)} {self.lname(m)} :=\n"
                            "  stepCert_of_beq _ _ _ _ (by decide +kernel)\n"]
                    imps = pimports + [self.datamod[m], base]
                else:
                    cms, Ds = [], []
                    for j, (cn, cd) in enumerate(zip(self.pchunks(p), self.pchunk_data(p))):
                        Dj = S.normalize(self.step_entries(cd, q))
                        Ds.append(Dj)
                        cms.append(write(f"S_{i}_C{j}", [x for x in [self.datamod[p]] if x] + [base],
                                         f"step to {qlist(m)}, chunk {j}",
                                         [f"def Tt_D_{i}_c{j} : List (SKey × ℚ) :=\n  {V.enc(Dj)}\n",
                                          f"theorem Tt_s_{i}_c{j} : StepCert {N3} (stepFactor g {q}) {cn} Tt_D_{i}_c{j} :=\n"
                                          "  stepCert_of_beq _ _ _ _ (by decide +kernel)\n"]))
                    assert V.merge_all(Ds) == self.L[m]
                    k = len(Ds)
                    f2 = "".join(f"(List.Forall₂.cons Tt_s_{i}_c{j} " for j in range(k)) + "List.Forall₂.nil" + ")" * k
                    body = [f"theorem Tt_s_{i} : StepCert {N3} (stepFactor g {q}) {self.lname(p)} {self.lname(m)} :=\n"
                            f"  stepCert_runs {N3} (stepFactor g {q}) [{', '.join(self.pchunks(p))}]\n"
                            f"    [{', '.join(f'Tt_D_{i}_c{j}' for j in range(k))}] {self.lname(m)}\n    {f2}\n"
                            "    (by decide +kernel)\n"]
                    imps = pimports + cms + [self.datamod[m]]
                body.append(f"theorem Tt_c_{i} : ChainCert {N3} (psFactors g {qlist(m)}) [([], 1)] {self.lname(m)} :=\n"
                            f"  chainCert_snoc {N3} g {qlist(p)} {q} _ _ _ {self.chain(p)} Tt_s_{i}\n")
                self.chainmod[m] = write(f"S_{i}", list(dict.fromkeys(imps)), f"the step to the stored node {qlist(m)}", body)
                # profile of a stored node, from its stored chunks
                cs = self.chunks[m]
                groups = V.split(list(range(len(cs))), max(1, PROF_B // max(1, self.csize[m])))
                Ps = [prof(c) for c in cs]
                body = []
                for j in range(len(cs)):
                    body.append(f"def Tt_P_{i}_c{j} : List ((ℕ × ℕ) × ℚ) := {V.penc(Ps[j])}\n")
                    body.append(f"theorem Tt_pq_{i}_c{j} : abProfile {self.lname(m, j)} = Tt_P_{i}_c{j} := by\n  decide +kernel\n")
                P = prof(self.L[m])
                assert V.merge_profiles(Ps) == P
                k = len(cs)
                f2 = "".join(f"(List.Forall₂.cons Tt_pq_{i}_c{j} " for j in range(k)) + "List.Forall₂.nil" + ")" * k
                body.append(f"theorem Tt_pc_{i} : ProfCert {N3} g {qlist(m)} Tt_P_{i} :=\n"
                            f"  profCert_of_chunks _ _ _ [{', '.join(self.lname(m, j) for j in range(k))}]\n"
                            f"    [{', '.join(f'Tt_P_{i}_c{j}' for j in range(k))}] _ Tt_c_{i}\n    {f2}\n    (by decide +kernel)\n")
                self.profmods.append(write(f"P_{i}", [self.chainmod[m], PDATA], f"the moment profile of {qlist(m)}", body))
        # leaves
        for p in self.stored:
            leaves = [c for c in self.children[p] if c not in self.stored]
            small = [c for c in leaves if self.gen[c] <= GEN_B]
            large = [c for c in leaves if self.gen[c] > GEN_B]
            pimports = [x for x in (self.datamod[p], self.chainmod[p]) if x] or ["Solution.SymTrie"]
            groups, cur, tot = [], [], 0
            for c in small:
                if cur and tot + self.gen[c] > GEN_B:
                    groups.append(cur)
                    cur, tot = [], 0
                cur.append(c)
                tot += self.gen[c]
            if cur:
                groups.append(cur)
            for gi, grp in enumerate(groups):
                body = []
                for c in grp:
                    i, q = ident(c), c[-1]
                    P = prof(self.L[c])
                    body.append(f"theorem Tt_pc_{i} : ProfCert {N3} g {qlist(c)} Tt_P_{i} :=\n"
                                f"  profCert_of_step {N3} g {qlist(p)} {self.lname(p)} {q} _ {self.chain(p)}\n"
                                "    (by decide +kernel)\n")
                self.profmods.append(write(f"G_{ident(p)}_{gi}", pimports + ["Solution.SymTrie", PDATA],
                                           f"moment profiles of leaves of {qlist(p)}", body))
            for c in large:
                i, q = ident(c), c[-1]
                cms, Ps = [], []
                for j, (cn, cd) in enumerate(zip(self.pchunks(p), self.pchunk_data(p))):
                    Pj = prof(S.normalize(self.step_entries(cd, q)))
                    Ps.append(Pj)
                    cms.append(write(f"L_{i}_C{j}", [x for x in [self.datamod[p]] if x] + ["Solution.SymTrie"],
                                     f"moment profile of {qlist(c)}, parent chunk {j}",
                                     [f"def Tt_P_{i}_c{j} : List ((ℕ × ℕ) × ℚ) := {V.penc(Pj)}\n",
                                      f"theorem Tt_pq_{i}_c{j} : abProfile (symStepAll {N3} (stepFactor g {q}) {cn}) =\n"
                                      f"    Tt_P_{i}_c{j} := by\n  decide +kernel\n"]))
                P = prof(self.L[c])
                assert V.merge_profiles(Ps) == P
                k = len(Ps)
                f2 = "".join(f"(List.Forall₂.cons Tt_pq_{i}_c{j} " for j in range(k)) + "List.Forall₂.nil" + ")" * k
                body = [f"theorem Tt_pc_{i} : ProfCert {N3} g {qlist(c)} Tt_P_{i} :=\n"
                        f"  profCert_of_step_chunks {N3} g {qlist(p)} [{', '.join(self.pchunks(p))}] {q}\n"
                        f"    [{', '.join(f'Tt_P_{i}_c{j}' for j in range(k))}] _ {self.chain(p)}\n    {f2}\n"
                        "    (by decide +kernel)\n"]
                self.profmods.append(write(f"L_{i}", [x for x in pimports if x] + cms + [PDATA],
                                           f"the moment profile of the leaf {qlist(c)}", body))


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    T = Trie()
    T.emit(root)
    nodes = [m for m in T.nodes if m]
    # assembly: trie and profiles
    trie_lit = "[" + ", ".join(f"({qlist(m)}, {T.lname(m)})" for m in reversed(T.stored) if m) + ", ([], [([], 1)])]"
    trie_pf = "(trieOK_root _ g)"
    for m in T.stored:
        if m:
            trie_pf = f"(trieOK_cons_chain _ g _ {qlist(m)} _ Tt_c_{ident(m)} {trie_pf})"
    prof_pf = "(profOK_cons _ g [] [] Tt_P_root Tt_pc_root (profOK_nil _ g))"
    for m in nodes:
        prof_pf = f"(profOK_cons _ g _ {qlist(m)} _ Tt_pc_{ident(m)}\n    {prof_pf})"
    imports = [PDATA] + sorted(set(T.profmods))
    o = [HDR + "".join(f"import {i}\n" for i in imports) + "\n"
         "/-! # V2m: the certified subtree at Table 3, piece (6, 3)\n\n"
         "(generated by `specs/checks/sym_trie_v2m_demo.py`) -/\n\nnamespace BGP212.V2e\n\n" + OPEN,
         "/-- **Definition (certified trie).** The stored nodes and their states. -/\n"
         f"def Tt_trie : List (List ℕ × List (SKey × ℚ)) :=\n  {trie_lit}\n",
         f"theorem Tt_trie_ok : TrieOK {N3} g Tt_trie :=\n  {trie_pf}\n",
         f"theorem Tt_pc_root : ProfCert {N3} g [] Tt_P_root :=\n"
         f"  profCert_of_chain _ _ _ _ _ (chainCert_nil {N3} [([], 1)]) (by decide +kernel)\n",
         f"theorem Tt_prof_ok : ProfOK {N3} g Tt_prof :=\n  {prof_pf}\n",
         "end BGP212.V2e\n"]
    open(os.path.join(root, "Solution", "SymTrieNodes.lean"), "w").write("\n".join(o))
    demos = write_demos(root, T)
    order = T.order + ["Solution.SymTrieNodes"]
    sh = ["#!/usr/bin/env bash",
          "# V2m: build the certified subtree one `lean` process at a time (for a 3.8 GiB machine without",
          "# swap): each `lake build` below finds its dependencies already built and runs one `lean`.",
          "set -euo pipefail",
          "lake build Solution.SymTrie Solution.SymStagedDemo6",
          "for m in \\"] + [f"  {m} \\" for m in order + demos] + ["  ; do", "  echo \"== $m\"", "  lake build \"$m\"", "done", "lake build Solution.SymTrieSuite Challenge.SymTrie", ""]
    os.makedirs(os.path.join(root, "specs", "checks"), exist_ok=True)
    open(os.path.join(root, "specs", "checks", "sym_trie_v2m_build.sh"), "w").write("\n".join(sh))
    os.chmod(os.path.join(root, "specs", "checks", "sym_trie_v2m_build.sh"), 0o755)
    print("nodes", len(nodes), "stored", len([m for m in T.stored if m]), "leaves", len(nodes) - len([m for m in T.stored if m]),
          "modules", len(T.order), "max len", max(map(len, nodes)), "max degree", max(map(sum, nodes)),
          "generated", sum(T.gen.values()))
    T.summary = dict(nodes=len(nodes))


def prof_table(T, ws):
    groups = {}
    for (w, a1, l1, a2, l2) in ws:
        for (K1, p1, q1, c1) in Q.innerTerms(a1, l1):
            for (K2, p2, q2, c2) in Q.innerTerms(a2, l2):
                key = (tuple(sorted(K1 + K2, reverse=True)), p1 + p2, q1 + q2)
                groups[key] = groups.get(key, Fr(0)) + w * c1 * c2
    acc = {}
    for (Qd, m, nn), c in sorted(groups.items()):
        for (A, B), v in prof(T.L[Qd]):
            acc[(A, B, m, nn)] = acc.get((A, B, m, nn), Fr(0)) + c * v
    return sorted(acc.items())


def ws_lit(ws):
    return "[" + ", ".join(f"(({V.rlit(w)} : ℚ), {a1}, {qlist(l1)}, {a2}, {qlist(l2)})" for (w, a1, l1, a2, l2) in ws) + "]"


PART_B = 120000      # bytes of looked-up profile literals per certified table part (block |λ| ≤ 6)
PART_B1 = 100000     # the same for the one-part generators (larger rationals)
MERGE_K = 4          # tables per kernel merge check
RECDEPTH = "set_option maxRecDepth 20000\n\n"


def write_demos(root, T):
    hd = lambda imps, doc: (HDR + "".join(f"import {i}\n" for i in imps) + "\n" +  # noqa: E731
                            f"/-! # V2m: {doc}\n\nCOMPUTATIONAL DEMONSTRATION (generated by "
                            "`specs/checks/sym_trie_v2m_demo.py`). Tables are coefficient representations;\n"
                            "the rational moments `pieceMn` are evaluated separately. -/\n\nnamespace BGP212.V2e\n\n" + OPEN)
    sol = lambda name: os.path.join(root, "Solution", f"{name}.lean")  # noqa: E731
    out = lambda name, parts: open(sol(name), "w").write("\n".join(parts + ["end BGP212.V2e\n"]))  # noqa: E731
    mods = []
    # the kept-part lists of B₂₁, certified once
    kl = "[" + ", ".join(qlist(x) for x in sorted(kept(lambda l: True))) + "]"
    out("SymTrieKept", [hd(["BGP212.SymTrie"], "the kept-part lists of B₂₁ (certified once, reused below)"),
                        f"/-- The 139 kept-part lists of `B₂₁`, in `natListCmp` order. -/\ndef b21KeptLit : List (List ℕ) :=\n  {kl}\n",
                        "theorem b21Kept_eq : b21Kept = b21KeptLit := by\n  decide +kernel\n"])
    mods.append("Solution.SymTrieKept")
    # Demo 1: counts and shapes
    out("SymTrieDemo1", [hd(["Solution.SymTrieKept"], "counts and trie shapes of the enumerated multisets"),
         "/-- The `B₂₁` partitions and kept-part lists: 139 each. -/\n"
         "theorem b21_counts : b21Lambdas.length = 139 ∧ b21Kept.length = 139 :=\n"
         "  ⟨by decide +kernel, by rw [b21Kept_eq]; decide +kernel⟩\n",
         "/-- The block `|λ| ≤ 6`: 22 factor multisets, sorted and prefix-closed. -/\n"
         "theorem block6_shape : (blockMultisets 6).length = 22 ∧ trieShapeOK (blockMultisets 6) = true := by\n  decide +kernel\n",
         "/-- The multisets of `B₂₁` with at most two factors: 66, sorted and prefix-closed. -/\n"
         "theorem short2_shape : (shortMultisets 2).length = 66 ∧ trieShapeOK (shortMultisets 2) = true := by\n"
         "  rw [shortMultisets, b21Kept_eq]; decide +kernel\n"])
    mods.append("Solution.SymTrieDemo1")
    out("SymTrieDemo2", [hd(["Solution.SymTrieKept", PDATA], "the certified subtree covers the enumerated multisets"),
         "/-- **Coverage.** Every multiset of the block `|λ| ≤ 6` and every multiset of `B₂₁` with at most\n"
         "two factors has a certified moment profile at piece `(6, 3)` (`Tt_prof_ok`). -/\n"
         "theorem Tt_covers : ((blockMultisets 6).all fun Q => natListMem Q (Tt_prof.map Prod.fst)) = true ∧\n"
         "    ((shortMultisets 2).all fun Q => natListMem Q (Tt_prof.map Prod.fst)) = true := by\n"
         "  rw [shortMultisets, b21Kept_eq]; decide +kernel\n"])
    mods.append("Solution.SymTrieDemo2")
    piece = "(fun A B m n => pieceMn 44 6 3 A B g L τ C m n)"
    wsum = lambda ws: (f"(List.map (fun w : WPair ℚ => w.1 * genPieceWith 44 6 3 g\n"  # noqa: E731
                       f"    {piece} w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)\n    {ws_lit(ws)}).sum")

    def table(k, name, doc, ws, Tb):
        out(f"SymTrieTab{k}", [hd([PDATA], doc + " (the table)") + RECDEPTH,
             f"theorem {name} : profTable 44 6 3 g Tt_prof {ws_lit(ws)} =\n    ({V.tenc(Tb)}) := by\n  decide +kernel\n"])
        mods.append(f"Solution.SymTrieTab{k}")

    # Demo 3: J_T[P_(2,2,2), P_(2,2,2)] again (V2ℓ's statement) from the trie profiles
    ws = [(Fr(1), 0, (2, 2, 2), 0, (2, 2, 2))]
    Tb = prof_table(T, ws)
    assert Tb == S.gen_table(6, 3, 0, [2, 2, 2], 0, [2, 2, 2])
    table(3, "tabT_P222_6_3", "V2ℓ's degree-12 table from the trie profiles", ws, Tb)
    out("SymTrieDemo3", [hd(["Solution.SymTrieNodes", "Solution.SymTrieTab3", "Solution.SymStagedDemo6"],
                            "V2ℓ's degree-12 table from the trie profiles") + RECDEPTH,
         "theorem genPieceP222_6_3_trie_expansion : genPiece 44 6 3 g L τ C 0 [2, 2, 2] 0 [2, 2, 2] =\n"
         f"    tableVal ({V.tenc(Tb)})\n      {piece} :=\n"
         "  (genPieceWith_eq_profTable 44 6 3 g Tt_prof Tt_prof_ok _ 0 [2, 2, 2] 0 [2, 2, 2]).trans\n"
         f"    (congrArg (fun T => tableVal T {piece}) tabT_P222_6_3)\n",
         "/-- The same statement as V2ℓ's `genPieceP222_6_3_staged_expansion`. -/\n"
         "theorem genPieceP222_6_3_trie_same : genPieceP222_6_3_trie_expansion =\n    genPieceP222_6_3_staged_expansion := rfl\n"])
    mods.append("Solution.SymTrieDemo3")
    pbytes = {}

    def cost(w):
        c_ = 0
        for (K1, *_r) in Q.innerTerms(w[1], w[2]):
            for (K2, *_r2) in Q.innerTerms(w[3], w[4]):
                key = tuple(sorted(K1 + K2, reverse=True))
                if key not in pbytes:
                    pbytes[key] = len(V.penc(prof(T.L[key])))
                c_ += pbytes[key]
        return c_

    def parted(k, tag, doc, ws, docstring, stmt, budget):
        """Certified parts of `ws` (each one kernel table check), merged in a tree of MERGE_K-way merges."""
        wss, cur, tot = [], [], 0
        for w in ws:
            if cur and tot + cost(w) > budget:
                wss.append(cur)
                cur, tot = [], 0
            cur.append(w)
            tot += cost(w)
        wss.append(cur)
        Ts = [prof_table(T, w) for w in wss]
        Tb = V.merge_profiles(Ts)
        assert Tb == prof_table(T, ws)
        lit = f"(fun A B m n => pieceMn 44 6 3 A B g L τ C m n)"
        # leaves: (name of table, ws, proof that the weighted sum is its table value, module)
        level = []
        for r, (w, Tr) in enumerate(zip(wss, Ts)):
            out(f"SymTrieTab{k}_R{r}", [hd([PDATA], f"{doc}, part {r}") + RECDEPTH,
                 f"def Tt_T{k}_{r} : List (MKey × ℚ) :=\n  {V.tenc(Tr)}\n",
                 f"theorem tabT_{tag}_{r} : profTable 44 6 3 g Tt_prof {ws_lit(w)} = Tt_T{k}_{r} := by\n  decide +kernel\n"])
            mods.append(f"Solution.SymTrieTab{k}_R{r}")
            pf = (f"((trieProf_table_eq 44 6 3 g Tt_prof Tt_prof_ok {ws_lit(w)} {lit}).trans\n"
                  f"      (congrArg (fun T => tableVal T {lit}) tabT_{tag}_{r}))")
            level.append((f"Tt_T{k}_{r}", w, Tr, pf, f"Solution.SymTrieTab{k}_R{r}"))
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
                name = f"Tt_T{k}_M{depth}_{gi}"
                thm = f"tabT_{tag}_M{depth}_{gi}"
                rhs = f"({V.tenc(Tm)})" if final else name
                body = [] if final else [f"def {name} : List (MKey × ℚ) :=\n  {V.tenc(Tm)}\n"]
                body.append(f"theorem {thm} : mergeAll mkeyCmp 64 [{', '.join(x[0] for x in grp)}] =\n"
                            f"    {rhs} := by\n  decide +kernel\n")
                mname = f"SymTrieTab{k}_M{depth}_{gi}" if not final else f"SymTrieTab{k}"
                out(mname, [hd([x[4] for x in grp], f"{doc}, merge {depth}.{gi}") + RECDEPTH] + body)
                mods.append(f"Solution.{mname}")
                f2 = "".join(f"(List.Forall₂.cons\n    {x[3]} " for x in grp) + "List.Forall₂.nil" + ")" * len(grp)
                pf = (f"(table_parts_merge 44 6 3 g {lit}\n    [{', '.join(ws_lit(x[1]) for x in grp)}]\n"
                      f"    {ws_lit(wm)} rfl _\n    {f2}\n    _ {thm})")
                nxt.append((name, wm, Tm, pf, f"Solution.{mname}"))
            level = nxt
        assert level[0][1] == ws and level[0][2] == Tb and depth >= 1
        out(f"SymTrieDemo{k}", [hd(["Solution.SymTrieNodes", f"Solution.SymTrieTab{k}"], doc) + RECDEPTH,
             docstring.replace("PARTS", str(len(wss))) +
             f"theorem {stmt} : {wsum(ws)} =\n"
             f"    tableVal ({V.tenc(Tb)})\n      {piece} :=\n  {level[0][3]}\n"])
        mods.append(f"Solution.SymTrieDemo{k}")
        return Tb, len(wss)

    # Demo 4: the block |λ| ≤ 6, all 49 pairs of the generators P_λ, weights c_i c_j with c = 1, …, 7
    lams = sorted({l for l in LAMBDAS if sum(l) <= 6}, key=lambda l: (sum(l), l))
    c = {l: Fr(i + 1) for i, l in enumerate(lams)}
    ws = [(c[x] * c[y], 0, x, 0, y) for x in lams for y in lams]
    gen_check = {}
    for (w, a1, l1, a2, l2) in ws:
        for s_, v in S.gen_table(6, 3, a1, list(l1), a2, list(l2)):
            gen_check[s_] = gen_check.get(s_, Fr(0)) + w * v
    Tb, T.block_parts = parted(4, "block6", "the block |λ| ≤ 6 of B₂₁ at piece (6, 3)", ws,
        "/-- **The block `|λ| ≤ 6`.** `Σ_{i,j} cᵢ cⱼ J_T[P_{λᵢ}, P_{λⱼ}]` on piece `(6, 3)` for the seven\n"
        "generators `P_λ`, `|λ| ≤ 6`, with `c = 1, …, 7`: 49 pairs, one table from 22 certified profiles\n"
        "(PARTS certified parts merged by `table_parts_merge`). -/\n", "block6_6_3_expansion", PART_B)
    assert {s_: v for s_, v in Tb if v != 0} == {s_: v for s_, v in gen_check.items() if v != 0}
    T.block_keys = len(Tb)
    # Demo 5: one-part generators P_{2i}, i = 1, …, 10, all 100 pairs (degree up to 40), in parts
    lams1 = [(2 * i,) for i in range(1, 11)]
    ws = [(Fr(1), 0, x, 0, y) for x in lams1 for y in lams1]
    Tb, T.onepart_parts = parted(5, "onepart", "the one-part generators P_{2i} at piece (6, 3)", ws,
        "/-- **One-part generators.** `Σ_{i,j} J_T[P_{2i}, P_{2j}]`, `1 ≤ i, j ≤ 10`, on piece `(6, 3)`: 100 pairs\n"
        "(factor degrees up to 40) from the certified profiles of the multisets with at most two factors\n"
        "(PARTS certified parts merged in a tree by `table_parts_merge`). -/\n", "onepart_6_3_expansion",
        PART_B1)
    T.onepart_keys = len(Tb)
    # Demo 6: degree 40: J_T[P_20, P_20]
    ws = [(Fr(1), 0, (20,), 0, (20,))]
    Tb = prof_table(T, ws)
    assert Tb == S.gen_table(6, 3, 0, [20], 0, [20])
    table(6, "tabT_P20_6_3", "degree 40: J_T[P_20, P_20] at piece (6, 3)", ws, Tb)
    out("SymTrieDemo6", [hd(["Solution.SymTrieNodes", "Solution.SymTrieTab6"], "degree 40: J_T[P_20, P_20] at piece (6, 3)") + RECDEPTH,
         "/-- **Degree 40.** Piece `(6, 3)` of `J_T[P_20, P_20]` as an explicit combination of moments. -/\n"
         "theorem genPieceP20_6_3_trie_expansion : genPiece 44 6 3 g L τ C 0 [20] 0 [20] =\n"
         f"    tableVal ({V.tenc(Tb)})\n      {piece} :=\n"
         "  (genPieceWith_eq_profTable 44 6 3 g Tt_prof Tt_prof_ok _ 0 [20] 0 [20]).trans\n"
         f"    (congrArg (fun T => tableVal T {piece}) tabT_P20_6_3)\n"])
    mods.append("Solution.SymTrieDemo6")
    print("tables: block", T.block_keys, "keys in", T.block_parts, "parts; one-part", T.onepart_keys, "keys in",
          T.onepart_parts, "parts; P20", len(Tb))
    return mods


if __name__ == "__main__":
    main()
