#!/usr/bin/env python3
"""V2n exploratory projection: direct (order-1 marks of the two-factor parents, then order-0 leaves) against
staged (V2m) for the three-factor layer of B₂₁ at Table 3, piece (6, 3). Python only; not a certificate.

Usage: python3 -I specs/checks/sym_profile_v2n_projection.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_trie_v2m_demo as D  # noqa: E402
import sym_profile_v2n_model as M  # noqa: E402
import sym_profile_v2n_demo as N  # noqa: E402
T=D.Trie()
kall=D.kept(lambda l: True)
three=sorted({tuple(sorted(x+y,reverse=True)) for x in kall for y in kall if len(x)+len(y)==3})
print("three-factor multisets",len(three))
parents=sorted({m[:2] for m in three}); print("two-factor parents",len(parents))
# staged: generated entries to reach each 3-factor node from the 2-factor parent's states
L={}
def st(m):
    if m in L: return L[m]
    if m in T.L: L[m]=T.L[m]; return L[m]
    L[m]=D.S.normalize(T.step_entries(st(m[:-1]),m[-1])); return L[m]
staged=0; direct_leaf=0; direct_par=0; par_marked=0; par_states=0
gp_marked={}
for p in parents:
    g=p[:1]
    if g not in gp_marked: gp_marked[g]=M.aug_lean(2,st(g))
    PP=gp_marked[g]
    em=M.emit(1,N.NCLS,N.fac(p[1]),PP); direct_par+=len(em)
    P1=M.step_lean(1,N.NCLS,N.fac(p[1]),PP); par_marked+=len(P1); par_states+=len(st(p))
    for m in three:
        if m[:2]==p:
            staged+=len(T.step_entries(st(p),m[2]))
            direct_leaf+=len(M.emit(0,N.NCLS,N.fac(m[2]),[e for e in P1 if len(e[0][2])<=1]))
print("staged generated (3-factor steps)",staged)
print("direct: parents order-1 emitted",direct_par,"leaves emitted",direct_leaf,"total",direct_par+direct_leaf)
print("parents: states",par_states,"order-1 marked entries",par_marked)
