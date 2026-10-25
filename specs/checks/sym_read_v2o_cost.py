#!/usr/bin/env python3
"""V2o exploratory cost analysis (Python only; not a certificate).

For the 150 three-factor nodes of B₂₁ at Table 3, piece (6, 3), and their 54 two-factor parents:
  * stored information of each parent beyond its profile: order-1 marks (V2n), the binomial read
    summary of degree d (the largest child degree), and the minimum Σ min(|E|, d) over the groups
    (A, B, c) with exponent sets E;
  * kernel work for the leaves: marks route (V2n's order-0 step) and summary route (computing the
    summary, then readStep);
and, for the 66 nodes of degree ≤ 26 certified in V2o, the comparison with V2m's staged route and
V2n's multi-level route.

Usage: python3 -I specs/checks/sym_read_v2o_cost.py
"""
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_trie_v2m_demo as D, sym_profile_v2n_model as M, sym_profile_v2n_demo as N
from math import comb, factorial
T=D.Trie()
kall=D.kept(lambda l: True)
three=sorted({tuple(sorted(x+y,reverse=True)) for x in kall for y in kall if len(x)+len(y)==3})
parents=sorted({m[:2] for m in three})
kids={p:[m for m in three if m[:2]==p] for p in parents}
def AB(k): return M.AB(k)
tot=dict(states=0,marks=0,prof=0,bm=0,bm_needed=0,emit_bm=0,emit_marks=0,staged=0)
def supp(q):
    f=N.fac(q); return {c:[a for a in range(1,len(f(c))) if f(c)[a]!=0] for c in range(3)}
for p in parents:
    L=T.L[p]
    tot['states']+=len(L); tot['staged']+=sum(len(T.step_entries(L,m[2])) for m in kids[p])
    P1=M.aug(1,L)
    marks=[k for k in P1 if len(k[2])==1]; prof=[k for k in P1 if len(k[2])==0]
    tot['marks']+=len(marks); tot['prof']+=len(prof)
    abc={(A,B,u[0][0]) for (A,B,u) in marks}
    qmax=max(m[2] for m in kids[p])
    tot['bm']+=len(abc)*qmax
    need=set()
    for m in kids[p]:
        s=supp(m[2])
        for (A,B,c) in abc:
            for a in s[c]: need.add((A,B,c,a))
        # emission: bm route
        tot['emit_bm']+=len(prof)*(1+sum(len(s[c]) for c in range(3))) + sum(len(s[c]) for (A,B,c) in abc)
        tot['emit_marks']+=len(M.emit(0,N.NCLS,N.fac(m[2]),[(k,v) for k,v in P1.items()]))
    tot['bm_needed']+=len(need)
print(len(three),len(parents)); print(tot)
# summary cost and minimal dimension
tot2=dict(bm_cost=0, mindim=0, abc=0, Esizes=[])
for p in parents:
    L=T.L[p]; P1=M.aug(1,L); qmax=max(m[2] for m in kids[p])
    marks=[(k,v) for k,v in P1.items() if len(k[2])==1]
    tot2['bm_cost']+=len(marks)*qmax
    E={}
    for (A,B,u),v in marks: E.setdefault((A,B,u[0][0]),set()).add(u[0][1])
    tot2['abc']+=len(E)
    for key,es in E.items():
        tot2['mindim']+=min(len(es),qmax); tot2['Esizes'].append(len(es))
import collections
print({k:v for k,v in tot2.items() if k!='Esizes'}, collections.Counter(tot2['Esizes']).most_common(6))
print("bm route total", tot2['bm_cost']+tot['emit_bm'])

import sym_read_v2o_demo as O, sym_profile_v2n_model as M, sym_profile_v2n_demo as N
pl=O.Plan(); T=pl.T
# V2m staged route for the same leaves: generated entries of the leaf steps from parent states
staged_leaf=sum(len(T.step_entries(T.L[m[:2]],m[2])) for m in pl.leaves)
staged_states=sum(len(O.S.normalize(T.step_entries(T.L[m[:2]],m[2]))) for m in pl.leaves)
# V2n multi-level route: parents' order-1 marks by direct steps from the one-factor nodes' order-2 marks
src={}
v2n_par=0
for p in pl.parents:
    x=p[:1]
    if x not in src: src[x]=M.aug_lean(2,T.L[x])
    v2n_par+=len(M.emit(1,N.NCLS,N.fac(p[1]),src[x]))
srcm=sum(len(v) for v in src.values())
v2o_leaf=sum(len(M.emit(0,N.NCLS,N.fac(m[2]),pl.P1[m[:2]])) for m in pl.leaves)
print(dict(staged_leaf_gen=staged_leaf, staged_leaf_states=staged_states, v2n_parent_emit=v2n_par, v2n_source_marks=srcm,
           v2o_leaf_emit=v2o_leaf, parents_marked=sum(len(pl.P1[p]) for p in pl.parents), parents_states=sum(len(T.L[p]) for p in pl.parents)))
