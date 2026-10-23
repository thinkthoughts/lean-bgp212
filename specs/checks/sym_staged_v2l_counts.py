#!/usr/bin/env python3
"""V2ℓ exploratory counts over the 846 generators of B₂₁ (not theorems).

Generators (L − P₁)^a P_λ with λ of even parts, a + |λ| ≤ 21 (V0). For each generator the inner
integral keeps a sub-list of the parts of λ (V2i's `subsetTerms`); a Gram entry pairs two of them.
Counts: distinct ordered kept-part lists; distinct ordered factor lists t₁ ++ t₂ and distinct
multisets (V2ℓ's `placeVal_perm`: one run per multiset); the prefix trie of the sorted multisets
(V2ℓ's `chainCert_snoc`: one certified step per trie node).

Usage: python3 -I specs/checks/sym_staged_v2l_counts.py
"""
import itertools
def parts(j, k):  # partitions of j with parts <= k, descending
    if j == 0: yield (); return
    for p in range(min(j, k), 0, -1):
        for r in parts(j - p, p): yield (p,) + r
gens = []
for j in range(0, 11):
    for lam in parts(j, j):
        l = tuple(2 * x for x in lam)
        for a in range(0, 21 - 2 * j + 1):
            gens.append((a, l))
print("generators", len(gens))
def subsets(l):
    if not l: return [((), 0)]
    q, rest = l[0], l[1:]
    st = subsets(rest)
    return [((q,) + K, s) for K, s in st] + [(K, s + q) for K, s in st]
kept = set()
for a, l in gens:
    for K, s in subsets(l): kept.add(K)
print("distinct kept-part lists (ordered)", len(kept))
ordered = set(); multis = set()
for x in kept:
    for y in kept:
        ordered.add(x + y); multis.add(tuple(sorted(x + y, reverse=True)))
print("distinct factor lists t1++t2: ordered", len(ordered), "multisets", len(multis))
# prefix trie over sorted multisets (descending order): number of distinct nonempty prefixes = steps
pref = set()
for m in multis:
    for i in range(1, len(m) + 1): pref.add(m[:i])
print("prefix-shared steps", len(pref), "vs unshared steps", sum(len(m) for m in multis), "max length", max(len(m) for m in multis))
asc=set()
for m in multis:
    mm=tuple(sorted(m))
    for i in range(1,len(mm)+1): asc.add(mm[:i])
print("prefix-shared steps (ascending order)", len(asc))
