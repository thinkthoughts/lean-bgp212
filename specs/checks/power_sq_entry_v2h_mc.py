#!/usr/bin/env python3
"""Vectorized Monte Carlo for J_T[P2, P2] at Table 3 (numpy; exploratory check for V2h).

Uniform samples of the tau-simplex in R^44, true rough-set endpoint, untranslated power sum.
Usage: python3 -I specs/checks/power_sq_entry_v2h_mc.py SAMPLES SEED  (SAMPLES a multiple of 200000)
Prints the estimate, its standard error and z against the certified value.
"""
import numpy as np, math, sys
BNUM=[777,794,875,917,953,983,1016,1042,1063,1081]
g,L,tau=41/625,53/50,249/250
Cv=np.array([0.0]+[4*BNUM[min(m,10)-1]/5000 for m in range(1,47)])
rng=np.random.default_rng(int(sys.argv[2])); n=int(sys.argv[1]); B=200000
vals=[]
for _ in range(n//B):
    e=rng.exponential(size=(B,45)); x=tau*e[:,:44]/e.sum(1,keepdims=True)
    S=x.sum(1); m=x>g; cnt=m.sum(1); rho=(x*m).sum(1)
    ok=rho<=Cv[cnt]; U=np.minimum(L-S,np.maximum(g,Cv[np.minimum(cnt+1,46)]-rho))
    v=(U*(x*x).sum(1)+U**3/3)**2*ok; vals.append(v)
v=np.concatenate(vals); vol=tau**44/math.factorial(44)
print(45*vol*v.mean(), 45*vol*v.std()/math.sqrt(len(v)), (45*vol*v.mean()-2.2710673939201377e-58)/(45*vol*v.std()/math.sqrt(len(v))))
