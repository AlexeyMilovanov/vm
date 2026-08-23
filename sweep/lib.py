"""Candidate-function library for the POIC_2 vs H* sweep."""
import numpy as np, itertools
from hs2 import cube

def _pairdist(n2):
    m=n2//2; X=cube(n2); d=np.abs(X[:,:m]-X[:,m:]).sum(1); return X,d

def library():
    """Returns list of (name, X, f). Every f is nonconstant."""
    out=[]
    for n2 in (8,10):
        X,d=_pairdist(n2); m=n2//2
        for k in range(1,m+1):
            out.append(("T%d_n%d"%(k,n2), X, (d>=k).astype(float)))
        for a in range(0,m+1):
            for b in range(a,m+1):
                if (a,b)==(0,m): continue
                f=((d>=a)&(d<=b)).astype(float)
                if 0<f.sum()<len(f): out.append(("W%d%d_n%d"%(a,b,n2),X,f))
    # fresh-XOR of the 8-bit gates with a 9th bit
    X9=cube(9); d9=np.abs(X9[:,:4]-X9[:,4:8]).sum(1)
    for k in (1,2,3):
        out.append(("T%dxorz_n9"%k, X9, np.abs((d9>=k).astype(float)-X9[:,8])))
    # random degree-2 PTFs at n=8 (deterministic seeds)
    X=cube(8); pairs=list(itertools.combinations(range(8),2))
    for s in range(40):
        rr=np.random.default_rng(1000+s)
        Q=rr.normal()+X@rr.normal(0,1,8)+sum(c*X[:,a]*X[:,b] for c,(a,b) in zip(rr.normal(0,1,len(pairs)),pairs))
        if np.abs(Q).min()<1e-9: continue
        f=(Q>0).astype(float)
        if 6<f.sum()<250: out.append(("rq%02d_n8"%s,X,f))
    return out

ORBITS=[("A",[[0],[1],[0,1]],2),
        ("B",[[0],[1],[0,2]],3),
        ("C",[[0,1],[1,2],[2,0]],3),
        ("D",[[0],[1,2]],3),
        ("Fp",[[0],[0,1],[1,2]],3)]
