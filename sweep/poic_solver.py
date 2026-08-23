"""POIC_2 membership test: is f = sign( sum_t L_t / prod_{j in J_t} B_j ) for some
admissible positive pool B and affine numerators L?   For fixed B the test is an LP."""
import numpy as np, itertools, time, sys
from scipy.optimize import linprog, minimize
from scipy import sparse
from hs2 import cube

def poic_hinge(X,f,pattern,orients,W,ret=False):
    npts,n=X.shape
    B=[]
    for h in range(len(orients)):
        z=X if orients[h]>0 else (1.0-X)
        B.append(1.0+z@W[h])
    cols=[]
    for J in pattern:
        den=np.ones(npts)
        for j in J: den=den*B[j]
        cols.append((1.0/den).reshape(npts,1)); cols.append(X/den[:,None])
    A=np.hstack(cols)*(2.0*f-1.0)[:,None]; nc=A.shape[1]
    Aub=sparse.hstack([sparse.csr_matrix(-A),-sparse.eye(npts,format='csr')])
    obj=np.concatenate([np.zeros(nc),np.ones(npts)])
    bnds=[(None,None)]*nc+[(0,None)]*npts
    r=linprog(obj,A_ub=Aub,b_ub=-np.ones(npts),bounds=bnds,method='highs')
    if r.status!=0: return (np.inf,None) if ret else np.inf
    return (float(r.fun),r.x[:nc]) if ret else float(r.fun)

def poic_solve(X,f,pattern,s,restarts=4,maxfev=900,seed=0):
    n=X.shape[1]; rr=np.random.default_rng(seed); best=np.inf
    for orients in itertools.product([1,-1],repeat=s):
        for t in range(restarts):
            w0=rr.normal(-0.5,1.0,s*n)
            def obj(p):
                v=poic_hinge(X,f,pattern,orients,np.exp(np.clip(p,-25.0,25.0)).reshape(s,n))
                return v if np.isfinite(v) else 1e12
            res=minimize(obj,w0,method='Nelder-Mead',options={'maxfev':maxfev,'xatol':1e-3,'fatol':1e-9})
            if res.fun<best: best=res.fun
            if best<1e-9: return 0.0
    return best

if __name__=="__main__":
    n=9; X=cube(n)
    d=np.abs(X[:,:4]-X[:,4:8]).sum(1)
    f8=(d>=2).astype(float); z=X[:,8]
    f=np.abs(f8-z)                                   # f_8 XOR z, the lab's central target
    print("f_8 XOR z on 9 bits, |f|=%d/512   (deg_pm = 3)"%int(f.sum()),flush=True)
    pats={'all-singleton {1},{2},{3}  (= H*<=3)':[[0],[1],[2]],
          'mixed        {1},{2},{1,3}':[[0],[1],[0,2]],
          'pure 3-cycle {1,2},{2,3},{3,1}':[[0,1],[1,2],[2,0]]}
    for name,pat in pats.items():
        t0=time.time()
        v=poic_solve(X,f,pat,3,restarts=4,maxfev=900,seed=3)
        print("  %-32s : %s   [%.0fs]"%(name,"FEASIBLE" if v<1e-9 else "fails, hinge=%.3f"%v,time.time()-t0),flush=True)
