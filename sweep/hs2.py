import numpy as np, itertools, time, sys
from scipy.optimize import linprog, minimize
from scipy import sparse
rng=None

def cube(n): return ((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)

def hinge(X,f,orients,W,ret=False):
    """min sum xi  s.t. sigma*(c+sum N_h/D_h) >= 1-xi ;  returns hinge value (0 == representable)"""
    npts,n=X.shape; H=len(orients)
    cols=[np.ones((npts,1))]
    for h in range(H):
        z=X if orients[h]>0 else (1.0-X)
        D=1.0+z@W[h]
        cols.append((1.0/D).reshape(npts,1)); cols.append(X/D[:,None])
    A=np.hstack(cols)*(2.0*f-1.0)[:,None]; nc=A.shape[1]
    Aub=sparse.hstack([sparse.csr_matrix(-A),-sparse.eye(npts,format='csr')])
    obj=np.concatenate([np.zeros(nc),np.ones(npts)])
    bnds=[(None,None)]*nc+[(0,None)]*npts
    r=linprog(obj,A_ub=Aub,b_ub=-np.ones(npts),bounds=bnds,method='highs')
    if r.status!=0: return (np.inf,None) if ret else np.inf
    return (float(r.fun),r.x[:nc]) if ret else float(r.fun)

def solve(X,f,H,restarts=4,maxfev=700,seed=0):
    n=X.shape[1]; rr=np.random.default_rng(seed); best=np.inf
    for orients in itertools.product([1,-1],repeat=H):
        for t in range(restarts):
            w0=rr.normal(-0.5,1.0,H*n)
            def obj(p):
                W=np.exp(np.clip(p,-25.0,25.0)).reshape(H,n)
                v=hinge(X,f,orients,W)
                return v if np.isfinite(v) else 1e12
            res=minimize(obj,w0,method='Nelder-Mead',
                         options={'maxfev':maxfev,'xatol':1e-3,'fatol':1e-9})
            if res.fun<best: best=res.fun
            if best<1e-9: return 0.0
    return best

def admissible(n,rr,orient):
    w=rr.uniform(0.15,1.2,n)
    return w,orient          # D = 1 + <w, x or 1-x>

def instance(n,rr):
    X=cube(n)
    w1,o1=admissible(n,rr,+1); w2,o2=admissible(n,rr,-1)     # MIXED pair
    w3,o3=admissible(n,rr,rr.choice([-1,1]))
    def D(w,o): return 1.0+((X if o>0 else 1.0-X)@w)
    B1,B2,B3=D(w1,o1),D(w2,o2),D(w3,o3)
    L1=rr.normal(0,1,n+1); L2=rr.normal(0,1,n+1)
    A1=L1[0]+X@L1[1:]; A2=L2[0]+X@L2[1:]
    R=A1/(B1*B2)+A2/B3
    f=(R>0).astype(float)
    return X,f,R

if __name__=="__main__":
    n=int(sys.argv[1]); ninst=int(sys.argv[2]); seed=int(sys.argv[3])
    rr=np.random.default_rng(seed)
    print("n=%d  budget-3 POIC_2 with a MIXED double pole"%n,flush=True)
    for k in range(ninst):
        X,f,R=instance(n,rr)
        bal=int(f.sum())
        if bal in (0,len(f)): print(" inst %d: constant, skip"%k,flush=True); continue
        t0=time.time(); line=" inst %2d  |f|=%4d/%4d "%(k,bal,len(f))
        hstar=None
        for H in [1,2,3,4]:
            v=solve(X,f,H,restarts=3 if H<4 else 2,maxfev=600,seed=seed*100+k)
            line+=" H%d:%s"%(H,"OK" if v<1e-9 else "%.1f"%v)
            if v<1e-9: hstar=H; break
        print(line+"   H*=%s  [%.0fs]"%(hstar,time.time()-t0),flush=True)
