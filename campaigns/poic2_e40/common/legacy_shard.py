import os, sys, json, itertools, time
import numpy as np
from scipy.optimize import minimize
from hs2 import cube, hinge
from poic_solver import poic_hinge
task, shard, nshard, H, restarts, maxfev, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
def build(task):
    if task=="f8":
        X=cube(8); d=np.abs(X[:,:4]-X[:,4:]).sum(1); return X,(d>=2).astype(float),None
    if task=="f8xz":
        X=cube(9); d=np.abs(X[:,:4]-X[:,4:8]).sum(1); return X,np.abs((d>=2).astype(float)-X[:,8]),None
    if task=="r5":
        X=cube(10); d=np.abs(X[:,:5]-X[:,5:]).sum(1); return X,(d>=2).astype(float),None
    if task.startswith("W"):
        a,b=int(task[1]),int(task[2]); X=cube(8); d=np.abs(X[:,:4]-X[:,4:]).sum(1)
        return X,((d>=a)&(d<=b)).astype(float),None
    if task.startswith("r5orb:"):
        pat=json.loads(task.split(":",1)[1]); X=cube(10); d=np.abs(X[:,:5]-X[:,5:]).sum(1)
        return X,(d>=2).astype(float),pat
    if task.startswith("f8xzorb:"):
        pat=json.loads(task.split(":",1)[1]); X=cube(9); d=np.abs(X[:,:4]-X[:,4:8]).sum(1)
        return X,np.abs((d>=2).astype(float)-X[:,8]),pat
    if task.startswith("cpr"):
        seed=int(task[3:]); n=12; X=cube(n)
        rr=np.random.default_rng(seed)
        for trial in range(40):
            B=[]; sl=[]
            for k in range(3):
                w=np.zeros(n); w[4*k:4*k+4]=rr.uniform(.3,1.0,4); sl.append(w); B.append(1.0+X@w)
            L=[rr.normal(0,1,n+1) for _ in range(3)]
            Lv=[c[0]+X@c[1:] for c in L]
            T=[Lv[0]*B[2],Lv[1]*B[0],Lv[2]*B[1]]
            T=[t/np.sqrt((t*t).mean()) for t in T]
            Q=T[0]+T[1]+T[2]
            if np.abs(Q).min()<1e-9: continue
            f=(Q>0).astype(float); m=int(f.sum())
            M=np.zeros((n,n))
            for (li,bi) in [(0,2),(1,0),(2,1)]:
                M+=np.outer(L[li][1:],sl[bi])+np.outer(sl[bi],L[li][1:])
            rk=np.linalg.matrix_rank(M,tol=1e-8*np.abs(M).max())
            if rk>=6 and 1200<m<2900: return X,f,None
        raise SystemExit("no instance for "+task)
    raise SystemExit("unknown task "+task)
X,f,pat=build(task); n=X.shape[1]
cells=[(o,r) for o in itertools.product([1,-1],repeat=H) for r in range(restarts)]
mine=[c for i,c in enumerate(cells) if i%nshard==shard]
# per-cell checkpointing: append one line per finished cell; on restart skip done cells
ndone=0
try: ndone=sum(1 for _ in open(out))
except Exception: pass
mine=mine[ndone:]
best=np.inf; t0=time.time()
try:
    for line in open(out):
        v=float(line.split()[0])
        if v<best: best=v
except Exception: pass
for o,r in mine:
    rr=np.random.default_rng(abs(hash((shard,r,o)))%(2**31))
    w0=rr.normal(-0.5,1.0,H*n)
    if pat is None:
        obj=lambda p:(lambda v: v if np.isfinite(v) else 1e12)(hinge(X,f,o,np.exp(np.clip(p,-25,25)).reshape(H,n)))
    else:
        obj=lambda p:(lambda v: v if np.isfinite(v) else 1e12)(poic_hinge(X,f,pat,o,np.exp(np.clip(p,-25,25)).reshape(H,n)))
    res=minimize(obj,w0,method="Nelder-Mead",options={"maxfev":maxfev,"xatol":1e-3,"fatol":1e-9})
    if res.fun<best: best=res.fun
    with open(out,"a") as fh: fh.write("%.10g 1 %.0f\n"%(res.fun,time.time()-t0))
    if best<1e-9: break
