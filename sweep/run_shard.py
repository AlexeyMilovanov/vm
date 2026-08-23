"""Run one slice of the sweep. Usage: python run_shard.py <shard> <nshards>
Writes results/shard_<i>.jsonl -- one JSON object per (function, test)."""
import sys, json, os, time
import numpy as np
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from hs2 import solve
from poic_solver import poic_solve
from lib import library, ORBITS

shard, nsh = int(sys.argv[1]), int(sys.argv[2])
os.makedirs("results",exist_ok=True)
outp="results/shard_%d.jsonl"%shard
done=set()
if os.path.exists(outp):
    for L in open(outp):
        try: done.add(json.loads(L)["key"])
        except Exception: pass
out=open(outp,"a",buffering=1)
lib=library()
tasks=[]
for name,X,f in lib:
    tasks.append(("H", name, None))
    for oname,pat,s in ORBITS: tasks.append(("O", name, oname))
tasks=[t for i,t in enumerate(tasks) if i%nsh==shard]
byname={n:(X,f) for n,X,f in lib}
print("shard %d/%d: %d tasks"%(shard,nsh,len(tasks)),flush=True)
for kind,name,oname in tasks:
    key="%s|%s|%s"%(kind,name,oname)
    if key in done: continue
    X,f=byname[name]; t0=time.time(); rec={"key":key,"kind":kind,"f":name}
    try:
        if kind=="H":
            hs=None
            for H in (1,2,3,4):
                v=solve(X,f,H,restarts=3,maxfev=700,seed=7+H)
                rec["h%d"%H]=round(float(v),4)
                if v<1e-9: hs=H; break
            rec["Hstar"]=hs
        else:
            pat,s=[(p,ss) for nm,p,ss in ORBITS if nm==oname][0][0:2]
            v=poic_solve(X,f,pat,s,restarts=3,maxfev=700,seed=11)
            rec["orbit"]=oname; rec["hinge"]=round(float(v),4)
            rec["feasible"]=bool(v<1e-9); rec["per_vertex"]=round(float(v)/len(f),4)
    except Exception as e:
        rec["error"]=str(e)[:200]
    rec["secs"]=round(time.time()-t0,1)
    out.write(json.dumps(rec)+"\n")
print("shard %d done"%shard,flush=True)
