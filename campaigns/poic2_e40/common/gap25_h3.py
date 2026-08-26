"""M1 interior 3-head search with active-set cutting planes and DE outer.
Orientation cells reduced to the 4 multiset classes (+++), (++-), (+--), (---).

usage: python3 gap25_h3.py <instance> <budget_seconds> [seed] [H]
"""
import numpy as np, sys, time
from scipy.optimize import minimize
from gap25_common import hinge_heads
from gap25_sig import get_inst

def run(tag, budget_s, seed=0, H=3):
    inst = get_inst(tag); n = inst['n']; X = inst['X']; f = inst['f']
    rng = np.random.default_rng(seed)
    npts = len(f)
    cells = {3: [(1,1,1),(1,1,-1),(1,-1,-1),(-1,-1,-1)],
             2: [(1,1),(1,-1),(-1,-1)],
             4: [(1,1,1,1),(1,1,1,-1),(1,1,-1,-1),(1,-1,-1,-1),(-1,-1,-1,-1)]}[H]
    log = open('../results/gap25_h%d_%s.txt' % (H, tag), 'a')
    def logline(s):
        log.write(s + '\n'); log.flush(); print(s, flush=True)
    logline('== %s H=%d interior search seed=%d sha=%s' % (tag, H, seed, inst['sha'][:16]))
    t0 = time.time()

    def full_margins(orients, W):
        v, th = hinge_heads(X, f, orients, W, ret=True)
        if th is None: return np.inf, None
        score = np.full(npts, th[0])
        for h in range(H):
            z = X if orients[h] > 0 else (1.0 - X)
            D = 1.0 + z @ W[h]
            k = 1 + h*(n+1)
            score += th[k]/D + (X @ th[k+1:k+1+n])/D
        return v, np.argsort((2.0*f - 1.0)*score)

    def cell_search(orients, budget, pop=32, idx0=None, seedp=None):
        idx = np.sort(rng.choice(npts, size=min(768, npts), replace=False)) if idx0 is None else idx0
        def sub(p):
            W = np.exp(np.clip(p, -25, 25)).reshape(H, n)
            return hinge_heads(X, f, orients, W, idx=idx)
        P = [rng.normal(-0.5, 1.0, H*n) for _ in range(pop-2)]
        if seedp is not None:
            P = [seedp + rng.normal(0, sc, H*n) for sc in (0.0, 0.1, 0.3, 0.6)] + P[:-4]
        # warm: source-pool-shaped slopes
        s_stack = np.concatenate([np.log(np.maximum(s_ + 0.02, 1e-3)) for s_ in inst['s']])[:H*n]
        if len(s_stack) == H*n: P.append(s_stack)
        P.append(np.full(H*n, -1.0))
        vals = [sub(p) for p in P]
        bestf = np.inf; bestp = None
        tstart = time.time(); gen = 0
        while time.time() - tstart < budget:
            gen += 1
            for i in range(len(P)):
                a, b, c = rng.choice(len(P), 3, replace=False)
                trial = P[a] + 0.7*(P[b] - P[c])
                mask = rng.random(H*n) < 0.9
                trial = np.where(mask, trial, P[i])
                tv = sub(trial)
                if tv < vals[i]: P[i], vals[i] = trial, tv
            ib = int(np.argmin(vals))
            if gen % 8 == 0 or vals[ib] < 1e-7:
                W = np.exp(np.clip(P[ib], -25, 25)).reshape(H, n)
                fv, order_v = full_margins(orients, W)
                if fv < bestf: bestf, bestp = fv, P[ib].copy()
                if fv < 1e-9: return bestf, bestp, idx
                if vals[ib] < 0.02*fv and len(idx) < npts:
                    add = [j for j in order_v[:256] if j not in set(idx)][:192]
                    if add:
                        idx = np.sort(np.concatenate([idx, np.array(add, dtype=idx.dtype)]))
                        vals = [sub(p) for p in P]
            if gen % 30 == 0:
                res = minimize(sub, P[ib], method='Nelder-Mead',
                               options={'maxfev': 500, 'xatol': 1e-4, 'fatol': 1e-10})
                if res.fun < vals[ib]: P[ib], vals[ib] = res.x, res.fun
        return bestf, bestp, idx

    # dedicated-cell mode: GAP25_CELL="1,1,1" skips screening entirely
    import os
    if os.environ.get('GAP25_CELL'):
        orients = tuple(int(v) for v in os.environ['GAP25_CELL'].split(','))
        logline('  dedicated cell %s, full budget' % str(orients))
        bf, bp, idx = cell_search(orients, budget_s - (time.time()-t0), pop=44)
        logline('  dedicated cell %s: best full %.4f (%.4f/v) (%.0fs)' %
                (str(orients), bf, bf/npts, time.time()-t0))
        if bf < 1e-9:
            logline('CERTIFICATE FOUND in dedicated cell %s' % str(orients))
            np.savez('../results/gap25_h%d_%s_cert.npz' % (H, tag),
                     orients=np.array(orients), logW=bp)
        else:
            logline('END %s H=%d dedicated: NOT FOUND, best %.4f = %.4f/v [%.0fs]' %
                    (tag, H, bf, bf/npts, time.time()-t0))
        log.close(); return
    # screening pass over cells, then deep on the best two
    screen = 0.12 * budget_s
    results = []
    for orients in cells:
        bf, bp, idx = cell_search(orients, screen)
        logline('  screen cell %s: best full %.4f (%.4f/v) (%.0fs)' %
                (str(orients), bf, bf/npts, time.time()-t0))
        results.append((bf, orients, bp, idx))
        if bf < 1e-9:
            logline('CERTIFICATE FOUND in screening, cell %s' % str(orients)); log.close(); return
    results.sort(key=lambda r: r[0])
    deep_each = (budget_s - (time.time()-t0)) / 2.2
    for bf0, orients, bp, idx in results[:2]:
        bf, bp2, idx2 = cell_search(orients, deep_each, pop=40, idx0=idx, seedp=bp)
        logline('  deep cell %s: best full %.4f (%.4f/v) (%.0fs)' %
                (str(orients), bf, bf/npts, time.time()-t0))
        if bf < 1e-9:
            logline('CERTIFICATE FOUND in deep pass, cell %s' % str(orients))
            np.savez('../results/gap25_h%d_%s_cert.npz' % (H, tag),
                     orients=np.array(orients), logW=bp2)
            log.close(); return
    best_overall = min(r[0] for r in results)
    logline('END %s H=%d: NOT FOUND, best full %.4f = %.4f/v [%.0fs]' %
            (tag, H, best_overall, best_overall/npts, time.time()-t0))
    log.close()

if __name__ == '__main__':
    run(sys.argv[1], float(sys.argv[2]),
        int(sys.argv[3]) if len(sys.argv) > 3 else 0,
        int(sys.argv[4]) if len(sys.argv) > 4 else 3)
