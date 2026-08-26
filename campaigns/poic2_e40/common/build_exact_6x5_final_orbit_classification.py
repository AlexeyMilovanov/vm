#!/usr/bin/env python3
"""Close the 48-table 6x5 residue by exact grid-symmetry transport.

This script does not assert anything about H*.  It transports only the
algebraic axis-GES predicates under r -> 5-r, s -> 4-s and output negation.
"""

from fractions import Fraction as F
from math import comb
import argparse
import json

import verify_exact_6x5_full_ges as v


E_REPS = {
    283156, 284244, 285368, 285808,
    1873121, 1873123, 1873125, 1877219, 1880980, 1947022,
}
S_REPS = {1881413, 1945101}


def fs(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def table(key, bds):
    bi, mask = divmod(key, 1 << len(v.INTERIOR))
    return v.labels(bds[bi], mask)


def reflected_index(r, s, rr, ss):
    return v.NID[(5-r if rr else r, 4-s if ss else s)]


def relation(source, target):
    """Return rr,ss,sg with target(r,s)=sg*source(reflected r,s)."""
    for rr in (0, 1):
        for ss in (0, 1):
            for sg in (1, -1):
                if all(target[v.NID[(r, s)]] ==
                       sg*source[reflected_index(r, s, rr, ss)]
                       for r, s in v.G):
                    return rr, ss, sg
    return None


def transform_poly(raw, rr, ss, sg):
    """Substitute r'=5-r, s'=4-s and multiply by sg, exactly."""
    out = {m: F(0) for m in v.MONO3}
    ar, br = (F(5), F(-1)) if rr else (F(0), F(1))
    ass, bs = (F(4), F(-1)) if ss else (F(0), F(1))
    for a, (i, j) in zip(map(F, raw), v.MONO3):
        for u in range(i+1):
            cr = F(comb(i, u))*ar**(i-u)*br**u
            for w in range(j+1):
                cs = F(comb(j, w))*ass**(j-w)*bs**w
                out[(u, w)] += F(sg)*a*cr*cs
    return [out[m] for m in v.MONO3]


def edge_name(e):
    return f'{e[0]}={e[1]}'


def load_sources(initial_path, new_path, direct_path):
    initial = json.load(open(initial_path))
    old = dict(initial['records'])
    erefs = {k: rec['elliptic_reference'] for k, rec in old.items()
             if rec['k'] == 'E'}
    newer = json.load(open(new_path))
    for rec in newer['records']:
        assert rec['kind'] == 'E'
        assert rec['key'] not in erefs
        erefs[rec['key']] = rec['elliptic_reference']
    direct = json.load(open(direct_path))
    srecs = {item['key']: item['record'] for item in direct['results']
             if item['record'] is not None}
    assert set(erefs) == E_REPS
    assert set(srecs) == S_REPS
    return erefs, srecs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', required=True)
    ap.add_argument('--initial-e', required=True)
    ap.add_argument('--new-e', required=True)
    ap.add_argument('--direct-s', required=True)
    ap.add_argument('--orbit-out', required=True)
    ap.add_argument('--full-out', required=True)
    ns = ap.parse_args()

    base = json.load(open(ns.base))
    assert base['counts']['U'] == 48
    ukeys = {k for k, _ in base['unresolved']}
    bds = v.quiet_boundaries()
    erefs, srecs = load_sources(ns.initial_e, ns.new_e, ns.direct_s)
    source_tables = {k: table(k, bds) for k in E_REPS | S_REPS}

    orbit_records = []
    source_counts = {k: 0 for k in E_REPS | S_REPS}
    for key in sorted(ukeys):
        y = table(key, bds)
        hits = []
        for rep, src in source_tables.items():
            rel = relation(src, y)
            if rel is not None:
                hits.append((rep, rel))
        assert len(hits) == 1, (key, hits)
        rep, (rr, ss, sg) = hits[0]
        source_counts[rep] += 1
        if rep in S_REPS:
            p = transform_poly(srecs[rep]['p'], rr, ss, sg)
            assert v.strict(p, y, v.MONO3)
            splits = [(e, v.discriminant(v.edge_coeffs(p, e)))
                      for e in v.EDGES]
            e, d = next((e, d) for e, d in splits if d >= 0)
            rec = {'k': 'S', 'rep': rep, 'rr': rr, 'ss': ss, 'sg': sg,
                   'e': edge_name(e), 't': 'exact-grid-symmetry',
                   'p': [fs(x) for x in p], 'd': fs(d)}
        else:
            p = transform_poly(erefs[rep]['p'], rr, ss, sg)
            assert v.strict(p, y, v.MONO3)
            ds = {edge_name(e): v.discriminant(v.edge_coeffs(p, e))
                  for e in v.EDGES}
            assert all(d < 0 for d in ds.values())
            rec = {'k': 'E', 'rep': rep, 'rr': rr, 'ss': ss, 'sg': sg,
                   'p': [fs(x) for x in p],
                   'd': {name: fs(d) for name, d in ds.items()}}
        orbit_records.append([key, rec])

    assert set(source_counts) == E_REPS | S_REPS
    assert set(source_counts.values()) == {4}
    kinds = {'S': 0, 'E': 0}
    for _, rec in orbit_records:
        kinds[rec['k']] += 1
    assert kinds == {'S': 8, 'E': 40}
    orbit = {
        'schema': 'exact-6x5-final-orbit-transport-v1',
        'status': 'EXACT_AXIS_GES_ORBIT_CLASSIFICATION',
        'grid': [6, 5],
        'scope': 'axis-GES only; no H-star invariance claim',
        'source_counts': {str(k): source_counts[k] for k in sorted(source_counts)},
        'counts': kinds,
        'records': orbit_records,
    }
    with open(ns.orbit_out, 'w') as fh:
        json.dump(orbit, fh, indent=2)

    certs = dict(base['certs'])
    unresolved = dict(base['unresolved'])
    for key, rec in orbit_records:
        assert key in unresolved and key not in certs
        certs[key] = rec
        del unresolved[key]
    assert not unresolved
    counts = {'A': base['analytic_count'], 'Q': 0, 'S': 0,
              'N': 0, 'E': 0, 'U': 0}
    for rec in certs.values():
        counts[rec['k']] += 1
    assert counts == {'A': 1659152, 'Q': 0, 'S': 175671,
                      'N': 303249, 'E': 40, 'U': 0}
    base['schema'] = 'exact-6x5-full-axis-ges-classification-v1'
    base['status'] = 'EXACT_AXIS_GES_CLASSIFICATION_WITH_OBSTRUCTIONS'
    base['counts'] = counts
    base['unresolved'] = []
    base['certs'] = sorted(certs.items())
    base['orbit_closure'] = {
        'source': ns.orbit_out, 'replaced': 48,
        'S': 8, 'E': 40,
        'meaning_E': 'strict cubic sign representation; no split on any axis extreme edge',
    }
    with open(ns.full_out, 'w') as fh:
        json.dump(base, fh, separators=(',', ':'))
    print('PASS built exact orbit classification', kinds)
    print('full counts', counts)


if __name__ == '__main__':
    main()
