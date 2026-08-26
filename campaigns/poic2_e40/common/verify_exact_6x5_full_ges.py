#!/usr/bin/env python3
"""Stdlib-only exact verifier for the full 6x5 GES census."""

from fractions import Fraction as F
import itertools
import json
import sys


NR, NS = 6, 5
MONO3 = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2),
         (3, 0), (2, 1), (1, 2), (0, 3)]
MONO2 = MONO3[:6]
G = [(r, s) for r in range(NR) for s in range(NS)]
NID = {x: i for i, x in enumerate(G)}
V3 = [[r**i*s**j for i, j in MONO3] for r, s in G]
EDGES = [('s', 0), ('s', 4), ('r', 0), ('r', 5)]
BORDER = [x for x in G if x[0] in (0, NR-1) or x[1] in (0, NS-1)]
INTERIOR = [x for x in G if x not in BORDER]


def changes(seq):
    return sum(a != b for a, b in zip(seq, seq[1:]))


def edge_points(edge):
    kind, val = edge
    return ([(r, val) for r in range(NR)] if kind == 's'
            else [(val, s) for s in range(NS)])


def cut(seq):
    if changes(seq) != 1:
        return None
    k = next(i for i in range(len(seq)-1) if seq[i] != seq[i+1])
    return k, (seq[k], seq[k+1])


def quiet_boundaries():
    out = []
    for tail in itertools.product((-1, 1), repeat=len(BORDER)-1):
        bd = dict(zip(BORDER, (1,)+tail))
        if all(changes([bd[p] for p in edge_points(e)]) <= 1 for e in EDGES):
            out.append(bd)
    assert len(out) == 522
    return out


def labels(bd, mask):
    val = dict(bd)
    for k, x in enumerate(INTERIOR):
        val[x] = 1 if (mask >> k) & 1 else -1
    return tuple(val[x] for x in G)


def qj_rows(rows):
    c0, c4 = cut(rows[0]), cut(rows[4])
    if c0 is None or c4 is None:
        return False
    if c0[1] != c4[1]:
        return True
    k0, ori = c0
    k4, _ = c4
    for j in (1, 2, 3):
        cj = cut(rows[j])
        if cj is None:
            continue
        kj, oj = cj
        wanted = ori if j in (1, 3) else (ori[1], ori[0])
        a = (4-j)*k0+j*k4
        if oj == wanted and a < 4*(kj+1) and 4*kj < a+4:
            return True
    return False


def analytic(y):
    rows = [[y[NID[(r, s)]] for r in range(NR)] for s in range(NS)]
    if qj_rows(rows):
        return True
    c0 = cut([rows[s][0] for s in range(NS)])
    c5 = cut([rows[s][NR-1] for s in range(NS)])
    return c0 is not None and c5 is not None and c0[1] != c5[1]


def strict(p, y, monos):
    return all(F(yy)*sum(a*F(r**i*s**j) for a, (i, j) in zip(p, monos)) > 0
               for yy, (r, s) in zip(y, G))


def edge_coeffs(p, edge):
    kind, val = edge
    co = [F(0)]*4
    for a, (i, j) in zip(p, MONO3):
        if kind == 's':
            co[i] += a*F(val)**j
        else:
            co[j] += a*F(val)**i
    return co


def discriminant(co):
    d, c, b, a = co
    return b*b*c*c-4*a*c*c*c-4*b*b*b*d-27*a*a*d*d+18*a*b*c*d


def parse_edge(text):
    kind, val = text.split('=')
    edge = (kind, int(val))
    assert edge in EDGES
    return edge


def main(path):
    with open(path) as fh:
        data = json.load(fh)
    assert data['status'] == 'EXACT_CERTIFICATES'
    assert data['grid'] == [6, 5]
    assert data['unresolved'] == []
    bds = quiet_boundaries()
    certs = {}
    for key, rec in data['certs']:
        assert key not in certs
        certs[key] = rec
    counts = {'A': 0, 'Q': 0, 'S': 0, 'N': 0, 'U': 0}
    expected = set()
    for bi, bd in enumerate(bds):
        for mask in range(1 << len(INTERIOR)):
            key = (1 << len(INTERIOR))*bi+mask
            y = labels(bd, mask)
            if analytic(y):
                counts['A'] += 1
                assert key not in certs
                continue
            expected.add(key)
            rec = certs[key]
            kind = rec['k']
            counts[kind] += 1
            if kind == 'Q':
                p = [F(x) for x in rec['p']]
                assert len(p) == 6 and strict(p, y, MONO2)
            elif kind == 'S':
                p = [F(x) for x in rec['p']]
                assert len(p) == 10 and strict(p, y, MONO3)
                d = discriminant(edge_coeffs(p, parse_edge(rec['e'])))
                assert d >= 0 and d == F(rec['d'])
            elif kind == 'N':
                supp = rec['s']
                w = [F(x) for x in rec['w']]
                assert len(supp) == len(w) and len(set(supp)) == len(supp)
                assert all(0 <= i < 30 for i in supp)
                assert all(x >= 0 for x in w) and any(x > 0 for x in w)
                for k in range(10):
                    assert sum(w[t]*F(y[i]*V3[i][k])
                               for t, i in enumerate(supp)) == 0
            else:
                raise AssertionError(kind)
    assert set(certs) == expected
    assert counts == data['counts']
    assert counts['A'] == data['analytic_count'] == 1659152
    assert sum(counts.values()) == data['quiet_total'] == 2138112
    nonquiet = ((1 << (len(BORDER)-1))-len(bds))*(1 << len(INTERIOR))
    assert nonquiet+data['quiet_total'] == 1 << (len(G)-1)
    print('PASS exact full 6x5 quiet-boundary GES trichotomy modulo global sign')
    print(counts, 'M1 tables', nonquiet)


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'exact_6x5_full_ges.json')
