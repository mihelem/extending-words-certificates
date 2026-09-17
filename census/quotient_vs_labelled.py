"""quotient_vs_labelled.py -- shares in the quotient convention against the labelled
shares, obtained by reweighting each representative with the size of its first letter's
conjugacy class.

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A.1: the share of automata with no permutation letter moves from 76.18 percent
      in the quotient convention to 91.37 percent labelled on the synchronizing strongly
      connected {d<=2} population at n=6 (260,461 automata), and on the unfiltered
      enumeration at n=6 from 90.13 to 96.94 percent.
  Appendix A: the {d<=2} stratum at n=4 has 811 automata.

Method (Appendix A.1): in the quotient convention an isomorphism class of automaton A
contributes |C(a)|/|Aut(A)| representatives (a, b), against n!/|Aut(A)| labelled automata,
where C(a) is the centraliser of the letter a in the symmetric group.  Weighting each
representative (a0, b) by n!/|C(a0)|, the size of the conjugacy class of a0, therefore
turns the quotient count of any isomorphism-invariant property into its labelled count:

    sum over representatives with P of n!/|C(a0)|
      = sum over classes [A] with P of (|C(a0)|/|Aut(A)|) * (n!/|C(a0)|)
      = sum over classes [A] with P of n!/|Aut(A)|  =  labelled count of P.

Population / convention: letter a ranges over one representative of each conjugacy class
  of maps [n]->[n], the lexicographically least conjugate (19, 47, 130 classes at n=4, 5, 6;
  sequence A001372), letter b over all n^n maps; then MODE:
    all         synchronizing and strongly connected, every deviation
    d2          synchronizing and strongly connected, deviation d <= 2
    unfiltered  no filter (at n=6: 130 x 46,656 = 6,065,280 representatives, and
                6^12 = 2,176,782,336 labelled automata)
  d = sum_q |indeg_a(q) + indeg_b(q) - 2|.

Usage:    python quotient_vs_labelled.py N all|d2|unfiltered [OUT.json]
          The runs behind the paper:
            python quotient_vs_labelled.py 6 d2
            python quotient_vs_labelled.py 6 unfiltered
            python quotient_vs_labelled.py 4 d2

Output:   a line "n=.. mode=.. a-classes=.. population(quotient)=.. labelled=..", then the
          line NOPERM (neither letter is a permutation) with its quotient share, labelled share
          (percent, rounded to 4 decimals), their difference in points and the quotient count
          (76.1788 / 91.3666 at n=6 d2; 90.1258 / 96.9374 at n=6 unfiltered); for the three runs
          behind the paper, [PASS]/[FAIL] rows against the paper's values; exit status = number
          of failed rows.  With OUT.json the exact quotient and labelled counts, and the counts
          per a-class, are also written to OUT.json.

Runtime:  one core: n=4 under 1 s; n=6 d2 about 30 s; n=6 unfiltered about 2 min.

Requires: Python 3.8+, numpy.
"""
import itertools
import json
import sys
import time

import numpy as np


# ---------------------------------------------------------------- maps

def all_maps(n):
    """Every map [n] -> [n] as rows of an (n^n, n) int array."""
    return np.array(list(itertools.product(range(n), repeat=n)), dtype=np.int8)


def perms(n):
    return np.array(list(itertools.permutations(range(n))), dtype=np.int8)


def a_classes(n, maps):
    """Return (rep_index_per_map, rep_indices, orbit_size_per_rep).

    Canonical form of a map m is the lexicographic minimum of its conjugates
    g m g^{-1}, over all g in S_n.  |C(m)| = n! / (orbit size).
    """
    P = perms(n)
    N = maps.shape[0]
    powers = (n ** np.arange(n - 1, -1, -1)).astype(np.int64)
    best = np.full(N, np.iinfo(np.int64).max, dtype=np.int64)
    for g in P:
        ginv = np.empty(n, dtype=np.int8)
        ginv[g] = np.arange(n, dtype=np.int8)
        # (g m g^{-1})(x) = g[ m[ ginv[x] ] ]
        conj = g[maps[:, ginv]]
        key = conj.astype(np.int64) @ powers
        np.minimum(best, key, out=best)
    uniq, inv, counts = np.unique(best, return_inverse=True, return_counts=True)
    # representative = the map whose own key equals the canonical key
    own = maps.astype(np.int64) @ powers
    reps = np.full(uniq.shape[0], -1, dtype=np.int64)
    hit = np.nonzero(own == best)[0]
    reps[inv[hit]] = hit
    assert (reps >= 0).all()
    return inv, reps, counts


# ------------------------------------------------------- automaton tests

def strongly_connected(a, b, n):
    """Forward reachability from 0 and backward reachability to 0."""
    fwd = [[] for _ in range(n)]
    bwd = [[] for _ in range(n)]
    for q in range(n):
        for r in (a[q], b[q]):
            fwd[q].append(r)
            bwd[r].append(q)

    def reach(adj):
        seen = [False] * n
        seen[0] = True
        stack = [0]
        cnt = 1
        while stack:
            q = stack.pop()
            for r in adj[q]:
                if not seen[r]:
                    seen[r] = True
                    cnt += 1
                    stack.append(r)
        return cnt

    return reach(fwd) == n and reach(bwd) == n


def synchronizing(a, b, n):
    """Backward BFS in the pair automaton from the diagonal."""
    idx = {}
    for p in range(n):
        for q in range(p + 1, n):
            idx[(p, q)] = len(idx)
    m = len(idx)
    pre = [[] for _ in range(m)]
    diag = [False] * m
    for (p, q), i in idx.items():
        for f in (a, b):
            u, v = f[p], f[q]
            if u == v:
                diag[i] = True
            else:
                j = idx[(min(u, v), max(u, v))]
                pre[j].append(i)
    seen = list(diag)
    stack = [i for i in range(m) if diag[i]]
    while stack:
        i = stack.pop()
        for j in pre[i]:
            if not seen[j]:
                seen[j] = True
                stack.append(j)
    return all(seen)


def is_perm(f, n):
    return len(set(f)) == n


# ------------------------------------------------------------- the run

def run(n, mode, outpath):
    t0 = time.time()
    maps = all_maps(n)
    inv, reps, orbit = a_classes(n, maps)
    nfac = 1
    for i in range(2, n + 1):
        nfac *= i
    assert int(orbit.sum()) == n ** n, (orbit.sum(), n ** n)

    IND = np.zeros((maps.shape[0], n), dtype=np.int16)
    for q in range(n):
        np.add.at(IND, (np.arange(maps.shape[0]), maps[:, q].astype(np.int64)), 1)

    # properties measured, as names; each rep contributes its a-class size
    # (n!/|C(a_0)| == orbit size) to the LABELLED count, and 1 to the QUOTIENT
    props = ['ALL', 'NOPERM']
    Q = {p: 0 for p in props}
    L = {p: 0 for p in props}
    per_class = {}

    for ci, ri in enumerate(reps):
        a = [int(x) for x in maps[ri]]
        w = int(orbit[ci])                     # = n!/|C(a_0)| = class size
        va = IND[ri].astype(np.int32)
        dev = np.abs(IND.astype(np.int32) + va - 2).sum(axis=1)
        cand = np.nonzero(dev <= 2)[0] if mode == 'd2' else np.arange(maps.shape[0])
        aperm = is_perm(a, n)
        loc = {p: 0 for p in props}
        for bi in cand:
            b = [int(x) for x in maps[bi]]
            if mode != 'unfiltered':
                if not strongly_connected(a, b, n):
                    continue
                if not synchronizing(a, b, n):
                    continue
            bperm = is_perm(b, n)
            flags = {
                'ALL': True,
                'NOPERM': (not aperm) and (not bperm),
            }
            for p in props:
                if flags[p]:
                    loc[p] += 1
        for p in props:
            Q[p] += loc[p]
            L[p] += loc[p] * w
        if loc['ALL']:
            per_class[str(a)] = {'w': w, 'counts': loc}

    out = {'n': n, 'mode': mode, 'n_factorial': nfac,
           'a_classes': int(len(reps)), 'quotient': Q, 'labelled': L,
           'per_a_class': per_class,
           'shares': {}, 'elapsed': round(time.time() - t0, 1)}
    for p in props:
        if p == 'ALL':
            continue
        base_q, base_l = Q['ALL'], L['ALL']
        out['shares'][p] = {
            'quotient_pct': round(100.0 * Q[p] / base_q, 4) if base_q else None,
            'labelled_pct': round(100.0 * L[p] / base_l, 4) if base_l else None,
            'delta_points': (round(100.0 * L[p] / base_l - 100.0 * Q[p] / base_q, 4)
                             if base_q and base_l else None),
            'quotient_count': Q[p], 'labelled_count': L[p],
        }
    if outpath is not None:
        with open(outpath, 'w', encoding='utf-8') as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
    return out


if __name__ == '__main__':
    n = int(sys.argv[1])
    mode = sys.argv[2]
    outp = sys.argv[3] if len(sys.argv) > 3 else None
    r = run(n, mode, outp)
    print('n=%d mode=%s  a-classes=%d  population(quotient)=%d  labelled=%d'
          % (n, mode, r['a_classes'], r['quotient']['ALL'], r['labelled']['ALL']))
    for p in sorted(r['shares']):
        s = r['shares'][p]
        print('  %-12s quotient %8s %%   labelled %8s %%   delta %+8s pts   (q=%d)'
              % (p, s['quotient_pct'], s['labelled_pct'], s['delta_points'],
                 s['quotient_count']))
    print('  elapsed %.1f s' % r['elapsed'])
    # the paper's values (Appendix A.1 and Appendix A)
    paper = {(6, 'd2'): (260461, 76.18, 91.37), (6, 'unfiltered'): (None, 90.13, 96.94),
             (4, 'd2'): (811, None, None)}
    failed = 0
    if (n, mode) in paper:
        pop, qs, ls = paper[(n, mode)]
        s = r['shares']['NOPERM']
        rows = []
        if pop is not None:
            rows.append(('population %d' % pop, r['quotient']['ALL'] == pop))
        if qs is not None:
            rows.append(('no permutation letter: %.2f percent in the quotient convention, %.2f labelled'
                         % (qs, ls),
                         round(s['quotient_pct'], 2) == qs and round(s['labelled_pct'], 2) == ls))
        for text, ok in rows:
            failed += not ok
            where = 'Appendix A' if text.startswith('population') else 'Appendix A.1'
            print('  [%s] %s, n=%d %s: %s' % ('PASS' if ok else 'FAIL', where, n, mode, text))
        print('%d rows, %d FAILED' % (len(rows), failed))
    sys.exit(min(failed, 255))
