#!/usr/bin/env python3
"""ks_family.py -- the Kisielewicz-Szykula family: Table E.1 and the B_e values of Appendix C.

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix E and Table E.1: the family of Kisielewicz and Szykula [ks] on
      n = 2m-1 states (a permutation letter with two cycles of coprime lengths
      m-1 and m, and a second letter whose image has m+1 states) has deviation
      d = n-3; the maximum of minext over its subsets of size at least 2 and at
      most n-1 is 8, 14, 22, 31, 44, 56 at n = 5, 7, 9, 11, 13, 15, attained at a
      single subset, of size m-1; these values equal the length of the extending
      word produced by the strategy of [ks], m^2-m+2 for odd m and m^2-3m/2+4 for
      even m, that is (n^2+7)/4 for n = 1 mod 4 and (n^2-n+14)/4 for n = 3 mod 4;
      against the budget 2n = 10, 14, 18, 22, 26, 30 the family meets the budget
      at d = 2, is tight at d = 4, and exceeds it from d = 6 on.
  Appendix C: on this family the maximising subsets sit deep inside {B_e < 0},
      at B_e = -13 already at n = 5 and falling with n.

The automaton is built from the definition in [ks] (A. Kisielewicz, M. Szykula,
Synchronizing automata with extremal properties, MFCS 2015; arXiv:1608.01268,
Section 2), quoted below, with states 0-indexed (q_i <-> i-1):

    For m >= 3, let n = 2m-1.  A_{2m-1} = <Q_{2m-1}, {a,b}, delta_{2m-1}>,
    Q_{2m-1} = {q_1,...,q_{2m-1}},
    delta(q_i, a) = q_1 if i = m;  q_{m+1} if i = 2m-1;  q_{i+1} otherwise
    delta(q_i, b) = q_i if 1 <= i <= m-1;  q_{2m-1} if i = m;  q_m if i = 2m-1;
                    q_{i-m} otherwise
    Q_U = {q_{m+1},...,q_{2m-1}}.

minext(S) is computed for every proper nonempty subset at once, by breadth-first
search on the reversed preimage digraph from the subsets of larger size.  B_e is
the paper's centred Friedman weight at uniform letter weights,
B_e(S) = n e(S) - |S| e(Q), with e the positive integer left eigenvector of
M = pi(a) + pi(b) for the eigenvalue 2, normalised to coprime entries (computed
exactly from the principal minors of 2I - M, by the matrix-tree theorem).

Usage:    python ks_family.py
Output:   one [PASS]/[FAIL] line per statement, a table of the six sizes, then
          "N rows, M FAILED".
Runtime:  under a minute.
Requires: Python 3.8 or later, standard library only.  Exit status = number of
          failed rows.
"""
import sys
from math import gcd

rows = []


def check(label, ok):
    rows.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}", flush=True)


# --------------------------------------------------------------------------
# the family
# --------------------------------------------------------------------------

def ks_odd(m):
    """A_{2m-1} of [ks], Section 2.  Returns (n, [a, b]) 0-indexed."""
    assert m >= 3
    n = 2 * m - 1
    a = [None] * n
    b = [None] * n
    for i in range(1, n + 1):          # i is the 1-based index of [ks]
        if i == m:
            a[i - 1] = 1 - 1
        elif i == 2 * m - 1:
            a[i - 1] = (m + 1) - 1
        else:
            a[i - 1] = (i + 1) - 1
        if 1 <= i <= m - 1:
            b[i - 1] = i - 1
        elif i == m:
            b[i - 1] = (2 * m - 1) - 1
        elif i == 2 * m - 1:
            b[i - 1] = m - 1
        else:
            b[i - 1] = (i - m) - 1
    assert all(0 <= x < n for x in a) and all(0 <= x < n for x in b)
    return n, [a, b]


def q_upper(m):
    """Q_U = {q_{m+1}, ..., q_{2m-1}} as a bitmask (0-indexed)."""
    mask = 0
    for i in range(m + 1, 2 * m):
        mask |= 1 << (i - 1)
    return mask


# --------------------------------------------------------------------------
# structure
# --------------------------------------------------------------------------

def cycle_lengths(f):
    """Sorted lengths of the cycles of the functional digraph of f."""
    n = len(f)
    colour = [0] * n                   # 0 unseen, 1 in progress, 2 done
    out = []
    for s in range(n):
        if colour[s]:
            continue
        path, pos, q = [], {}, s
        while colour[q] == 0:
            colour[q] = 1
            pos[q] = len(path)
            path.append(q)
            q = f[q]
        if colour[q] == 1:             # closed a new cycle
            out.append(len(path) - pos[q])
        for x in path:
            colour[x] = 2
    return sorted(out)


def strongly_connected(n, dels):
    def reach(adj):
        seen, stack = {0}, [0]
        while stack:
            q = stack.pop()
            for r in adj[q]:
                if r not in seen:
                    seen.add(r)
                    stack.append(r)
        return len(seen) == n
    fwd = [[] for _ in range(n)]
    bwd = [[] for _ in range(n)]
    for f in dels:
        for q in range(n):
            fwd[q].append(f[q])
            bwd[f[q]].append(q)
    return reach(fwd) and reach(bwd)


def synchronizing(n, dels):
    """Breadth-first search over images Q.w; True when a singleton is reached."""
    full = (1 << n) - 1
    seen, frontier = {full}, [full]
    while frontier:
        nxt = []
        for S in frontier:
            if S & (S - 1) == 0:
                return True
            for f in dels:
                T, M = 0, S
                while M:
                    low = M & -M
                    T |= 1 << f[low.bit_length() - 1]
                    M ^= low
                if T not in seen:
                    seen.add(T)
                    nxt.append(T)
        frontier = nxt
    return False


# --------------------------------------------------------------------------
# shortest extending words
# --------------------------------------------------------------------------

def preimage_tables(n, dels):
    """pre[li][q] = bitmask of states mapped to q by letter li."""
    pre = []
    for f in dels:
        t = [0] * n
        for q in range(n):
            t[f[q]] |= 1 << q
        pre.append(t)
    return pre


def preimage(mask, tab):
    T, M = 0, mask
    while M:
        low = M & -M
        T |= tab[low.bit_length() - 1]
        M ^= low
    return T


def all_subset_minext(n, dels):
    """minext(S) for every nonempty proper S (None: no extending word exists).

    Builds the preimage digraph on 2^n nodes and runs, for each size s, a
    multi-source breadth-first search on the reversed digraph from every node of
    size > s."""
    N = 1 << n
    popc = [0] * N
    for S in range(1, N):
        popc[S] = popc[S >> 1] + (S & 1)
    pre = preimage_tables(n, dels)
    succ = [[preimage(S, pre[li]) for li in range(len(dels))] for S in range(N)]
    rev = [[] for _ in range(N)]
    for S in range(N):
        for T in succ[S]:
            rev[T].append(S)
    f = {}
    for s in range(1, n):
        dist = [-1] * N
        frontier = [S for S in range(N) if popc[S] > s]
        for S in frontier:
            dist[S] = 0
        while frontier:
            nxt = []
            for U in frontier:
                du = dist[U]
                for T in rev[U]:
                    if dist[T] < 0:
                        dist[T] = du + 1
                        nxt.append(T)
            frontier = nxt
        for S in range(1, N):
            if popc[S] == s:
                f[S] = dist[S] if dist[S] > 0 else None
    return f


# --------------------------------------------------------------------------
# the stationary vector at uniform weights
# --------------------------------------------------------------------------

def det_int(mat):
    """Fraction-free (Bareiss) determinant of a square integer matrix."""
    m = [r[:] for r in mat]
    size = len(m)
    if size == 0:
        return 1
    sign, prev = 1, 1
    for i in range(size - 1):
        if m[i][i] == 0:
            for r in range(i + 1, size):
                if m[r][i] != 0:
                    m[i], m[r] = m[r], m[i]
                    sign = -sign
                    break
            else:
                return 0
        for r in range(i + 1, size):
            for c in range(i + 1, size):
                m[r][c] = (m[r][c] * m[i][i] - m[r][i] * m[i][c]) // prev
        prev = m[i][i]
    return sign * m[size - 1][size - 1]


def stationary_integer(n, dels):
    k = len(dels)
    lap = [[0] * n for _ in range(n)]
    for q in range(n):
        lap[q][q] += k
        for f in dels:
            lap[q][f[q]] -= 1
    e = [det_int([[lap[i][j] for j in range(n) if j != q] for i in range(n) if i != q])
         for q in range(n)]
    g = 0
    for x in e:
        g = gcd(g, abs(x))
    e = [x // g for x in e]
    if e[0] < 0:
        e = [-x for x in e]
    lhs = [0] * n                      # exact check: e^T M = k e^T
    for q in range(n):
        for f in dels:
            lhs[f[q]] += e[q]
    assert lhs == [k * x for x in e] and all(x > 0 for x in e)
    return e


# --------------------------------------------------------------------------
# the checks
# --------------------------------------------------------------------------

M_RANGE = [3, 4, 5, 6, 7, 8]
TABLE_N = [5, 7, 9, 11, 13, 15]
TABLE_D = [2, 4, 6, 8, 10, 12]
TABLE_MINEXT = [8, 14, 22, 31, 44, 56]
TABLE_2N = [10, 14, 18, 22, 26, 30]
APPENDIX_C_BE = -13


def ks_strategy_in_m(m):
    return m * m - m + 2 if m % 2 else m * m - 3 * m // 2 + 4


def ks_closed_in_n(n):
    return (n * n + 7) // 4 if n % 4 == 1 else (n * n - n + 14) // 4


def main():
    print("ks_family -- the Kisielewicz-Szykula family at n = 2m-1, m = 3..8")
    print()
    results = []
    for m in M_RANGE:
        n, dels = ks_odd(m)
        a, b = dels
        indeg = [0] * n
        for f in dels:
            for q in range(n):
                indeg[f[q]] += 1
        d = sum(abs(x - 2) for x in indeg)
        mx = all_subset_minext(n, dels)
        sized = {S: v for S, v in mx.items() if 2 <= bin(S).count("1") <= n - 1}
        best = max(v for v in sized.values() if v is not None)
        argmax = [S for S, v in sized.items() if v == best]
        never = [S for S, v in mx.items() if v is None]
        e = stationary_integer(n, dels)
        QU = q_upper(m)
        eQ, eS = sum(e), sum(e[q] for q in range(n) if QU >> q & 1)
        excess_max = n * eS - bin(QU).count("1") * eQ
        results.append(dict(m=m, n=n, d=d, a=a, b=b, best=best, argmax=argmax,
                            never=never, be=excess_max, sc=strongly_connected(n, dels),
                            sync=synchronizing(n, dels)))
        print("  m=%d n=%2d  d=%2d  max minext (2<=|S|<=n-1) = %2d  attained by %d subset(s) "
              "of size %s  B_e(maximiser) = %d"
              % (m, n, d, best, len(argmax), sorted({bin(S).count('1') for S in argmax}), excess_max))
    print()

    check("the six members are strongly connected and synchronizing",
          all(r["sc"] and r["sync"] for r in results))
    check("the first letter is a permutation with exactly two cycles, of the coprime lengths m-1 and m",
          all(len(set(r["a"])) == r["n"] and cycle_lengths(r["a"]) == [r["m"] - 1, r["m"]]
              and gcd(r["m"] - 1, r["m"]) == 1 for r in results))
    check("the image of the second letter has m+1 states",
          all(len(set(r["b"])) == r["m"] + 1 for r in results))
    check("the deviation is d = n-3: Table E.1 prints 2, 4, 6, 8, 10, 12",
          [r["d"] for r in results] == TABLE_D
          and all(r["d"] == r["n"] - 3 for r in results) and [r["n"] for r in results] == TABLE_N)
    check("every proper nonempty subset extends at some length",
          all(not r["never"] for r in results))
    check("Table E.1: the maximum of minext over subsets of size 2..n-1 is 8, 14, 22, 31, 44, 56",
          [r["best"] for r in results] == TABLE_MINEXT)
    check("Table E.1: the maximum is attained at a single subset, of size m-1, namely Q_U",
          all(r["argmax"] == [q_upper(r["m"])] and bin(r["argmax"][0]).count("1") == r["m"] - 1
              for r in results))
    check("the values equal m^2-m+2 (odd m) and m^2-3m/2+4 (even m), the length produced by the strategy of [ks]",
          [ks_strategy_in_m(m) for m in M_RANGE] == TABLE_MINEXT)
    check("and equal (n^2+7)/4 for n = 1 mod 4 and (n^2-n+14)/4 for n = 3 mod 4; the two forms "
          "agree for every m from 3 to 200 and are exact integers",
          [ks_closed_in_n(n) for n in TABLE_N] == TABLE_MINEXT
          and all(ks_closed_in_n(2 * m - 1) == ks_strategy_in_m(m) for m in range(3, 201))
          and all((m % 2 == 1) == ((2 * m - 1) % 4 == 1) for m in range(3, 201))
          and all((n * n + 7) % 4 == 0 for n in range(5, 402, 4))
          and all((n * n - n + 14) % 4 == 0 for n in range(7, 402, 4)))
    check("against 2n = 10, 14, 18, 22, 26, 30 the family meets the budget at d = 2, is tight at d = 4 "
          "and exceeds it from d = 6 on",
          [2 * r["n"] for r in results] == TABLE_2N
          and results[0]["best"] < 2 * results[0]["n"]
          and results[1]["best"] == 2 * results[1]["n"]
          and all(r["best"] > 2 * r["n"] for r in results[2:]))
    check("Appendix C: B_e at the maximising subset is -13 at n = 5 and falls with n (%s)"
          % ", ".join(str(r["be"]) for r in results),
          results[0]["be"] == APPENDIX_C_BE
          and all(results[i + 1]["be"] < results[i]["be"] for i in range(len(results) - 1)))

    print(f"\n{len(rows)} rows, {rows.count(False)} FAILED", flush=True)
    return rows.count(False)


if __name__ == "__main__":
    sys.exit(min(main(), 255))
