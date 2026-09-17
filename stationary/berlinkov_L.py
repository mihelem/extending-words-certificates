#!/usr/bin/env python3
"""berlinkov_L.py -- Berlinkov's factor L on the binary six-state automata whose first letter is a permutation.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 7.3: at the uniform choice of the probability vector on the alphabet,
      over the exhaustively enumerated stratum of the binary six-state population
      on which the first letter is a permutation, L (the least common multiple of
      the denominators of the stationary distribution mu) reaches 135, at which
      1+(n-1)(L-2) evaluates to 666, against the exact maximum reset threshold 25
      at that size.

Population: n = 6; the first letter a ranges over one permutation of each of the
11 cycle types of S_6, the second letter b over all 6^6 = 46,656 maps; kept when
synchronizing and strongly connected.  This is the quotient convention of
Appendix A.1 restricted to the permutation classes of the first letter.
mu is computed exactly: by the matrix-tree theorem the stationary vector of
M = pi(a) + pi(b) is proportional to the principal minors of 2I - M, which are
integers; e is that vector divided by the gcd of its entries, mu = e / e(Q), and
L = lcm_q (e(Q) / gcd(e_q, e(Q))).  The reset threshold is computed by
breadth-first search over the images Q.w.

Usage:    python berlinkov_L.py
Output:   the population size, a breakdown by deviation d (automata, largest L,
          largest reset threshold), then [PASS]/[FAIL] rows and "N rows, M FAILED".
Runtime:  about 30 seconds.
Requires: Python 3.8 or later, standard library only.  Exit status = number of
          failed rows.
"""
import itertools
import math
import sys
from collections import defaultdict

N = 6
rows = []


def check(label, ok):
    rows.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}", flush=True)


def cycle_type_representatives(n):
    """One permutation of [n] for each partition of n (its cycle type)."""
    def partitions(m, largest):
        if m == 0:
            yield []
            return
        for p in range(min(m, largest), 0, -1):
            for rest in partitions(m - p, p):
                yield [p] + rest
    reps = []
    for part in partitions(n, n):
        perm, start = [0] * n, 0
        for p in part:
            for i in range(p):
                perm[start + i] = start + (i + 1) % p
            start += p
        reps.append(tuple(perm))
    return reps


def strongly_connected(a, b, n):
    seen, stack = {0}, [0]
    while stack:
        q = stack.pop()
        for r in (a[q], b[q]):
            if r not in seen:
                seen.add(r)
                stack.append(r)
    if len(seen) < n:
        return False
    pre = [[] for _ in range(n)]
    for q in range(n):
        pre[a[q]].append(q)
        pre[b[q]].append(q)
    seen, stack = {0}, [0]
    while stack:
        q = stack.pop()
        for r in pre[q]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    return len(seen) == n


def reset_threshold(a, b, n):
    """Length of a shortest reset word, or None if not synchronizing."""
    full = (1 << n) - 1
    ima = [0] * (1 << n)
    imb = [0] * (1 << n)
    for S in range(1, 1 << n):
        low = (S & -S).bit_length() - 1
        T = S & (S - 1)
        ima[S] = ima[T] | (1 << a[low])
        imb[S] = imb[T] | (1 << b[low])
    seen, frontier, d = {full}, [full], 0
    while frontier:
        d += 1
        nxt = []
        for S in frontier:
            for T in (ima[S], imb[S]):
                if T not in seen:
                    if T & (T - 1) == 0:
                        return d
                    seen.add(T)
                    nxt.append(T)
        frontier = nxt
    return None


def det_int(m):
    """Fraction-free (Bareiss) determinant of a square integer matrix."""
    m = [row[:] for row in m]
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


def stationary_integer(a, b, n):
    lap = [[0] * n for _ in range(n)]
    for q in range(n):
        lap[q][q] += 2
        lap[q][a[q]] -= 1
        lap[q][b[q]] -= 1
    e = [det_int([[lap[i][j] for j in range(n) if j != q] for i in range(n) if i != q])
         for q in range(n)]
    g = 0
    for x in e:
        g = math.gcd(g, abs(x))
    e = [x // g for x in e]
    if e[0] < 0:
        e = [-x for x in e]
    return e


def main():
    reps = cycle_type_representatives(N)
    by_d = defaultdict(lambda: [0, 0, 0])      # d -> [automata, largest L, largest rt]
    total, max_L, max_rt, arg_L = 0, 0, 0, None
    for a in reps:
        for b in itertools.product(range(N), repeat=N):
            if not strongly_connected(a, b, N):
                continue
            rt = reset_threshold(a, b, N)
            if rt is None:
                continue
            indeg = [0] * N
            for q in range(N):
                indeg[a[q]] += 1
                indeg[b[q]] += 1
            d = sum(abs(x - 2) for x in indeg)
            e = stationary_integer(a, b, N)
            lhs = [0] * N
            for q in range(N):
                lhs[a[q]] += e[q]
                lhs[b[q]] += e[q]
            assert lhs == [2 * x for x in e] and all(x > 0 for x in e)
            s = sum(e)
            L = 1
            for x in e:
                den = s // math.gcd(x, s)
                L = L * den // math.gcd(L, den)
            total += 1
            cell = by_d[d]
            cell[0] += 1
            cell[1] = max(cell[1], L)
            cell[2] = max(cell[2], rt)
            max_rt = max(max_rt, rt)
            if L > max_L:
                max_L, arg_L = L, (a, b, e)
    print("berlinkov_L -- n = 6, first letter a permutation (%d cycle types), second letter any map"
          % len(reps))
    print("  synchronizing and strongly connected: %d automata" % total)
    for d in sorted(by_d):
        print("    d=%2d  automata=%7d  largest L=%4d  largest reset threshold=%3d" % ((d,) + tuple(by_d[d])))
    print("  largest L = %d, e.g. a = %s, b = %s, e = %s" % (max_L, list(arg_L[0]), list(arg_L[1]), arg_L[2]))
    print()
    check("11 cycle types for the first letter", len(reps) == 11)
    check("L reaches 135 on the stratum", max_L == 135)
    check("1 + (n-1)(L-2) = 666 at L = 135", 1 + (N - 1) * (max_L - 2) == 666)
    check("the exact maximum reset threshold on the stratum is 25 = (n-1)^2", max_rt == 25)
    print(f"\n{len(rows)} rows, {rows.count(False)} FAILED", flush=True)
    return rows.count(False)


if __name__ == "__main__":
    sys.exit(min(main(), 255))
