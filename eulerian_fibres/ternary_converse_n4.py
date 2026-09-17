"""ternary_converse_n4.py -- the coprimality conjecture of Section 5.2 is binary: with three letters it fails at n = 4.

Checks (one [PASS]/[FAIL] row each, exit code = number of failures):
  1. the automaton a = [0,0,2,2], b = [0,1,3,2], c = [3,1,1,3] on Q = {0,1,2,3} is Eulerian (every in-degree 3),
     synchronizing and strongly connected, with kappa_a = kappa_c = 2 and kappa_b = 0;
  2. S = {0,1} has minext(S) = 3 = n-1, attained by the word cbc, and gcd(|S|, n) = 2;
  3. over all Eulerian synchronizing strongly connected ternary automata on 4 states, with the first letter
     ranging over one representative per conjugacy class of maps and the other two letters ordered, there are
     24,606 automata, the maximum of minext at every subset size is 3, and 832 pairs (automaton, subset) of
     size 2 attain 3.
Runs in about a minute.  Standard library only.
"""
import sys, itertools
from itertools import product
from math import gcd

def preimage(T, f, n):
    return frozenset(q for q in range(n) if f[q] in T)

def minext(S, letters, n, cap):
    S = frozenset(S); seen = {S}; frontier = [S]
    for length in range(1, cap + 1):
        nxt = []
        for T in frontier:
            for f in letters:
                P = preimage(T, f, n)
                if len(P) > len(S): return length
                if P not in seen: seen.add(P); nxt.append(P)
        frontier = nxt
        if not frontier: return None
    return None

def synchronizing(letters, n):
    inv = [[[] for _ in range(n)] for _ in letters]
    for x, f in enumerate(letters):
        for q in range(n): inv[x][f[q]].append(q)
    merged = {(p, p) for p in range(n)}; stack = list(merged)
    while stack:
        p, q = stack.pop()
        for x in range(len(letters)):
            for p2 in inv[x][p]:
                for q2 in inv[x][q]:
                    if (p2, q2) not in merged:
                        merged.add((p2, q2)); merged.add((q2, p2)); stack.append((p2, q2))
    return len(merged) == n * n

def strongly_connected(letters, n):
    def reach(fwd):
        seen = {0}; stack = [0]
        while stack:
            q = stack.pop()
            for f in letters:
                nb = [f[q]] if fwd else [p for p in range(n) if f[p] == q]
                for r in nb:
                    if r not in seen: seen.add(r); stack.append(r)
        return len(seen) == n
    return reach(True) and reach(False)

def canon(f, n):
    best = None
    for p in itertools.permutations(range(n)):
        inv = [0] * n
        for i in range(n): inv[p[i]] = i
        h = tuple(p[f[inv[i]]] for i in range(n))
        if best is None or h < best: best = h
    return best

def main():
    fails = 0
    def row(ok, text):
        nonlocal fails
        print(("[PASS] " if ok else "[FAIL] ") + text)
        if not ok: fails += 1
    n = 4
    a, b, c = [0, 0, 2, 2], [0, 1, 3, 2], [3, 1, 1, 3]
    L = [a, b, c]
    indeg = [sum(1 for f in L for q in range(n) if f[q] == i) for i in range(n)]
    kap = [n - len(set(f)) for f in L]
    row(indeg == [3, 3, 3, 3], "in-degrees %s: Eulerian" % indeg)
    row(synchronizing(L, n) and strongly_connected(L, n), "synchronizing and strongly connected")
    row(kap == [2, 0, 2], "kappa = %s" % kap)
    S = {0, 1}
    me = minext(S, L, n, n + 1)
    # S (cbc)^{-1} is computed as ((S c^{-1}) b^{-1}) c^{-1}
    T = preimage(preimage(preimage(S, c, n), b, n), c, n)
    row(me == 3, "minext({0,1}) = %s (expected 3 = n-1)" % me)
    row(len(T) == 4, "S (cbc)^{-1} = %s has size 4 > |S|" % sorted(T))
    row(gcd(2, n) == 2, "gcd(|S|, n) = 2")
    # exhaustive census
    maps = list(product(range(n), repeat=n))
    reps = sorted({canon(f, n) for f in maps})
    by_indeg = {}
    for f in maps:
        d = [0] * n
        for q in range(n): d[f[q]] += 1
        by_indeg.setdefault(tuple(d), []).append(f)
    total = 0; attaining = 0; maxima = {}
    for ra in reps:
        da = [0] * n
        for q in range(n): da[ra[q]] += 1
        for rb in maps:
            db = [0] * n
            for q in range(n): db[rb[q]] += 1
            need = tuple(3 - da[i] - db[i] for i in range(n))
            if min(need) < 0: continue
            for rc in by_indeg.get(need, []):
                letters = [list(ra), list(rb), list(rc)]
                if not strongly_connected(letters, n) or not synchronizing(letters, n): continue
                total += 1
                for m in (1, 2, 3):
                    for Sm in itertools.combinations(range(n), m):
                        v = minext(set(Sm), letters, n, n + 1)
                        if v is None: v = n + 1
                        maxima[m] = max(maxima.get(m, 0), v)
                        if m == 2 and v == 3: attaining += 1
    row(total == 24606, "Eulerian synchronizing strongly connected ternary automata on 4 states: %d (expected 24,606)" % total)
    row(all(maxima[m] == 3 for m in (1, 2, 3)), "maximum of minext by subset size: %s (expected 3 at every size)" % maxima)
    row(attaining == 832, "pairs (automaton, subset) of size 2 with minext = 3: %d (expected 832)" % attaining)
    print("%d FAILED" % fails)
    sys.exit(fails)

if __name__ == "__main__":
    main()
