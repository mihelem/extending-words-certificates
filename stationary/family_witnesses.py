#!/usr/bin/env python3
"""family_witnesses.py -- the infinite family of witnesses against B_e (Appendix C, Proposition on the family).

For n >= 5 write n = 2L + 1 + eps with L >= 2 and eps in {0, 1}, and r = L - 1 + eps.  States: the cycle
g_1, ..., g_L, the tail h_1, h_2 and the fixed points z_1, ..., z_r, n = L + 2 + r in all.  Letters:
    a: g_i -> g_{i+1} (g_L -> g_1), h_2 -> h_1 -> g_1, z_i -> z_i;
    c: the transposition (g_L h_2) times the cycle (g_{L-1} h_1 z_1 ... z_r), fixing g_1, ..., g_{L-2}.
Subset S = {g_L, h_2}.  Claims checked here for every n in the range given (default 5..40):
    (1) strongly connected and synchronizing;
    (2) minext(S) = 2L + 2 >= n (breadth-first search over the preimage sets of size <= 2, exhaustive);
    (3) at letter weights (t, 1-t) the stationary vector is proportional to
          e(g_i) = 1 + 2u (i <= L-2), e(g_{L-1}) = 1 + u, e(g_L) = 1, e(h_1) = e(z_i) = 2u, e(h_2) = u,  u = 1 - t,
        so that n e(S) - 2 e(Q) = (n - 2L) - u (3n - 8): checked exactly at t = 1/2, 2/3, 9/10 and at the
        threshold t* = 1 - (n - 2L)/(3n - 8), where it vanishes (a witness with B_e(S) = 0), and at the midpoint
        of (t*, 1), where it is positive.
Prints one PASS/FAIL line per claim and exits 0 iff all pass.  Pure Python, exact rational arithmetic.
Usage: python family_witnesses.py [nmin nmax]
"""
import sys
from fractions import Fraction

def build(n):
    L = (n - 1) // 2; eps = (n - 1) % 2; r = L - 1 + eps
    assert n == L + 2 + r and L >= 2 and r >= 1
    g = list(range(L)); h1, h2 = L, L + 1; z = list(range(L + 2, n))
    a = [(i + 1) % L for i in range(L)] + [g[0], h1] + z
    c = list(range(n))
    c[g[-1]], c[h2] = h2, g[-1]
    cyc = [g[L - 2], h1] + z
    for i in range(len(cyc)): c[cyc[i]] = cyc[(i + 1) % len(cyc)]
    return L, r, a, c, [g[-1], h2]

def strongly_connected(letters, n):
    for fwd in (True, False):
        seen = {0}; stack = [0]
        while stack:
            q = stack.pop()
            for f in letters:
                nb = [f[q]] if fwd else [p for p in range(n) if f[p] == q]
                for x in nb:
                    if x not in seen: seen.add(x); stack.append(x)
        if len(seen) != n: return False
    return True

def synchronizing(letters, n):
    """pair automaton: every pair reaches a singleton"""
    inv = [[[] for _ in range(n)] for _ in letters]
    for x, f in enumerate(letters):
        for q in range(n): inv[x][f[q]].append(q)
    merged = {(p, p) for p in range(n)}; stack = list(merged)
    while stack:
        p, q = stack.pop()
        for x in range(len(letters)):
            for p2 in inv[x][p]:
                for q2 in inv[x][q]:
                    for pair in ((p2, q2), (q2, p2)):
                        if pair not in merged: merged.add(pair); stack.append(pair)
    return len(merged) == n * n

def minext(letters, n, S):
    """shortest |u| with |S u^{-1}| > |S|, exploring the sets of size <= |S| (exact: sizes change by <= 1 per step)"""
    inv = [[0] * n for _ in letters]
    for x, f in enumerate(letters):
        for q in range(n): inv[x][f[q]] |= 1 << q
    size = bin(S).count("1"); layer = {S}; seen = {S}
    for l in range(1, 4 * n):
        nxt = set()
        for T in layer:
            for x in range(len(letters)):
                U = 0; TT = T
                while TT:
                    q = (TT & -TT).bit_length() - 1; TT &= TT - 1; U |= inv[x][q]
                if bin(U).count("1") > size: return l
                if U and U not in seen: seen.add(U); nxt.add(U)
        layer = nxt
        if not layer: return None
    return None

def stationary(letters, n, w):
    """exact stationary row vector of sum_x w_x pi(x), normalised to e(Q) = 1"""
    A = [[Fraction(0)] * n for _ in range(n)]
    for x, f in enumerate(letters):
        for i in range(n): A[i][f[i]] += w[x]
    for i in range(n): A[i][i] -= 1
    M = [[A[i][j] for i in range(n)] + [Fraction(0)] for j in range(n)]
    M[n - 1] = [Fraction(1)] * n + [Fraction(1)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None: continue
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]; M[col] = [v / pv for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                fac = M[r][col]; M[r] = [p - fac * q for p, q in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]

def closed_form(n, L, t):
    u = 1 - t
    e = [1 + 2 * u] * (L - 2) + [1 + u, Fraction(1), 2 * u, u] + [2 * u] * (n - L - 2)
    tot = sum(e)
    return [v / tot for v in e]

def main():
    nmin, nmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (5, 40)
    ok = True
    def report(name, cond, detail=""):
        nonlocal ok
        ok = ok and cond
        print("%s  %s %s" % ("PASS" if cond else "FAIL", name, detail))
    for n in range(nmin, nmax + 1):
        L, r, a, c, S = build(n); Sm = sum(1 << q for q in S)
        report("n=%2d L=%2d r=%2d strongly connected and synchronizing" % (n, L, r),
               strongly_connected([a, c], n) and synchronizing([a, c], n))
        me = minext([a, c], n, Sm)
        report("n=%2d minext(S) = 2L+2 = %d >= n" % (n, 2 * L + 2), me == 2 * L + 2 and me >= n, "(measured %s)" % me)
        tstar = 1 - Fraction(n - 2 * L, 3 * n - 8)
        for t in (Fraction(1, 2), Fraction(2, 3), Fraction(9, 10), tstar, (tstar + 1) / 2):
            e = stationary([a, c], n, [t, 1 - t]); f = closed_form(n, L, t)
            val = n * sum(e[q] for q in S) - 2
            pred = ((n - 2 * L) - (1 - t) * (3 * n - 8)) / (L + 2 * (n - 2) * (1 - t))
            report("n=%2d t=%s closed form of e_t and of n e(S)-|S|e(Q)" % (n, t), e == f and val == pred,
                   "value %s" % val)
        e = stationary([a, c], n, [tstar, 1 - tstar]); v0 = n * sum(e[q] for q in S) - 2
        e = stationary([a, c], n, [(tstar + 1) / 2, 1 - (tstar + 1) / 2]); v1 = n * sum(e[q] for q in S) - 2
        report("n=%2d B_e(S) = 0 at t* = %s and > 0 at (t*+1)/2" % (n, tstar), v0 == 0 and v1 > 0)
    print("ALL PASS" if ok else "SOME FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
