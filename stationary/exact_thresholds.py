"""exact_thresholds.py -- exact bias thresholds of the BOUNDARY lines of a permutation_stratum.c (or
bias_census_exact.c) output

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix C: on the stratum of the binary n = 9 population whose first letter is a permutation, the least threshold
    is the root 0.594 of 11t^2 - 20t + 8, attained by 384 pairs, with 32 pairs at the root 0.643 of t^3 + 8t^2 - 18t + 8
    and 1,568 at 2/3.
  Appendix A: the n = 9 stratum's "1,984 pairs with threshold at most 2/3 were re-verified exactly by an implementation
    sharing no code with it" (14 distinct orbits, weighted by orbit size).  On the n = 8 stratum the same program gives
    2 - sqrt 2 (t^2 - 4t + 2, 384 pairs), 0.603 (2t^3 - 4t^2 + 5t - 2, 32) and 2/3 (3t - 2, 32).
Method:   for every distinct (a, b, S, biased letter) among the BOUNDARY lines, solve e P = e exactly over Q(t) with
  P = t pi(biased) + (1-t) pi(other) (sympy nullspace), form the excess n e_t(S) - |S| e_t(Q), factor its numerator,
  and report the least root in [1/2, 1] together with the minimal polynomial of that root and the (orbit-weighted)
  number of pairs sharing it; the sign change of the excess at that root is asserted.  Also checks minext(S) = n,
  strong connectivity and synchronization independently of the census (assertions).
Usage:    python exact_thresholds.py OUT [OUT ...]        (all part outputs of one run)
Output:   distinct (a,b,S,x): <orbits>  weighted pairs: <pairs>
          threshold <root>  minimal polynomial <p>  weighted pairs <count>  example ...   (one line per polynomial)
          DONE exact_thresholds groups= min_threshold=
Runtime:  about 40 seconds at n = 9, a few seconds at n <= 8.
Requires: Python 3, sympy.
"""
import sys, re
from fractions import Fraction
import sympy as sp

def parse(line):
    a = [int(x) for x in re.search(r"a=\[([\d,]+)\]", line).group(1).split(",")]
    b = [int(x) for x in re.search(r"b=\[([\d,]+)\]", line).group(1).split(",")]
    S = [int(x) for x in re.search(r"S=\{([\d,]*)\}", line).group(1).strip(",").split(",")]
    x = re.search(r"biased=([ab])", line).group(1)
    w = re.search(r"orbit=(\d+)", line); w = int(w.group(1)) if w else 1
    return tuple(a), tuple(b), tuple(sorted(S)), x, w

def minext(n, lets, S):
    m = len(S); cur = {frozenset(S)}; seen = set(cur)
    for depth in range(1, n + 1):
        nxt = set()
        for T in cur:
            for L in lets:
                pre = frozenset(p for p in range(n) if L[p] in T)
                if len(pre) > m: return depth
                if pre not in seen: seen.add(pre); nxt.add(pre)
        if not nxt: return n + 1
        cur = nxt
    return n + 1

def sc_sync(n, lets):
    reach = {0}; fr = [0]
    while fr:
        p = fr.pop()
        for L in lets:
            if L[p] not in reach: reach.add(L[p]); fr.append(L[p])
    if len(reach) < n: return False
    co = {0}; changed = True
    while changed:
        changed = False
        for p in range(n):
            if p not in co and any(L[p] in co for L in lets): co.add(p); changed = True
    if len(co) < n: return False
    merged = {(p, p) for p in range(n)}; changed = True
    while changed:
        changed = False
        for p in range(n):
            for q in range(p + 1, n):
                if (p, q) in merged: continue
                for L in lets:
                    u, v = sorted((L[p], L[q]))
                    if (u, v) in merged: merged.add((p, q)); changed = True; break
    return all((p, q) in merged for p in range(n) for q in range(p + 1, n))

t = sp.symbols('t')
def excess(n, a, b, S, x):
    heavy, light = (b, a) if x == 'b' else (a, b)
    P = sp.zeros(n, n)
    for p in range(n):
        P[p, heavy[p]] += t; P[p, light[p]] += 1 - t
    M = (P.T - sp.eye(n))
    ns = M.nullspace()
    assert len(ns) == 1, "stationary vector not unique"
    e = ns[0]
    ex = sp.together(n * sum(e[q] for q in S) - len(S) * sum(e))
    num, den = sp.fraction(sp.cancel(ex))
    return sp.factor(num), sp.factor(den), e

def least_root(num):
    best = None
    for fac, mult in sp.factor_list(sp.Poly(num, t))[1]:
        fac = sp.Poly(fac, t)
        if fac.degree() == 0: continue
        for r in fac.nroots(n=30):
            if r.is_real and sp.Rational(1, 2) - sp.Rational(1, 10**9) <= r <= 1:
                if best is None or r < best[0]: best = (r, fac.as_expr())
    return best

def main():
    groups = {}
    for fn in sys.argv[1:]:
        for line in open(fn, encoding='utf-8', errors='replace'):
            if line.startswith("BOUNDARY"):
                a, b, S, x, w = parse(line)
                groups[(a, b, S, x)] = groups.get((a, b, S, x), 0) + w
    print("distinct (a,b,S,x):", len(groups), " weighted pairs:", sum(groups.values()))
    bypoly = {}
    for (a, b, S, x), w in sorted(groups.items()):
        n = len(a)
        assert minext(n, (a, b), S) == n, ("not stuck at exactly n", a, b, S)
        assert sc_sync(n, (a, b)), ("not SC+sync", a, b)
        num, den, e = excess(n, a, b, S, x)
        lr = least_root(num)
        assert lr is not None, ("no root in [1/2,1]", a, b, S, x, num)
        r, fac = lr
        key = str(sp.expand(fac)); bypoly.setdefault(key, [0, r, None]); bypoly[key][0] += w
        if bypoly[key][2] is None: bypoly[key][2] = (a, b, S, x, str(num))
        # sign check: negative just below the root and nonnegative at the root's right neighbourhood
        below = num.subs(t, r - sp.Rational(1, 10**6)); above = num.subs(t, r + sp.Rational(1, 10**6))
        d_at = den.subs(t, r)
        assert (below * d_at < 0) and (above * d_at > 0), ("excess does not change sign upward at the root", a, b, S, x, num, r)
    for key, (w, r, ex) in sorted(bypoly.items(), key=lambda kv: kv[1][1]):
        print("threshold %.12f  minimal polynomial %s  weighted pairs %d  example a=%s b=%s S=%s biased=%s  numerator %s" % (
            float(r), key, w, list(ex[0]), list(ex[1]), list(ex[2]), ex[3], ex[4]))
    print("DONE exact_thresholds groups=%d min_threshold=%.12f" % (len(groups), min(float(v[1]) for v in bypoly.values())))

if __name__ == "__main__":
    main()
