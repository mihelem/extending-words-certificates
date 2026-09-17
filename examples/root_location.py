#!/usr/bin/env python3
"""root_location.py -- where the roots of p and q_c lie relative to the circle |z| = k.

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A (on Theorem 3): min|root(p)|/k, with
      p(z) = sum_{j=0}^{n-2} (n-1-j) k^{n-2-j} z^j, does not depend on k (substitute
      z = k zeta), and it falls strictly at every step from 2 at n = 3 to 1.05427
      at n = 40, exceeding 1 at every one of those sizes.
  Appendix A (on Theorem 5): 1,760 random strictly positive weightings over
      k = 2..5 and n = 3..13 give no root of q_c with |z| <= k, the smallest ratio
      observed being min|z|/k = 1.00075.  Taking c = (eps, ..., eps, 1) sends q_c
      coefficientwise to h_{n-1}, whose roots lie on |z| = k; at n = 13 and k = 2
      the ratio is 1.00000004 already at eps = 1e-6, stays above 1 for every
      eps > 0, and equals 1 at eps = 0, so the infimum over the positive cone is
      exactly 1 and is not attained.
  Section 5.4: the roots of h_t(z) = sum_{j<t} k^{t-1-j} z^j all have modulus
      exactly k.

The random weightings are drawn exactly as stated in the sweep below (uniform on
[0.001, 100] for every c_t, seed 11, 40 weightings per (k, n) cell, numpy root
finding); the series and the eps family use 60-digit mpmath.

Usage:    python root_location.py
Output:   one [PASS]/[FAIL] line per statement, then "N rows, M FAILED".
Runtime:  under a minute.
Requires: Python 3.8 or later, mpmath and numpy.  Exit status = number of failed
          rows.
"""

import random
import sys

import mpmath as mp

mp.mp.dps = 60

ROWS = []
FAILED = 0


def row(tag, text, fn):
    global FAILED
    try:
        ok, detail = fn()
    except Exception as exc:                              # noqa: BLE001
        ok, detail = False, "EXCEPTION %s: %s" % (type(exc).__name__, exc)
    status = "PASS" if ok else "FAIL"
    if not ok:
        FAILED += 1
    line = "  [%s] %s: %s -- %s" % (status, tag, text, detail)
    ROWS.append(line)
    print(line)
    sys.stdout.flush()


# ---------------------------------------------------------------- the polynomials

def coeffs_P(n):
    """P_n(zeta) = sum_{j=0}^{n-2} (n-1-j) zeta^j, ascending."""
    return [mp.mpf(n - 1 - j) for j in range(n - 1)]


def coeffs_p(n, k):
    """Theorem 3's p(z) = sum_{j=0}^{n-2} (n-1-j) k^{n-2-j} z^j, ascending."""
    return [mp.mpf(n - 1 - j) * mp.mpf(k) ** (n - 2 - j) for j in range(n - 1)]


def coeffs_q(c, k):
    """Theorem 5's q_c, ascending.  c is c_1..c_{n-1} as a 0-based list."""
    m = len(c)                                            # m = n-1
    return [sum(mp.mpf(c[t - 1]) * mp.mpf(k) ** (t - 1 - j) for t in range(j + 1, m + 1))
            for j in range(m)]


def coeffs_h(t, k):
    """Section 5.4's h_t(z) = sum_{j<t} k^{t-1-j} z^j, ascending.  Roots on |z|=k."""
    return [mp.mpf(k) ** (t - 1 - j) for j in range(t)]


def minroot(asc):
    """Smallest root modulus of a polynomial given ascending, as an mpf."""
    if len(asc) < 2:
        return None
    rs = mp.polyroots(list(reversed(asc)), maxsteps=200, extraprec=400)
    return min(abs(r) for r in rs)


# ---------------------------------------------------------------- Theorem 3

MINZ = {}


def r1():
    """k-independence, measured."""
    worst, where = mp.mpf(0), None
    for n in list(range(3, 21)) + [30, 40]:
        base = minroot(coeffs_P(n))
        for k in (2, 3, 4, 5):
            got = minroot(coeffs_p(n, k)) / k
            d = abs(got - base)
            if d > worst:
                worst, where = d, (n, k)
    return worst < mp.mpf("1e-40"), (
        "max |min|root(p)|/k - min|root(P_n)|| = %.3e over n in 3..20,30,40 and "
        "k = 2,3,4,5 (worst at n=%d, k=%d)" % (worst, where[0], where[1]))


def r2():
    """The series, 3 <= n <= 40, and the values printed at n=3 and n=40."""
    for n in range(3, 41):
        MINZ[n] = minroot(coeffs_P(n))
    v3, v40 = MINZ[3], MINZ[40]
    ok = abs(v3 - 2) < mp.mpf("1e-40") and mp.nstr(v40, 6) == "1.05427"
    return ok, ("n=3: %s, n=4: %s, n=10: %s, n=20: %s, n=40: %s (60-digit mpmath)"
                % (mp.nstr(MINZ[3], 8), mp.nstr(MINZ[4], 8), mp.nstr(MINZ[10], 8),
                   mp.nstr(MINZ[20], 8), mp.nstr(v40, 10)))


def r2b():
    """numpy agrees with the 60-digit values."""
    import numpy as np
    worst, where = 0.0, None
    for n in range(3, 41):
        asc = [float(n - 1 - j) for j in range(n - 1)]
        rs = np.roots(asc[::-1])
        got = float(min(abs(rs)))
        d = abs(got - float(MINZ[n]))
        if d > worst:
            worst, where = d, n
    return worst < 1e-9, ("max |numpy - mpmath| = %.3e over 3 <= n <= 40 "
                          "(worst at n=%d)" % (worst, where))


def r3():
    """Strictly decreasing at every step."""
    bad = [n for n in range(4, 41) if not MINZ[n] < MINZ[n - 1]]
    return not bad, ("strictly decreasing at every one of the 37 steps from "
                     "n=3 to n=40: %s -> %s"
                     % (mp.nstr(MINZ[3], 6), mp.nstr(MINZ[40], 8)))


def r4():
    """Theorem 3's conclusion: strictly outside the circle at every n."""
    worst = min(MINZ[n] - 1 for n in MINZ)
    at = [n for n in MINZ if MINZ[n] - 1 == worst][0]
    return worst > 0, ("min over 3 <= n <= 40 of (min|root|/k - 1) = %s, at n=%d"
                       % (mp.nstr(worst, 8), at))


def r5():
    """Section 5.4: the roots of h_t lie exactly on |z| = k."""
    worst = mp.mpf(0)
    for k in (2, 3, 5):
        for t in (2, 5, 13, 39):
            got = minroot(coeffs_h(t, k)) / k
            worst = max(worst, abs(got - 1))
    return worst < mp.mpf("1e-40"), (
        "h_t: min|z|/k = 1 to %.3e over k=2,3,5 and t=2,5,13,39" % worst)


# ---------------------------------------------------------------- Theorem 5

def sweep(seed, per_cell, ks=(2, 3, 4, 5), ns=range(3, 14), lo=1e-3, hi=100.0):
    """Random strictly positive weightings c; roots of q_c by numpy.

    Returned min is over |z|/k; bad counts roots at or inside the circle."""
    import numpy as np
    rnd = random.Random()
    rnd.seed(seed)
    bad, mn, tested, worst_at = 0, 1e9, 0, None
    for k in ks:
        for n in ns:
            for _ in range(per_cell):
                c = [rnd.uniform(lo, hi) for _ in range(n - 1)]
                gam = [sum(c[t - 1] * k ** (t - 1 - j) for t in range(j + 1, n))
                       for j in range(n - 1)]
                if len(gam) < 2:
                    continue
                rs = np.roots(gam[::-1])
                tested += 1
                m = float(min(abs(rs))) / k
                if m < mn:
                    mn, worst_at = m, (k, n)
                if m <= 1 - 1e-9:
                    bad += 1
    return bad, mn, tested, worst_at


def random_weightings():
    """1,760 weightings: seed 11, 40 per (k, n) cell."""
    bad, mn, tested, at = sweep(11, 40)
    ok = (bad == 0 and tested == 1760 and abs(mn - 1.000748) < 5e-7
          and "%.5f" % mn == "1.00075")
    return ok, ("%d weightings, %d roots with |z| <= k, min |z|/k = %.6f "
                "(worst cell k=%d, n=%d)" % (tested, bad, mn, at[0], at[1]))


def eps_family():
    """c = (eps,...,eps,1) at n=13, k=2: strictly above 1, decreasing to 1."""
    n, k = 13, 2
    out = []
    for e in ("1e-1", "1e-2", "1e-3", "1e-4", "1e-6"):
        c = [mp.mpf(e)] * (n - 2) + [mp.mpf(1)]
        v = minroot(coeffs_q(c, k)) / k
        out.append((e, v))
    strict = all(v > 1 for _, v in out)
    mono = all(out[i][1] > out[i + 1][1] for i in range(len(out) - 1))
    printed = mp.nstr(out[-1][1], 9) == "1.00000004"
    return strict and mono and printed, (
        "n=13, k=2, c=(eps,...,eps,1): min|z|/k = %s, %s, %s, %s, %s for "
        "eps = 1e-1, 1e-2, 1e-3, 1e-4, 1e-6"
        % tuple(mp.nstr(v, 10) for _, v in out))


def eps_zero():
    """At eps = 0 (not strictly positive) the ratio is exactly 1: c = e_{n-1} gives h_{n-1}."""
    n, k = 13, 2
    c = [mp.mpf(0)] * (n - 2) + [mp.mpf(1)]
    v = minroot(coeffs_q(c, k)) / k
    return abs(v - 1) < mp.mpf("1e-40"), (
        "c = (0,...,0,1) gives min|z|/k = %s" % mp.nstr(v, 12))


# ---------------------------------------------------------------- main

def main():
    print("root_location -- roots of p (Theorem 3) and q_c (Theorem 5)")
    print()
    print("  ---- Theorem 3: min|root(p)|/k over 3 <= n <= 40 ----")
    row("R1", "the ratio min|root(p)|/k does not depend on k", r1)
    row("R2", "the series is 2 at n=3 and 1.05427 at n=40", r2)
    row("R2b", "numpy agrees with the 60-digit values at every n", r2b)
    row("R3", "the series is strictly decreasing in n", r3)
    row("R4", "every value exceeds 1", r4)
    row("R5", "Section 5.4: the roots of h_t have modulus exactly k", r5)
    print()
    print("  ---- Theorem 5: strictly positive weightings ----")
    row("V1", "1,760 random weightings: no root with |z| <= k (to within 1e-9), smallest ratio 1.00075", random_weightings)
    row("V2", "c = (eps,...,eps,1): 1.00000004 at eps = 1e-6, strictly above 1", eps_family)
    row("V3", "eps = 0, a weighting that is not strictly positive: the ratio is exactly 1", eps_zero)
    print()
    print("%d rows, %d FAILED" % (len(ROWS), FAILED))
    return FAILED


if __name__ == "__main__":
    sys.exit(min(main(), 255))
