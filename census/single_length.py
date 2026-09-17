"""single_length.py -- how often a single defect sigma_t vanishes identically on a
non-Eulerian automaton, counted over all transition tables.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 5.4: counting all transition tables, with no quotient, 6 of the 639 non-Eulerian
      binary automata at n=3 and 48 of the 63,016 at n=4 have sigma_t == 0 for some single
      t >= 2, against 0 of the 18,003 non-Eulerian ternary automata at n=3.
      The first such automaton in enumeration order at n=3 is the automaton of Example 2,
      a = (1,0,0), b = (2,0,0), with w = (2,-1,-1) and sigma_2 == 0.

Definitions (Sections 2, 3, 5.3): for t >= 1, w_t = 1^T M^t - k^t 1, so that
sigma_t(S) = w_t [S]^T and sigma_t == 0 exactly when w_t = 0; w_1 = w, and the automaton is
Eulerian exactly when w = 0.  The lengths tested are 2 <= t <= n-1.

Population / convention: every k-tuple of maps [n]->[n] (states labelled, letters ordered;
no quotient and no filter): 3^6 = 729 tables at (n,k) = (3,2), 4^8 = 65,536 at (4,2) and
3^9 = 19,683 at (3,3).

Usage:    python single_length.py

Output:   one [PASS]/[FAIL] row per population, "non-Eulerian automata" and "with
          sigma_t == 0 for some single t in [2, n-1]", with the paper's values; one row for
          the first witness at n=3; then "N rows, M FAILED".  Exit status = number of
          failed rows.

Runtime:  about 1 s (one core).

Requires: Python 3.8+ (standard library only).
"""
import sys


def single_horizon(n, k):
    """count complete DFAs with w != 0 and w_t == 0 for some t >= 2."""
    import itertools as it
    tot, hit, ex = 0, 0, None
    for maps in it.product(it.product(range(n), repeat=n), repeat=k):
        v = [1] * n
        ws, kt = [], 1
        for _ in range(n - 1):
            nv = [0] * n
            for f in maps:
                for q in range(n):
                    nv[f[q]] += v[q]
            v = nv
            kt *= k
            ws.append([v[q] - kt for q in range(n)])
        if all(x == 0 for x in ws[0]):
            continue
        tot += 1
        for t in range(1, len(ws)):
            if all(x == 0 for x in ws[t]):
                hit += 1
                if ex is None:
                    ex = ([list(f) for f in maps], t + 1, ws[0])
                break
    return tot, hit, ex


def main():
    paper = {(3, 2): (639, 6), (4, 2): (63016, 48), (3, 3): (18003, 0)}
    names = {(3, 2): "binary, n=3", (4, 2): "binary, n=4", (3, 3): "ternary, n=3"}
    rows, failed = 0, 0
    res = {}
    for (n, k) in ((3, 2), (4, 2), (3, 3)):
        res[(n, k)] = single_horizon(n, k)
        tot, hit, _ = res[(n, k)]
        ok = (tot, hit) == paper[(n, k)]
        rows += 1
        failed += 0 if ok else 1
        print("[%s] %s, all %d^%d transition tables: %d non-Eulerian automata, %d of them "
              "with sigma_t == 0 for some single t in [2, %d] (Section 5.4: %d of %d)"
              % ("PASS" if ok else "FAIL", names[(n, k)], n, n * k, tot, hit, n - 1,
                 paper[(n, k)][1], paper[(n, k)][0]))
    ex = res[(3, 2)][2]
    ok = ex == ([[1, 0, 0], [2, 0, 0]], 2, [2, -1, -1])
    rows += 1
    failed += 0 if ok else 1
    print("[%s] binary, n=3: first such automaton in enumeration order: letters %s, "
          "vanishing sigma_t at t=%s, w=%s (Example 2: a=(1,0,0), b=(2,0,0), t=2, "
          "w=(2,-1,-1))" % ("PASS" if ok else "FAIL", ex[0] if ex else None,
                            ex[1] if ex else None, ex[2] if ex else None))
    print("\n%d rows, %d FAILED" % (rows, failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main())
