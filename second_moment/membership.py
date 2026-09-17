"""membership.py -- the exact membership test on (|S|, sigma_t(S), sum x_u^2) against the (Q-CERT+) threshold

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix D: "On the exhaustive synchronizing strongly connected binary
    populations, one row per proper nonempty subset and length t <= n-1, it
    certifies 0 rows of 708 at n=3 that the threshold misses, 80 of 52,080 at
    n=4, 15,053 of 3,910,560 at n=5 and 2,083,316 of 347,983,990 at n=6, that
    is 0, 0.15, 0.38 and 0.60 percent, rising at each size" -- this program
    computes n=3, 4, 5; membership.rs computes n=6 (and n<=5 as a cross-check).
  Appendix D: "at k^t=4, |S|=3 and -sigma_t(S)=3 the values attainable with
    every x_u<=0 are 3, 5 and 9", with 9 - 5 = 4 = 2(|S|-1).
Population / convention: binary automata on Q = {0,...,n-1}; letter a over one
  representative of each conjugacy class of endofunctions of Q (7, 19, 47
  classes at n=3, 4, 5), letter b over all n^n maps; kept if synchronizing and
  strongly connected (59, 1,240 and 32,588 automata: the quotient convention of
  Appendix A.1).  One row per kept automaton, proper nonempty subset S and
  length t = 1..n-1, so rows = automata x (2^n - 2) x (n-1).
  For a row: x_u = |S u^{-1}| - |S| over the 2^t words u of length t (applied
  letter by letter), m = -sigma_t(S) = -sum x_u, c = |S|, q = floor(m/c),
  r = m - qc.
    THRESHOLD (Q-CERT+, Proposition 4) fires iff sum x_u^2 > q c^2 + r^2
              (always when m < 0).
    MEMBERSHIP fires iff sum x_u^2 is not a value of sum y_u^2 over integers
              y_u in [0, c] (one per word) with sum y_u = m, i.e. iff the data
              (c, sigma_t(S), sum x_u^2) cannot come from x_u <= 0 for every u.
  A row counted in memonly_rows_syncsc is one where MEMBERSHIP fires and the
  THRESHOLD does not.
Usage:    python membership.py N          (N = 3, 4 or 5)
Output:   KEY=VALUE counters, with the keys printed by membership.rs: classes,
          autos (automata enumerated), syncsc (kept), eul (Eulerian among them),
          rows, thr, mem, memonly, memonly_sync (rows of kept automata only),
          rows_syncsc, thr_syncsc, memonly_rows_syncsc; then one [PASS]/[FAIL]
          row per checked statement and "R rows, F FAILED"; exit status F.
          Appendix D's figures are memonly_rows_syncsc of rows_syncsc.
Runtime:  one core: n=3 and n=4 about 1 s, n=5 about 30 s.
Requires: Python 3 (standard library only).
"""
import itertools
import sys
import time
from functools import lru_cache


# ---------- endofunction conjugacy classes under S_n
def canon(f, n, perms):
    best = None
    for p in perms:
        inv = [0] * n
        for i, pi in enumerate(p):
            inv[pi] = i
        g = tuple(p[f[inv[i]]] for i in range(n))
        if best is None or g < best:
            best = g
    return best


def classes(n):
    perms = list(itertools.permutations(range(n)))
    seen, reps = set(), []
    for f in itertools.product(range(n), repeat=n):
        c = canon(list(f), n, perms)
        if c not in seen:
            seen.add(c)
            reps.append(list(f))
    return reps


# ---------- automaton predicates
def is_sync(a, b, n):
    """pair-automaton reachability: synchronizing iff every pair merges"""
    frontier = {(p, q) for p in range(n) for q in range(p + 1, n)}
    merged = set()
    for pair in frontier:
        seen = {pair}
        stack = [pair]
        ok = False
        while stack:
            p, q = stack.pop()
            if p == q:
                ok = True
                break
            for f in (a, b):
                nx = (min(f[p], f[q]), max(f[p], f[q]))
                if nx not in seen:
                    seen.add(nx)
                    stack.append(nx)
        if not ok:
            return False
    return True


def is_sc(a, b, n):
    fwd = [set() for _ in range(n)]
    rev = [set() for _ in range(n)]
    for q in range(n):
        for f in (a, b):
            fwd[q].add(f[q])
            rev[f[q]].add(q)

    def reach(g, s):
        seen, st = {s}, [s]
        while st:
            x = st.pop()
            for y in g[x]:
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        return seen
    return len(reach(fwd, 0)) == n and len(reach(rev, 0)) == n


# ---------- attainable sum-of-squares under all-non-positivity
@lru_cache(maxsize=None)
def attainable(N, c, m):
    """set of sum(y^2) over y in [0,c]^N with sum(y)=m"""
    if m < 0 or m > N * c:
        return frozenset()
    cur = {0: {0}}
    for _ in range(N):
        nxt = {}
        for s, sq in cur.items():
            for y in range(0, c + 1):
                s2 = s + y
                if s2 > m:
                    break
                d = nxt.setdefault(s2, set())
                yy = y * y
                for v in sq:
                    d.add(v + yy)
        cur = nxt
    return frozenset(cur.get(m, ()))


def run(n, tmax, want_filter):
    """returns counters over the quotient-convention corpus"""
    reps = classes(n)
    allmaps = list(itertools.product(range(n), repeat=n))
    subsets = [tuple(s) for size in range(1, n)
               for s in itertools.combinations(range(n), size)]
    C = dict(autos=0, sync=0, sc=0, syncsc=0, eul=0, rows=0,
             thr=0, mem=0, memonly=0, memonly_sync=0,
             memonly_rows_syncsc=0, rows_syncsc=0, thr_syncsc=0,
             bneg_rows=0, memonly_bneg=0)
    for a in reps:
        for bt in allmaps:
            b = list(bt)
            C["autos"] += 1
            sy = is_sync(a, b, n)
            sc = is_sc(a, b, n)
            if sy:
                C["sync"] += 1
            if sc:
                C["sc"] += 1
            keep = sy and sc
            if keep:
                C["syncsc"] += 1
                indeg = [0] * n
                for q in range(n):
                    for f in (a, b):
                        indeg[f[q]] += 1
                if all(d == 2 for d in indeg):
                    C["eul"] += 1
            if want_filter and not keep:
                continue
            # per-word preimage-size vectors, per length t
            for t in range(1, tmax + 1):
                words = list(itertools.product((0, 1), repeat=t))
                vs = []
                for w in words:
                    v = [0] * n
                    for q in range(n):
                        x = q
                        for ch in w:
                            x = (a if ch == 0 else b)[x]
                        v[x] += 1
                    vs.append(v)
                for S in subsets:
                    c = len(S)
                    xs = [sum(v[r] for r in S) - c for v in vs]
                    sig = sum(xs)
                    sq = sum(x * x for x in xs)
                    m = -sig
                    C["rows"] += 1
                    if keep:
                        C["rows_syncsc"] += 1
                    # threshold (Q-CERT+)
                    if m < 0:
                        thr = True
                    else:
                        q_, r_ = divmod(m, c)
                        thr = sq > q_ * c * c + r_ * r_
                    mem = sq not in attainable(len(words), c, m)
                    if thr:
                        C["thr"] += 1
                        if keep:
                            C["thr_syncsc"] += 1
                    if mem:
                        C["mem"] += 1
                    if mem and not thr:
                        C["memonly"] += 1
                        if sy:
                            C["memonly_sync"] += 1
                        if keep:
                            C["memonly_rows_syncsc"] += 1
    return C


# the paper's values: n -> (automata, Eulerian, rows, membership-only rows, share as printed)
PAPER = {
    3: (59, 8, 708, 0, "0"),
    4: (1240, 72, 52080, 80, "0.15"),
    5: (32588, 954, 3910560, 15053, "0.38"),
}
KEYS = ("classes", "autos", "syncsc", "eul", "rows", "thr", "mem", "memonly",
        "memonly_sync", "rows_syncsc", "thr_syncsc", "memonly_rows_syncsc")


def main(argv):
    if len(argv) != 2 or argv[1] not in ("3", "4", "5"):
        sys.exit("usage: python membership.py N    (N = 3, 4 or 5; n = 6: membership.rs)")
    n = int(argv[1])
    t0 = time.time()
    C = run(n, n - 1, want_filter=True)
    C["classes"] = len(classes(n))
    wall = time.time() - t0
    print("n=%d" % n)
    for key in KEYS:
        print("%s=%d" % (key, C[key]))
    print("wall=%.1fs" % wall)
    print("")

    checks = []

    def row(ok, text):
        checks.append(ok)
        print("[%s] %s" % ("PASS" if ok else "FAIL", text))

    autos, eul, rows, memonly, share = PAPER[n]
    got_share = 100.0 * C["memonly_rows_syncsc"] / C["rows_syncsc"] if C["rows_syncsc"] else float("nan")
    got_share_txt = "0" if C["memonly_rows_syncsc"] == 0 else "%.2f" % got_share
    row(C["syncsc"] == autos and C["eul"] == eul,
        "Appendix A, n=%d binary synchronizing strongly connected population: %s automata, "
        "%s Eulerian (paper: %s, %s)" % (n, "{:,}".format(C["syncsc"]), "{:,}".format(C["eul"]),
                                          "{:,}".format(autos), "{:,}".format(eul)))
    row(C["rows_syncsc"] == rows == autos * (2 ** n - 2) * (n - 1),
        "Appendix D, n=%d: %s subset-length rows = automata x (2^n-2) x (n-1) (paper: %s)"
        % (n, "{:,}".format(C["rows_syncsc"]), "{:,}".format(rows)))
    row(C["memonly_rows_syncsc"] == memonly,
        "Appendix D, n=%d: membership certifies %s rows the (Q-CERT+) threshold misses (paper: %s of %s)"
        % (n, "{:,}".format(C["memonly_rows_syncsc"]), "{:,}".format(memonly), "{:,}".format(rows)))
    row(got_share_txt == share,
        "Appendix D, n=%d: share %.4f percent, printed %s (paper: %s percent)"
        % (n, got_share, got_share_txt, share))
    vals = sorted(attainable(4, 3, 3))
    row(vals == [3, 5, 9],
        "Appendix D: k^t=4, |S|=3, -sigma_t(S)=3: second moments attainable with every x_u<=0 = %s "
        "(paper: 3, 5 and 9)" % vals)
    q_, r_ = divmod(3, 3)
    thr = q_ * 3 * 3 + r_ * r_
    below = max(v for v in vals if v < thr)
    row(thr == 9 and 7 not in vals and thr - below == 4 == 2 * (3 - 1),
        "Appendix D: there the (Q-CERT+) threshold is %d, the observation 7 is not attainable, and the "
        "largest attainable value below the threshold falls short by %d-%d = %d = 2(|S|-1) "
        "(paper: 9-5=4=2(|S|-1))" % (thr, thr, below, thr - below))
    failed = checks.count(False)
    print("%d rows, %d FAILED" % (len(checks), failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
