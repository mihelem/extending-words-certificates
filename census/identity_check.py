"""identity_check.py -- identity (2), sigma_t(S) = sum over |u| = t of
(|S u^-1| - |S|), checked against direct enumeration of the words, for every
automaton, every proper nonempty subset S and every length t = 1, ..., n-1.

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: identity (2) was verified against direct enumeration of every
    word of Sigma^{<=n-1} applied letter by letter, with no matrix algebra,
    with 0 disagreements in the 977,640 proper-subset instances of the
    exhaustive binary n=5 population and 0 again at k=3.

Population / convention (Appendix A.1).  Q = {0,...,n-1}; a map f of Q is the
  tuple (f(0),...,f(n-1)), and the n^n maps are ordered lexicographically (a
  map's position is its code).  A class representative is the
  lexicographically least map of a conjugacy class of maps (f ~ p f p^-1).
  binary n=5:  first letter over the 47 class representatives, second letter
               over all 3,125 maps (146,875 automata); the 32,588 synchronizing
               strongly connected ones, 30 proper nonempty subsets each, give
               977,640 instances.
  ternary n=4 (k=3): first letter over the 19 class representatives, the other
               two over all 256 maps; the synchronizing strongly connected
               automata number 395,299 in the multiset convention
               (code(b) <= code(c); 5,534,186 instances) and 789,358 in the
               ordered convention (11,051,012 instances).
  An instance is a pair (automaton, S); each is compared at every t <= n-1.

Method.  Left side: indeg_t = 1^T M^t by t products with M, summed over S,
  minus k^t |S|.  Right side: the action q -> q.u of every word u of length t
  is built letter by letter, q.(u x) = (q.u).x; S u^-1 is the set of states q
  with q.u in S; |S u^-1| - |S| is summed over the k^t words.  The right side
  uses neither M nor in-degrees.  As a control of the comparison itself, the
  left side at length t is also compared with the right side at length t-1,
  where disagreements must appear.

Usage:    python identity_check.py [--procs P] [--populations binary5,ternary4]
          (default: both populations in one process)
Output:   population sizes, then one [PASS]/[FAIL] row per population,
          convention and length t (instances compared, disagreements, and the
          instances with sigma_t(S) != 0, so that the comparison is not void),
          and one row per population and convention counting the instances
          that disagree at some t; ending "N rows, M FAILED"; exit status =
          number of failed rows.
Runtime:  measured on a shared 8-core machine: 9 minutes in one process
          (binary n=5 half a minute, ternary n=4 in both conventions 8.5
          minutes) and 4.2 minutes with --procs 2 (12 seconds and 4 minutes).
Requires: Python 3 (run with 3.10), standard library only.
"""

import argparse
import itertools
import sys
import time
from multiprocessing import get_context


def map_code(f, n):
    """Position of the map f in the lexicographic list of all n^n maps."""
    code = 0
    for v in f:
        code = code * n + v
    return code


def class_representatives(n):
    """The lexicographically least map of each conjugacy class of maps of Q
    (f ~ p f p^-1 for permutations p), in increasing order: 19 at n=4, 47 at
    n=5."""
    perms = list(itertools.permutations(range(n)))
    inverses = []
    for p in perms:
        inv = [0] * n
        for i, v in enumerate(p):
            inv[v] = i
        inverses.append(inv)
    seen = set()
    reps = []
    for f in itertools.product(range(n), repeat=n):
        if f in seen:
            continue
        orbit = {tuple(p[f[pinv[q]]] for q in range(n)) for p, pinv in zip(perms, inverses)}
        seen |= orbit
        reps.append(min(orbit))
    return reps


class Tables:
    """Lookup tables shared by all automata on n states."""

    def __init__(self, n):
        self.n = n
        self.N = 1 << n                          # number of subsets of Q
        self.full = self.N - 1                   # the bitmask of Q
        self.maps = list(itertools.product(range(n), repeat=n))
        self.popcount = [bin(X).count("1") for X in range(self.N)]
        self.low = [(X & -X).bit_length() - 1 for X in range(self.N)]
        self.rest = [X & (X - 1) for X in range(self.N)]
        # img[i][X] = {f(q) : q in X} for the map f of code i (synchronization filter only)
        self.img = []
        for f in self.maps:
            img = [0] * self.N
            for X in range(1, self.N):
                img[X] = img[self.rest[X]] | (1 << f[self.low[X]])
            self.img.append(img)
        self.class_reps = [map_code(f, n) for f in class_representatives(n)]


_TABLES = {}


def tables(n):
    if n not in _TABLES:
        _TABLES[n] = Tables(n)
    return _TABLES[n]


def strongly_connected(letters, n):
    """Every state is reachable from state 0 and reaches state 0."""
    full = (1 << n) - 1
    forward = [0] * n
    backward = [0] * n
    for f in letters:
        for q in range(n):
            forward[q] |= 1 << f[q]
            backward[f[q]] |= 1 << q
    for adjacency in (forward, backward):
        reach = frontier = 1
        while frontier:
            grown = 0
            for q in range(n):
                if (frontier >> q) & 1:
                    grown |= adjacency[q]
            frontier = grown & ~reach
            reach |= grown
        if reach != full:
            return False
    return True


def synchronizing(tab, idx):
    """Some word maps Q onto one state: depth-first search over the images Q.u."""
    imgs = [tab.img[i] for i in idx]
    seen = 1 << tab.full
    stack = [tab.full]
    while stack:
        X = stack.pop()
        for img in imgs:
            Y = img[X]
            if Y & (Y - 1) == 0:
                return True
            if not (seen >> Y) & 1:
                seen |= 1 << Y
                stack.append(Y)
    return False


def sigma_from_in_degrees(letters, tab, T):
    """sig[t][S] = indeg_t(S) - k^t |S| with indeg_t = 1^T M^t, t = 1..T."""
    n, k = tab.n, len(letters)
    v = [1] * n
    sig = [None]
    for t in range(1, T + 1):
        nxt = [0] * n                            # v <- v M
        for f in letters:
            for q in range(n):
                nxt[f[q]] += v[q]
        v = nxt
        indeg = [0] * tab.N                      # indeg_t(S) for every subset S
        for X in range(1, tab.N):
            indeg[X] = indeg[tab.rest[X]] + v[tab.low[X]]
        sig.append([indeg[X] - k ** t * tab.popcount[X] for X in range(tab.N)])
    return sig


def sigma_from_words(letters, tab, T):
    """sig[t][S] = sum over all words u of length t of (|S u^-1| - |S|),
    t = 1..T.  Words of length t are the words of length t-1 followed by one
    letter, and each word's action on the states is built from its prefix's
    action by applying that letter."""
    n, N, PC = tab.n, tab.N, tab.popcount
    rest, low = tab.rest, tab.low
    actions = [tuple(range(n))]                  # the action of the empty word
    sig = [None]
    for t in range(1, T + 1):
        actions = [tuple(f[p] for p in phi) for phi in actions for f in letters]
        total = [0] * N                          # total[S] = sum over u of |S u^-1|
        for phi in actions:
            fibre = [0] * n                      # fibre[r] = {q : q.u = r}
            for q in range(n):
                fibre[phi[q]] |= 1 << q
            pulled = [0] * N                     # pulled[S] = S u^-1 = {q : q.u in S}
            for X in range(1, N):
                pulled[X] = pulled[rest[X]] | fibre[low[X]]
                total[X] += PC[pulled[X]]
        sig.append([total[X] - len(actions) * PC[X] for X in range(N)])
    return sig


def check_unit(unit):
    """unit = (population, a, b_start, b_stop): every automaton of the
    population whose first letter has code a and second letter a code in
    [b_start, b_stop)."""
    population, a, b_start, b_stop = unit
    out = {}

    def add(key, v=1):
        out[key] = out.get(key, 0) + v

    if population == "binary5":
        tab = tables(5)
        automata = [(a, b) for b in range(b_start, b_stop)]
    else:
        tab = tables(4)
        automata = [(a, b, c) for b in range(b_start, b_stop) for c in range(len(tab.maps))]
    n, full = tab.n, tab.full
    T = n - 1
    for idx in automata:
        if population == "binary5":
            conventions = ["binary5"]
        else:
            conventions = ["ordered", "multiset"] if idx[2] >= idx[1] else ["ordered"]
        for conv in conventions:
            add((conv, "candidates"))
        letters = [tab.maps[i] for i in idx]
        if not (strongly_connected(letters, n) and synchronizing(tab, idx)):
            continue
        k = len(letters)
        indeg = [0] * n
        for f in letters:
            for q in range(n):
                indeg[f[q]] += 1
        d = sum(abs(x - k) for x in indeg)
        left = sigma_from_in_degrees(letters, tab, T)
        right = sigma_from_words(letters, tab, T)
        record = {("automata", d): 1, "automata": 1, "instances": full - 1}
        record["instances disagreeing"] = sum(
            1 for S in range(1, full) if any(left[t][S] != right[t][S] for t in range(1, T + 1)))
        for t in range(1, T + 1):
            record[("disagreements", t)] = sum(1 for S in range(1, full) if left[t][S] != right[t][S])
            record[("sigma nonzero", t)] = sum(1 for S in range(1, full) if left[t][S] != 0)
            if t >= 2:
                record[("control disagreements", t)] = sum(1 for S in range(1, full) if left[t][S] != right[t - 1][S])
        for conv in conventions:
            for key, v in record.items():
                add((conv,) + (key if isinstance(key, tuple) else (key,)), v)
    return out


def num(x):
    return format(x, ",")


def main():
    ap = argparse.ArgumentParser(description="Identity (2) against word enumeration (see the module docstring).")
    ap.add_argument("--procs", type=int, default=1, help="number of processes (default 1)")
    ap.add_argument("--populations", default="binary5,ternary4", help="comma-separated subset of binary5,ternary4")
    args = ap.parse_args()
    want = set(args.populations.split(","))
    unknown = want - {"binary5", "ternary4"}
    if unknown:
        ap.error("unknown population(s): " + ", ".join(sorted(unknown)))

    total = {}
    for population, n, step in (("binary5", 5, 125), ("ternary4", 4, 1)):
        if population not in want:
            continue
        t0 = time.time()
        units = [(population, a, b, min(b + step, n ** n))
                 for a in tables(n).class_reps for b in range(0, n ** n, step)]
        if args.procs <= 1:
            parts = map(check_unit, units)
            pool = None
        else:
            pool = get_context("spawn").Pool(args.procs)
            parts = pool.imap_unordered(check_unit, units, 4)
        for part in parts:
            for key, v in part.items():
                total[key] = total.get(key, 0) + v
        if pool is not None:
            pool.close()
            pool.join()
        print("%s done in %.1f s" % (population, time.time() - t0), file=sys.stderr)

    def get(*key):
        return total.get(key, 0)

    results = []

    def row(ok, text):
        results.append(ok)
        print("[%s] %s" % ("PASS" if ok else "FAIL", text))

    layout = []
    if "binary5" in want:
        layout.append(("binary5", "binary n=5", 4, 32588, 977640))
        strata = sorted(key[2] for key in total if key[0] == "binary5" and key[1] == "automata" and len(key) == 3)
        print("binary n=5, k=2: %s automata, %s synchronizing and strongly connected; by deviation %s"
              % (num(get("binary5", "candidates")), num(get("binary5", "automata")),
                 ", ".join("d=%d: %s" % (d, num(get("binary5", "automata", d))) for d in strata)))
    if "ternary4" in want:
        layout.append(("multiset", "ternary n=4, multiset convention", 3, 395299, 5534186))
        layout.append(("ordered", "ternary n=4, ordered convention", 3, 789358, 11051012))
        for conv in ("multiset", "ordered"):
            print("ternary n=4, k=3, %s convention: %s automata, %s synchronizing and strongly connected"
                  % (conv, num(get(conv, "candidates")), num(get(conv, "automata"))))
    print()
    for conv, name, T, automata, instances in layout:
        row(get(conv, "automata") == automata and get(conv, "instances") == instances,
            "Appendix A: %s: %s synchronizing strongly connected automata, %s proper-subset instances "
            "(expected %s and %s)" % (name, num(get(conv, "automata")), num(get(conv, "instances")),
                                      num(automata), num(instances)))
        for t in range(1, T + 1):
            row(get(conv, "disagreements", t) == 0 and get(conv, "sigma nonzero", t) > 0
                and get(conv, "instances") == instances,
                "Appendix A: %s, t=%d: identity (2) compared on %s instances: %s disagreements; sigma_%d(S) != 0 on "
                "%s of them" % (name, t, num(get(conv, "instances")), num(get(conv, "disagreements", t)), t,
                                num(get(conv, "sigma nonzero", t))))
        controls = [get(conv, "control disagreements", t) for t in range(2, T + 1)]
        row(get(conv, "instances disagreeing") == 0 and get(conv, "instances") == instances and all(controls),
            "Appendix A: %s: %s of the %s proper-subset instances disagree at some t <= %d (paper: 0); control, "
            "left side at t against right side at t-1: %s disagreements at t = %s"
            % (name, num(get(conv, "instances disagreeing")), num(get(conv, "instances")), T,
               ", ".join(num(c) for c in controls), ", ".join(str(t) for t in range(2, T + 1))))

    failed = results.count(False)
    print("\n%d rows, %d FAILED" % (len(results), failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main())
