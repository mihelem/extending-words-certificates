"""ternary.py -- the ternary populations at n=4 and n=5, with the binary n=4
population for comparison: Theorem 1, the Eulerian fibre, stuck subsets, attainment
of n-1, the region C#, (Q-CERT), (Q-CERT+) and the gap census.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 6.2: on the ternary n=4 population the largest value of B on a stuck
    subset is -1; stratified by deviation it runs -1, -2, -6, -4, -50, -68 at
    d = 2, 4, 6, 8, 10, 12, not monotone.
  Section 6.3: 7,724 of the 17,360 proper-subset instances at binary n=4 have
    B < 0; the bound n-1 is attained inside {B >= 0} at every size measured
    (for the two ternary populations: at every subset size).
  Section 6.5: at ternary n=4 the C# gain is 3.06 percent against 3.42 at k=2.
  Appendix A: the ternary n=5 sub-population has 7 x 3,125 x 47 = 1,028,125
    automata, of which 580,893 are synchronizing and strongly connected.
  Appendix A: Theorem 1 was checked with 0 violations on 24,210,616 automata,
    23,234,424 of them binary, the rest being the exhaustive ternary n=4
    population and the ternary n=5 sub-population; no never-extendable subset
    occurs on these strongly connected populations.
  Appendix A: {beta* = 0} coincides with the Eulerian locus with no
    disagreement in either direction; the two ternary populations agree.
  Appendix A: the bound n-1 is reached inside {B >= 0} by 11,385 subsets on the
    exhaustive ternary n=4 population and 9,698 on the ternary n=5
    sub-population.
  Appendix A.1: at n=4 and k=3 the multiset convention gives 395,299
    synchronizing strongly connected automata, against 789,358 if the two
    letters after the first are ordered.
  Appendix D: on the exhaustive ternary n=4 population (Q-CERT)'s share of
    {B < 0} moves from 79.29 percent at k=2 to 90.04 at k=3 and (Q-CERT+)'s
    from 82.07 to 90.64, while the C# gain moves from 3.42 to 3.06 (the k=2
    values are the n=4 column of Table D.1: 3.4179, 79.29, 82.07); the gap
    instances number 1,952, 1,157 and 125 at d = 6, 8 and 10, and none lie
    below.

Population / convention (Appendix A and A.1).  Q = {0,...,n-1}; a map f of Q
  is the tuple (f(0),...,f(n-1)), and the n^n maps are ordered
  lexicographically (a map's position is its code).  A class representative is
  the lexicographically least map of a conjugacy class of maps (f ~ p f p^-1).
  binary n=4:   a over the 19 class representatives, b over all 256 maps;
                4,864 automata.
  ternary n=4:  a over the 19 class representatives, b and c over all 256
                maps.  Multiset convention: code(b) <= code(c), 625,024
                automata; ordered convention: every (b, c), 1,245,184.  Shares
                are shares of the multiset enumeration.
  ternary n=5 sub-population: a over one permutation of each of the 7 cycle
                types (cycles (0 1 ... c1-1)(c1 ... c1+c2-1)... on consecutive
                states, c1 >= c2 >= ...), b over all 3,125 maps, c over the 47
                class representatives; 1,028,125 automata.
  Each population is filtered to the synchronizing strongly connected automata.
  Every statistic is counted in proper-subset instances (automaton, S), S a
  proper nonempty subset.

Definitions (Sections 2, 3, 6.5, 6.6, Appendix D).  indeg_t = 1^T M^t;
  sigma_t(S) = indeg_t(S) - k^t |S|; beta*_q = sum_{t<=n-1} k^(n-1-t)
  (indeg_t(q) - k^t); B(S) = sum_{q in S} beta*_q; minext(S) = least |u| with
  |S u^-1| > |S|; S is stuck if minext(S) > n-1.  A subset with B(S) < 0 is
  removed by C# if sigma_t(S) > 0 for some t <= n-1, by (Q-CERT) if
  sum_{|u|=t} x_u^2 > |S| (-sigma_t(S)) for some t <= n-1 and by (Q-CERT+) if
  sum_{|u|=t} x_u^2 > q|S|^2 + r^2 for some t <= n-1, where x_u = |S u^-1| - |S|
  and -sigma_t(S) = q|S| + r, 0 <= r < |S|; the shares are shares of the
  subsets with B < 0.  A gap instance is an (automaton, S, t) with
  minext(S) <= t <= n-1 such that no word of length exactly t extends S.

Usage:    python ternary.py [--procs P] [--populations binary4,ternary4,ternary5]
          (default: all three populations in one process)
Output:   population sizes and per-deviation tables, then one [PASS]/[FAIL] row
          per statement with the computed numbers next to the paper's, ending
          "N rows, M FAILED"; exit status = number of failed rows.
Runtime:  measured on a shared 8-core machine: 7.7 minutes in one process
          (ternary n=4 4.1, ternary n=5 3.6, binary n=4 under a second) and
          3 minutes with --procs 2 (1.6 and 1.4).
Requires: Python 3 (run with 3.10), standard library only.
"""

import argparse
import itertools
import sys
import time
from multiprocessing import get_context


# ---------------------------------------------------------------------------
# Maps, subsets and lookup tables


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


def cycle_type_permutations(n):
    """One permutation of each cycle type: for the partition c1 + c2 + ... = n
    with c1 >= c2 >= ..., the cycles (0 1 ... c1-1), (c1 ... c1+c2-1), ... on
    consecutive states.  Partitions in reverse lexicographic order; 7 at n=5."""
    def partitions(m, largest):
        if m == 0:
            yield []
            return
        for part in range(min(m, largest), 0, -1):
            for rest in partitions(m - part, part):
                yield [part] + rest

    perms = []
    for parts in partitions(n, n):
        f = [0] * n
        base = 0
        for c in parts:
            for i in range(c):
                f[base + i] = base + (i + 1) % c
            base += c
        perms.append(tuple(f))
    return perms


class Tables:
    """Lookup tables shared by all automata on n states."""

    def __init__(self, n):
        self.n = n
        self.N = 1 << n                          # number of subsets of Q
        self.full = self.N - 1                   # the bitmask of Q
        self.maps = list(itertools.product(range(n), repeat=n))
        self.popcount = [bin(X).count("1") for X in range(self.N)]
        self.square = [c * c for c in self.popcount]
        self.low = [(X & -X).bit_length() - 1 for X in range(self.N)]
        self.rest = [X & (X - 1) for X in range(self.N)]
        # pre[i][X] = X f^-1 = {q : f(q) in X} and img[i][X] = {f(q) : q in X}
        # for the map f of code i
        self.pre = []
        self.img = []
        for f in self.maps:
            fibre = [0] * n
            for q in range(n):
                fibre[f[q]] |= 1 << q
            pre = [0] * self.N
            img = [0] * self.N
            for X in range(1, self.N):
                pre[X] = pre[self.rest[X]] | fibre[self.low[X]]
                img[X] = img[self.rest[X]] | (1 << f[self.low[X]])
            self.pre.append(pre)
            self.img.append(img)
        self.class_reps = [map_code(f, n) for f in class_representatives(n)]
        self.cycle_perms = [map_code(f, n) for f in cycle_type_permutations(n)]

    def subset_sums(self, vec):
        """s[X] = sum of vec[q] over the states q in X, for every subset X."""
        s = [0] * self.N
        rest, low = self.rest, self.low
        for X in range(1, self.N):
            s[X] = s[rest[X]] + vec[low[X]]
        return s


_TABLES = {}


def tables(n):
    if n not in _TABLES:
        _TABLES[n] = Tables(n)
    return _TABLES[n]


# ---------------------------------------------------------------------------
# Filters


def strongly_connected(tab, idx):
    """Every state is reachable from state 0 and reaches state 0."""
    for family in (tab.img, tab.pre):
        steps = [family[i] for i in idx]
        reach = 1
        while True:
            grown = reach
            for step in steps:
                grown |= step[reach]
            if grown == reach:
                break
            reach = grown
        if reach != tab.full:
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


def accepted(tab, idx):
    return strongly_connected(tab, idx) and synchronizing(tab, idx)


# ---------------------------------------------------------------------------
# Per-automaton statistics


def in_degree_rows(letters, n, T):
    """rows[t][q] = indeg_t(q) = (1^T M^t)_q for t = 0..T."""
    rows = [[1] * n]
    for _ in range(T):
        prev = rows[-1]
        nxt = [0] * n
        for f in letters:
            for q in range(n):
                nxt[f[q]] += prev[q]
        rows.append(nxt)
    return rows


def minimal_extension(S, pres, popcount):
    """minext(S), by breadth-first search over the sets S u^-1 (the sets at
    depth t are exactly those with |u| = t); None if no word extends S."""
    size = popcount[S]
    level = [S]
    seen = 1 << S
    t = 0
    while level:
        t += 1
        nxt = []
        for X in level:
            for pre in pres:
                Y = pre[X]
                if popcount[Y] > size:
                    return t
                if not (seen >> Y) & 1:
                    seen |= 1 << Y
                    nxt.append(Y)
        level = nxt
    return None


def word_columns(pres, T):
    """cols[t][S] = the tuple of the sets S u^-1 over all k^t words u of length
    t, one entry per word.  Words grow on the left, S (x u)^-1 = (S u^-1) x^-1,
    so the table of x u is the table of u followed by that of the letter x."""
    level = list(pres)
    cols = [None, list(zip(*level))]
    for _ in range(2, T + 1):
        level = [list(map(pre.__getitem__, U)) for U in level for pre in pres]
        cols.append(list(zip(*level)))
    return cols


def analyse(tab, idx, words):
    """Counts over the proper nonempty subsets of the automaton whose letters
    have the codes idx.  words=True adds the statistics over the words of each
    length t <= n-1: second moments, extension at exact length, (Q-CERT),
    (Q-CERT+) and gaps, together with three internal consistency counts."""
    n, full, PC, SQ = tab.n, tab.full, tab.popcount, tab.square
    k = len(idx)
    T = n - 1
    letters = [tab.maps[i] for i in idx]
    pres = [tab.pre[i] for i in idx]

    rows = in_degree_rows(letters, n, T)
    kt = [k ** t for t in range(T + 1)]
    excess = [[rows[t][q] - kt[t] for q in range(n)] for t in range(T + 1)]
    d = sum(abs(x) for x in excess[1])                    # deviation, w = excess[1]
    beta = [sum(k ** (T - t) * excess[t][q] for t in range(1, T + 1)) for q in range(n)]
    sigma = [None] + [tab.subset_sums(excess[t]) for t in range(1, T + 1)]
    B = tab.subset_sums(beta)
    cols = word_columns(pres, T) if words else None

    n_bge0 = n_violations = n_never = n_stuck = n_attain = 0
    n_hard = n_gain = n_qcert = n_qplus = n_gaps = 0
    bad_identity = bad_minext = bad_sound = 0
    attain_by_size = [0] * n
    max_stuck_B = None
    for S in range(1, full):
        c = PC[S]
        b = B[S]
        me = minimal_extension(S, pres, PC)
        stuck = me is None or me > T
        if me is None:
            n_never += 1
        if stuck:
            n_stuck += 1
            if max_stuck_B is None or b > max_stuck_B:
                max_stuck_B = b
        if b >= 0:
            n_bge0 += 1
            if stuck:
                n_violations += 1                          # Theorem 1 would fail
            elif me == T:
                n_attain += 1
                attain_by_size[c] += 1
        else:
            n_hard += 1
            if any(sigma[t][S] > 0 for t in range(1, T + 1)):
                n_gain += 1                                # in C# but not in {B >= 0}
        if not words:
            continue

        extends = [False] * (T + 1)                        # some word of length exactly t extends S
        fires_q = fires_p = False
        for t in range(1, T + 1):
            col = cols[t][S]
            sizes = list(map(PC.__getitem__, col))
            total = sum(sizes)
            if total - kt[t] * c != sigma[t][S]:           # identity (2)
                bad_identity += 1
            extends[t] = max(sizes) > c
            # sum over u of x_u^2 = sum |S u^-1|^2 - 2|S| sum |S u^-1| + k^t |S|^2
            moment = sum(map(SQ.__getitem__, col)) - 2 * c * total + kt[t] * c * c
            m = -sigma[t][S]
            if m < 0:                                      # sigma_t > 0: both thresholds are negative
                fq = fp = True
            else:
                fq = moment > c * m                        # (Q-CERT)
                q, r = divmod(m, c)
                fp = moment > q * c * c + r * r            # (Q-CERT+)
            if (fq or fp) and (stuck or me > t):
                bad_sound += 1                             # a test fired beyond minext
            fires_q = fires_q or fq
            fires_p = fires_p or fp
        first = next((t for t in range(1, T + 1) if extends[t]), None)
        if first != (None if stuck else me):
            bad_minext += 1
        if not stuck:
            n_gaps += sum(1 for t in range(me + 1, T + 1) if not extends[t])
        if b < 0:
            n_qcert += fires_q
            n_qplus += fires_p

    beta_zero = not any(beta)
    counts = {
        "automata": 1, "subsets": full - 1, ("automata", d): 1,
        "eulerian": int(d == 0), "beta zero": int(beta_zero),
        "eulerian, beta nonzero": int(d == 0 and not beta_zero),
        "beta zero, not eulerian": int(d != 0 and beta_zero),
        "B>=0": n_bge0, "violations": n_violations, "never extendable": n_never,
        "stuck": n_stuck, ("stuck", d): n_stuck, "attain": n_attain,
        "hard": n_hard, ("hard", d): n_hard, "C# gain": n_gain,
    }
    for size in range(1, n):
        counts[("attain, size", size)] = attain_by_size[size]
    if words:
        counts.update({
            "Q-CERT": n_qcert, "Q-CERT+": n_qplus, ("gaps", d): n_gaps,
            "identity mismatches": bad_identity, "minext mismatches": bad_minext,
            "tests firing beyond minext": bad_sound,
        })
    highs = {}
    if max_stuck_B is not None:
        highs = {"max B stuck": max_stuck_B, ("max B stuck", d): max_stuck_B}
    return counts, highs


class Tally:
    """Integer counters (summed) and maxima (kept) under hashable keys."""

    def __init__(self):
        self.count = {}
        self.high = {}

    def add(self, counts, weight=1):
        for key, v in counts.items():
            self.count[key] = self.count.get(key, 0) + weight * v

    def raise_to(self, highs):
        for key, v in highs.items():
            if key not in self.high or v > self.high[key]:
                self.high[key] = v

    def merge(self, other):
        self.add(other.count)
        self.raise_to(other.high)

    def __getitem__(self, key):
        return self.count.get(key, 0)

    def deviations(self):
        return sorted(key[1] for key in self.count if isinstance(key, tuple) and key[0] == "automata")


# ---------------------------------------------------------------------------
# Populations.  A unit fixes the first letters; units are processed in any
# order and their tallies summed.


def unit_binary4(a):
    tab = tables(4)
    out = Tally()
    for b in range(len(tab.maps)):
        idx = (a, b)
        out.add({"candidates": 1})
        if accepted(tab, idx):
            counts, highs = analyse(tab, idx, words=True)
            out.add(counts)
            out.raise_to(highs)
    return out


def unit_ternary4(ab):
    """All c for fixed (a, b).  An automaton with code(c) < code(b) is the
    letter swap of (a, c, b), which is analysed instead: every quantity here is
    invariant under that swap.  The ordered tally counts the accepted triples
    directly, and also receives each analysed automaton with weight 2 (b != c)
    or 1 (b = c)."""
    a, b = ab
    tab = tables(4)
    multiset, ordered = Tally(), Tally()
    for c in range(len(tab.maps)):
        idx = (a, b, c)
        ordered.add({"candidates": 1})
        if c >= b:
            multiset.add({"candidates": 1})
        if not accepted(tab, idx):
            continue
        ordered.add({"automata, counted directly": 1})
        if c < b:
            continue
        counts, highs = analyse(tab, idx, words=True)
        multiset.add(counts)
        multiset.raise_to(highs)
        ordered.add(counts, 1 if c == b else 2)
        if c == b:
            multiset.add({"b=c": 1})
    return multiset, ordered


def unit_ternary5(ab):
    a, b = ab
    tab = tables(5)
    out = Tally()
    for c in tab.class_reps:
        idx = (a, b, c)
        out.add({"candidates": 1})
        if accepted(tab, idx):
            counts, highs = analyse(tab, idx, words=False)
            out.add(counts)
            out.raise_to(highs)
    return out


def sweep(fn, units, procs, chunksize):
    if procs <= 1:
        for unit in units:
            yield fn(unit)
    else:
        with get_context("spawn").Pool(procs) as pool:
            yield from pool.imap_unordered(fn, units, chunksize)


# ---------------------------------------------------------------------------
# Report


def num(x):
    return format(x, ",")


def share(part, whole, digits=2):
    return "%.*f" % (digits, 100.0 * part / whole)


def print_table(title, tally, words):
    print(title)
    head = "  %4s %10s %12s %10s %15s" % ("d", "automata", "B<0 subsets", "stuck", "max B on stuck")
    print(head + ("  %13s" % "gap instances" if words else ""))
    for d in tally.deviations():
        mx = tally.high.get(("max B stuck", d))
        line = "  %4d %10s %12s %10s %15s" % (d, num(tally[("automata", d)]), num(tally[("hard", d)]),
                                            num(tally[("stuck", d)]), "-" if mx is None else mx)
        print(line + ("  %13s" % num(tally[("gaps", d)]) if words else ""))
    print()


def main():
    ap = argparse.ArgumentParser(description="Ternary populations at n=4 and n=5 (see the module docstring).")
    ap.add_argument("--procs", type=int, default=1, help="number of processes (default 1)")
    ap.add_argument("--populations", default="binary4,ternary4,ternary5",
                    help="comma-separated subset of binary4,ternary4,ternary5")
    args = ap.parse_args()
    want = set(args.populations.split(","))
    unknown = want - {"binary4", "ternary4", "ternary5"}
    if unknown:
        ap.error("unknown population(s): " + ", ".join(sorted(unknown)))

    bin4 = tern4 = tern4_ord = tern5 = None
    if "binary4" in want:
        t0 = time.time()
        bin4 = Tally()
        for part in sweep(unit_binary4, tables(4).class_reps, 1, 1):
            bin4.merge(part)
        print("binary n=4 done in %.1f s" % (time.time() - t0), file=sys.stderr)
    if "ternary4" in want:
        t0 = time.time()
        tern4, tern4_ord = Tally(), Tally()
        units = [(a, b) for a in tables(4).class_reps for b in range(4 ** 4)]
        for m, o in sweep(unit_ternary4, units, args.procs, 8):
            tern4.merge(m)
            tern4_ord.merge(o)
        print("ternary n=4 done in %.1f s" % (time.time() - t0), file=sys.stderr)
    if "ternary5" in want:
        t0 = time.time()
        tern5 = Tally()
        units = [(a, b) for a in tables(5).cycle_perms for b in range(5 ** 5)]
        for part in sweep(unit_ternary5, units, args.procs, 32):
            tern5.merge(part)
        print("ternary n=5 done in %.1f s" % (time.time() - t0), file=sys.stderr)

    # -- populations and per-deviation tables
    if bin4:
        print("binary n=4, k=2: %s automata, %s synchronizing and strongly connected (%s Eulerian), "
              "%s proper nonempty subsets" % (num(bin4["candidates"]), num(bin4["automata"]),
                                               num(bin4["eulerian"]), num(bin4["subsets"])))
    if tern4:
        print("ternary n=4, k=3, multiset {b,c}: %s automata, %s synchronizing and strongly connected "
              "(%s Eulerian), %s proper nonempty subsets" % (num(tern4["candidates"]), num(tern4["automata"]),
                                                            num(tern4["eulerian"]), num(tern4["subsets"])))
        print("ternary n=4, k=3, ordered (b,c):  %s automata, %s synchronizing and strongly connected "
              "(%s Eulerian), %s proper nonempty subsets" % (num(tern4_ord["candidates"]),
                                                            num(tern4_ord["automata, counted directly"]),
                                                            num(tern4_ord["eulerian"]), num(tern4_ord["subsets"])))
    if tern5:
        print("ternary n=5 sub-population, k=3: %s automata, %s synchronizing and strongly connected "
              "(%s Eulerian), %s proper nonempty subsets" % (num(tern5["candidates"]), num(tern5["automata"]),
                                                            num(tern5["eulerian"]), num(tern5["subsets"])))
    print()
    if tern4:
        print_table("ternary n=4, multiset convention, by deviation d:", tern4, True)
    if tern5:
        print_table("ternary n=5 sub-population, by deviation d:", tern5, False)

    # -- the statements
    results = []

    def row(ok, text):
        results.append(ok)
        print("[%s] %s" % ("PASS" if ok else "FAIL", text))

    if bin4:
        row(bin4["candidates"] == 4864 and bin4["automata"] == 1240 and bin4["eulerian"] == 72,
            "Appendix A: binary n=4: %s synchronizing strongly connected automata of %s, %s of them Eulerian "
            "(paper: 1,240 and 72)" % (num(bin4["automata"]), num(bin4["candidates"]), num(bin4["eulerian"])))
    if tern4:
        mult, ordd, same = tern4["automata"], tern4_ord["automata, counted directly"], tern4["b=c"]
        row(tern4["candidates"] == 625024 and tern4_ord["candidates"] == 1245184 and mult == 395299
            and ordd == 789358 and 2 * mult == ordd + same,
            "Appendix A.1: ternary n=4: %s automata in the multiset convention against %s with the two letters "
            "after the first ordered (paper: 395,299 against 789,358); %s have b = c, and (%s + %s)/2 = %s"
            % (num(mult), num(ordd), num(same), num(ordd), num(same), num((ordd + same) // 2)))
    if tern5:
        row(tern5["candidates"] == 1028125 and tern5["automata"] == 580893,
            "Appendix A: ternary n=5 sub-population: %s automata, %s synchronizing and strongly connected "
            "(paper: 1,028,125 and 580,893)" % (num(tern5["candidates"]), num(tern5["automata"])))
    for name, tally, n in (("ternary n=4 (multiset)", tern4, 4), ("ternary n=5 sub-population", tern5, 5)):
        if tally:
            row(tally["violations"] == 0 and tally["B>=0"] > 0 and tally["stuck"] > 0,
                "Appendix A: Theorem 1 on %s: %s subsets with B(S) >= 0 and minext(S) > %d (paper: 0), among "
                "%s subsets with B >= 0; the %s stuck subsets all have B < 0"
                % (name, num(tally["violations"]), n - 1, num(tally["B>=0"]), num(tally["stuck"])))
    if tern4 and tern5:
        ternary_total = tern4["automata"] + tern5["automata"]
        row(ternary_total == 24210616 - 23234424,
            "Appendix A: the ternary part of the Theorem 1 sweep: %s + %s = %s = 24,210,616 - 23,234,424"
            % (num(tern4["automata"]), num(tern5["automata"]), num(ternary_total)))
    for name, tally in (("ternary n=4 (multiset)", tern4), ("ternary n=5 sub-population", tern5)):
        if tally:
            row(tally["never extendable"] == 0,
                "Appendix A: %s: %s never-extendable subsets among %s (paper: none)"
                % (name, num(tally["never extendable"]), num(tally["subsets"])))
    for name, tally in (("ternary n=4 (multiset)", tern4), ("ternary n=5 sub-population", tern5)):
        if tally:
            ok = (tally["eulerian, beta nonzero"] == 0 and tally["beta zero, not eulerian"] == 0
                  and tally["eulerian"] > 0 and tally["beta zero"] == tally["eulerian"])
            extra = " (ordered convention: %s)" % num(tern4_ord["eulerian"]) if tally is tern4 else ""
            row(ok, "Appendix A: beta* = 0 exactly on the Eulerian automata, %s: %s Eulerian%s, %s with beta* = 0; "
                    "%s Eulerian with beta* != 0 and %s non-Eulerian with beta* = 0 (paper: no disagreement in "
                    "either direction)" % (name, num(tally["eulerian"]), extra, num(tally["beta zero"]),
                                           num(tally["eulerian, beta nonzero"]),
                                           num(tally["beta zero, not eulerian"])))
    if tern4:
        row(tern4.high.get("max B stuck") == -1,
            "Section 6.2: ternary n=4 (multiset): the largest B on a stuck subset is %s over the %s stuck subsets "
            "(paper: -1)" % (tern4.high.get("max B stuck"), num(tern4["stuck"])))
        paper = {2: -1, 4: -2, 6: -6, 8: -4, 10: -50, 12: -68}
        got = {key[1]: v for key, v in tern4.high.items() if isinstance(key, tuple)}
        series = [got[d] for d in sorted(got)]
        monotone = all(x >= y for x, y in zip(series, series[1:])) or all(x <= y for x, y in zip(series, series[1:]))
        row(got == paper and not monotone,
            "Section 6.2: ternary n=4: largest B on a stuck subset by deviation: %s; %s (paper: -1, -2, -6, -4, "
            "-50, -68 at d = 2, 4, 6, 8, 10, 12, not monotone)"
            % (", ".join("d=%d: %d" % (d, got[d]) for d in sorted(got)), "monotone" if monotone else "not monotone"))
        sizes = [tern4[("attain, size", c)] for c in range(1, 4)]
        row(tern4["attain"] == 11385 and all(sizes),
            "Appendix A and Section 6.3: ternary n=4: %s subsets with B >= 0 and minext = n-1 = 3 in the multiset "
            "convention (paper: 11,385), at every subset size: %s at |S| = 1, 2, 3; %s in the ordered convention"
            % (num(tern4["attain"]), ", ".join(num(x) for x in sizes), num(tern4_ord["attain"])))
    if tern5:
        sizes = [tern5[("attain, size", c)] for c in range(1, 5)]
        row(tern5["attain"] == 9698 and all(sizes),
            "Appendix A and Section 6.3: ternary n=5 sub-population: %s subsets with B >= 0 and minext = n-1 = 4 "
            "(paper: 9,698), at every subset size: %s at |S| = 1, 2, 3, 4"
            % (num(tern5["attain"]), ", ".join(num(x) for x in sizes)))
    if bin4:
        gain4 = share(bin4["C# gain"], bin4["hard"], 4)
        qcert, qplus = share(bin4["Q-CERT"], bin4["hard"]), share(bin4["Q-CERT+"], bin4["hard"])
        row(bin4["hard"] == 7724 and bin4["subsets"] == 17360 and (gain4, qcert, qplus) == ("3.4179", "79.29", "82.07"),
            "Section 6.3 and Table D.1: binary n=4: %s of the %s subsets have B < 0 (paper: 7,724 of 17,360); removed "
            "by C# %s (%s percent), by (Q-CERT) %s (%s), by (Q-CERT+) %s (%s) (paper: 3.4179, 79.29, 82.07)"
            % (num(bin4["hard"]), num(bin4["subsets"]), num(bin4["C# gain"]), gain4,
               num(bin4["Q-CERT"]), qcert, num(bin4["Q-CERT+"]), qplus))
    if tern4 and bin4:
        for label, key, paper3, paper2 in (("C# gain", "C# gain", "3.06", "3.42"),
                                           ("removed by (Q-CERT)", "Q-CERT", "90.04", "79.29"),
                                           ("removed by (Q-CERT+)", "Q-CERT+", "90.64", "82.07")):
            s3, s2 = share(tern4[key], tern4["hard"]), share(bin4[key], bin4["hard"])
            where = "Section 6.5 and Appendix D" if key == "C# gain" else "Appendix D"
            row(s3 == paper3 and s2 == paper2,
                "%s: n=4, %s: %s of the %s subsets with B < 0 at k=3 (ternary, multiset), %s percent, against %s of "
                "%s at k=2, %s percent (paper: %s against %s)"
                % (where, label, num(tern4[key]), num(tern4["hard"]), s3, num(bin4[key]), num(bin4["hard"]), s2,
                   paper3, paper2))
    if tern4:
        gaps = {d: tern4[("gaps", d)] for d in tern4.deviations()}
        paper = {6: 1952, 8: 1157, 10: 125}
        ok = all(gaps.get(d, 0) == v for d, v in paper.items()) and all(gaps[d] == 0 for d in gaps if d < 6)
        row(ok, "Appendix D: ternary n=4 (multiset): gap instances (automaton, S, t) by deviation: %s; %s in all "
                "(paper: 1,952, 1,157 and 125 at d = 6, 8 and 10, none below)"
            % (", ".join("d=%d: %s" % (d, num(v)) for d, v in sorted(gaps.items())), num(sum(gaps.values()))))
    checks = [t for t in (bin4, tern4) if t]           # every analysed automaton once
    if checks:
        bad = sum(t["identity mismatches"] + t["minext mismatches"] + t["tests firing beyond minext"] for t in checks)
        consistent = not tern4 or tern4_ord["automata"] == tern4_ord["automata, counted directly"]
        row(bad == 0 and consistent,
            "internal consistency (n=4 populations): %d mismatches of identity (2) between in-degrees and words, "
            "%d between minext by search and by word levels, %d firings of (Q-CERT) or (Q-CERT+) at a length t < "
            "minext(S) (so no stuck subset certified)%s"
            % (sum(t["identity mismatches"] for t in checks), sum(t["minext mismatches"] for t in checks),
               sum(t["tests firing beyond minext"] for t in checks),
               "; ordered automata counted directly %s, by weights %s" % (
                   num(tern4_ord["automata, counted directly"]), num(tern4_ord["automata"])) if tern4 else ""))

    failed = results.count(False)
    print("\n%d rows, %d FAILED" % (len(results), failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main())
