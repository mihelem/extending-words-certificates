"""tables.py -- check the paper's second-moment and void-share numbers against census_engine's JSON files

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: the population sizes 59 (8 Eulerian), 1,240 (72 Eulerian),
    32,588, 1,122,529, 811, 260,461; the ternary n=4 population, 789,358 with
    the letters after the first ordered and 395,299 as multisets; the ternary
    {d<=2} strata 249,605 and 37,946,778; the eleven populations of Section 6.6.
  Section 4.1 and Table A.1 (Appendix A.2): the seven cells (non-Eulerian
    automata; those with no proper nonempty subset having all sigma_t = 0; the
    fraction), the range 55.3 to 93.3 percent, not monotone in n.
  Appendix A.1: the same fractions in both conventions (93.28/93.16,
    55.31/54.27, 70.59/68.75, 79.02/76.54) and "the shift is under 2.5 points at
    every cell computed".
  Section 6.3: {B<0}: 138 of 354, 7,724 of 17,360, 463,047 of
    977,640, 33,481,397 of 69,596,798; 39.0, 44.5, 47.4, 48.1 percent.
  Section 6.4 (n=5): 314,393; 12,064; 12,644 (T=2) and 29,396 (T=4); the boundary
    half 402, 2,428, 8,528 at n=4, 5, 6.
  Section 6.5 and Table D.1: C# shrinks {B<0} by 0.0000, 3.4179, 5.7934,
    1.8838, 9.0504, 3.6524, 4.8300 percent; 3.4, 5.8, 9.1 at n=4, 5, 6; gain 0 on
    the 59 automata at n=3; 3.42 at binary n=4.
  Section 6.6 and Table D.1: (Q-CERT) 60.14 ... 89.79 and (Q-CERT+) 60.14 ...
    91.23 percent of {B<0}; the ranges 60.14-90.03 and 60.14-91.44
    against at most 9.05 for C#; 0 stuck subsets certified on all eleven
    populations; the largest firing length per subset size is n-1 for sigma_t>0,
    (Q-CERT) and (Q-CERT+), as is the largest minext <= n-1.
  Appendix D: (Q-CERT) removes between 9.94 and 44.30 times as much of the hard
    core as C# where the C# share is nonzero; on the binary sweeps the gap is
    empty on every {d<=2} population and every instance found lies at d>=4.
Population / convention: the eleven JSON files of run_populations.py (see
  census_engine.c).  Every share is computed exactly from the quotient
  integers ([0]; [1] is labelled) and rounded half up to the paper's number of
  decimals.  The ternary files count the two letters after the first as ORDERED
  pairs, while Appendix A.1 counts them as multisets; for automaton counts
  multiset = (ordered + diagonal)/2, the diagonal being the automata with c = b,
  which this program enumerates itself (a few seconds): the diagonal equals the
  binary population only when there is no deviation filter, since (a,b,b) at
  k=3 and (a,b) at k=2 have different deviations.
Usage:    python tables.py DIR
          DIR holds n3_all.json n4_all.json n5_all.json n6_all.json n4_d2.json
          n5_d2.json n6_d2.json n7_d2.json n4k3_all.json n4k3_d2.json
          n5k3_d2.json, as written by python run_populations.py ./census_engine DIR
Output:   one [PASS]/[FAIL] row per checked statement (paper location, the
          engine fields used, the computed and the paper's values), a NOTE line
          pointing to the program that checks the k=3 multiset shares, and
          "R rows, F FAILED"; exit status F (at most 255).  A missing input
          file fails the rows that need it.
Runtime:  about 2 s (one core), after the engine runs.
Requires: Python 3.6 or later (standard library only).
"""
import itertools
import json
import math
import os
import sys
from fractions import Fraction

# name, n, k, dmax (-1: every deviation), label
POPS = [
    ("n3_all", 3, 2, -1, "n=3 all d"),
    ("n4_all", 4, 2, -1, "n=4 all d"),
    ("n5_all", 5, 2, -1, "n=5 all d"),
    ("n6_all", 6, 2, -1, "n=6 all d"),
    ("n4_d2", 4, 2, 2, "n=4 d<=2"),
    ("n5_d2", 5, 2, 2, "n=5 d<=2"),
    ("n6_d2", 6, 2, 2, "n=6 d<=2"),
    ("n7_d2", 7, 2, 2, "n=7 d<=2"),
    ("n4k3_all", 4, 3, -1, "k=3 n=4 all d"),
    ("n4k3_d2", 4, 3, 2, "k=3 n=4 d<=2"),
    ("n5k3_d2", 5, 3, 2, "k=3 n=5 d<=2"),
]
META = {p[0]: p for p in POPS}
LABEL = {p[0]: p[4] for p in POPS}

# column order of Tables A.1 and D.1
CELLS = ["n3_all", "n4_all", "n5_all", "n5_d2", "n6_all", "n6_d2", "n7_d2"]

# Table A.1: non-Eulerian automata, those with no proper nonempty subset having all sigma_t = 0, fraction
TABLE_A1 = {
    "n3_all": (51, 36, "70.6"),
    "n4_all": (1168, 923, "79.0"),
    "n5_all": (31634, 29508, "93.3"),
    "n5_d2": (12509, 11104, "88.8"),
    "n6_all": (1110301, 719484, "64.8"),
    "n6_d2": (248233, 137301, "55.3"),
    "n7_d2": (4873053, 4359891, "89.5"),
}
# Appendix A.1: emptiness fraction, quotient against labelled, and the shift in points
A1_PAIRS = [
    ("n5_all", "93.28", "93.16", "0.12"),
    ("n6_d2", "55.31", "54.27", "1.04"),
    ("n3_all", "70.59", "68.75", "1.84"),
    ("n4_all", "79.02", "76.54", "2.49"),
]
# Section 6.3: {B<0} among the proper-subset instances
HARD_CORE = [
    ("n3_all", 138, 354, "39.0"),
    ("n4_all", 7724, 17360, "44.5"),
    ("n5_all", 463047, 977640, "47.4"),
    ("n6_all", 33481397, 69596798, "48.1"),
]
# Table D.1: C#, (Q-CERT), (Q-CERT+)
TABLE_D1 = {
    "n3_all": ("0.0000", "60.14", "60.14"),
    "n4_all": ("3.4179", "79.29", "82.07"),
    "n5_all": ("5.7934", "86.83", "88.98"),
    "n5_d2": ("1.8838", "83.44", "86.33"),
    "n6_all": ("9.0504", "90.03", "91.44"),
    "n6_d2": ("3.6524", "86.74", "88.80"),
    "n7_d2": ("4.8300", "89.79", "91.23"),
}

ROWS = []            # True/False per checked row
DATA = {}            # name -> parsed JSON or None


# ------------------------------------------------------------------ helpers
def fmt(q, places):
    """the nonnegative rational q rounded half up to `places` decimals"""
    r = math.floor(q * 10 ** places + Fraction(1, 2))
    if places == 0:
        return str(r)
    s = str(r).rjust(places + 1, "0")
    return s[:-places] + "." + s[-places:]


def share(num, den):
    return Fraction(100 * num, den)


def c(x):
    return "{:,}".format(x)


def q(name, field, conv=0):
    return DATA[name]["acc"][field][conv]


def row(needs, check):
    """needs: population names; check: function returning (ok, text)"""
    missing = [nm for nm in needs if DATA.get(nm) is None]
    if missing:
        ok, text = False, "missing input %s" % ", ".join(nm + ".json" for nm in missing)
    else:
        ok, text = check()
    ROWS.append(bool(ok))
    print("[%s] %s" % ("PASS" if ok else "FAIL", text))


def note(text):
    print("       NOTE: " + text)


def section(title):
    print("")
    print("-- " + title)


def load(directory):
    for name, n, k, dmax, _ in POPS:
        path = os.path.join(directory, name + ".json")
        if not os.path.exists(path):
            DATA[name] = None
            continue
        with open(path) as fh:
            d = json.load(fh)
        want_dmax = None if dmax < 0 else dmax
        if (d.get("n"), d.get("k"), d.get("dmax")) != (n, k, want_dmax):
            sys.exit("%s: n, k, dmax = %s, %s, %s; expected %s, %s, %s"
                     % (path, d.get("n"), d.get("k"), d.get("dmax"), n, k, want_dmax))
        DATA[name] = d


# ------------------------------------------- own enumeration of the diagonal
def class_representatives(n):
    """one endofunction of {0..n-1} per conjugacy class under relabelling"""
    perms = list(itertools.permutations(range(n)))
    seen, reps = set(), []
    for f in itertools.product(range(n), repeat=n):
        if f in seen:
            continue
        reps.append(f)
        for p in perms:
            g = [0] * n
            for i in range(n):
                g[p[i]] = p[f[i]]
            seen.add(tuple(g))
    return reps


def is_synchronizing(letters, n):
    """every pair of states is merged by some word (fixpoint from the diagonal)"""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    good = set()
    changed = True
    while changed:
        changed = False
        for x, y in pairs:
            if (x, y) in good:
                continue
            for f in letters:
                u, v = f[x], f[y]
                if u == v or (min(u, v), max(u, v)) in good:
                    good.add((x, y))
                    changed = True
                    break
    return len(good) == len(pairs)


def is_strongly_connected(letters, n):
    fwd = [set(f[s] for f in letters) for s in range(n)]
    bwd = [set() for _ in range(n)]
    for s in range(n):
        for r in fwd[s]:
            bwd[r].add(s)

    def reaches_all(graph):
        seen, stack = {0}, [0]
        while stack:
            for r in graph[stack.pop()]:
                if r not in seen:
                    seen.add(r)
                    stack.append(r)
        return len(seen) == n
    return reaches_all(fwd) and reaches_all(bwd)


def count_pairs(n, copies_of_b, dmax):
    """number of (a, b), a over class representatives and b over all n^n maps,
    whose automaton with letters a, b, ..., b (copies_of_b copies of b) is
    strongly connected, synchronizing and of deviation d <= dmax (dmax < 0: any)"""
    k = 1 + copies_of_b
    count = 0
    for a in class_representatives(n):
        for b in itertools.product(range(n), repeat=n):
            if dmax >= 0:
                indeg = [0] * n
                for s in range(n):
                    indeg[a[s]] += 1
                    indeg[b[s]] += copies_of_b
                if sum(abs(x - k) for x in indeg) > dmax:
                    continue
            if is_strongly_connected((a, b), n) and is_synchronizing((a, b), n):
                count += 1
    return count


# ------------------------------------------------------------------- checks
def check_populations():
    section("Appendix A: populations (field autos; Eulerian = autos - autos_nonEul)")
    for name, autos, eul in (("n3_all", 59, 8), ("n4_all", 1240, 72)):
        row([name], lambda name=name, autos=autos, eul=eul: (
            q(name, "autos") == autos and q(name, "autos") - q(name, "autos_nonEul") == eul,
            "Appendix A: %s: %s automata, %d Eulerian (paper: %s, %d)"
            % (LABEL[name], c(q(name, "autos")), q(name, "autos") - q(name, "autos_nonEul"), c(autos), eul)))
    for name, autos, where in (("n5_all", 32588, "Appendix A"), ("n6_all", 1122529, "Appendix A"),
                               ("n4_d2", 811, "Appendix A"), ("n6_d2", 260461, "Appendix A.1")):
        row([name], lambda name=name, autos=autos, where=where: (
            q(name, "autos") == autos,
            "%s: %s: %s automata (paper: %s)" % (where, LABEL[name], c(q(name, "autos")), c(autos))))
    names = ["n4_all", "n5_all", "n6_all", "n7_d2"]
    row(names, lambda: (
        [DATA[nm]["a_classes"] for nm in names] == [19, 47, 130, 343],
        "Appendix A.1: conjugacy classes of endofunctions at n=4,5,6,7: %s (field a_classes; paper: 19, 47, 130, 343)"
        % ", ".join(str(DATA[nm]["a_classes"]) for nm in names)))
    row([p[0] for p in POPS], lambda: (
        sum(1 for p in POPS if p[3] == 2) == 6 and all(q(p[0], "autos_nonEul") > 0 for p in POPS),
        "Appendix A: of the eleven populations of Section 6.6, %d are {d<=2} strata and none is an "
        "Eulerian fibre (non-Eulerian automata on each: %s)"
        % (sum(1 for p in POPS if p[3] == 2), ", ".join(c(q(p[0], "autos_nonEul")) for p in POPS))))

    section("Appendix A and A.1: ternary populations, ordered pairs (engine) and multisets")
    row(["n4k3_all"], lambda: (
        q("n4k3_all", "autos") == 789358,
        "Appendix A.1: ternary n=4, all d, letters after the first ordered: %s automata (paper: 789,358)"
        % c(q("n4k3_all", "autos"))))
    need = ["n4_all", "n4_d2", "n5_d2", "n4k3_all", "n4k3_d2", "n5k3_d2"]
    if any(DATA.get(nm) is None for nm in need):
        row(need, lambda: (False, ""))
        return
    own = {(4, -1): count_pairs(4, 1, -1), (4, 2): count_pairs(4, 1, 2), (5, 2): count_pairs(5, 1, 2)}
    row(["n4_all", "n4_d2", "n5_d2"], lambda: (
        own[(4, -1)] == q("n4_all", "autos") and own[(4, 2)] == q("n4_d2", "autos")
        and own[(5, 2)] == q("n5_d2", "autos"),
        "this program's own enumeration of binary automata reproduces the engine's populations: "
        "n=4 all d %s, n=4 d<=2 %s, n=5 d<=2 %s (engine: %s, %s, %s)"
        % (c(own[(4, -1)]), c(own[(4, 2)]), c(own[(5, 2)]),
           c(q("n4_all", "autos")), c(q("n4_d2", "autos")), c(q("n5_d2", "autos")))))
    diag = {(4, -1): count_pairs(4, 2, -1), (4, 2): count_pairs(4, 2, 2), (5, 2): count_pairs(5, 2, 2)}
    row(["n4_all"], lambda: (
        diag[(4, -1)] == q("n4_all", "autos"),
        "identity check: ternary n=4 automata with c=b, all d: %s = binary n=4 population %s "
        "(holds without a deviation filter: (a,b,b) and (a,b) are synchronizing and strongly "
        "connected together)" % (c(diag[(4, -1)]), c(q("n4_all", "autos")))))
    multiset4 = Fraction(q("n4k3_all", "autos") + diag[(4, -1)], 2)
    row(["n4k3_all"], lambda: (
        multiset4 == 395299,
        "Appendix A.1: ternary n=4, all d, multiset convention: (789,358 + %s)/2 = %s automata "
        "(paper: 395,299)" % (c(diag[(4, -1)]), c(int(multiset4)))))
    row(["n4_d2", "n5_d2"], lambda: (
        diag[(4, 2)] != q("n4_d2", "autos") and diag[(5, 2)] != q("n5_d2", "autos"),
        "identity check: with the filter d<=2 the c=b automata are NOT the binary strata: "
        "%s at n=4 (binary %s), %s at n=5 (binary %s), the deviation of (a,b,b) at k=3 "
        "differing from that of (a,b) at k=2"
        % (c(diag[(4, 2)]), c(q("n4_d2", "autos")), c(diag[(5, 2)]), c(q("n5_d2", "autos")))))
    for name, n, paper in (("n4k3_d2", 4, 249605), ("n5k3_d2", 5, 37946778)):
        ordered = q(name, "autos")
        total = ordered + diag[(n, 2)]
        row([name], lambda name=name, n=n, paper=paper, ordered=ordered, total=total: (
            ordered == paper and total % 2 == 0,
            "Appendix A: ternary n=%d, d<=2: %s automata with the letters after the first ordered "
            "(paper: %s); as multisets (%s + %s)/2 = %s"
            % (n, c(ordered), c(paper), c(ordered), c(diag[(n, 2)]), c(total // 2))))


def check_table_a1():
    section("Section 4.1 and Table A.1 (fields autos_nonEul, autos_noSigZeroSub; quotient)")
    for name in CELLS:
        ne, no, fr = TABLE_A1[name]
        row([name], lambda name=name, ne=ne, no=no, fr=fr: (
            q(name, "autos_nonEul") == ne and q(name, "autos_noSigZeroSub") == no
            and fmt(share(no, ne), 1) == fr,
            "Table A.1, %s: %s non-Eulerian, %s with no proper nonempty subset having all sigma_t=0, "
            "%s%% (paper: %s, %s, %s%%)"
            % (LABEL[name], c(q(name, "autos_nonEul")), c(q(name, "autos_noSigZeroSub")),
               fmt(share(q(name, "autos_noSigZeroSub"), q(name, "autos_nonEul")), 1), c(ne), c(no), fr)))

    def fractions():
        return {nm: share(q(nm, "autos_noSigZeroSub"), q(nm, "autos_nonEul")) for nm in CELLS}

    def rng():
        f = fractions()
        lo = min(CELLS, key=lambda nm: f[nm])
        hi = max(CELLS, key=lambda nm: f[nm])
        return (lo == "n6_d2" and hi == "n5_all" and fmt(f[lo], 1) == "55.3" and fmt(f[hi], 1) == "93.3",
                "Section 4.1 and Appendix A.2: the share runs from %s%% (%s) to %s%% (%s) "
                "(paper: 55.3 percent (n=6, {d<=2}) to 93.3 percent (n=5, all deviations))"
                % (fmt(f[lo], 1), LABEL[lo], fmt(f[hi], 1), LABEL[hi]))
    row(CELLS, rng)

    def monotone():
        f = fractions()
        alld = [f[nm] for nm in ("n3_all", "n4_all", "n5_all", "n6_all")]
        d2 = [f[nm] for nm in ("n5_d2", "n6_d2", "n7_d2")]
        ok = alld[0] < alld[1] < alld[2] > alld[3] and d2[0] > d2[1] < d2[2]
        return (ok, "Section 4.1 and Appendix A.2: not monotone in n: all d %s (n=3..6), {d<=2} %s (n=5..7) "
                "(paper: rises from 70.6 to 93.3 at n=5, collapses to 64.8 at n=6; 88.8, 55.3, 89.5)"
                % (" ".join(fmt(x, 1) for x in alld), " ".join(fmt(x, 1) for x in d2)))
    row(CELLS, monotone)


def check_conventions():
    section("Appendix A.1: the same fractions in both conventions ([0] quotient, [1] labelled)")

    def fr(nm, conv):
        return share(q(nm, "autos_noSigZeroSub", conv), q(nm, "autos_nonEul", conv))
    for name, pq, pl, shift in A1_PAIRS:
        row([name], lambda name=name, pq=pq, pl=pl, shift=shift: (
            fmt(fr(name, 0), 2) == pq and fmt(fr(name, 1), 2) == pl and fmt(fr(name, 0) - fr(name, 1), 2) == shift,
            "Appendix A.1, %s: %s%% quotient against %s%% labelled, shift %s points (paper: %s against %s, %s points)"
            % (LABEL[name], fmt(fr(name, 0), 2), fmt(fr(name, 1), 2), fmt(fr(name, 0) - fr(name, 1), 2), pq, pl, shift)))

    def under():
        shifts = {nm: abs(fr(nm, 0) - fr(nm, 1)) for nm in CELLS}
        by_n = [shifts[nm] for nm in ("n3_all", "n4_all", "n5_all", "n6_all")]
        mono = all(x <= y for x, y in zip(by_n, by_n[1:])) or all(x >= y for x, y in zip(by_n, by_n[1:]))
        return (all(s < Fraction(5, 2) for s in shifts.values()) and not mono,
                "Appendix A.1 and A.2: the shift is under 2.5 points at every cell computed and not monotone "
                "in n: %s" % ", ".join("%s %s" % (LABEL[nm], fmt(shifts[nm], 3)) for nm in CELLS))
    row(CELLS, under)


def check_hard_core():
    section("Section 6.3: {B<0} (fields Bneg, rows)")
    for name, bneg, rows, pct in HARD_CORE:
        row([name], lambda name=name, bneg=bneg, rows=rows, pct=pct: (
            q(name, "Bneg") == bneg and q(name, "rows") == rows and fmt(share(bneg, rows), 1) == pct,
            "Section 6.3, %s: {B<0} holds %s of %s proper-subset instances, %s%% (paper: %s of %s, %s)"
            % (LABEL[name], c(q(name, "Bneg")), c(q(name, "rows")),
               fmt(share(q(name, "Bneg"), q(name, "rows")), 1), c(bneg), c(rows), pct)))
    names = [h[0] for h in HARD_CORE]
    row(names, lambda: (
        all(share(q(a, "Bneg"), q(a, "rows")) < share(q(b, "Bneg"), q(b, "rows")) < 50
            for a, b in zip(names, names[1:])),
        "Section 6.3: the share rises with n and stays below one half: %s"
        % ", ".join(fmt(share(q(nm, "Bneg"), q(nm, "rows")), 4) for nm in names)))


def check_grading():
    section("Section 6.4, n=5 all d (fields sig_pos, sig_first, exists_sig_le, BT_pos, Csharp_minus_Bge0)")
    nm = "n5_all"
    row([nm], lambda: (
        q(nm, "autos") == 32588 and q(nm, "rows") == 977640,
        "Section 6.4: %s automata, %s proper-subset instances (paper: 32,588; 977,640)"
        % (c(q(nm, "autos")), c(q(nm, "rows")))))
    row([nm], lambda: (
        DATA[nm]["acc"]["sig_pos"][1][0] == 314393 and DATA[nm]["acc"]["sig_first"][1][0] == 314393,
        "Section 6.4: the certificate fires at t=1 (sigma_1>0) on %s instances (sig_pos[1]; paper: 314,393)"
        % c(DATA[nm]["acc"]["sig_pos"][1][0])))
    row([nm], lambda: (
        DATA[nm]["acc"]["sig_first"][4][0] == 12064,
        "Section 6.4: %s instances fire only at the full length t=n-1=4 (sig_first[4]; paper: 12,064)"
        % c(DATA[nm]["acc"]["sig_first"][4][0])))
    for T, paper in ((2, 12644), (4, 29396)):
        def chk(T=T, paper=paper):
            a = DATA[nm]["acc"]
            union, strict = a["exists_sig_le"][T][0], a["BT_pos"][T][0]
            return (strict <= union and union - strict == paper,
                    "Section 6.4: the union of {sigma_t>0}, t<=%d, exceeds {B_%d>0} by %s - %s = %s instances "
                    "(exists_sig_le[%d] - BT_pos[%d]; paper: %s)"
                    % (T, T, c(union), c(strict), c(union - strict), T, T, c(paper)))
        row([nm], chk)
    row([nm], lambda: (
        q(nm, "Csharp_minus_Bge0") == 26826,
        "Section 6.4: at T=n-1=4 the union holds %s instances that {B_T>=0} misses (C# minus {B>=0}, "
        "Csharp_minus_Bge0; paper: 26,826; the T=2 value 9,108 is not computed by this engine)"
        % c(q(nm, "Csharp_minus_Bge0"))))
    for name, paper in (("n4_all", 402), ("n5_all", 2428), ("n6_all", 8528)):
        row([name], lambda name=name, paper=paper: (
            q(name, "boundary_nograde") == paper,
            "Section 6.4, %s: boundary half not graded: %s subsets with sigma_t=0 for every t<=n-2 and "
            "minext>n-2 (boundary_nograde; paper: %s)" % (LABEL[name], c(q(name, "boundary_nograde")), c(paper))))


def removed(name):
    """C#, (Q-CERT), (Q-CERT+) removals from {B<0}, quotient integers"""
    g = q(name, "Csharp_minus_Bge0")
    return g, g + q(name, "Hsharp_qcert"), g + q(name, "Hsharp_qplus")


def check_table_d1():
    section("Sections 6.5, 6.6 and Table D.1: shares of {B<0} removed "
            "(C# = Csharp_minus_Bge0; (Q-CERT) = Csharp_minus_Bge0 + Hsharp_qcert; "
            "(Q-CERT+) = Csharp_minus_Bge0 + Hsharp_qplus; all over Bneg)")
    for name in CELLS:
        pc, pq, pp = TABLE_D1[name]

        def chk(name=name, pc=pc, pq=pq, pp=pp):
            b = q(name, "Bneg")
            g, gq, gp = removed(name)
            got = (fmt(share(g, b), 4), fmt(share(gq, b), 2), fmt(share(gp, b), 2))
            return (got == (pc, pq, pp),
                    "Table D.1, %s: C# %s/%s = %s%%, (Q-CERT) %s = %s%%, (Q-CERT+) %s = %s%% (paper: %s, %s, %s)"
                    % (LABEL[name], c(g), c(b), got[0], c(gq), got[1], c(gp), got[2], pc, pq, pp))
        row([name], chk)

    def ranges():
        s = {nm: [share(x, q(nm, "Bneg")) for x in removed(nm)] for nm in CELLS}
        qmin = min(s[nm][1] for nm in CELLS)
        qmax = max(s[nm][1] for nm in CELLS)
        pmin = min(s[nm][2] for nm in CELLS)
        pmax = max(s[nm][2] for nm in CELLS)
        cmax = max(s[nm][0] for nm in CELLS)
        got = (fmt(qmin, 2), fmt(qmax, 2), fmt(pmin, 2), fmt(pmax, 2), fmt(cmax, 2))
        return (got == ("60.14", "90.03", "60.14", "91.44", "9.05"),
                "Section 6.6: over the seven populations of Table D.1, (Q-CERT) removes between %s and %s%%, "
                "(Q-CERT+) between %s and %s%%, C# at most %s%% (exactly %s) (paper: 60.14-90.03, 60.14-91.44, "
                "at most 9.05)" % (got + (fmt(cmax, 4),)))
    row(CELLS, ranges)

    section("Section 6.5: C# (Csharp_minus_Bge0 / Bneg)")
    row(["n4_all", "n5_all", "n6_all"], lambda: (
        [fmt(share(q(nm, "Csharp_minus_Bge0"), q(nm, "Bneg")), 1) for nm in ("n4_all", "n5_all", "n6_all")]
        == ["3.4", "5.8", "9.1"],
        "Section 6.5: passing from {B>=0} to C# shrinks {B<0} by %s, %s and %s percent at n=4,5,6 "
        "(paper: 3.4, 5.8, 9.1)"
        % tuple(fmt(share(q(nm, "Csharp_minus_Bge0"), q(nm, "Bneg")), 1) for nm in ("n4_all", "n5_all", "n6_all"))))
    row(["n3_all"], lambda: (
        q("n3_all", "Csharp_minus_Bge0") == 0 and q("n3_all", "Csharp") == q("n3_all", "Bge0")
        and q("n3_all", "autos") == 59,
        "Section 6.5: at n=3 the gain is %d and C# = {B>=0} (%d = %d instances) on all %d automata "
        "(paper: gain 0 on all 59)" % (q("n3_all", "Csharp_minus_Bge0"), q("n3_all", "Csharp"),
                                       q("n3_all", "Bge0"), q("n3_all", "autos"))))
    row(["n4_all"], lambda: (
        fmt(share(q("n4_all", "Csharp_minus_Bge0"), q("n4_all", "Bneg")), 2) == "3.42",
        "Section 6.5 and Appendix D: at k=2, n=4 the C# gain is %s percent (paper: 3.42)"
        % fmt(share(q("n4_all", "Csharp_minus_Bge0"), q("n4_all", "Bneg")), 2)))
    note("the shares at k=3, n=4 quoted in Section 6.5 and Appendix D (multiset convention) are "
         "checked by ternary/ternary.py")


def check_eleven():
    section("Section 6.6 on the eleven populations (stuck, stuck_qcert, stuck_qplus; byj_f, byj_g1, byj_g2, byj_g2p)")
    for name, n, k, dmax, label in POPS:
        row([name], lambda name=name, label=label: (
            DATA[name]["acc"]["stuck_qcert"] == [0, 0] and DATA[name]["acc"]["stuck_qplus"] == [0, 0]
            and q(name, "stuck") > 0,
            "Section 6.6, %s: 0 stuck subsets certified by (Q-CERT) and by (Q-CERT+) (stuck_qcert %s, "
            "stuck_qplus %s; of %s stuck)"
            % (label, DATA[name]["acc"]["stuck_qcert"], DATA[name]["acc"]["stuck_qplus"], c(q(name, "stuck")))))
    for name, n, k, dmax, label in POPS:
        def chk(name=name, n=n, label=label):
            a = DATA[name]["acc"]
            prof = [(a["byj_g1"][j], a["byj_g2"][j], a["byj_g2p"][j], a["byj_f"][j]) for j in range(1, n)]
            ok = all(v == n - 1 for p in prof for v in p)
            return (ok, "Section 6.6, %s: per size j=1..%d the largest firing length of sigma_t>0, (Q-CERT), "
                    "(Q-CERT+) and the largest minext<=n-1 are %s (paper: n-1 = %d at every size)"
                    % (label, n - 1, " ".join("%d/%d/%d/%d" % p for p in prof), n - 1))
        row([name], chk)


def check_appendix_d():
    section("Appendix D: (Q-CERT) against C#, and the gap (ex_gap_any)")
    nonzero = [nm for nm in CELLS if DATA.get(nm) is None or q(nm, "Csharp_minus_Bge0") > 0]

    def ratio():
        rs = {nm: Fraction(removed(nm)[1], removed(nm)[0]) for nm in nonzero}
        lo = min(nonzero, key=lambda nm: rs[nm])
        hi = max(nonzero, key=lambda nm: rs[nm])
        ok = len(nonzero) == 6 and all(Fraction(994, 100) <= r <= Fraction(4430, 100) for r in rs.values())
        return (ok, "Appendix D: where the C# share is nonzero (%d populations of Table D.1) (Q-CERT) removes "
                    "between %s (%s) and %s (%s) times as much as C# (paper: between 9.94 and 44.30)"
                % (len(nonzero), fmt(rs[lo], 4), LABEL[lo], fmt(rs[hi], 4), LABEL[hi]))
    row(CELLS, ratio)
    d2 = ["n4_d2", "n5_d2", "n6_d2", "n7_d2"]
    alld = ["n3_all", "n4_all", "n5_all", "n6_all"]
    row(d2 + alld, lambda: (
        all(q(nm, "ex_gap_any") == 0 for nm in d2)
        and all(q(nm, "ex_gap_any") > 0 for nm in ("n4_all", "n5_all", "n6_all")),
        "Appendix D: binary sweeps: gap instances (subsets extending within some t but at no length exactly t) "
        "on the {d<=2} strata n=4..7: %s; on all deviations n=3..6: %s; the {d<=2} strata of n=4,5,6 hold none "
        "of them, so every instance found lies at d>=4 (d is even) (paper: empty on every {d<=2} population, "
        "every instance at d>=4)"
        % (", ".join(c(q(nm, "ex_gap_any")) for nm in d2), ", ".join(c(q(nm, "ex_gap_any")) for nm in alld))))
    row(["n4k3_d2", "n5k3_d2"], lambda: (
        q("n4k3_d2", "ex_gap_any") == 0 and q("n5k3_d2", "ex_gap_any") == 0,
        "Appendix D (Lemma 5 at k=3): no gap instance on the ternary {d<=2} strata at n=4 and n=5: %s, %s"
        % (c(q("n4k3_d2", "ex_gap_any")), c(q("n5k3_d2", "ex_gap_any")))))


def check_implementation():
    section("implementation checks (every viol_* counter must be 0)")
    for name, n, k, dmax, label in POPS:
        row([name], lambda name=name, label=label: (
            all(v == [0, 0] for f, v in DATA[name]["acc"].items() if f.startswith("viol_"))
            and sum(1 for f in DATA[name]["acc"] if f.startswith("viol_")) == 8,
            "%s: the 8 viol_* counters are 0 (a test firing at t with no word of length exactly t extending S, "
            "minext above a firing length, a negative second moment, (Q-CERT) without (Q-CERT+))" % label))


def main(argv):
    if len(argv) != 2 or not os.path.isdir(argv[1]):
        sys.exit("usage: python tables.py DIR   (DIR written by run_populations.py)")
    load(argv[1])
    missing = [p[0] + ".json" for p in POPS if DATA[p[0]] is None]
    if missing:
        print("missing input files: %s" % " ".join(missing))
    check_populations()
    check_table_a1()
    check_conventions()
    check_hard_core()
    check_grading()
    check_table_d1()
    check_eleven()
    check_appendix_d()
    check_implementation()
    failed = ROWS.count(False)
    print("")
    print("%d rows, %d FAILED" % (len(ROWS), failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
