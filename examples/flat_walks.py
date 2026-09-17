#!/usr/bin/env python3
"""flat_walks.py -- Section 8.3: the flat-walk strengthening of Theorem 1 fails at n = 5.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 8.3: the statement "B(S) >= 0 implies a flat walk of length at most n-2
      reaching a subset with an extending letter" is false already at n = 5.  On
      the automaton a: 0,1,2,3,4 -> 1,2,0,0,3 and b: 0,1,2,3,4 -> 0,1,4,0,1
      (synchronizing, strongly connected, indeg = (4,3,1,1,1),
      beta* = (42,55,-12,-47,-38)) the subset S = {1,2,4} has B(S) = 5, while
      S a^-1 = {0,1} shrinks and S b^-1 = S, so no flat walk of any length leaves S;
      minext(S) = 2, by u = ba.  Over the exhaustive binary populations the
      statement holds at n = 3 and n = 4, where the largest value of B on a subset
      from which no such walk exists is -1, and fails on 49 subsets at n = 5,
      where that largest value is +5.
  Section 6.1: the unfiltered n = 5 enumeration has 146,875 automata:
      31,895 not synchronizing, 82,392 synchronizing but not strongly connected,
      32,588 synchronizing and strongly connected.
  Section 6.2 and Appendix A: the n = 5 population has 11,042 stuck subsets and
      the largest value of B on a stuck subset is -1.
  Section 6.3 and Appendix A: {B<0} holds 463,047 of the 977,640
      proper-subset instances at n = 5, and exactly as many have B > 0.
  Section 5.2 and Table A.1: 954 of the 32,588 automata are Eulerian, 31,634 are not.

Population / convention (Appendix A.1): the first letter a ranges over one
representative of each conjugacy class of endofunctions of an n-element set
(7, 19, 47 classes at n = 3, 4, 5; sequence A001372), the second letter b over
all n^n maps; then the filters synchronizing and strongly connected.  The first
rows rebuild the population and check its sizes before anything else.

Definitions (Sections 8.2 and 8.3): a move S -> S x^-1 is flat if it preserves
cardinality; a flat walk is a sequence of flat moves; a subset T has an
extending letter if |T x^-1| > |T| for some letter x.  A walk of length 0 is
admitted.

Usage:    python flat_walks.py
Output:   one [PASS]/[FAIL] line per statement, then "N rows, M FAILED".
Runtime:  under a minute.
Requires: Python 3.8 or later, standard library only.  Exit status = number of
          failed rows.
"""

import itertools
import sys

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


# ------------------------------------------------------------------ the population

def class_reps(n):
    """One representative of each conjugacy class of endofunctions of [n]."""
    seen, reps = set(), []
    perms = list(itertools.permutations(range(n)))
    for f in itertools.product(range(n), repeat=n):
        if f in seen:
            continue
        orb = set()
        for p in perms:                                   # g = p f p^{-1}
            inv = [0] * n
            for i, pi in enumerate(p):
                inv[pi] = i
            orb.add(tuple(p[f[inv[q]]] for q in range(n)))
        seen |= orb
        reps.append(min(orb))
    return reps


def preimage_tables(letters, n):
    """pre[x][T] = T x^{-1} as bitmasks, over all 2^n subsets."""
    out = []
    for f in letters:
        bit = [1 << f[q] for q in range(n)]
        tab = [0] * (1 << n)
        for T in range(1 << n):
            m = 0
            for q in range(n):
                if T & bit[q]:
                    m |= 1 << q
            tab[T] = m
        out.append(tab)
    return out


def synchronizing(letters, n):
    """Backward search on unordered pairs: every pair must be mergeable."""
    need = {(p, q) for p in range(n) for q in range(p + 1, n)}
    done = set()
    frontier = [(p, p) for p in range(n)]
    seen = set(frontier)
    while frontier:
        nxt = []
        for (p, q) in frontier:
            for f in letters:
                for a in range(n):
                    if f[a] != p:
                        continue
                    for b in range(n):
                        if f[b] != q:
                            continue
                        key = (min(a, b), max(a, b))
                        if key in seen:
                            continue
                        seen.add(key)
                        nxt.append(key)
                        if key[0] != key[1]:
                            done.add(key)
        frontier = nxt
    return need <= done


def strongly_connected(letters, n):
    adj = [set() for _ in range(n)]
    for f in letters:
        for q in range(n):
            adj[q].add(f[q])

    def reach(start, g):
        seen, st = {start}, [start]
        while st:
            u = st.pop()
            for v in g[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        return seen
    rev = [set() for _ in range(n)]
    for u in range(n):
        for v in adj[u]:
            rev[v].add(u)
    return len(reach(0, adj)) == n and len(reach(0, rev)) == n


def beta_star(letters, n):
    """beta*^T = sum_{j=0}^{n-2} (n-1-j) k^{n-2-j} w^T M^j   (Lemma 2)."""
    k = len(letters)
    M = [[0] * n for _ in range(n)]
    for f in letters:
        for q in range(n):
            M[q][f[q]] += 1
    indeg = [sum(M[q][r] for q in range(n)) for r in range(n)]
    w = [indeg[r] - k for r in range(n)]
    v = w[:]                                              # w^T M^j
    beta = [0] * n
    for j in range(n - 1):
        c = (n - 1 - j) * k ** (n - 2 - j)
        for r in range(n):
            beta[r] += c * v[r]
        v = [sum(v[q] * M[q][r] for q in range(n)) for r in range(n)]
    return beta, indeg, w


POP = []                                                  # the n=5 population
COUNTS = {}


def build(n=5):
    reps = class_reps(n)
    allmaps = list(itertools.product(range(n), repeat=n))
    total = nosync = syncnotsc = 0
    for a in reps:
        for b in allmaps:
            total += 1
            L = (a, b)
            if not synchronizing(L, n):
                nosync += 1
                continue
            if not strongly_connected(L, n):
                syncnotsc += 1
                continue
            POP.append(L)
    COUNTS.update(nosync=nosync, syncnotsc=syncnotsc)
    return len(reps), total


def p1():
    nreps, ntotal = build(5)
    ok = (nreps == 47 and ntotal == 146875 and COUNTS["nosync"] == 31895
          and COUNTS["syncnotsc"] == 82392 and len(POP) == 32588)
    return ok, (
        "%d conjugacy classes (A001372: 47); %d automata unfiltered = %d not "
        "synchronizing + %d synchronizing not strongly connected + %d synchronizing "
        "and strongly connected (Section 6.1: 146,875 = 31,895 + 82,392 + 32,588)"
        % (nreps, ntotal, COUNTS["nosync"], COUNTS["syncnotsc"], len(POP)))


def p2():
    n = 5
    euler = sum(1 for L in POP if all(x == 0 for x in beta_star(L, n)[2]))
    return (euler == 954 and len(POP) - euler == 31634), (
        "%d Eulerian (Section 5.2: 954), %d non-Eulerian (Table A.1: 31,634)"
        % (euler, len(POP) - euler))


def p3():
    n = 5
    neg = pos = zero = 0
    for L in POP:
        beta = beta_star(L, n)[0]
        for S in range(1, (1 << n) - 1):
            b = sum(beta[q] for q in range(n) if S >> q & 1)
            if b < 0:
                neg += 1
            elif b > 0:
                pos += 1
            else:
                zero += 1
    return (neg == 463047 and pos == 463047 and neg + pos + zero == 977640), (
        "B<0: %d, B>0: %d, B=0: %d, total %d proper-subset instances "
        "(Section 6.3 and Appendix A: 463,047 of 977,640, and #{B>0} = #{B<0})"
        % (neg, pos, zero, neg + pos + zero))


# ------------------------------------------------------- the Section 8.3 sweep

def popcount(x):
    return bin(x).count("1")


def flat_ok(S, pre, horizon):
    """Does some flat walk of length <= horizon from S reach a subset with an
    extending letter?  Length 0 counts."""
    size = popcount(S)
    seen = {S}
    layer = [S]
    for _ in range(horizon + 1):
        nxt = []
        for T in layer:
            for tab in pre:
                U = tab[T]
                c = popcount(U)
                if c > size:
                    return True                           # T has an extending letter
                if c == size and U not in seen:
                    seen.add(U)
                    nxt.append(U)
        if not nxt:
            return False
        layer = nxt
    return False


def sweep():
    n, horizon = 5, 3                                     # n-2 = 3 flat moves
    fails_nonneg, worst = 0, None
    for L in POP:
        beta = beta_star(L, n)[0]
        pre = preimage_tables(L, n)
        for S in range(1, (1 << n) - 1):
            b = sum(beta[q] for q in range(n) if S >> q & 1)
            if not flat_ok(S, pre, horizon):
                if worst is None or b > worst:
                    worst = b
                if b >= 0:
                    fails_nonneg += 1
    return fails_nonneg, worst


def s1():
    fails, worst = sweep()
    return (fails == 49 and worst == 5), (
        "over the n=5 population: %d subsets have B>=0 and admit no flat walk of "
        "length <= n-2 to a subset with an extending letter, and the largest B on a "
        "subset admitting no such walk is %+d (Section 8.3: 49 subsets, +5)" % (fails, worst))


def s2():
    """The witness printed in Section 8.3."""
    n = 5
    a = (1, 2, 0, 0, 3)
    b = (0, 1, 4, 0, 1)
    L = (a, b)
    beta, indeg, w = beta_star(L, n)
    S = 0b10110                                           # {1,2,4}
    B = sum(beta[q] for q in range(n) if S >> q & 1)
    pre = preimage_tables(L, n)
    reach = flat_ok(S, pre, 99)
    minext = None
    for ln in range(1, 6):
        for u in itertools.product((0, 1), repeat=ln):
            T = S
            for x in reversed(u):                         # S (x_1 ... x_l)^{-1}
                T = pre[x][T]
            if popcount(T) > popcount(S):
                minext = ln
                break
        if minext:
            break
    ba_grows = popcount(pre[1][pre[0][S]]) > popcount(S)  # S(ba)^-1 = (S a^-1) b^-1
    ok = (tuple(indeg) == (4, 3, 1, 1, 1) and tuple(beta) == (42, 55, -12, -47, -38)
          and B == 5 and pre[0][S] == 0b00011 and pre[1][S] == S
          and not reach and minext == 2 and ba_grows
          and synchronizing(L, n) and strongly_connected(L, n))
    return ok, ("indeg=%s, beta*=%s, B({1,2,4})=%+d, S a^-1=%s, S b^-1=S: %s, "
                "flat walk to an extending letter exists: %s, minext=%s (ba extends: %s), "
                "synchronizing=%s, strongly connected=%s"
                % (tuple(indeg), tuple(beta), B,
                   sorted(q for q in range(n) if pre[0][S] >> q & 1), pre[1][S] == S,
                   reach, minext, ba_grows, synchronizing(L, n), strongly_connected(L, n)))


def small(n):
    """The same sweep at the sizes n = 3 and n = 4."""
    reps = class_reps(n)
    allmaps = list(itertools.product(range(n), repeat=n))
    pop, worst, fails = 0, None, 0
    for a in reps:
        for b in allmaps:
            L = (a, b)
            if not synchronizing(L, n) or not strongly_connected(L, n):
                continue
            pop += 1
            beta = beta_star(L, n)[0]
            pre = preimage_tables(L, n)
            for S in range(1, (1 << n) - 1):
                if flat_ok(S, pre, n - 2):
                    continue
                b_ = sum(beta[q] for q in range(n) if S >> q & 1)
                if worst is None or b_ > worst:
                    worst = b_
                if b_ >= 0:
                    fails += 1
    return pop, worst, fails


def s3():
    out = {}
    for n in (3, 4):
        out[n] = small(n)
    ok = (out[3][0] == 59 and out[4][0] == 1240
          and out[3][2] == 0 and out[4][2] == 0
          and out[3][1] == -1 and out[4][1] == -1)
    return ok, ("n=3: %d automata, largest B on a subset admitting no such walk %+d, "
                "%d with B>=0; n=4: %d automata, largest B %+d, %d with B>=0 "
                "(Section 8.3: the statement holds at n=3 and n=4, largest value -1; "
                "Appendix A: 59 and 1,240 automata)"
                % (out[3][0], out[3][1], out[3][2], out[4][0], out[4][1], out[4][2]))


def stuck_subsets():
    """Stuck subsets of the n=5 population and the largest B on them."""
    n = 5
    stuck_seen = 0
    stuck_maxB = None
    for L in POP:
        beta = beta_star(L, n)[0]
        pre = preimage_tables(L, n)
        for S in range(1, (1 << n) - 1):
            # stuck = no word of length <= n-1 grows S
            grew = False
            frontier = {S}
            for _ in range(n - 1):
                nxt = set()
                for T in frontier:
                    for tab in pre:
                        U = tab[T]
                        if popcount(U) > popcount(S):
                            grew = True
                            break
                        nxt.add(U)
                    if grew:
                        break
                if grew:
                    break
                frontier = nxt
            if grew:
                continue
            stuck_seen += 1
            b = sum(beta[q] for q in range(n) if S >> q & 1)
            if stuck_maxB is None or b > stuck_maxB:
                stuck_maxB = b
    return (stuck_seen == 11042 and stuck_maxB == -1), (
        "%d stuck subsets, largest B on a stuck subset %+d "
        "(Appendix A: 11,042; Section 6.2: -1)" % (stuck_seen, stuck_maxB))


def main():
    print("flat_walks -- Section 8.3 on the exhaustive binary populations")
    print()
    print("  ---- the n=5 population ----")
    row("N1", "the enumeration of Appendix A.1 reproduces the partition of Section 6.1", p1)
    row("N2", "Eulerian and non-Eulerian counts", p2)
    row("N3", "the subsets with B<0", p3)
    row("N4", "stuck subsets", stuck_subsets)
    print()
    print("  ---- Section 8.3 ----")
    row("S1", "the strengthening fails at n=5", s1)
    row("S2", "the witness", s2)
    row("S3", "the strengthening holds at n=3 and n=4", s3)
    print()
    print("%d rows, %d FAILED" % (len(ROWS), FAILED))
    return FAILED


if __name__ == "__main__":
    sys.exit(min(main(), 255))
