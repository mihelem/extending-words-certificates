#!/usr/bin/env python3
"""examples_and_figures.py -- the small, hand-checkable automata of the paper.

Checks, from the definitions and by direct enumeration of words, every number
the paper states about its explicit small examples:

  Example 1 and Figures 1-2 (Section 3): the Cerny automaton C_3, its in-degrees,
      w, w^T M, beta* = (-4,3,1), B on all eight subsets, minext on the six proper
      subsets, the two stuck subsets {0} and {0,1}, the antipodal pairing.
  Section 5.2 and Section 6.1: group automata (every letter a permutation) have
      beta* = 0, no proper nonempty subset extends at any length, and they are
      not synchronizing.
  Example 2 and Figure 3 (Section 5.4): indeg = (4,1,1), w = (2,-1,-1),
      w^T M = -2 w^T, sigma_2 vanishes identically, every edge crosses the
      bipartition {0} | {1,2}; the automaton is strongly connected and not
      synchronizing.
  Section 6.2: on C_3, S = {0,1} has B(S) = -1 and minext(S) = 3; five of the
      six nonempty words of length at most 2 leave |S u^-1| at 2, ba leaves it
      at 1, and u = baa attains 3.
  Section 6.3: on C_3, {2} has B = 1 and minext = 2 = n-1.
  Section 6.4: the witness family for the grading of the strict half
      (minext({t}) = t and sigma_t({t}) = 1; not synchronizing for n >= 3),
      checked for 2 <= n <= 7, 1 <= t <= n-1 and alphabets of size 1 to 3.
  Section 8.1: C_n carries the one-letter fibre {1} b^-1 = {0,1}, and
      rt(C_n) = (n-1)^2 (here for 3 <= n <= 8), so rt(C_3) = 4 > 3.
  Section 8.2: on C_3 the flat move {0} -> {0}a^-1 = {2} raises B from -4 to 1
      and {1} -> {1}a^-1 = {0} lowers it from 3 to -4.
  Appendix C: the four-state witness (a sends every state to 0, b sends 0,1,2,3
      to 1,2,3,2): synchronizing, strongly connected, e = (6,3,2,1), S = {1} has
      sigma_1 = -1, sigma_2 = sigma_3 = 0 (so S lies in H#), epsilon_1 = 0, and
      minext(S) = 2 by the word ab, which sends every state to 1.
  Appendix D: with k^t = 4, |S| = 3 and -sigma_t(S) = 3 the second moments
      attainable with every x_u <= 0 are exactly 3, 5 and 9, so an observed 7
      refutes non-positivity although 7 is below the threshold 9 of (Q-CERT)
      and (Q-CERT+); 9 - 5 = 4 = 2(|S|-1).
  Appendix D: the gap witness (n = 4; a sends 0,1,2 to 0 and 3 to 1; b sends
      0,1,2,3 to 2,3,3,0): synchronizing, strongly connected, deviation 4,
      S = {3} at t = 2 has x_u = -1,-1,0,0 while minext(S) = 1.

Words act on the right: q.(uv) = (q.u).v, so "ba" applies b first.

Usage:    python examples_and_figures.py
Output:   one [PASS]/[FAIL] line per statement, then "N rows, M FAILED".
Runtime:  about one second.
Requires: Python 3.8 or later, standard library only.  Exit status = number of
          failed rows.
"""
import sys
from fractions import Fraction
from itertools import product

rows = []


def check(label, ok):
    rows.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}", flush=True)


# ---------------------------------------------------------------- helpers

def pre(S, word, n):
    """S u^-1 for the word u given as a list of maps applied left to right."""
    out = set()
    for q in range(n):
        s = q
        for f in word:
            s = f[s]
        if s in S:
            out.add(q)
    return out


def minext_of(S, letters, n, maxlen):
    for L in range(1, maxlen + 1):
        for word in product(letters, repeat=L):
            if len(pre(S, word, n)) > len(S):
                return L
    return None


def is_synchronizing(letters, n):
    """Breadth-first search over images of Q."""
    start = frozenset(range(n))
    seen, frontier = {start}, [start]
    while frontier:
        nxt = []
        for S in frontier:
            if len(S) == 1:
                return True
            for f in letters:
                T = frozenset(f[q] for q in S)
                if T not in seen:
                    seen.add(T)
                    nxt.append(T)
        frontier = nxt
    return False


def reset_threshold(letters, n):
    start = frozenset(range(n))
    if n == 1:
        return 0
    seen, frontier, d = {start}, [start], 0
    while frontier:
        d += 1
        nxt = []
        for S in frontier:
            for f in letters:
                T = frozenset(f[q] for q in S)
                if len(T) == 1:
                    return d
                if T not in seen:
                    seen.add(T)
                    nxt.append(T)
        frontier = nxt
    return None


def is_strongly_connected(letters, n):
    def reach(adj):
        seen, st = {0}, [0]
        while st:
            u = st.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        return len(seen) == n
    fwd = [set(f[q] for f in letters) for q in range(n)]
    bwd = [set() for _ in range(n)]
    for q in range(n):
        for r in fwd[q]:
            bwd[r].add(q)
    return reach(fwd) and reach(bwd)


def indeg_t(t, letters, n):
    """indeg_t(q) = #{(p,u): |u| = t, p.u = q}, by enumerating every word."""
    out = [0] * n
    for word in product(letters, repeat=t):
        for p in range(n):
            s = p
            for f in word:
                s = f[s]
            out[s] += 1
    return out


def sigma_t(t, S, letters, n):
    k = len(letters)
    it = indeg_t(t, letters, n)
    return sum(it[q] for q in S) - k ** t * len(S)


def det_int(m):
    """Fraction-free (Bareiss) determinant of a square integer matrix."""
    m = [row[:] for row in m]
    size = len(m)
    if size == 0:
        return 1
    sign, prev = 1, 1
    for i in range(size - 1):
        if m[i][i] == 0:
            for r in range(i + 1, size):
                if m[r][i] != 0:
                    m[i], m[r] = m[r], m[i]
                    sign = -sign
                    break
            else:
                return 0
        for r in range(i + 1, size):
            for c in range(i + 1, size):
                m[r][c] = (m[r][c] * m[i][i] - m[r][i] * m[i][c]) // prev
        prev = m[i][i]
    return sign * m[size - 1][size - 1]


def stationary_integer(letters, n):
    """Positive left eigenvector e of M = sum_x pi(x) for the eigenvalue k,
    normalised to coprime integers: by the matrix-tree theorem e_q is
    proportional to the principal minor of kI - M at q."""
    k = len(letters)
    lap = [[0] * n for _ in range(n)]
    for q in range(n):
        lap[q][q] += k
        for f in letters:
            lap[q][f[q]] -= 1
    e = [det_int([[lap[i][j] for j in range(n) if j != q]
                  for i in range(n) if i != q]) for q in range(n)]
    g = 0
    for x in e:
        g = abs(x) if g == 0 else _gcd(g, abs(x))
    e = [x // g for x in e]
    if e[0] < 0:
        e = [-x for x in e]
    return e


def _gcd(x, y):
    while y:
        x, y = y, x % y
    return x


def verify_stationary(e, letters, n):
    """e^T M = k e^T, checked exactly."""
    k = len(letters)
    lhs = [0] * n
    for q in range(n):
        for f in letters:
            lhs[f[q]] += e[q]
    return lhs == [k * x for x in e]


# ---------------------------------------------------------------- Example 1: C_3
n, k = 3, 2
a = {0: 1, 1: 2, 2: 0}          # the cycle 0 -> 1 -> 2 -> 0
b = {0: 1, 1: 1, 2: 2}          # sends 0 to 1, fixes 1 and 2
letters = [a, b]

indeg = [sum(1 for f in letters for q in range(n) if f[q] == r) for r in range(n)]
check("Example 1: indeg = (1,3,2)", indeg == [1, 3, 2])
w = [indeg[q] - k for q in range(n)]
check("Example 1: w = (-1,1,0)", w == [-1, 1, 0])

M = [[sum(1 for f in letters if f[q] == r) for r in range(n)] for q in range(n)]
wM = [sum(w[q] * M[q][r] for q in range(n)) for r in range(n)]
check("Example 1: w^T M = (0,-1,1)", wM == [0, -1, 1])

beta = [2 * k * w[q] + wM[q] for q in range(n)]
check("Example 1: beta* = 2k w^T + w^T M = (-4,3,1) (Lemma 2)", beta == [-4, 3, 1])
check("Example 1: beta* sums to 0", sum(beta) == 0)

beta_def = [sum(k ** (n - 1 - t) * (indeg_t(t, letters, n)[q] - k ** t)
                for t in (1, 2)) for q in range(n)]
check("Example 1: beta* from its definition (word enumeration) agrees", beta_def == beta)


def B(S):
    return sum(beta[q] for q in S)


check("Example 1: B({1,2}) = 4", B({1, 2}) == 4)
check("Example 1: sigma_1({1,2}) = w_1 + w_2 = 1", (indeg[1] + indeg[2]) - k * 2 == 1)
check("Example 1: b extends {1,2}: |{1,2} b^-1| = 3", len(pre({1, 2}, [b], n)) == 3)
check("Example 1: beta*_0 = -4 and no nonempty word of length <= 2 extends {0}",
      beta[0] == -4 and all(len(pre({0}, list(u), n)) <= 1
                            for L in (1, 2) for u in product(letters, repeat=L)))
check("Example 1: B({0,2}) = -3 and the word ba extends {0,2}",
      B({0, 2}) == -3 and len(pre({0, 2}, [b, a], n)) == 3)

# ---------------------------------------------------------------- Figure 2: the subset cube
subsets = [frozenset(q for q in range(n) if m >> q & 1) for m in range(8)]
Bval = {S: B(S) for S in subsets}
expected_B = {frozenset(): 0, frozenset({0}): -4, frozenset({1}): 3,
              frozenset({2}): 1, frozenset({0, 1}): -1, frozenset({0, 2}): -3,
              frozenset({1, 2}): 4, frozenset({0, 1, 2}): 0}
check("Figure 2: B on the eight subsets is 0, -4, 3, 1, -1, -3, 4, 0", Bval == expected_B)

proper = [S for S in subsets if 0 < len(S) < n]
mvals = {S: minext_of(S, letters, n, 8) for S in proper}
expected_m = {frozenset({0}): 3, frozenset({1}): 1, frozenset({2}): 2,
              frozenset({0, 1}): 3, frozenset({0, 2}): 2, frozenset({1, 2}): 1}
check("Figure 2: minext on {0},{1},{2},{0,1},{0,2},{1,2} is 3,1,2,3,2,1", mvals == expected_m)
stuck = {S for S in proper if mvals[S] > n - 1}
check("Figure 2: the stuck subsets are exactly {0} and {0,1}, both in {B<0}, the larger at B=-1",
      stuck == {frozenset({0}), frozenset({0, 1})}
      and all(Bval[S] < 0 for S in stuck) and Bval[frozenset({0, 1})] == -1)
check("Figure 2: no proper subset lies on the plane B = 0",
      all(Bval[S] != 0 for S in proper))
check("Figure 2: antipodal subsets carry opposite values, so one of each pair has B >= 0",
      all(Bval[S] == -Bval[frozenset(range(n)) - S]
          and (Bval[S] >= 0 or Bval[frozenset(range(n)) - S] >= 0) for S in proper))
check("Theorem 1 on C_3: every proper subset with B >= 0 extends within n-1",
      all(mvals[S] <= n - 1 for S in proper if Bval[S] >= 0))

# ---------------------------------------------------------------- Section 6.2 and 6.3 on C_3
S01 = {0, 1}
sizes = {"".join("ab"[letters.index(f)] for f in u): len(pre(S01, list(u), n))
         for L in (1, 2) for u in product(letters, repeat=L)}
check("Section 6.2: S={0,1} has B=-1 and minext 3; the words a,b,aa,ab,bb leave |S u^-1| = 2, "
      "ba leaves 1, baa gives 3",
      Bval[frozenset(S01)] == -1 and mvals[frozenset(S01)] == 3
      and all(sizes[u] == 2 for u in ("a", "b", "aa", "ab", "bb")) and sizes["ba"] == 1
      and len(pre(S01, [b, a, a], n)) == 3)
check("Section 6.3: {2} has B = 1 >= 0 and minext = 2 = n-1",
      Bval[frozenset({2})] == 1 and mvals[frozenset({2})] == 2)

# ---------------------------------------------------------------- Section 8.2: flat moves on C_3
flat = [(S, f, frozenset(q for q in range(n) if f[q] in S)) for S in proper for f in letters]
rise = [(S, P) for S, f, P in flat if f is a and len(P) == len(S) and B(P) > B(S)]
fall = [(S, P) for S, f, P in flat if f is a and len(P) == len(S) and B(P) < B(S)]
check("Section 8.2: {0} a^-1 = {2} is flat and raises B from -4 to 1",
      (frozenset({0}), frozenset({2})) in rise and B({0}) == -4 and B({2}) == 1)
check("Section 8.2: {1} a^-1 = {0} is flat and lowers B from 3 to -4",
      (frozenset({1}), frozenset({0})) in fall and B({1}) == 3 and B({0}) == -4)

# ---------------------------------------------------------------- Section 8.1: the Cerny automata C_n
def cerny(m):
    return [{q: (q + 1) % m for q in range(m)}, {q: (1 if q == 0 else q) for q in range(m)}]


check("Section 8.1: C_n carries the one-letter fibre {1} b^-1 = {0,1}, for 3 <= n <= 8",
      all(pre({1}, [cerny(m)[1]], m) == {0, 1} for m in range(3, 9)))
check("Section 8.1: rt(C_n) = (n-1)^2 for 3 <= n <= 8; in particular rt(C_3) = 4 > 3",
      all(reset_threshold(cerny(m), m) == (m - 1) ** 2 for m in range(3, 9))
      and reset_threshold(letters, 3) == 4)

# ---------------------------------------------------------------- group automata (Sections 5.2, 6.1)
def group_case(m, perms):
    lets = [dict(enumerate(p)) for p in perms]
    kk = len(lets)
    ind = [sum(1 for f in lets for q in range(m) if f[q] == r) for r in range(m)]
    ww = [ind[q] - kk for q in range(m)]
    MM = [[sum(1 for f in lets if f[q] == r) for r in range(m)] for q in range(m)]
    vec, bet = ww[:], [0] * m
    for j in range(m - 1):
        c = (m - 1 - j) * kk ** (m - 2 - j)
        bet = [bet[q] + c * vec[q] for q in range(m)]
        vec = [sum(vec[p] * MM[p][r] for p in range(m)) for r in range(m)]
    grows = False
    for size in range(1, m):
        for bits in product([0, 1], repeat=m):
            if sum(bits) != size:
                continue
            cur = {frozenset(q for q in range(m) if bits[q])}
            for _ in range(2 * m):
                cur = {frozenset(q for q in range(m) if f[q] in T) for T in cur for f in lets}
                if any(len(T) > size for T in cur):
                    grows = True
    return bet, grows, is_synchronizing(lets, m)


for label, m, perms in [("a 3-cycle twice", 3, [(1, 2, 0), (1, 2, 0)]),
                        ("a 4-cycle and a transposition", 4, [(1, 2, 3, 0), (1, 0, 3, 2)])]:
    bet, grows, sync = group_case(m, perms)
    check(f"Section 5.2: group automaton ({label}): beta* = 0, so B = 0 >= 0 on every subset",
          bet == [0] * m)
    check(f"Section 5.2: group automaton ({label}): no proper nonempty subset grows (words up to length 2n)",
          not grows)
    check(f"Section 6.1: group automaton ({label}): not synchronizing", not sync)

# ---------------------------------------------------------------- Example 2 and Figure 3
a2 = {0: 1, 1: 0, 2: 0}
b2 = {0: 2, 1: 0, 2: 0}
letters2 = [a2, b2]
indeg2 = [sum(1 for f in letters2 for q in range(n) if f[q] == r) for r in range(n)]
check("Example 2: indeg = (4,1,1)", indeg2 == [4, 1, 1])
w2 = [indeg2[q] - k for q in range(n)]
check("Example 2: w = (2,-1,-1)", w2 == [2, -1, -1])
MM2 = [[sum(1 for f in letters2 if f[q] == r) for r in range(n)] for q in range(n)]
w2M = [sum(w2[q] * MM2[q][r] for q in range(n)) for r in range(n)]
check("Example 2: w^T M = -2 w^T (eigenvalue -2, of modulus k)", w2M == [-2 * x for x in w2])
check("Example 2: w_2^T = w^T M + k w^T = 0, so sigma_2 vanishes identically",
      [w2M[q] + k * w2[q] for q in range(n)] == [0, 0, 0]
      and all(sigma_t(2, {q for q in range(n) if m >> q & 1}, letters2, n) == 0 for m in range(8)))
check("Example 2: strongly connected and not synchronizing",
      is_strongly_connected(letters2, n) and not is_synchronizing(letters2, n))
check("Figure 3: every edge crosses the bipartition {0} | {1,2}",
      all((q in {0}) != (f[q] in {0}) for f in letters2 for q in range(n)))

# ---------------------------------------------------------------- Section 6.4: the grading witness family
def grading_witness(nn, t, kk):
    a_ = {i: (i + 1 if i < t else (1 if i == t else i)) for i in range(nn)}
    ident = {i: i for i in range(nn)}
    return [a_] + [ident] * (kk - 1)


ok_family, ok_nonsync = True, True
for nn in range(2, 8):
    for t in range(1, nn):
        for kk in (1, 2, 3):
            lets = grading_witness(nn, t, kk)
            if minext_of({t}, lets, nn, t) != t or sigma_t(t, {t}, lets, nn) != 1:
                ok_family = False
            if nn >= 3 and kk == 2 and is_synchronizing(lets, nn):
                ok_nonsync = False
check("Section 6.4: the witness family has minext({t}) = t and sigma_t({t}) = 1 "
      "(2 <= n <= 7, 1 <= t <= n-1, k = 1, 2, 3)", ok_family)
check("Section 6.4: the witness is not synchronizing for n >= 3 (checked at k = 2)", ok_nonsync)

# ---------------------------------------------------------------- Appendix C: the four-state witness
n4 = 4
a4 = {q: 0 for q in range(n4)}
b4 = {0: 1, 1: 2, 2: 3, 3: 2}
letters4 = [a4, b4]
e4 = stationary_integer(letters4, n4)
eps = [n4 * e4[q] - sum(e4) for q in range(n4)]
check("Appendix C: the four-state witness is synchronizing and strongly connected, e = (6,3,2,1)",
      is_synchronizing(letters4, n4) and is_strongly_connected(letters4, n4)
      and e4 == [6, 3, 2, 1] and verify_stationary(e4, letters4, n4))
check("Appendix C: S = {1} has sigma_1 = -1, sigma_2 = sigma_3 = 0, so S lies in H#",
      [sigma_t(t, {1}, letters4, n4) for t in (1, 2, 3)] == [-1, 0, 0])
check("Appendix C: epsilon_1 = 4*3 - 12 = 0, so B_e({1}) = 0 >= 0",
      eps[1] == 0 and n4 * e4[1] - sum(e4) == 4 * 3 - 12)
check("Appendix C: minext({1}) = 2, by the word ab, which sends every state to 1",
      minext_of({1}, letters4, n4, 6) == 2
      and all(b4[a4[q]] == 1 for q in range(n4)) and len(pre({1}, [a4, b4], n4)) == n4)

# ---------------------------------------------------------------- Appendix D: attainable second moments
def attainable_nonpositive(kt, size, deficit):
    """Second moments sum x_u^2 over k^t values x_u in {-size..0} with sum -deficit."""
    vals = set()
    for xs in product(range(0, size + 1), repeat=kt):
        if sum(xs) == deficit:
            vals.add(sum(x * x for x in xs))
    return sorted(vals)


att = attainable_nonpositive(4, 3, 3)
q_, r_ = divmod(3, 3)
check("Appendix D: at k^t = 4, |S| = 3, -sigma_t(S) = 3 the attainable values are exactly 3, 5, 9",
      att == [3, 5, 9])
check("Appendix D: 7 is not attainable and lies below the threshold 9 = q|S|^2 + r^2 = |S|(-sigma_t)",
      7 not in att and q_ * 9 + r_ * r_ == 9 and 3 * 3 == 9)
check("Appendix D: the shortfall 9 - 5 = 4 = 2(|S| - 1)", 9 - max(v for v in att if v < 9) == 2 * (3 - 1))

# ---------------------------------------------------------------- Appendix D: the gap witness
ag = {0: 0, 1: 0, 2: 0, 3: 1}
bg = {0: 2, 1: 3, 2: 3, 3: 0}
lettersg = [ag, bg]
indg = [sum(1 for f in lettersg for q in range(n4) if f[q] == r) for r in range(n4)]
xs = sorted(len(pre({3}, list(u), n4)) - 1 for u in product(lettersg, repeat=2))
check("Appendix D: the gap witness is synchronizing and strongly connected, with deviation d = 4",
      is_synchronizing(lettersg, n4) and is_strongly_connected(lettersg, n4)
      and sum(abs(x - 2) for x in indg) == 4)
check("Appendix D: S = {3} at t = 2 has x_u = -1,-1,0,0 while minext(S) = 1",
      xs == [-1, -1, 0, 0] and minext_of({3}, lettersg, n4, 4) == 1)
check("Section 6.6: on the multiset -1,-1,0,0 the second moment is 2 > 0 although no x_u > 0",
      sum(x * x for x in xs) == 2 and max(xs) <= 0)

print(f"\n{len(rows)} rows, {rows.count(False)} FAILED", flush=True)
sys.exit(min(rows.count(False), 255))
