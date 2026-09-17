"""equal_weight_witnesses.py -- verification of the two witnesses of Proposition 9 (stuck subsets with B_e(S) = 0 in
two-letter automata at equal letter weights)

Supports, in "Certificates for short extending words in a finite automaton":
  Proposition 9 (i): on Q = {0,...,8} with a = [8,3,4,0,2,7,6,5,0] and b = [0,0,6,4,5,5,2,1,5] the automaton is
    synchronizing and strongly connected, S = {0,1,3,8} has minext(S) = 9, and at equal weights e = (6,2,1,1,1,8,1,4,3),
    so B_e(S) = 9*12 - 4*27 = 0.
  Proposition 9 (ii): on Q = {0,...,9} with a = [8,5,2,3,4,1,7,7,0,4] and b = [0,1,6,4,2,9,3,5,7,8] the automaton is
    synchronizing and strongly connected, S = {4,6,7,9} has minext(S) = 10, and e(S) = (2/5) e(Q) = (|S|/n) e(Q) for
    every weighting of the letters; in particular B_e(S) = 0 at equal weights.
  Appendix C, proof of Proposition 9: the words bbabaaababaaabababb and abbbababbbabababbbababa send every state to 5,
    respectively 7; every word of length at most n-1 has |S u^{-1}| <= 4, and bbababbab, respectively ababababab,
    gives 5; for (ii) Lemma 4 applies with Y = {0,3,6,8,9} and Z = {1,2,4,5,7}: b is a permutation, a fixes 2, 4 and 7
    and swaps 1 and 5, a(Y) = {0,3,4,7,8} = b(Y), and S has two states in each block.  In (i) neither letter is a
    permutation and at every length from 1 to 8 some word shrinks the subset; in (ii) the subset is flat to depth
    7 = n-3, then loses a state on exactly one word of length 8 and on four words of length 9, never more than one.
Method:   letters are lists of images; q.u applies the letters of u left to right; S u^{-1} = {q : q.u in S}.  Every
  word of length <= n-1 (and n) is enumerated and applied letter by letter to every state; strong connectivity and
  synchronization by breadth-first search, minext(S) by breadth-first search over preimage sets, and the integer
  eigenvector from e^T M = k e^T with exact rationals (exact_lib.py); the eigenvector is compared with the in-tree
  counts of the matrix-tree theorem; e(S)/e(Q) for (ii) is solved symbolically in the letter weights (sympy) and at
  twelve rational weightings.
Usage:    python equal_weight_witnesses.py
Output:   per witness a length profile (t, min and max of |S u^{-1}| over the words of length t, the number of words with
  |S u^{-1}| < |S|, and sigma_t(S) = the sum of |S u^{-1}| - |S| over all words u of length t), then one [PASS]/[FAIL] line per checked
  statement; last line "N rows, M FAILED"; exit status = number of failed rows.
Runtime:  about 20 seconds.
Requires: Python 3, sympy; exact_lib.py in the same directory.
"""
import os
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp  # noqa: E402
from exact_lib import (strongly_connected, synchronizing, minext, perron_integer, stationary,  # noqa: E402
                       tree_weights, integer_vector, is_permutation)

ROWS = 0
FAILED = 0


def check(label, ok):
    global ROWS, FAILED
    ROWS += 1
    FAILED += 0 if ok else 1
    print(("[PASS] " if ok else "[FAIL] ") + label)


def act(letters, q, word):
    """q.word, the letters of word (a string over 'ab') applied left to right"""
    for ch in word:
        q = letters["ab".index(ch)][q]
    return q


def pre(letters, S, word):
    """S word^{-1} = {q : q.word in S}"""
    return frozenset(q for q in range(len(letters[0])) if act(letters, q, word) in S)


def profile(letters, S, tmax):
    """for t = 0..tmax: (min, max) of |S u^{-1}| over the words u of length t, the words with |S u^{-1}| < |S|,
    and sigma_t(S) = sum_u (|S u^{-1}| - |S|)"""
    rows = []
    for t in range(tmax + 1):
        sizes = {}
        for tup in product("ab", repeat=t):
            u = "".join(tup)
            sizes[u] = len(pre(letters, S, u))
        below = [u for u, s in sizes.items() if s < len(S)]
        rows.append((t, min(sizes.values()), max(sizes.values()), below, sum(s - len(S) for s in sizes.values())))
    return rows


def show_profile(rows, S):
    print("   t | min |Su^-1| | max |Su^-1| | words with |Su^-1| < |S| | sigma_t(S)")
    for t, lo, hi, below, sig in rows:
        print("  %2d | %11d | %11d | %9d of %-12d | %d" % (t, lo, hi, len(below), 2 ** t, sig))


def common(tag, letters, S, reset_word, reset_target, grow_word, e_expected):
    """the checks shared by (i) and (ii); returns (profile rows, integer eigenvector)"""
    n = len(letters[0])
    a, b = letters
    print("=" * 100)
    print("%s  n=%d  a=%s  b=%s  S=%s" % (tag, n, a, b, sorted(S)))
    print("=" * 100)
    check("%s S is a proper nonempty subset of Q = {0..%d}, |S| = %d" % (tag, n - 1, len(S)), 0 < len(S) < n)
    check("%s strongly connected" % tag, strongly_connected(letters))
    check("%s synchronizing (breadth-first search over image sets)" % tag, synchronizing(letters))
    img = sorted({act(letters, q, reset_word) for q in range(n)})
    print("  image of Q under %s (length %d): %s" % (reset_word, len(reset_word), img))
    check("%s the word %s sends every state to %d" % (tag, reset_word, reset_target), img == [reset_target])
    rows = profile(letters, S, n - 1)
    show_profile(rows, S)
    check("%s every word of length <= n-1 = %d has |S u^{-1}| <= %d (%d words)" % (tag, n - 1, len(S), 2 ** n - 1),
          max(hi for _, _, hi, _, _ in rows) <= len(S))
    g = pre(letters, S, grow_word)
    print("  S %s^{-1} = %s" % (grow_word, sorted(g)))
    check("%s the word %s (length %d) gives |S u^{-1}| = %d" % (tag, grow_word, len(grow_word), len(S) + 1),
          len(grow_word) == n and len(g) == len(S) + 1)
    me = minext(S, letters)
    print("  minext(S) by breadth-first search over preimage sets: %s" % me)
    check("%s minext(S) = %d = n" % (tag, n), me == n)
    e = perron_integer(letters)
    eS, eQ = sum(e[q] for q in S), sum(e)
    print("  equal weights: integer eigenvector e = %s, e(S) = %d, e(Q) = %d, B_e(S) = %d*%d - %d*%d = %d"
          % (tuple(e), eS, eQ, n, eS, len(S), eQ, n * eS - len(S) * eQ))
    check("%s at equal weights e = %s" % (tag, tuple(e_expected)), tuple(e) == tuple(e_expected))
    check("%s e agrees with the in-tree counts of the matrix-tree theorem at weights (1/2, 1/2)" % tag,
          integer_vector(tree_weights(letters, [Fraction(1, 2), Fraction(1, 2)])) == list(e))
    check("%s B_e(S) = %d*%d - %d*%d = 0" % (tag, n, eS, len(S), eQ), n * eS - len(S) * eQ == 0)
    return rows, e


# ------------------------------------------------------------------------------------------------ (i)
a9 = [8, 3, 4, 0, 2, 7, 6, 5, 0]
b9 = [0, 0, 6, 4, 5, 5, 2, 1, 5]
S9 = frozenset({0, 1, 3, 8})
rows9, e9 = common("(i)", [a9, b9], S9, "bbabaaababaaabababb", 5, "bbababbab", (6, 2, 1, 1, 1, 8, 1, 4, 3))
check("(i) e(S) = 12 and e(Q) = 27", sum(e9[q] for q in S9) == 12 and sum(e9) == 27)
check("(i) neither letter is a permutation", not is_permutation(a9) and not is_permutation(b9))
check("(i) at every length t = 1..8 some word shrinks S (min |S u^{-1}| per length: %s)"
      % [lo for _, lo, _, _, _ in rows9[1:]], all(lo < len(S9) for _, lo, _, _, _ in rows9[1:]))

# ------------------------------------------------------------------------------------------------ (ii)
print()
a10 = [8, 5, 2, 3, 4, 1, 7, 7, 0, 4]
b10 = [0, 1, 6, 4, 2, 9, 3, 5, 7, 8]
S10 = frozenset({4, 6, 7, 9})
n10 = 10
rows10, e10 = common("(ii)", [a10, b10], S10, "abbbababbbabababbbababa", 7, "ababababab", (1, 2, 2, 1, 2, 2, 1, 2, 1, 1))

# e(S) = (2/5) e(Q) for every weighting: symbolic in the letter weights
pa, pb = sp.symbols("pi_a pi_b", positive=True)
P = sp.zeros(n10, n10)
for p in range(n10):
    P[p, a10[p]] += pa / (pa + pb)
    P[p, b10[p]] += pb / (pa + pb)
A = (P - sp.eye(n10)).T
A[n10 - 1, :] = sp.ones(1, n10)
rhs = sp.zeros(n10, 1)
rhs[n10 - 1] = 1
esym = A.LUsolve(rhs)
share = sp.simplify(sum(esym[q] for q in S10))
print("  symbolic stationary vector e (normalised to e(Q) = 1) at weights (pi_a, pi_b): %s"
      % [sp.simplify(v) for v in esym])
print("  e(S)/e(Q) = %s" % share)
check("(ii) e(S) = (2/5) e(Q) identically in the letter weights (pi_a, pi_b) (sympy)", sp.simplify(share - sp.Rational(2, 5)) == 0)
weightings = [(1, 1), (1, 2), (2, 1), (3, 5), (5, 3), (7, 2), (1, 100), (100, 1), (13, 17), (41, 1), (1, 41), (6, 35)]
shares = [sum(stationary([a10, b10], [Fraction(wa, wa + wb), Fraction(wb, wa + wb)])[q] for q in S10) for wa, wb in weightings]
check("(ii) e(S)/e(Q) = 2/5 = |S|/n at %d rational weightings, exact" % len(weightings),
      all(s == Fraction(2, 5) for s in shares) and Fraction(len(S10), n10) == Fraction(2, 5))

# Lemma 4's hypotheses
Y = {0, 3, 6, 8, 9}
Z = {1, 2, 4, 5, 7}
check("(ii) Y = {0,3,6,8,9} and Z = {1,2,4,5,7} partition Q", Y | Z == set(range(n10)) and not (Y & Z))
check("(ii) b is a permutation", is_permutation(b10))
check("(ii) a maps Z bijectively onto Z", sorted(a10[q] for q in Z) == sorted(Z))
check("(ii) a fixes 2, 4 and 7 and swaps 1 and 5", a10[2] == 2 and a10[4] == 4 and a10[7] == 7 and a10[1] == 5 and a10[5] == 1)
aY = sorted(a10[q] for q in Y)
bY = sorted(b10[q] for q in Y)
print("  a(Y) = %s (as a list of images of Y), b(Y) = %s" % (aY, bY))
check("(ii) a maps Y bijectively onto b(Y) = {0,3,4,7,8}", aY == bY == [0, 3, 4, 7, 8])
check("(ii) S has two states in each block (|S cap Z| n = %d = |S| |Z|)" % (len(S10 & Z) * n10),
      len(S10 & Y) == 2 and len(S10 & Z) == 2 and len(S10 & Z) * n10 == len(S10) * len(Z))

# the length profile of (ii)
for t in (8, 9):
    print("  words of length %d with |S u^{-1}| < |S|: %s" % (t, rows10[t][3]))
check("(ii) flat to depth 7 = n-3: every word of length <= 7 has |S u^{-1}| = 4",
      all(lo == hi == len(S10) for t, lo, hi, _, _ in rows10[:8]))
check("(ii) at length 8 exactly one word loses a state", len(rows10[8][3]) == 1 and rows10[8][1] == len(S10) - 1)
check("(ii) at length 9 exactly four words lose a state", len(rows10[9][3]) == 4 and rows10[9][1] == len(S10) - 1)
check("(ii) never more than one state lost: min |S u^{-1}| over the words of length <= 9 is 3",
      min(lo for _, lo, _, _, _ in rows10) == len(S10) - 1)

print()
print("%d rows, %d FAILED" % (ROWS, FAILED))
sys.exit(min(FAILED, 255))
