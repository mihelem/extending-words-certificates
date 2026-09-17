"""boundary_classes.py -- the pairs attaining the least bias threshold 2/3 at n = 5, 6, 7: exact thresholds,
isomorphism classes, and the factorisation of the excess in each class

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix C: over every stuck subset of every synchronizing strongly connected binary automaton at n = 5, 6, 7 the
    minimum of t* is exactly 2/3, attained by 9, 8 and 116 pairs (automaton, subset, biased letter) which fall into
    one, one and four isomorphism classes, and no pair has t* in (1/2, 2/3); the two-letter automata underlying the
    first two witnesses of Proposition 8 are two of these six classes; in every attaining pair the light letter is a
    permutation and the heavy letter has deficiency 1 or 2; and for each class n hat e_t(S) - |S| hat e_t(Q), in the
    matrix-tree normalisation of e_t, is (3t-2) times a monomial c t^i (1-t)^j.
  Appendix A: the 133 attaining pairs of the bias census at n <= 7 "were re-verified exactly, with the value 2/3
    established as an exact root".
Input:    the outputs of bias_census.c at n = 5, 6 and 7 (every part, each file once); their EXTREMAL lines are the
  pairs whose grid threshold lies in bin 67, the bin that holds 2/3 (bias_census_exact.c BOUNDARY lines are also read).
Method:   exact rational arithmetic (exact_lib.py).  Six class representatives symbolically in t (sympy): stuckness,
  strong connectivity, synchronization, the light letter a permutation, the deficiency of the heavy letter, the excess
  n hat e_t(S) - m hat e_t(Q) factored and compared with (3t-2) c t^i (1-t)^j, its sign on [1/2, 2/3].  Every census
  line: the excess polynomial by interpolation of matrix-tree cofactors at rational t, its exact value at t = 2/3 and
  its real roots in [1/2, 2/3] (sympy), and a canonical form under simultaneous conjugation of (heavy letter, light
  letter, S) by all n! permutations, which sorts the lines into isomorphism classes.
Usage:    python boundary_classes.py BC5.out BC6_part0.out BC6_part1.out BC7_part0.out BC7_part1.out
Output:   the computed values, and one [PASS]/[FAIL] line per checked statement; last line "N rows, M FAILED";
  exit status = number of failed rows.
Runtime:  about 20 seconds.
Requires: Python 3, sympy; exact_lib.py in the same directory.
"""
import sys, os, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from itertools import permutations
import sympy as sp
from exact_lib import *

t = sp.symbols('t')
FAIL = 0
ROWS = 0


def check(label, ok):
    global FAIL, ROWS
    ROWS += 1
    print(("[PASS] " if ok else "[FAIL] ") + label)
    if not ok:
        FAIL += 1


def sym_tree_weights(letters, weights):
    n = len(letters[0])
    L = sp.eye(n)
    for x, w in zip(letters, weights):
        for p in range(n):
            L[p, x[p]] -= w
    out = []
    for q in range(n):
        minor = L.copy()
        minor.row_del(q)
        minor.col_del(q)
        out.append(sp.factor(minor.det(method='berkowitz')))
    return out


classes = [
    # (n, heavy a (t), light b (1-t), S, (c,i,j) of the monomial)
    (5, [0, 2, 1, 1, 3], [3, 1, 4, 0, 2], {2, 4}, (1, 2, 1)),
    (6, [0, 0, 1, 3, 3, 4], [1, 4, 3, 5, 2, 0], {0, 2, 5}, (3, 1, 2)),
    (7, [0, 0, 2, 4, 3, 3, 5], [1, 4, 5, 3, 6, 2, 0], {0, 1}, (1, 2, 3)),
    (7, [0, 0, 2, 4, 3, 3, 5], [6, 0, 5, 3, 1, 2, 4], {0, 6}, (1, 2, 2)),
    (7, [0, 0, 2, 4, 3, 3, 5], [6, 4, 5, 3, 1, 2, 0], {0, 6}, (1, 3, 2)),
    (7, [0, 2, 3, 1, 1, 4, 5], [4, 1, 6, 3, 0, 5, 2], {3, 5}, (1, 4, 1)),
]
print("=== the six class representatives: matrix-tree excess, symbolic ===")
for idx, (n, a, b, S, cij) in enumerate(classes, 1):
    letters = [a, b]
    m = len(S)
    sc, sy = strongly_connected(letters), synchronizing(letters)
    stuck = minext(S, letters, cap=n - 1) is None
    w = sym_tree_weights(letters, [t, 1 - t])
    B = sp.factor(n * sum(w[q] for q in S) - m * sum(w))
    c, i, j = cij
    target = (3 * t - 2) * c * t ** i * (1 - t) ** j
    e_t = [sp.factor(wq / sum(w)) for wq in w]
    exc = sp.factor(n * sum(e_t[q] for q in S) - m)
    print(f"class {idx}: n={n} heavy a={a} (def {deficiency(a)}, cycle type {cycle_type(a)}), light b={b} "
          f"(permutation={is_permutation(b)}, cycle type {cycle_type(b)}), S={sorted(S)}")
    print(f"  SC={sc} sync={sy} stuck={stuck}")
    print(f"  n hat e(S) - m hat e(Q) = {B}")
    print(f"  n e_t(S) - m = {exc}   hat e(Q) = {sp.factor(sum(w))}")
    check(f"class {idx}: light letter a permutation", is_permutation(b))
    check(f"class {idx}: heavy deficiency in {{1,2}} (is {deficiency(a)})", deficiency(a) in (1, 2))
    check(f"class {idx}: strongly connected, synchronizing, S stuck", sc and sy and stuck)
    check(f"class {idx}: excess == (3t-2) * {c} t^{i} (1-t)^{j}", sp.simplify(B - target) == 0)
    # t* = 2/3 exactly: excess < 0 on [1/2, 2/3), = 0 at 2/3, > 0 just above
    vals_below = [exc.subs(t, sp.Rational(1, 2) + sp.Rational(k, 60)) for k in range(0, 10)]
    check(f"class {idx}: excess < 0 at t = 1/2 + k/60 (k<10), = 0 at 2/3, > 0 at 0.7",
          all(v < 0 for v in vals_below) and exc.subs(t, sp.Rational(2, 3)) == 0 and exc.subs(t, sp.Rational(7, 10)) > 0)

print()
print("=== the attaining pairs of the census outputs: exact thresholds and isomorphism classes ===")
paths = sys.argv[1:]
pat = re.compile(r"(?:EXTREMAL|BOUNDARY) n=(\d) a=\[([\d,]+)\] b=\[([\d,]+)\]\s+S=\{([\d,]+),?\} biased=(\w)")


def canon(heavy, light, S):
    n = len(heavy)
    best = None
    for perm in permutations(range(n)):
        h = [0] * n
        l = [0] * n
        for p in range(n):
            h[perm[p]] = perm[heavy[p]]
            l[perm[p]] = perm[light[p]]
        key = (tuple(h), tuple(l), tuple(sorted(perm[q] for q in S)))
        if best is None or key < best:
            best = key
    return best


found_classes = set()
for n in (5, 6, 7):
    triples = []
    used = None
    for path in paths:
        if not os.path.exists(path):
            continue
        got = []
        with open(path) as f:
            for ln in f:
                m = pat.match(ln.strip())
                if m and int(m.group(1)) == n:
                    a = list(map(int, m.group(2).split(',')))
                    b = list(map(int, m.group(3).split(',')))
                    S = set(int(s) for s in m.group(4).split(',') if s != '')
                    heavy, light = (a, b) if m.group(5) == 'a' else (b, a)
                    got.append((heavy, light, S))
        if got:
            triples.extend(got)
            used = (used or []) + [os.path.basename(path)]
    print(f"n={n}: {len(triples)} attaining lines read from {used}")
    t0 = time.time()
    exact_23 = 0
    root_in_open = 0
    cls = {}
    for heavy, light, S in triples:
        coeffs = excess_polynomial([heavy, light], lambda tt: [tt, 1 - tt], S, degree=n - 1)
        polyB = sp.Poly([sp.Rational(c.numerator, c.denominator) for c in reversed(coeffs)], t)
        if poly_eval(coeffs, Fraction(2, 3)) == 0:
            exact_23 += 1
        # roots in [1/2, 2/3): count_roots on the closed interval minus the root at 2/3
        cr = polyB.count_roots(sp.Rational(1, 2), sp.Rational(2, 3))
        if cr - (1 if poly_eval(coeffs, Fraction(2, 3)) == 0 else 0) > 0:
            root_in_open += 1
        key = canon(heavy, light, S)
        cls[key] = cls.get(key, 0) + 1
    found_classes.update(cls)
    print(f"  exact excess 0 at t=2/3: {exact_23} of {len(triples)};  lines with a root in [1/2,2/3): {root_in_open};"
          f"  isomorphism classes (simultaneous conjugation of heavy, light, S): {len(cls)} with multiplicities "
          f"{sorted(cls.values(), reverse=True)}  ({time.time() - t0:.1f}s)")
    for key, mult in sorted(cls.items(), key=lambda kv: -kv[1]):
        h, l, Sk = key
        print(f"    class rep: heavy={list(h)} light={list(l)} S={list(Sk)} light_perm={is_permutation(list(l))} "
              f"heavy_def={deficiency(list(h))} raw={mult}")
    expected = {5: (9, 1), 6: (8, 1), 7: (116, 4)}[n]
    check(f"n={n}: {expected[0]} lines, all with t* = 2/3 exactly and nothing in [1/2,2/3)",
          len(triples) == expected[0] == exact_23 and root_in_open == 0)
    check(f"n={n}: {expected[1]} isomorphism class(es)", len(cls) == expected[1])

print()
check("the six class representatives are, up to isomorphism, exactly the classes found in the census lines",
      {canon(a, b, S) for (n, a, b, S, cij) in classes} == found_classes)
check("class 1 is (a,c) of the first witness of Proposition 8, with S={2,4}",
      classes[0][1] == [0, 2, 1, 1, 3] and classes[0][2] == [3, 1, 4, 0, 2] and classes[0][3] == {2, 4})
check("class 3 is (a,b) of the second witness of Proposition 8, with S={0,1}", classes[2][1] == [0, 0, 2, 4, 3, 3, 5] and
      classes[2][2] == [1, 4, 5, 3, 6, 2, 0] and classes[2][3] == {0, 1})
print()
print(f"{ROWS} rows, {FAIL} FAILED")
sys.exit(min(FAIL, 255))
