"""witnesses.py -- exact verification of the four witnesses of Proposition 8 and of the mechanism they share

Supports, in "Certificates for short extending words in a finite automaton":
  Proposition 8, proof (Appendix C): on Q = {0,...,4} let a = [0,2,1,1,3] and c = [3,1,4,0,2] = (0 3)(2 4).  With the
    three letters a,a,c the automaton is synchronizing and strongly connected, e = (1,4,3,1,1), and S = {2,4} has
    B_e(S) = 5*4 - 2*10 = 0 while minext(S) = 5, the chain {2,4} -> {1} -> {2,3} -> {1,4} -> {1,2} -> {1,2,3} of
    preimages under a,a,a,c,a being a shortest extension; with a three times e = (1,5,4,1,1) and B_e(S) = 1; with a
    once e = (1,3,2,1,1) and B_e(S) = -1.  On Q = {0,...,6} let a = [0,0,2,4,3,3,5], b = [1,4,5,3,6,2,0] and
    a' = [0,5,2,4,3,3,0] = a o (1 6): the three letters are pairwise distinct, the automaton is synchronizing and
    strongly connected, e = (3,1,1,4,3,1,1), and S = {0,1} has B_e(S) = 7*4 - 2*14 = 0 with minext(S) = 7.  The five
    pairwise distinct letters x1,...,x5: synchronizing, strongly connected, e = (5,1,4,4,16,5,5), and S = Q minus {6}
    has B_e(S) = 7*35 - 6*40 = 5 > 0 and minext(S) = 7.
  Appendix C, the mechanism: at weights (t, 1-t) the stationary vector of (a,c) is proportional to
    (1-t, 2-t, 1, 1-t, 1-t) and 5 e_t(S) - 2 is a positive multiple of 3t - 2, so (a,a,c) is (a,c) at weights
    (2/3, 1/3); in the second witness the states 1, 2, 5, 6 have equal stationary weight at every t, so
    e_t pi(a o sigma) = e_t pi(a) for every permutation sigma of them and (a,b,a') has the stationary vector of (a,b)
    at weights (2/3, 1/3); in the third, four letters act on e like one letter against a fifth, weights (4/5, 1/5).
Method:   exact rational arithmetic (exact_lib.py): the integer eigenvector from e^T M = k e^T (checked against the
  integer eigen-equation), strong connectivity and synchronization by breadth-first search, minext(S) by breadth-first
  search over all preimage sets; sympy for the stationary vectors at symbolic t.
Usage:    python witnesses.py
Output:   the computed values, and one [PASS]/[FAIL] line per checked statement; last line "N rows, M FAILED";
  exit status = number of failed rows.
Runtime:  about 7 seconds.
Requires: Python 3, sympy; exact_lib.py in the same directory.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from itertools import permutations
import sympy as sp
from exact_lib import *

FAIL = 0
ROWS = 0


def check(label, ok):
    global FAIL, ROWS
    ROWS += 1
    print(("[PASS] " if ok else "[FAIL] ") + label)
    if not ok:
        FAIL += 1


def report_witness(name, letters, S, e_expected, Be_expected, minext_expected, distinct_expected):
    n = len(letters[0])
    k = len(letters)
    sc = strongly_connected(letters)
    sy = synchronizing(letters)
    e = perron_integer(letters)
    be = B_e(S, e, n)
    me = minext(S, letters)
    distinct = len({tuple(x) for x in letters}) == k
    print(f"{name}: n={n} k={k} letters={[list(x) for x in letters]}")
    print(f"  strongly_connected={sc} synchronizing={sy} pairwise_distinct={distinct}")
    print(f"  integer eigenvector e={fmt(e)} e(Q)={sum(e)}  S={sorted(S)}  e(S)={sum(e[q] for q in S)}  "
          f"B_e(S)=n*e(S)-|S|*e(Q)={n}*{sum(e[q] for q in S)}-{len(S)}*{sum(e)}={be}")
    print(f"  minext(S)={me}  n-1={n-1}  stuck={me is None or me > n-1}")
    check(f"{name}: strongly connected", sc)
    check(f"{name}: synchronizing", sy)
    check(f"{name}: e == {fmt(e_expected)} digit for digit", list(e) == list(e_expected))
    check(f"{name}: B_e(S) == {Be_expected}", be == Be_expected)
    check(f"{name}: minext(S) == {minext_expected}", me == minext_expected)
    check(f"{name}: pairwise distinct == {distinct_expected}", distinct == distinct_expected)
    return e


print("=== the witnesses of Proposition 8, as printed in the paper ===")
a = [0, 2, 1, 1, 3]
c = [3, 1, 4, 0, 2]
print(f"c={c}: cycle type {cycle_type(c)}, permutation={is_permutation(c)}; "
      f"c[0]={c[0]} c[3]={c[3]} c[2]={c[2]} c[4]={c[4]} c[1]={c[1]}")
check("c is the permutation (0 3)(2 4)", is_permutation(c) and c[0] == 3 and c[3] == 0 and c[2] == 4 and c[4] == 2 and c[1] == 1)

S1 = {2, 4}
report_witness("n=5 (a,a,c)", [a, a, c], S1, (1, 4, 3, 1, 1), 0, 5, False)
report_witness("n=5 (a,a,a,c)", [a, a, a, c], S1, (1, 5, 4, 1, 1), 1, 5, False)
print("(a,c) once, not a witness:")
e_ac = perron_integer([a, c])
print(f"  e={fmt(e_ac)}  B_e(S)={B_e(S1, e_ac, 5)}  minext(S)={minext(S1, [a, c])}")
check("(a,c): e == (1,3,2,1,1) and B_e(S) == -1", list(e_ac) == [1, 3, 2, 1, 1] and B_e(S1, e_ac, 5) == -1)

print("quoted chain {2,4}->{1}->{2,3}->{1,4}->{1,2}->{1,2,3} under a,a,a,c,a:")
chain = [frozenset(S1)]
for x, nm in [(a, 'a'), (a, 'a'), (a, 'a'), (c, 'c'), (a, 'a')]:
    chain.append(preimage(chain[-1], x))
print("  " + " -> ".join("{" + ",".join(map(str, sorted(T))) + "}" for T in chain))
expected_chain = [{2, 4}, {1}, {2, 3}, {1, 4}, {1, 2}, {1, 2, 3}]
check("chain matches the paper", [set(T) for T in chain] == expected_chain)
check("chain length 5 equals minext(S)=5 (a shortest extension)", minext(S1, [a, a, c]) == 5 and len(chain[-1]) > 2)
# no shorter extension: BFS says minext = 5; also check no word of length <= 4 grows S in (a,c) alone
check("no extension of length <= 4 in (a,c)", minext(S1, [a, c], cap=4) is None)

print()
a7 = [0, 0, 2, 4, 3, 3, 5]
b7 = [1, 4, 5, 3, 6, 2, 0]
a7p = [0, 5, 2, 4, 3, 3, 0]
print(f"a o (1 6) = {compose(a7, transposition(7, 1, 6))}  (paper: a'={a7p})")
check("a' == a o (1 6)", compose(a7, transposition(7, 1, 6)) == a7p)
S3 = {0, 1}
e3 = report_witness("n=7 (a,b,a')", [a7, b7, a7p], S3, (3, 1, 1, 4, 3, 1, 1), 0, 7, True)

print()
x1 = [5, 3, 2, 4, 4, 0, 6]
x2 = [1, 0, 0, 2, 3, 6, 5]
x3 = [0, 3, 2, 4, 4, 5, 6]
x4 = [0, 3, 2, 4, 4, 6, 5]
x5 = [5, 3, 2, 4, 4, 6, 0]
S4 = set(range(6))
e4 = report_witness("n=7 (x1,...,x5)", [x1, x2, x3, x4, x5], S4, (5, 1, 4, 4, 16, 5, 5), 5, 7, True)

print()
print("=== the mechanism shared by the witnesses (Appendix C) ===")
t = sp.symbols('t')


def sym_stationary(letters, weights):
    n = len(letters[0])
    P = sp.zeros(n, n)
    for x, w in zip(letters, weights):
        for p in range(n):
            P[p, x[p]] += w
    e = sp.symbols('e0:%d' % n)
    eqs = [sp.Eq(sum(e[p] * P[p, q] for p in range(n)), e[q]) for q in range(n - 1)]
    eqs.append(sp.Eq(sum(e), 1))
    sol = sp.solve(eqs, e, dict=True)[0]
    return [sp.simplify(sol[v]) for v in e]


print("first witness (a,c) at weights (t on a, 1-t on c):")
et = sym_stationary([a, c], [t, 1 - t])
print("  e_t =", [sp.factor(v) for v in et])
target = [1 - t, 2 - t, 1, 1 - t, 1 - t]
ratios = [sp.simplify(et[q] / target[q]) for q in range(5)]
print("  e_t / (1-t, 2-t, 1, 1-t, 1-t) =", ratios)
check("e_t proportional to (1-t, 2-t, 1, 1-t, 1-t)", all(sp.simplify(r - ratios[0]) == 0 for r in ratios))
exc = sp.factor(5 * (et[2] + et[4]) - 2)
print("  5 e_t(S) - 2 =", exc, "  = (3t-2) *", sp.factor(exc / (3 * t - 2)))
mult = sp.simplify(exc / (3 * t - 2))
check("5 e_t(S)-2 = (3t-2) * positive multiple on (0,1)",
      all(mult.subs(t, sp.Rational(i, 10)) > 0 for i in range(1, 10)) and sp.simplify(exc - (3 * t - 2) * mult) == 0)
print("  values: t=1/2 ->", exc.subs(t, sp.Rational(1, 2)), " t=2/3 ->", exc.subs(t, sp.Rational(2, 3)),
      " t=3/4 ->", exc.subs(t, sp.Rational(3, 4)))
check("(a,a,c) uniform stationary vector equals e_{2/3} of (a,c)",
      [Fraction(v) for v in stationary([a, a, c], [Fraction(1, 3)] * 3)] ==
      [Fraction(str(sp.nsimplify(v.subs(t, sp.Rational(2, 3))))) for v in et])

print("second witness: e_t of (a,b), weights (t on a, 1-t on b):")
et7 = sym_stationary([a7, b7], [t, 1 - t])
print("  e_t =", [sp.factor(v) for v in et7])
check("states 1,2,5,6 have equal stationary weight at every t",
      all(sp.simplify(et7[q] - et7[1]) == 0 for q in (2, 5, 6)))


def push(e, x):
    n = len(x)
    out = [0] * n
    for p in range(n):
        out[x[p]] += e[p]
    return [sp.simplify(v) for v in out]


base = push(et7, a7)
ok = True
cnt = 0
for perm in permutations([1, 2, 5, 6]):
    sigma = list(range(7))
    for src, dst in zip([1, 2, 5, 6], perm):
        sigma[src] = dst
    if all(sp.simplify(u - v) == 0 for u, v in zip(push(et7, compose(a7, sigma)), base)):
        cnt += 1
    else:
        ok = False
print(f"  e_t pi(a o sigma) == e_t pi(a) for {cnt} of 24 permutations sigma of {{1,2,5,6}}")
check("a o sigma invisible to e_t for every permutation sigma of {1,2,5,6}", ok)
e_tern = stationary([a7, b7, a7p], [Fraction(1, 3)] * 3)
e23 = [Fraction(str(sp.nsimplify(v.subs(t, sp.Rational(2, 3))))) for v in et7]
print(f"  uniform (a,b,a'): e={fmt(e_tern)};  (a,b) at (2/3,1/3): e={fmt(e23)}")
check("three-letter automaton has the stationary vector of (a,b) at weights (2/3,1/3)", e_tern == e23)

print("third witness: four letters acting on e like one letter against a fifth, weights (4/5,1/5):")
e4f = [Fraction(v) for v in e4]
pushes = {}
for nm, x in [('x1', x1), ('x2', x2), ('x3', x3), ('x4', x4), ('x5', x5)]:
    out = [Fraction(0)] * 7
    for p in range(7):
        out[x[p]] += e4f[p]
    pushes[nm] = out
    print(f"  e pi({nm}) = {fmt(out)}")
same = [nm for nm in pushes if pushes[nm] == pushes['x1']]
print(f"  letters with e pi(x) == e pi(x1): {same}")
check("x1,x3,x4,x5 act alike on e and x2 differs", set(same) == {'x1', 'x3', 'x4', 'x5'})
e45 = stationary([x1, x2], [Fraction(4, 5), Fraction(1, 5)])
print(f"  stationary vector of (x1,x2) at weights (4/5,1/5): {fmt(integer_vector(e45))}")
check("(x1,x2) at (4/5,1/5) has stationary vector (5,1,4,4,16,5,5)", integer_vector(e45) == [5, 1, 4, 4, 16, 5, 5])
check("S = Q\\{6} is stuck in the binary (x1,x2) as well", minext(S4, [x1, x2], cap=6) is None)

print()
print(f"{ROWS} rows, {FAIL} FAILED")
sys.exit(min(FAIL, 255))
