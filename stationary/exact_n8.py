"""exact_n8.py -- the n = 8 permutation-first stratum: the example with threshold 2 - sqrt 2, and every pair with
threshold at most 2/3 re-verified exactly

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix C: on the stratum of the binary n = 8 population whose first letter is a permutation, the automaton with
    a = (0 1)(2 3)(4 5)(6 7) and b = [0,2,3,4,2,6,1,0] has the stuck subset S = {4,5}, with minext(S) = 8, and with
    weight t on b its excess 8 e_t(S) - 2 e_t(Q) is a positive multiple of -(t^2 - 4t + 2): the subset is heavy from
    t = 2 - sqrt 2 ~ 0.586 on.  Over the whole stratum 416 pairs lie below 2/3, 384 of them at 2 - sqrt 2 and 32 at
    the root 0.603 of 2t^3 - 4t^2 + 5t - 2, and none is heavy at t = 1/2.
  Appendix A: the 448 pairs of the n = 8 census with threshold at most 2/3 were re-verified exactly, the thresholds
    being the roots 2 - sqrt 2 of t^2 - 4t + 2 (384 pairs), 0.603 of 2t^3 - 4t^2 + 5t - 2 (32) and 2/3 (32).
Input:    the outputs of bias_census_exact.c on the n = 8 stratum (both parts); their BOUNDARY lines are the pairs
  with grid threshold at most bin 67.
Method:   (1) two pairs symbolically (sympy): the example above, and a pair at the root 0.603 (E2).  (2) For every
  BOUNDARY line, by code independent of the census: strong connectivity, synchronization and stuckness by
  breadth-first search; the exact polynomial n hat e_t(S) - m hat e_t(Q) from Fraction cofactors of I - P at rational t
  and Lagrange interpolation (exact_lib.py); its least real root >= 1/2 and the minimal polynomial of that root; and
  the census's exact integers 6^7 F(1/2) and 6^7 F(2/3) recomputed.
Usage:    python exact_n8.py BCE8_part0.out BCE8_part1.out
Output:   the computed values, and one [PASS]/[FAIL] line per checked statement; last line "N rows, M FAILED";
  exit status = number of failed rows.
Runtime:  about 30 seconds.
Requires: Python 3, sympy; exact_lib.py in the same directory.
"""
import sys, os, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
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


def least_root_ge_half(polyB):
    """least real root >= 1/2 of the sympy Poly B (exact), or None."""
    roots = [r for r in polyB.real_roots() if r >= sp.Rational(1, 2)]
    return min(roots) if roots else None


def named(name, heavy, light, S, expected):
    n = 8
    letters = [heavy, light]
    print(name)
    print(f"  heavy (weight t)   = {heavy}   cycle type {cycle_type(heavy)}  deficiency {deficiency(heavy)}")
    print(f"  light (weight 1-t) = {light}   cycle type {cycle_type(light)}  permutation={is_permutation(light)}")
    sc, sy = strongly_connected(letters), synchronizing(letters)
    me = minext(S, letters)
    print(f"  S={sorted(S)}  strongly_connected={sc}  synchronizing={sy}  minext(S)={me}  (n-1={n-1})")
    check(f"{name}: strongly connected and synchronizing", sc and sy)
    check(f"{name}: minext(S) == 8", me == 8)
    et = sym_stationary(letters, [t, 1 - t])
    F = sp.factor(n * sum(et[q] for q in S) - len(S))
    print(f"  8 e_t(S) - 2 e_t(Q) = {F}")
    check(f"{name}: excess equals {expected}", sp.simplify(F - expected) == 0)
    num, den = sp.fraction(sp.together(F))
    print(f"  numerator {sp.expand(num)}  denominator {sp.expand(den)}")
    dpoly = sp.Poly(den, t)
    print(f"  denominator real roots: {[sp.N(r, 6) for r in dpoly.real_roots()]}  (none in [0,1]: "
          f"{all(not (0 <= r <= 1) for r in dpoly.real_roots())})")
    vals = []
    for i in range(1, 13):
        tt = sp.Rational(i, 13)
        vals.append((tt, F.subs(t, tt)))
    print("  values at t=i/13: " + "  ".join(f"{tt}:{'+' if v > 0 else '-'}{sp.N(abs(v), 3)}" for tt, v in vals))
    v12 = F.subs(t, sp.Rational(1, 2))
    print(f"  value at t=1/2: {v12} = {sp.N(v12, 8)}")
    check(f"{name}: value at t=1/2 is negative", v12 < 0)
    npoly = sp.Poly(num, t)
    tstar = least_root_ge_half(sp.Poly(sp.expand(num), t))
    print(f"  least real root of the numerator >= 1/2: {tstar}  =  {sp.N(tstar, 12)};  minimal polynomial "
          f"{sp.minimal_polynomial(tstar, t)}")
    lo = tstar - sp.Rational(1, 10 ** 6)
    hi = tstar + sp.Rational(1, 10 ** 6)
    print(f"  sign just below t*: {'+' if F.subs(t, lo) > 0 else '-'}   sign just above t*: "
          f"{'+' if F.subs(t, hi) > 0 else '-'}   value at t=2/3: {F.subs(t, sp.Rational(2, 3))}")
    check(f"{name}: negative below t*, positive above", F.subs(t, lo) < 0 and F.subs(t, hi) > 0)
    return tstar


print("=== two n=8 pairs, symbolic ===")
a_inv = [1, 0, 3, 2, 5, 4, 7, 6]  # (0 1)(2 3)(4 5)(6 7)
b1 = [0, 2, 3, 4, 2, 6, 1, 0]
S = {4, 5}
ts1 = named("E1 (the example of Appendix C): a=(0 1)(2 3)(4 5)(6 7), b=[0,2,3,4,2,6,1,0], S={4,5}, weight t on b",
            b1, a_inv, S, -2 * (t ** 2 - 4 * t + 2) / (5 * t ** 2 - 20 * t + 18))
check("E1: t* == 2 - sqrt(2) exactly", sp.simplify(ts1 - (2 - sp.sqrt(2))) == 0)
print()
a_4 = [1, 2, 3, 0, 5, 4, 7, 6]  # (0 1 2 3)(4 5)(6 7)
b2 = [7, 3, 0, 3, 7, 2, 4, 6]
ts2 = named("E2 (a pair at the root 0.603): a=(0 1 2 3)(4 5)(6 7), b=[7,3,0,3,7,2,4,6], S={4,5}, weight t on b",
            b2, a_4, S, -2 * (2 * t ** 3 - 4 * t ** 2 + 5 * t - 2) / (2 * t ** 3 - 4 * t ** 2 + 9 * t - 10))
check("E2: t* is the root 0.603... of 2t^3-4t^2+5t-2 (minimal polynomial)",
      sp.expand(sp.minimal_polynomial(ts2, t)) == sp.expand(2 * t ** 3 - 4 * t ** 2 + 5 * t - 2) and
      abs(sp.N(ts2) - 0.603) < 0.0005)
print()

print("=== every BOUNDARY line of the n=8 census outputs, exact thresholds ===")
pat = re.compile(r"BOUNDARY n=8 a=\[([\d,]+)\] b=\[([\d,]+)\] S=\{([\d,]+),?\} biased=(\w) bin=(\d+) grid_t=([\d.]+) "
                 r"exact6dF_half=(-?\d+) exact6dF_23=(-?\d+) cert=(\d)")
lines = []
for logf in sys.argv[1:]:
    with open(logf) as f:
        for ln in f:
            m = pat.match(ln.strip())
            if m:
                lines.append(m)
print(f"BOUNDARY lines parsed: {len(lines)}")
t0 = time.time()
stats = {}
match_half = match_23 = 0
stuck_cnt = scsy_cnt = heavy_half = 0
light_perm = 0
ctypes = {}
SIX7 = 6 ** 7
for m in lines:
    a = list(map(int, m.group(1).split(',')))
    b = list(map(int, m.group(2).split(',')))
    Sset = set(int(s) for s in m.group(3).split(',') if s != '')
    biased = m.group(4)
    binno = int(m.group(5))
    x_half, x_23 = int(m.group(7)), int(m.group(8))
    heavy, light = (b, a) if biased == 'b' else (a, b)
    letters = [heavy, light]
    if strongly_connected(letters) and synchronizing(letters):
        scsy_cnt += 1
    if minext(Sset, letters, cap=7) is None:
        stuck_cnt += 1
    if is_permutation(light):
        light_perm += 1
    ctypes[cycle_type(light)] = ctypes.get(cycle_type(light), 0) + 1
    coeffs = excess_polynomial(letters, lambda tt: [tt, 1 - tt], Sset, degree=7)
    Bh = poly_eval(coeffs, Fraction(1, 2))
    B23 = poly_eval(coeffs, Fraction(2, 3))
    if Bh * SIX7 == x_half:
        match_half += 1
    if B23 * SIX7 == x_23:
        match_23 += 1
    if Bh >= 0:
        heavy_half += 1
    polyB = sp.Poly([sp.Rational(c.numerator, c.denominator) for c in reversed(coeffs)], t)
    tstar = least_root_ge_half(polyB)
    if tstar is None:
        key = 'none'
    else:
        mp = sp.expand(sp.minimal_polynomial(tstar, t))
        key = str(mp)
    stats.setdefault(binno, {}).setdefault(key, 0)
    stats[binno][key] += 1
print(f"elapsed {time.time() - t0:.1f}s")
print(f"strongly connected and synchronizing: {scsy_cnt} of {len(lines)};  stuck (no growth within 7 letters): "
      f"{stuck_cnt} of {len(lines)};  heavy at t=1/2: {heavy_half} of {len(lines)}")
print(f"6^7 B(1/2) equals the log's exact6dF_half: {match_half} of {len(lines)};  6^7 B(2/3) equals exact6dF_23: "
      f"{match_23} of {len(lines)}")
print(f"light letter a permutation: {light_perm} of {len(lines)};  light cycle types: {ctypes}")
for binno in sorted(stats):
    print(f"bin {binno} ({len([1 for m in lines if int(m.group(5)) == binno])} lines): minimal polynomial of the "
          f"exact threshold t* -> count: {stats[binno]}")
check("all 448 lines are stuck, strongly connected, synchronizing", stuck_cnt == len(lines) == scsy_cnt)
check("both exact6dF integers reproduce on every line", match_half == len(lines) == match_23)
check("no line is heavy at t=1/2", heavy_half == 0)
check("bin 35: 384 lines and every one has t* = 2 - sqrt(2) (minimal polynomial t^2-4t+2)",
      stats.get(35, {}).get('t**2 - 4*t + 2', 0) == 384 and sum(stats.get(35, {}).values()) == 384)
check("bin 42: 32 lines and every one has t* = the root of 2t^3-4t^2+5t-2",
      stats.get(42, {}).get('2*t**3 - 4*t**2 + 5*t - 2', 0) == 32 and sum(stats.get(42, {}).values()) == 32)
check("bin 67: 32 lines and every one has t* = 2/3 exactly",
      stats.get(67, {}).get('3*t - 2', 0) == 32 and sum(stats.get(67, {}).values()) == 32)
below = sum(v for bn in stats if bn < 67 for v in stats[bn].values())
print(f"pairs with t* < 2/3: {below}")
check("416 pairs below 2/3 = 384 + 32", below == 416)

# The census certifies, for every other pair, that the excess is <= 0 on the whole interval [1/2, 2/3]
# (UNCERT lines list the pairs without that certificate).  If each uncertified pair is among the lines
# re-verified exactly above, no threshold below 2/3 can have been missed between grid points.
upat = re.compile(r"UNCERT n=8 a=\[([\d,]+)\] b=\[([\d,]+)\] S=\{([\d,]+),?\} biased=(\w) bin=(\d+)")
uncert, unc_count, heavy_done, done_lines = set(), 0, 0, 0
for logf in sys.argv[1:]:
    with open(logf) as f:
        for ln in f:
            s_ = ln.strip()
            mu = upat.match(s_)
            if mu:
                uncert.add(mu.group(1, 2, 3, 4))
            if s_.startswith("DONE") and "uncertified=" in s_:
                done_lines += 1
                unc_count += int(re.search(r"uncertified=(\d+)", s_).group(1))
                heavy_done += int(re.search(r"heavy_at_half=(\d+)", s_).group(1))
boundary = set(m.group(1, 2, 3, 4) for m in lines)
print(f"pairs without the certificate on [1/2, 2/3]: {unc_count} (UNCERT lines: {len(uncert)}); "
      f"all among the BOUNDARY lines: {uncert <= boundary}")
check("every pair of the census without the certificate that its excess is <= 0 on [1/2, 2/3] is among "
      "the lines re-verified exactly", done_lines >= 1 and len(uncert) == unc_count and uncert <= boundary)
check("the census finds no stuck subset heavy at t = 1/2", done_lines >= 1 and heavy_done == 0)
print()
print(f"{ROWS} rows, {FAIL} FAILED")
sys.exit(min(FAIL, 255))
