"""exact_lib.py -- exact helpers for the stationary-vector checks: automata, preimages, minext, stationary vectors

Supports, in "Certificates for short extending words in a finite automaton" (imported by witnesses.py,
boundary_classes.py, exact_n8.py and equal_weight_witnesses.py):
  Appendix C, proof of Proposition 8: "the integer eigenvector is recomputed from e^T M = k e^T, strong connectivity
  and synchronization by breadth-first search, and minext(S) by breadth-first search over all preimage sets", with
  exact rational arithmetic; and the matrix-tree normalisation of the stationary vector used for the bias thresholds.

Conventions (Section 2 and Section 7.3 of the paper):
  * a letter x is the list of images of 0..n-1 (x[q] = q.x);  q.u applies the letters of u left to right;
  * S u^{-1} = {q : q.u in S};  so S (xy)^{-1} = (S y^{-1}) x^{-1};
  * minext(S) = least |u| with |S u^{-1}| > |S|;  S is stuck iff minext(S) > n-1;
  * P = sum_x pi_x pi(x) (row-stochastic), e the stationary row vector (e P = e), e(Q) = 1 unless stated;
  * uniform weights: e^T M = k e^T with M = sum_x pi(x), e scaled to coprime positive integers;
    epsilon_q = n e_q - e(Q),  B_e(S) = n e(S) - |S| e(Q);
  * matrix-tree normalisation: hat e_q = (q,q) cofactor of I - P = weighted count of spanning in-trees rooted at q.
Exact arithmetic throughout (fractions.Fraction).

Usage:    from exact_lib import *        (a library; nothing runs on import)
Requires: Python 3 (standard library only).
"""
from fractions import Fraction
from math import gcd
from functools import reduce


# ----------------------------------------------------------------------------------------------- automata
def preimage(T, x):
    """S x^{-1} for the letter x (list of images)."""
    return frozenset(q for q in range(len(x)) if x[q] in T)


def preimage_word(T, u, letters):
    """S u^{-1} for u a sequence of letter indices, q.u read left to right."""
    T = frozenset(T)
    for xi in reversed(u):
        T = preimage(T, letters[xi])
    return T


def image(T, x):
    return frozenset(x[q] for q in T)


def minext(S, letters, cap=None):
    """least |u| with |S u^{-1}| > |S|, by breadth-first search over all preimage sets;
    None if no such word exists (or none within `cap` letters when cap is given)."""
    S = frozenset(S)
    m = len(S)
    seen = {S}
    frontier = [S]
    depth = 0
    while frontier:
        depth += 1
        if cap is not None and depth > cap:
            return None
        nxt = []
        for T in frontier:
            for x in letters:
                U = preimage(T, x)
                if len(U) > m:
                    return depth
                if U not in seen:
                    seen.add(U)
                    nxt.append(U)
        frontier = nxt
    return None


def is_stuck(S, letters):
    n = len(letters[0])
    me = minext(S, letters, cap=n - 1)
    return me is None


def strongly_connected(letters):
    n = len(letters[0])
    fwd = [set() for _ in range(n)]
    bwd = [set() for _ in range(n)]
    for x in letters:
        for p in range(n):
            fwd[p].add(x[p])
            bwd[x[p]].add(p)

    def reach(adj):
        seen = {0}
        st = [0]
        while st:
            p = st.pop()
            for q in adj[p]:
                if q not in seen:
                    seen.add(q)
                    st.append(q)
        return len(seen) == n

    return reach(fwd) and reach(bwd)


def synchronizing(letters):
    """BFS on the power set from Q until a singleton is reached."""
    n = len(letters[0])
    Q = frozenset(range(n))
    if n == 1:
        return True
    seen = {Q}
    frontier = [Q]
    while frontier:
        nxt = []
        for T in frontier:
            for x in letters:
                U = image(T, x)
                if len(U) == 1:
                    return True
                if U not in seen:
                    seen.add(U)
                    nxt.append(U)
        frontier = nxt
    return False


def is_permutation(x):
    return len(set(x)) == len(x)


def deficiency(x):
    return len(x) - len(set(x))


def cycle_type(x):
    """cycle lengths of the functional graph of x (states on cycles), sorted decreasing."""
    n = len(x)
    on_cycle = set()
    for s in range(n):
        seen = []
        p = s
        idx = {}
        while p not in idx:
            idx[p] = len(seen)
            seen.append(p)
            p = x[p]
        cyc = seen[idx[p]:]
        on_cycle.update(cyc)
    lengths = []
    left = set(on_cycle)
    while left:
        s = next(iter(left))
        cyc = [s]
        p = x[s]
        while p != s:
            cyc.append(p)
            p = x[p]
        lengths.append(len(cyc))
        left -= set(cyc)
    return tuple(sorted(lengths, reverse=True))


def compose(x, sigma):
    """(x o sigma)(q) = x[sigma[q]]  -- the paper's a' = a o (1 6) exchanges the images of 1 and 6."""
    return [x[sigma[q]] for q in range(len(x))]


def transposition(n, p, q):
    s = list(range(n))
    s[p], s[q] = s[q], s[p]
    return s


def in_degrees(x):
    n = len(x)
    d = [0] * n
    for p in range(n):
        d[x[p]] += 1
    return d


# ----------------------------------------------------------------------------------------------- linear algebra
def solve(A, b):
    """Gaussian elimination over Fractions; A square nonsingular."""
    n = len(A)
    M = [list(map(Fraction, A[i])) + [Fraction(b[i])] for i in range(n)]
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            raise ZeroDivisionError("singular system")
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
        inv = 1 / M[i][i]
        M[i] = [v * inv for v in M[i]]
        for r in range(n):
            if r != i and M[r][i] != 0:
                f = M[r][i]
                M[r] = [M[r][c] - f * M[i][c] for c in range(n + 1)]
    return [M[i][n] for i in range(n)]


def det(A):
    M = [list(map(Fraction, row)) for row in A]
    n = len(M)
    d = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            d = -d
        d *= M[i][i]
        inv = 1 / M[i][i]
        for r in range(i + 1, n):
            if M[r][i] != 0:
                f = M[r][i] * inv
                M[r] = [M[r][c] - f * M[i][c] for c in range(n)]
    return d


def transition_matrix(letters, weights):
    """P = sum_x w_x pi(x) as a list of rows of Fractions."""
    n = len(letters[0])
    P = [[Fraction(0)] * n for _ in range(n)]
    for x, w in zip(letters, weights):
        for p in range(n):
            P[p][x[p]] += Fraction(w)
    return P


def stationary(letters, weights):
    """row vector e with e P = e and e(Q) = 1 (exact); requires an irreducible chain."""
    n = len(letters[0])
    P = transition_matrix(letters, weights)
    # e_q = sum_p e_p P[p][q]  ->  sum_p (P[p][q] - [p==q]) e_p = 0 ;  drop the last equation for normalisation
    A = [[P[p][q] - (1 if p == q else 0) for p in range(n)] for q in range(n)]
    A[n - 1] = [Fraction(1)] * n
    b = [Fraction(0)] * (n - 1) + [Fraction(1)]
    return solve(A, b)


def integer_vector(e):
    """scale a positive rational vector to coprime positive integers."""
    den = reduce(lambda a, b: a * b // gcd(a, b), [f.denominator for f in e], 1)
    v = [int(f * den) for f in e]
    g = reduce(gcd, v)
    return [x // g for x in v]


def perron_integer(letters):
    """the paper's e: e^T M = k e^T with M = sum_x pi(x), coprime positive integers (uniform weights)."""
    k = len(letters)
    e = stationary(letters, [Fraction(1, k)] * k)
    v = integer_vector(e)
    # independent check of the eigen-equation with integers:  sum_p v_p M[p][q] = k v_q
    n = len(letters[0])
    M = [[0] * n for _ in range(n)]
    for x in letters:
        for p in range(n):
            M[p][x[p]] += 1
    for q in range(n):
        assert sum(v[p] * M[p][q] for p in range(n)) == k * v[q], "eigen-equation failed"
    return v


def B_e(S, e_int, n):
    return n * sum(e_int[q] for q in S) - len(S) * sum(e_int)


def tree_weights(letters, weights):
    """hat e_q = (q,q) cofactor of L = I - P  (matrix-tree theorem: weighted spanning in-trees rooted at q)."""
    n = len(letters[0])
    P = transition_matrix(letters, weights)
    L = [[(1 if p == q else 0) - P[p][q] for q in range(n)] for p in range(n)]
    out = []
    for q in range(n):
        minor = [[L[r][c] for c in range(n) if c != q] for r in range(n) if r != q]
        out.append(det(minor))
    return out


def interpolate(points):
    """Lagrange interpolation over Fractions: points = [(t_i, v_i)] -> coefficients c_0..c_d (low to high)."""
    pts = [(Fraction(t), Fraction(v)) for t, v in points]
    d = len(pts) - 1
    coeffs = [Fraction(0)] * (d + 1)
    for i, (ti, vi) in enumerate(pts):
        # basis polynomial prod_{j != i} (t - t_j)/(t_i - t_j)
        num = [Fraction(1)]
        denom = Fraction(1)
        for j, (tj, _) in enumerate(pts):
            if j == i:
                continue
            num = poly_mul(num, [-tj, Fraction(1)])
            denom *= (ti - tj)
        for k in range(len(num)):
            coeffs[k] += vi * num[k] / denom
    return coeffs


def poly_mul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_eval(c, t):
    t = Fraction(t)
    v = Fraction(0)
    for a in reversed(c):
        v = v * t + a
    return v


def excess_polynomial(letters, weights_of_t, S, degree):
    """B(t) = n hat e_t(S) - |S| hat e_t(Q) as an exact polynomial in t (coefficients low..high), obtained by
    evaluating the cofactors at degree+2 rational points and interpolating (the extra point checks the degree).
    weights_of_t: function t -> list of letter weights."""
    n = len(letters[0])
    m = len(S)
    pts = []
    for i in range(degree + 2):
        t = Fraction(i, degree + 1)
        w = tree_weights(letters, weights_of_t(t))
        pts.append((t, n * sum(w[q] for q in S) - m * sum(w)))
    c = interpolate(pts)
    assert c[-1] == 0, "degree bound violated"
    return c[:-1]


def fmt(v):
    return "(" + ", ".join(str(x) for x in v) + ")"
