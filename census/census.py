"""census.py -- exhaustive census of the regions {B<0}, H#, C# and of the stuck subsets
on binary automata, with the grading, boundary and growth-chain counts.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 6.1: the unfiltered enumeration at n=5 has 146,875 = 31,895 + 82,392 + 32,588
      automata (not synchronizing / synchronizing and not strongly connected /
      synchronizing and strongly connected); the strict half (Corollary 1) has 0 failures
      on each of the three parts; the boundary case B=0 gives no violation over the 82,392
      and 58,060 violations over the 31,895.
  Section 6.2: the largest value of B on a stuck subset is -1 at n=3, 4 and 5.
  Section 6.3: {B<0} holds 138 of 354, 7,724 of 17,360, 463,047 of 977,640 and
      33,481,397 of 69,596,798 proper-subset instances at n=3, 4, 5, 6.
  Section 6.4: the subsets with sigma_t(S)=0 for every t<=n-2 and minext(S)>n-2 number 402,
      2,428 and 8,528 at n=4, 5, 6.
  Section 6.5: passing from {B>=0} to C# shrinks {B<0} by 3.4, 5.8 and 9.1 percent at
      n=4, 5, 6; at n=3 the gain is 0 on all 59 automata.
  Section 8.1: 23,965 of the 32,588 automata at n=5 admit a growth chain from a non-singleton
      one-letter fibre to Q every subset of which has B>=0, every step of length <= n-1.
  Appendix A: populations 59 (8 Eulerian), 1,240 (72 Eulerian), 32,588 and 1,122,529 at
      n=3..6; Theorem 1 with 0 violations at n=5 and n=6 (11,042 and 186,497 stuck subsets);
      no never-extendable subset on these populations; on the synchronizing, not strongly
      connected automata at n=5 never-extendable subsets occur, every one with B(S)<0;
      maximum reset threshold 9 at n=4 and 16 at n=5.

Definitions (Sections 2, 3, 6.5), for a complete automaton on Q = {0..n-1} over k=2 letters
and S a subset of Q:
    sigma_t(S) = indeg_t(S) - k^t |S|,   B(S) = sum_{t=1}^{n-1} k^(n-1-t) sigma_t(S),
    C# = { S : some sigma_t(S) > 0 }  union  { S : every sigma_t(S) = 0 },
    H# = { S : every sigma_t(S) <= 0, some sigma_t(S) != 0 },
minext(S) = least |u| with |S u^-1| > |S|; S is stuck if minext(S) > n-1.

Population / convention: the quotient convention of Appendix A.1.  Letter a ranges over one
  representative of each conjugacy class of maps [n]->[n] under simultaneous relabelling
  (7, 19, 47, 130 classes at n=3, 4, 5, 6; sequence A001372), letter b over all n^n maps;
  then the filter: default synchronizing and strongly connected; --nosync: not
  synchronizing; --syncnotsc: synchronizing and not strongly connected; --dmax D: deviation
  d <= D in addition.  The three filters partition the unfiltered enumeration
  (at n=5, 47 x 3,125 = 146,875 automata).  Every isomorphism class of binary automaton
  occurs; d, synchronization, strong connectivity, minext, rt, sigma_t and B are invariant
  under simultaneous conjugation.

Usage:    python census.py N [--nosync | --syncnotsc] [--dmax D] [--out FILE]
          The runs behind the paper:
            python census.py 3
            python census.py 4
            python census.py 5
            python census.py 5 --nosync
            python census.py 5 --syncnotsc
            python census.py 6

Output:   one JSON dict on stdout (also written to FILE with --out).  Counts are over
          proper nonempty subsets S ("instances"; population x (2^n - 2) of them) unless
          stated otherwise.
            population             automata after the filter (59, 1,240, 32,588, 1,122,529;
                                   31,895 with --nosync and 82,392 with --syncnotsc at n=5)
            dev_strata             automata per deviation d; d=0 is the Eulerian count
                                   (8 at n=3, 72 at n=4)
            stuck                  stuck subsets (11,042 at n=5, 186,497 at n=6)
            stuck_in_Bneg          stuck subsets with B<0 (equal to stuck on synchronizing
                                   automata, by Theorem 1); stuck_in_H likewise for H#
            stuck_maxB             largest B on a stuck subset (Section 6.2: -1)
            never_ext              subsets extended by no word of length <= 4n
                                   (0 on the synchronizing strongly connected populations;
                                   at n=5 the counts are unchanged with the bound 2^n, beyond
                                   which no shortest extending word can reach)
            Bneg                   instances in {B<0} (Section 6.3)
            H                      instances in H#
            Csharp_minus_Bge0      instances in C# but not in {B>=0}; Section 6.5's
                                   percentages are 100 * Csharp_minus_Bge0 / Bneg
            Bge0_not_Csharp        instances in {B>=0} but not in C# (always 0, Section 6.5)
            sigzero_proper         instances with every sigma_t(S) = 0
            grade_strict_fail      pairs (S,t) with sigma_t(S)>0 and minext(S)>t
                                   (Corollary 1 failures; Section 6.1: 0 in each run)
            grade_boundary_fail[T] instances with sigma_t(S)=0 for all t<=T and minext(S)>T;
                                   Section 6.4 reads T = n-2 (402, 2,428, 8,528)
            violations_boundary    instances with B>=0 and minext>n-1 (Theorem 1 violations)
            violations_Beq0        instances with B=0 and minext>n-1 (Section 6.1: 0 with
                                   --syncnotsc, 58,060 with --nosync at n=5)
            chain_np1_B            automata with a growth chain in {B>=0}, steps <= n-1
                                   (Section 8.1: 23,965 at n=5)
            maxrt                  largest reset threshold (9 at n=4, 16 at n=5)
            rtB_mismatch           automata where rt differs from 1 + the distance from the
                                   nearest non-singleton one-letter fibre to Q (always 0)
            violations_with_pos_sigma, violations_Beq0_with_pos_sigma
                                   the two violation counts restricted to S with some
                                   sigma_t(S) > 0 (always 0, by Corollary 1)
            auto_with_sigzero      automata having some proper nonempty S with every
                                   sigma_t(S) = 0 (Eulerian automata included)
            stuck_by_size, minext_max_by_size, Bneg_by_size, H_by_size, gain_by_size
                                   by subset size |S| (index 0 and n unused): stuck subsets,
                                   largest finite minext, {B<0}, H#, C# minus {B>=0}

Runtime:  one core (measured): n=3 and n=4 under 1 s; n=5 3 s; n=5 --nosync 2 s;
          n=5 --syncnotsc 4 s; n=6 230 s.

Requires: Python 3.8+, numpy.
"""
import json
import sys
import time
from itertools import permutations

import numpy as np

INF = 1 << 20


# ------------------------------------------------------------ population ----
def endofunction_reps(n):
    """One representative per conjugacy class of [n]->[n], the code-minimal one.

    Encoding: f  <->  sum_i f[i] * n^i.  Scanning codes upward and marking whole
    orbits makes the first unmarked code the minimum of its orbit.
    """
    pw = [n ** i for i in range(n)]
    N = n ** n
    seen = bytearray(N)
    reps = []
    P = list(permutations(range(n)))
    for code in range(N):
        if seen[code]:
            continue
        f = [(code // pw[i]) % n for i in range(n)]
        orbit = set()
        for p in P:
            g = [0] * n
            for i in range(n):
                g[p[i]] = p[f[i]]
            orbit.add(sum(g[i] * pw[i] for i in range(n)))
        for c in orbit:
            seen[c] = 1
        reps.append(tuple(f))
    return reps


def all_maps(n):
    """All n^n maps as an (n^n, n) int64 array, row i = the map with code i."""
    N = n ** n
    out = np.empty((N, n), dtype=np.int64)
    codes = np.arange(N, dtype=np.int64)
    for i in range(n):
        out[:, i] = (codes // (n ** i)) % n
    return out


def filter_sync_sc(n, a, B, dmax=None):
    """Given letter a (tuple) and all candidate b's (Nb,n), return the surviving
    b-rows plus their deviation.  Filters: deviation <= dmax (if given), then
    synchronizing, then strongly connected.  All three tested from definitions.
    """
    Nb = B.shape[0]
    a = np.asarray(a, dtype=np.int64)

    # --- deviation
    indeg = np.zeros((Nb, n), dtype=np.int64)
    for q in range(n):
        indeg[:, a[q]] += 1
    rows = np.arange(Nb)
    for j in range(n):
        indeg[rows, B[:, j]] += 1
    dev = np.abs(indeg - 2).sum(axis=1)
    keep = np.ones(Nb, dtype=bool) if dmax is None else (dev <= dmax)
    if not keep.any():
        return B[keep], dev[keep]
    B = B[keep]
    dev = dev[keep]
    Nb = B.shape[0]
    rows = np.arange(Nb)

    # --- synchronizing: every unordered pair reaches the diagonal
    pairs = [(p, q) for p in range(n) for q in range(p + 1, n)]
    pidx = {pr: i for i, pr in enumerate(pairs)}
    NP = len(pairs)
    # successor of pair under letter a  (-1 == already merged)
    succ_a = np.empty(NP, dtype=np.int64)
    for i, (p, q) in enumerate(pairs):
        u, v = int(a[p]), int(a[q])
        succ_a[i] = -1 if u == v else pidx[(min(u, v), max(u, v))]
    succ_b = np.empty((Nb, NP), dtype=np.int64)
    for i, (p, q) in enumerate(pairs):
        u = B[:, p]
        v = B[:, q]
        lo = np.minimum(u, v)
        hi = np.maximum(u, v)
        # index of (lo,hi) in the pair list
        idx = (lo * (2 * n - lo - 1)) // 2 + (hi - lo - 1)
        succ_b[:, i] = np.where(u == v, -1, idx)

    good = np.zeros((Nb, NP), dtype=bool)
    good |= (succ_a == -1)[None, :]
    good |= (succ_b == -1)
    ga = np.where(succ_a >= 0, succ_a, 0)
    gb = np.where(succ_b >= 0, succ_b, 0)
    for _ in range(NP):
        nxt = good.copy()
        nxt |= np.where((succ_a == -1)[None, :], True, good[:, ga])
        nxt |= np.where(succ_b == -1, True, good[rows[:, None], gb])
        if np.array_equal(nxt, good):
            break
        good = nxt
    sync = good.all(axis=1)

    # --- strongly connected: reachability closure of q -> a(q), q -> b(q)
    adj = np.zeros((Nb, n), dtype=np.int64)
    for q in range(n):
        adj[:, q] = (1 << a[q]) | (np.int64(1) << B[:, q])
    reach = adj.copy()
    for _ in range(n):
        new = adj.copy()
        for q in range(n):
            acc = adj[:, q].copy()
            for r in range(n):
                bit = (reach[:, q] >> r) & 1
                acc |= np.where(bit == 1, adj[:, r], 0)
            new[:, q] = acc
        if np.array_equal(new, reach):
            break
        reach = new
    full = (1 << n) - 1
    sc = (reach == full).all(axis=1)

    keep2 = sync & sc
    return B[keep2], dev[keep2]


def build_corpus(n, dmax=None, want="syncsc"):
    """Returns (A, Bm, dev): arrays of shape (N,n),(N,n),(N,) in the quotient
    convention.  want in {syncsc, nosync, syncnotsc}."""
    reps = endofunction_reps(n)
    allB = all_maps(n)
    As, Bs, Ds = [], [], []
    for a in reps:
        if want == "syncsc":
            b, d = filter_sync_sc(n, a, allB, dmax)
        else:
            b, d = filter_special(n, a, allB, dmax, want)
        if b.shape[0]:
            As.append(np.tile(np.asarray(a, dtype=np.int64), (b.shape[0], 1)))
            Bs.append(b)
            Ds.append(d)
    if not As:
        return (np.zeros((0, n), np.int64),) * 2 + (np.zeros(0, np.int64),)
    return np.concatenate(As), np.concatenate(Bs), np.concatenate(Ds)


def filter_special(n, a, B, dmax, want):
    """`nosync` = NOT synchronizing; `syncnotsc` = synchronizing and NOT SC."""
    Nb = B.shape[0]
    a = np.asarray(a, dtype=np.int64)
    indeg = np.zeros((Nb, n), dtype=np.int64)
    for q in range(n):
        indeg[:, a[q]] += 1
    rows = np.arange(Nb)
    for j in range(n):
        indeg[rows, B[:, j]] += 1
    dev = np.abs(indeg - 2).sum(axis=1)
    keep = np.ones(Nb, dtype=bool) if dmax is None else (dev <= dmax)
    B0, dev0 = B[keep], dev[keep]
    # the synchronization and strong-connectivity tests of filter_sync_sc, as flags
    Nb0 = B0.shape[0]
    if Nb0 == 0:
        return B0, dev0
    sync, sc = _sync_sc_flags(n, a, B0)
    if want == "nosync":
        m = ~sync
    else:
        m = sync & ~sc
    return B0[m], dev0[m]


def _sync_sc_flags(n, a, B):
    Nb = B.shape[0]
    rows = np.arange(Nb)
    a = np.asarray(a, dtype=np.int64)
    pairs = [(p, q) for p in range(n) for q in range(p + 1, n)]
    pidx = {pr: i for i, pr in enumerate(pairs)}
    NP = len(pairs)
    succ_a = np.empty(NP, dtype=np.int64)
    for i, (p, q) in enumerate(pairs):
        u, v = int(a[p]), int(a[q])
        succ_a[i] = -1 if u == v else pidx[(min(u, v), max(u, v))]
    succ_b = np.empty((Nb, NP), dtype=np.int64)
    for i, (p, q) in enumerate(pairs):
        u, v = B[:, p], B[:, q]
        lo, hi = np.minimum(u, v), np.maximum(u, v)
        idx = (lo * (2 * n - lo - 1)) // 2 + (hi - lo - 1)
        succ_b[:, i] = np.where(u == v, -1, idx)
    good = np.zeros((Nb, NP), dtype=bool)
    good |= (succ_a == -1)[None, :]
    good |= (succ_b == -1)
    ga = np.where(succ_a >= 0, succ_a, 0)
    gb = np.where(succ_b >= 0, succ_b, 0)
    for _ in range(NP):
        nxt = good.copy()
        nxt |= np.where((succ_a == -1)[None, :], True, good[:, ga])
        nxt |= np.where(succ_b == -1, True, good[rows[:, None], gb])
        if np.array_equal(nxt, good):
            break
        good = nxt
    sync = good.all(axis=1)
    adj = np.zeros((Nb, n), dtype=np.int64)
    for q in range(n):
        adj[:, q] = (1 << a[q]) | (np.int64(1) << B[:, q])
    reach = adj.copy()
    for _ in range(n):
        new = adj.copy()
        for q in range(n):
            acc = adj[:, q].copy()
            for r in range(n):
                bit = (reach[:, q] >> r) & 1
                acc |= np.where(bit == 1, adj[:, r], 0)
            new[:, q] = acc
        if np.array_equal(new, reach):
            break
        reach = new
    sc = (reach == ((1 << n) - 1)).all(axis=1)
    return sync, sc


# ------------------------------------------------------- per-batch engine ----
class Batch:
    """All subset-level machinery for a batch of automata, from the definitions.
    Subsets are bitmasks S in [0, 2^n); Q is the mask 2^n - 1."""

    def __init__(self, n, A, B):
        self.n = n
        self.k = 2
        self.M = 1 << n
        self.N = A.shape[0]
        self.A, self.B = A, B
        self.rows = np.arange(self.N)[:, None]
        S = np.arange(self.M, dtype=np.int64)
        self.S = S
        self.pc = np.array([bin(s).count("1") for s in range(self.M)], dtype=np.int64)
        self.bits = np.array([[(s >> q) & 1 for q in range(n)] for s in range(self.M)],
                             dtype=np.int64)          # (M,n)
        # preimage maps  P_x[S] = { q : x(q) in S }
        self.Pa = np.zeros((self.N, self.M), dtype=np.int64)
        self.Pb = np.zeros((self.N, self.M), dtype=np.int64)
        for q in range(n):
            self.Pa |= (((S[None, :] >> A[:, q][:, None]) & 1) << q)
            self.Pb |= (((S[None, :] >> B[:, q][:, None]) & 1) << q)

    # --- reverse BFS: which S reach `target` within L steps
    def within(self, target, L):
        X = target.copy()
        for _ in range(L):
            Y = X | X[self.rows, self.Pa] | X[self.rows, self.Pb]
            if np.array_equal(Y, X):
                break
            X = Y
        return X

    # --- reverse BFS distances to a target set (per automaton), capped
    def dists(self, target, cap):
        d = np.full((self.N, self.M), INF, dtype=np.int64)
        d[target] = 0
        cur = target.copy()
        vis = target.copy()
        for kk in range(1, cap + 1):
            nxt = cur[self.rows, self.Pa] | cur[self.rows, self.Pb]
            new = nxt & ~vis
            if not new.any():
                break
            d[new] = kk
            vis |= new
            cur = new
        return d

    def sigmas(self):
        """Sigma_t(S) for t=1..n-1 -> (n-1, N, M) int64, and B(S) -> (N,M)."""
        n, k = self.n, self.k
        v = np.ones((self.N, n), dtype=np.int64)          # 1^T M^0
        sig = np.empty((n - 1, self.N, self.M), dtype=np.int64)
        Bv = np.zeros((self.N, n), dtype=np.int64)
        for t in range(1, n):
            nv = np.zeros((self.N, n), dtype=np.int64)
            for q in range(n):
                np.add.at(nv, (self.rows[:, 0], self.A[:, q]), v[:, q])
                np.add.at(nv, (self.rows[:, 0], self.B[:, q]), v[:, q])
            v = nv
            g = v - (k ** t)                               # (N,n)
            sig[t - 1] = g @ self.bits.T                   # subset sums
            Bv += (k ** (n - 1 - t)) * g
        Bs = Bv @ self.bits.T
        return sig, Bs

    def fibres(self):
        """The <= 2n one-letter fibres {q}x^-1, as an (N, 2n) index array."""
        out = np.empty((self.N, 2 * self.n), dtype=np.int64)
        for q in range(self.n):
            out[:, q] = self.Pa[:, 1 << q]
            out[:, self.n + q] = self.Pb[:, 1 << q]
        return out


def chain_pass(bt, region, L):
    """Existential: some non-singleton fibre starts a region-chain to Q, all
    steps of length <= L.  `region` is (N,M) bool (Q's own membership ignored).

    A chain is F = X_0, X_1, ..., X_r = Q with F a one-letter fibre {q}x^-1 of
    size >= 2, |X_{i+1}| > |X_i|, every X_i (i < r) in the region, and X_{i+1}
    reachable from X_i by at most L steps X -> X y^-1 of the preimage digraph.
    Returns (pass (N,), good (N,M))."""
    n, M = bt.n, bt.M
    good = np.zeros((bt.N, M), dtype=bool)
    good[:, M - 1] = True
    for s in range(n - 1, 1, -1):
        target = good & (bt.pc > s)[None, :]
        X = bt.within(target, L)
        at_s = (bt.pc == s)[None, :]
        good |= at_s & region & X
    F = bt.fibres()
    ok = np.zeros(bt.N, dtype=bool)
    gf = good[bt.rows, F]                     # (N,2n)
    big = bt.pc[F] >= 2
    ok = (gf & big).any(axis=1)
    return ok, good


# ----------------------------------------------------------------- driver ----
def run(n, dmax=None, want="syncsc", batch=40000):
    t0 = time.time()
    A, B, dev = build_corpus(n, dmax, want)
    N = A.shape[0]
    M = 1 << n
    out = {"n": n, "convention": "quotient (a over one representative per conjugacy class, "
                                 "b over all n^n maps)",
           "filter": want, "dmax": dmax, "population": int(N),
           "dev_strata": {}, "seconds_corpus": round(time.time() - t0, 1)}
    for d in sorted(set(dev.tolist())):
        out["dev_strata"][int(d)] = int((dev == d).sum())
    if N == 0:
        return out

    pc = np.array([bin(s).count("1") for s in range(M)], dtype=np.int64)
    proper = (pc > 0) & (pc < n)

    agg = {
        "stuck": 0, "stuck_in_H": 0, "stuck_in_Bneg": 0, "stuck_maxB": -(1 << 40),
        "never_ext": 0,
        "Bneg": 0, "H": 0, "Csharp_minus_Bge0": 0, "sigzero_proper": 0,
        "Bneg_by_size": [0] * (n + 1), "H_by_size": [0] * (n + 1),
        "stuck_by_size": [0] * (n + 1), "gain_by_size": [0] * (n + 1),
        "auto_with_sigzero": 0, "Bge0_not_Csharp": 0,
        "maxrt": 0, "rtB_mismatch": 0,
        "chain_np1_B": 0,                                          # pass count at L=n-1
        "grade_boundary_fail": [0] * (n + 1),
        "grade_strict_fail": 0,
        "minext_max_by_size": [0] * (n + 1),
        "violations_boundary": 0, "violations_with_pos_sigma": 0,
        "violations_Beq0": 0, "violations_Beq0_with_pos_sigma": 0,
    }

    for st in range(0, N, batch):
        en = min(N, st + batch)
        bt = Batch(n, A[st:en], B[st:en])
        nb = bt.N
        rows = bt.rows

        sig, Bs = bt.sigmas()
        anypos = (sig > 0).any(axis=0)
        allzero = (sig == 0).all(axis=0)
        Csharp = anypos | allzero
        Hsharp = (~anypos) & (~allzero)
        Bge0 = Bs >= 0

        # distance to Q in the preimage digraph -> rt (min over singletons), cross-
        # checked through the one-letter fibres: a shortest reset word ends with a
        # letter x whose fibre {q}x^-1 has size >= 2
        tgt = np.zeros((nb, M), dtype=bool)
        tgt[:, M - 1] = True
        dQ = bt.dists(tgt, cap=4 * n * n)
        sing = np.array([1 << q for q in range(n)])
        rt = dQ[:, sing].min(axis=1)
        F = bt.fibres()
        dF = np.where(bt.pc[F] >= 2, dQ[rows, F], INF)
        rtB = 1 + dF.min(axis=1)
        fin = rt < INF
        agg["rtB_mismatch"] += int((rt[fin] != rtB[fin]).sum())
        if fin.any():
            agg["maxrt"] = max(agg["maxrt"], int(rt[fin].max()))

        # minext for every proper nonempty S
        minext = np.full((nb, M), INF, dtype=np.int64)
        for s in range(1, n):
            tg = np.zeros((nb, M), dtype=bool)
            tg[:, bt.pc > s] = True
            d = bt.dists(tg, cap=4 * n)
            sel = (bt.pc == s)[None, :]
            minext = np.where(sel, d, minext)
        stuck = (minext > n - 1) & proper[None, :]
        agg["stuck"] += int(stuck.sum())
        agg["never_ext"] += int(((minext >= INF) & proper[None, :]).sum())
        agg["stuck_in_H"] += int((stuck & Hsharp).sum())
        agg["stuck_in_Bneg"] += int((stuck & (Bs < 0)).sum())
        if stuck.any():
            agg["stuck_maxB"] = max(agg["stuck_maxB"], int(Bs[stuck].max()))
        for s in range(1, n):
            agg["stuck_by_size"][s] += int((stuck & (bt.pc == s)[None, :]).sum())
            fin = minext[:, bt.pc == s]
            fin = fin[fin < INF]
            if fin.size:
                agg["minext_max_by_size"][s] = max(agg["minext_max_by_size"][s], int(fin.max()))

        # region sizes
        pr = proper[None, :]
        agg["Bneg"] += int(((Bs < 0) & pr).sum())
        agg["H"] += int((Hsharp & pr).sum())
        agg["Csharp_minus_Bge0"] += int((Csharp & ~Bge0 & pr).sum())
        agg["Bge0_not_Csharp"] += int((Bge0 & ~Csharp & pr).sum())
        sz = allzero & pr
        agg["sigzero_proper"] += int(sz.sum())
        agg["auto_with_sigzero"] += int(sz.any(axis=1).sum())
        for s in range(1, n):
            at = (bt.pc == s)[None, :]
            agg["Bneg_by_size"][s] += int(((Bs < 0) & at).sum())
            agg["H_by_size"][s] += int((Hsharp & at).sum())
            agg["gain_by_size"][s] += int((Csharp & ~Bge0 & at).sum())

        # the strict half, Corollary 1 (no hypothesis): sigma_t>0 must force minext<=t
        for t in range(1, n):
            bad = (sig[t - 1] > 0) & (minext > t) & pr
            agg["grade_strict_fail"] += int(bad.sum())
        # the boundary half: sigma_t=0 for all t<=T  and  minext>T
        for T in range(1, n):
            az = (sig[:T] == 0).all(axis=0)
            bad = az & (minext > T) & pr
            agg["grade_boundary_fail"][T] += int(bad.sum())

        # Theorem 1 (0 on synchronizing automata) and its boundary case B=0
        viol = Bge0 & (minext > n - 1) & pr
        agg["violations_boundary"] += int(viol.sum())
        agg["violations_with_pos_sigma"] += int((viol & anypos).sum())
        viol0 = (Bs == 0) & (minext > n - 1) & pr
        agg["violations_Beq0"] += int(viol0.sum())
        agg["violations_Beq0_with_pos_sigma"] += int((viol0 & anypos).sum())

        # the growth chain of Section 8.1: region {B>=0}, every step <= n-1
        ok, _ = chain_pass(bt, Bge0, n - 1)
        agg["chain_np1_B"] += int(ok.sum())

    out.update(agg)
    out["seconds_total"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":
    n = int(sys.argv[1])
    dmax = None
    want = "syncsc"
    outpath = None
    args = sys.argv[2:]
    i = 0
    while i < len(args):
        if args[i] == "--dmax":
            dmax = int(args[i + 1]); i += 2
        elif args[i] == "--out":
            outpath = args[i + 1]; i += 2
        elif args[i] == "--nosync":
            want = "nosync"; i += 1
        elif args[i] == "--syncnotsc":
            want = "syncnotsc"; i += 1
        else:
            i += 1
    r = run(n, dmax, want)
    if outpath is not None:
        with open(outpath, "w") as f:
            json.dump(r, f, indent=1)
    print(json.dumps(r, indent=1))
