"""census_d4.py -- exhaustive censuses of minext, rt and beta* by deviation: every
deviation at n=4, 5, 6, and the class {d<=4} at n=7.

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A.1: 19, 47, 130 and 343 conjugacy classes of endofunctions at n=4, 5, 6, 7
      (sequence A001372).
  Appendix A:
    populations 1,240 at n=4 (72 Eulerian), 32,588 at n=5 and 1,122,529 at n=6, at all
      deviations, and 22,079,307 at n=7 on {d<=4};
    Theorem 1 checked with 0 violations at n=5, n=6 and n=7 on {d<=4} (11,042, 186,497 and
      1,853,891 stuck subsets); no never-extendable subset on these populations;
    Corollary 2: 0 complementary pairs stuck on both sides, against 11,042, 186,497 and
      1,853,891 one-sided pairs;
    {beta*=0} coincides with the Eulerian locus, with no disagreement in either direction:
      72, 954, 12,228 and 192,582 automata at n=4..7, 205,836 in total;
    min|root(p)|/k does not depend on k and falls strictly from 2 at n=3 to 1.05427 at
      n=40, exceeding 1 at every size (the root bound in the proof of Theorem 5, at the weights of Theorem 3);
    the maxima of rt, 9 at n=4 and 16 at n=5; max rt = (n-1)^2 is attained at d=2 only, at
      n=5 and n=6 over all deviations and at n=7 over {d<=4};
    the maximum of minext over singletons is n at every even deviation 2 through 8 at n=5;
    on the Eulerian automata (d=0, where B=0) the maxima of minext by subset size are
      3,2,3; 4,4,4,4; 5,4,4,4,5; 6,6,6,6,6,6 at n=4..7 (Section 5.2), so the bound n-1 is
      attained inside {B>=0}.
  Appendix E:
    over {d<=4}, the maximum of minext over subsets of size >= 2 is 14 = 2n at n=7
      (22,079,307 automata), 9 = 2n-1 at n=5 (28,968 automata: one unit of slack) and
      12 = 2n at n=6 (808,403 automata: none);
    max rt 9, 16, 25 at n=4, 5, 6 and 36 over {d<=4} at n=7, attained at d=2;
    at n=5 the maximum of minext over subsets of size 3 is larger on d=4 than on d=2;
    at n=7 the maximum over subsets of size n-1 is larger on d=4 than on {d<=2}.

Definitions (Sections 2, 3): d = sum_q |indeg(q) - 2| (d=0: Eulerian); minext(S) = least
|u| with |S u^-1| > |S|; a proper nonempty S is stuck if minext(S) > n-1; rt = length of a
shortest reset word; beta*_q = B({q}), computed by the closed form of Lemma 2,
beta* = sum_{j<=n-2} (n-1-j) k^(n-2-j) w^T M^j with w = indeg - k.

Population / convention: the quotient convention of Appendix A.1.  Letter a ranges over one
  representative of each conjugacy class of maps [n]->[n] (orbit marking over the codes),
  letter b over all n^n maps; kept: deviation d <= DMAX (DMAX = 2n in legs A and B, which
  keeps every strongly connected automaton, since there d <= 2n-2; DMAX = 4 in leg C),
  strongly connected (bitmask closure of the union digraph, both directions),
  synchronizing (rt finite, by BFS from Q in the image digraph).  Counts are pairs
  (a representative, b).  In the tables, cell i holds deviation d = 2i, split by
  h = 0 (a or b is a permutation) and h = 1 (neither is).

Usage:    python census_d4.py [LEGS] [I K] [--json FILE] [--checkpoint FILE]
            LEGS  letters among A B C E (default ABCE):
                  A  n=4 and n=5, all deviations
                  B  n=6, all deviations
                  C  n=7, {d<=4}
                  E  the root bound, and beta*=0 against d=0 over the legs run in the
                     same call
            I K   leg C on the a-classes whose index is I mod K only (I = 0..K-1, e.g. K
                  parts on K cores); rows that need the whole population are then not
                  checked.  The parts' counts (cand, cnt, extra) add up and their maxima
                  (fmax, rtmax) combine by maximum; they are in the --json output.
            --json FILE        write every row and the per-population tables (keys n4_all,
                               n5_all, n6_all, n7_d4) to FILE
            --checkpoint FILE  leg C: rewrite FILE with the running totals after each a-class
          The run behind the paper:  python census_d4.py ABCE

Output:   one line per checked statement of the paper, [PASS] or [FAIL], stating the
          population and the paper's value; then "N rows, M FAILED, T s".  Exit status =
          number of failed rows (at most 255).  Leg C also prints a progress line every 10
          a-classes.

Runtime:  one core, with numba (compilation included in leg A): leg A 12.5 s, leg B 15.1 s,
          leg C 802 s (13.4 min), leg E under 1 s.

Requires: Python 3.8+, numpy, and numba, which is required: the kernel _sweep is compiled
          with numba.njit (cache=True, so numba may store its compilation cache next to
          this file).
"""
import json
import sys
import time

import numpy as np
from numba import njit

JSON = None
CKPT = None

_rows = []
_data = {}
_t0 = time.time()


def row(tag, ok, detail):
    _rows.append({"row": tag, "ok": bool(ok), "detail": detail})
    print(("[PASS] " if ok else "[FAIL] ") + tag + ": " + detail, flush=True)


def flush():
    _data["rows"] = _rows
    _data["elapsed_s"] = round(time.time() - _t0, 1)
    if JSON is None:
        return
    with open(JSON, "w") as fh:
        json.dump(_data, fh, indent=1, sort_keys=True, default=str)


A001372 = [0, 1, 3, 7, 19, 47, 130, 343, 951]


# --------------------------------------------------------------- class reps

def endofunction_class_reps(n):
    """One representative code per conjugacy class of maps [n]->[n] under S_n.
    Orbit marking: total work is (#classes) * n!, not n^n * n!."""
    import itertools
    N = n ** n
    seen = bytearray(N)
    pw = [n ** i for i in range(n)]
    perms = list(itertools.permutations(range(n)))
    reps = []
    for c in range(N):
        if seen[c]:
            continue
        reps.append(c)
        f = [(c // pw[i]) % n for i in range(n)]
        for s in perms:
            code = 0                              # g = s f s^{-1}
            for q in range(n):
                code += pw[s[q]] * s[f[q]]
            seen[code] = 1
    return reps


def decode(c, n):
    return [(c // (n ** i)) % n for i in range(n)]


def indeg_table(n):
    """IB[c, q] = |{p : f_c(p) = q}| for every code c of a map [n]->[n]."""
    N = n ** n
    IB = np.zeros((N, n), np.int8)
    pw = [n ** i for i in range(n)]
    for c in range(N):
        for i in range(n):
            IB[c, (c // pw[i]) % n] += 1
    return IB


# ------------------------------------------------------------- numba kernel

@njit(cache=True)
def _sweep(n, A, IB, dmax, pc, lowidx, wcoef,
           pre0, pre1, im0, im1, revstart, revlist, dist, queue, mx, Bv,
           beta, vv, nv, inv0, inv1, indeg_a,
           cand, cnt, fmax, rtmax, extra, wit_val, wit_b, wit_k):
    """Sweep every b in [0, n^n) against one a-rep A.

    dc = d // 2 ;  h = 0 if some letter is a permutation else 1.
    extra[]: 0 never-extendable subsets, 1 automata with beta*=0,
             2 beta*=0 with d>0 (would contradict Theorem 3),
             3 d=0 with beta*!=0 (would contradict Theorem 3),
             4 stuck subsets, 5 Theorem 1 violations (stuck with B>=0),
             6 doubly-stuck complementary pairs, 7 one-sided pairs,
             8 automata fully analysed."""
    M = 1 << n
    NB = IB.shape[0]
    B = np.empty(n, np.int64)
    pwr = np.empty(n, np.int64)
    p = 1
    for i in range(n):
        pwr[i] = p
        p *= n
    da = 0
    for q in range(n):
        if indeg_a[q] == 0:
            da += 1
    aperm = 1 if da == 0 else 0
    for q in range(n):
        inv0[q] = 0
    for q in range(n):
        inv0[A[q]] |= 1 << q

    for bc in range(NB):
        d = 0
        for q in range(n):
            t = indeg_a[q] + IB[bc, q] - 2
            d += t if t >= 0 else -t
        if d > dmax:
            continue
        dc = d >> 1
        cand[dc] += 1
        for i in range(n):
            B[i] = (bc // pwr[i]) % n
        db = 0
        for q in range(n):
            if IB[bc, q] == 0:
                db += 1
        h = 0 if (aperm == 1 or db == 0) else 1

        # ---- strong connectivity of the union digraph (bitmask closure)
        R = 1
        while True:
            R2 = R
            for q in range(n):
                if (R >> q) & 1:
                    R2 |= (1 << A[q]) | (1 << B[q])
            if R2 == R:
                break
            R = R2
        if R != M - 1:
            continue
        R = 1
        while True:
            R2 = R
            for q in range(n):
                if ((R >> A[q]) & 1) or ((R >> B[q]) & 1):
                    R2 |= 1 << q
            if R2 == R:
                break
            R = R2
        if R != M - 1:
            continue

        # ---- image tables, then rt by BFS from Q   (sync <=> rt finite)
        im0[0] = 0
        im1[0] = 0
        for S in range(1, M):
            low = S & (-S)
            q = lowidx[low]
            im0[S] = im0[S ^ low] | (1 << A[q])
            im1[S] = im1[S ^ low] | (1 << B[q])
        for S in range(M):
            dist[S] = -1
        head = 0
        tail = 0
        queue[0] = M - 1
        tail = 1
        dist[M - 1] = 0
        rt = -1
        while head < tail:
            S = queue[head]
            head += 1
            if pc[S] == 1:
                rt = dist[S]
                break
            T = im0[S]
            if dist[T] < 0:
                dist[T] = dist[S] + 1
                queue[tail] = T
                tail += 1
            T = im1[S]
            if dist[T] < 0:
                dist[T] = dist[S] + 1
                queue[tail] = T
                tail += 1
        if rt < 0:
            continue

        cnt[dc, h] += 1
        if rt > rtmax[dc, h]:
            rtmax[dc, h] = rt

        # ---- preimage tables
        for q in range(n):
            inv1[q] = 0
        for q in range(n):
            inv1[B[q]] |= 1 << q
        pre0[0] = 0
        pre1[0] = 0
        for S in range(1, M):
            low = S & (-S)
            q = lowidx[low]
            pre0[S] = pre0[S ^ low] | inv0[q]
            pre1[S] = pre1[S ^ low] | inv1[q]

        # ---- reverse adjacency of  S -> S x^{-1}   (counting sort)
        for S in range(M + 1):
            revstart[S] = 0
        for S in range(M):
            revstart[pre0[S] + 1] += 1
            revstart[pre1[S] + 1] += 1
        for S in range(M):
            revstart[S + 1] += revstart[S]
        for S in range(M):
            T = pre0[S]
            revlist[revstart[T]] = S
            revstart[T] += 1
            T = pre1[S]
            revlist[revstart[T]] = S
            revstart[T] += 1
        for S in range(M, 0, -1):
            revstart[S] = revstart[S - 1]
        revstart[0] = 0

        # ---- minext for every proper nonempty S: one reverse BFS per level
        for k in range(1, n):
            for S in range(M):
                dist[S] = -1
            head = 0
            tail = 0
            for S in range(M):
                if pc[S] > k:
                    dist[S] = 0
                    queue[tail] = S
                    tail += 1
            while head < tail:
                T = queue[head]
                head += 1
                for idx in range(revstart[T], revstart[T + 1]):
                    S = revlist[idx]
                    if dist[S] < 0:
                        dist[S] = dist[T] + 1
                        queue[tail] = S
                        tail += 1
            bk = -1
            for S in range(M):
                if pc[S] == k:
                    mx[S] = dist[S]
                    if dist[S] < 0:
                        extra[0] += 1
                    elif dist[S] > bk:
                        bk = dist[S]
            if bk > fmax[dc, h, k]:
                fmax[dc, h, k] = bk
            if k >= 2 and bk > wit_val[dc, h]:
                wit_val[dc, h] = bk
                wit_b[dc, h] = bc
                wit_k[dc, h] = k

        # ---- beta* = sum_j (n-1-j) k^{n-2-j} w^T M^j        (k = 2)
        for q in range(n):
            vv[q] = indeg_a[q] + IB[bc, q] - 2
            beta[q] = 0
        for j in range(n - 1):
            cf = wcoef[j]
            for q in range(n):
                beta[q] += cf * vv[q]
            if j < n - 2:
                for q in range(n):
                    nv[q] = 0
                for q in range(n):
                    nv[A[q]] += vv[q]
                    nv[B[q]] += vv[q]
                for q in range(n):
                    vv[q] = nv[q]
        allzero = 1
        for q in range(n):
            if beta[q] != 0:
                allzero = 0
        if allzero == 1:
            extra[1] += 1
            if d != 0:
                extra[2] += 1
        elif d == 0:
            extra[3] += 1
        Bv[0] = 0
        for S in range(1, M):
            low = S & (-S)
            Bv[S] = Bv[S ^ low] + beta[lowidx[low]]

        # ---- Theorem 1, and Corollary 2 on complementary pairs
        for S in range(1, M - 1):
            if mx[S] > n - 1:
                extra[4] += 1
                if Bv[S] >= 0:
                    extra[5] += 1
            C = (M - 1) ^ S
            if S < C:
                s1 = 1 if mx[S] > n - 1 else 0
                s2 = 1 if mx[C] > n - 1 else 0
                if s1 == 1 and s2 == 1:
                    extra[6] += 1
                elif s1 + s2 == 1:
                    extra[7] += 1
        extra[8] += 1


def _blank(n, ncell):
    return dict(
        cand=np.zeros(ncell, np.int64),
        cnt=np.zeros((ncell, 2), np.int64),
        fmax=np.full((ncell, 2, n), -1, np.int64),
        rtmax=np.zeros((ncell, 2), np.int64),
        extra=np.zeros(16, np.int64),
        wit_val=np.full((ncell, 2), -1, np.int64),
        wit_b=np.zeros((ncell, 2), np.int64),
        wit_k=np.zeros((ncell, 2), np.int64),
        wit_a=np.zeros((ncell, 2), np.int64),
    )


def _merge(dst, src):
    dst["cand"] += src["cand"]
    dst["cnt"] += src["cnt"]
    np.maximum(dst["fmax"], src["fmax"], out=dst["fmax"])
    np.maximum(dst["rtmax"], src["rtmax"], out=dst["rtmax"])
    dst["extra"] += src["extra"]
    for i in range(dst["wit_val"].shape[0]):
        for j in range(2):
            if src["wit_val"][i, j] > dst["wit_val"][i, j]:
                dst["wit_val"][i, j] = src["wit_val"][i, j]
                dst["wit_b"][i, j] = src["wit_b"][i, j]
                dst["wit_k"][i, j] = src["wit_k"][i, j]
                dst["wit_a"][i, j] = src["wit_a"][i, j]


def census(n, dmax, progress=None, reps=None, IB=None):
    reps = reps or endofunction_class_reps(n)
    M = 1 << n
    ncell = dmax // 2 + 1
    pc = np.array([bin(S).count("1") for S in range(M)], np.int64)
    lowidx = np.zeros(M, np.int64)
    for i in range(n):
        lowidx[1 << i] = i
    wcoef = np.array([(n - 1 - j) * 2 ** (n - 2 - j) for j in range(n - 1)],
                     np.int64)
    if IB is None:
        IB = indeg_table(n)
    z = lambda k, t=np.int64: np.zeros(k, t)
    buf = dict(pre0=z(M), pre1=z(M), im0=z(M), im1=z(M), revstart=z(M + 1),
               revlist=z(2 * M), dist=z(M), queue=z(2 * M), mx=z(M), Bv=z(M),
               beta=z(n), vv=z(n), nv=z(n), inv0=z(n), inv1=z(n))
    total = _blank(n, ncell)
    permonly = _blank(n, ncell)
    for ai, c in enumerate(reps):
        A = np.array(decode(c, n), np.int64)
        indeg_a = np.zeros(n, np.int64)
        for q in range(n):
            indeg_a[A[q]] += 1
        acc = _blank(n, ncell)
        _sweep(n, A, IB, dmax, pc, lowidx, wcoef,
               buf["pre0"], buf["pre1"], buf["im0"], buf["im1"],
               buf["revstart"], buf["revlist"], buf["dist"], buf["queue"],
               buf["mx"], buf["Bv"], buf["beta"], buf["vv"], buf["nv"],
               buf["inv0"], buf["inv1"], indeg_a,
               acc["cand"], acc["cnt"], acc["fmax"], acc["rtmax"],
               acc["extra"], acc["wit_val"], acc["wit_b"], acc["wit_k"])
        acc["wit_a"][:, :] = c
        _merge(total, acc)
        if int(np.min(indeg_a)) >= 1:              # a is a permutation
            _merge(permonly, acc)
        if progress is not None:
            progress(ai, c, total)
    return reps, total, permonly


def prof(fmax, cell):
    v = np.max(fmax[cell], axis=0)
    return {k: int(v[k]) for k in range(1, v.shape[0]) if v[k] >= 0}


def pack(n, tot, po, reps):
    ncell = tot["fmax"].shape[0]
    return dict(
        classes=len(reps),
        cand=[int(x) for x in tot["cand"]],
        cnt=[[int(y) for y in x] for x in tot["cnt"]],
        f={2 * i: prof(tot["fmax"], i) for i in range(ncell)},
        f_by_half={2 * i: {h: {k: int(tot["fmax"][i, h, k])
                               for k in range(1, n)} for h in (0, 1)}
                   for i in range(ncell)},
        rtmax=[[int(y) for y in x] for x in tot["rtmax"]],
        extra=[int(x) for x in tot["extra"]],
        permfirst_cnt=[int(x) for x in po["cnt"].sum(axis=1)],
        permfirst_f={2 * i: prof(po["fmax"], i) for i in range(ncell)},
        witnesses={"d%d_h%d" % (2 * i, h): dict(
            value=int(tot["wit_val"][i, h]), k=int(tot["wit_k"][i, h]),
            a=decode(int(tot["wit_a"][i, h]), n),
            b=decode(int(tot["wit_b"][i, h]), n))
            for i in range(ncell) for h in (0, 1)
            if tot["wit_val"][i, h] >= 0})


# ------------------------------------------------------------------- legs

def leg_A():
    t = time.time()
    for n in (4, 5):
        reps, tot, po = census(n, 2 * n)
        row("n=%d" % n, len(reps) == A001372[n],
            "%d conjugacy classes of endofunctions (A001372: %d; Appendix A.1)"
            % (len(reps), A001372[n]))
        _data["n%d_all" % n] = pack(n, tot, po, reps)
    P = _data["n4_all"]
    tots = [sum(x) for x in P["cnt"]]
    row("n=4", sum(tots) == 1240 and tots[0] == 72,
        "all deviations: %d synchronizing strongly connected automata, %d Eulerian "
        "(Appendix A: 1,240, 72 Eulerian)" % (sum(tots), tots[0]))
    e = P["extra"]
    row("n=4", e[1] == 72 and e[2] == 0 and e[3] == 0,
        "beta*=0 on %d automata; beta*=0 with d>0: %d; d=0 with beta*!=0: %d "
        "(Appendix A: 72, no disagreement)" % (e[1], e[2], e[3]))
    rtd = [max(x) for x in P["rtmax"]]
    row("n=4", max(rtd) == 9 and rtd[1] == 9,
        "max rt = %d, attained at d=2 (Appendix A: 9; Appendix E: attained at d=2)"
        % max(rtd))
    f = P["f"]
    row("n=4", f[0] == {1: 3, 2: 2, 3: 3},
        "Eulerian automata (d=0, where B=0): max minext by subset size %s "
        "(Section 5.2: 3,2,3; n-1 = 3 is attained inside {B>=0})" % f[0])
    P = _data["n5_all"]
    d0 = sum(P["cnt"][0])
    d2 = sum(P["cnt"][1])
    row("n=5", (d2, d0) == (12509, 954),
        "synchronizing strongly connected: %d at d=2 (Table A.1: 12,509 non-Eulerian "
        "automata on {d<=2}), %d at d=0 (Section 5.2: 954)" % (d2, d0))
    f = P["f"]
    row("n=5", f[0] == {1: 4, 2: 4, 3: 4, 4: 4},
        "Eulerian automata (d=0, where B=0): max minext by subset size %s "
        "(Section 5.2: 4,4,4,4; n-1 = 4 is attained inside {B>=0})" % f[0])
    row("n=5", f[4][3] > f[2][3],
        "max minext over subsets of size 3: %d on d=4 against %d on d=2 "
        "(Appendix E: larger on d=4)" % (f[4][3], f[2][3]))
    row("n=5", all(f[d].get(1, -1) == 5 for d in (2, 4, 6, 8)),
        "max minext over singletons at d = 2,4,6,8: %s (Appendix A: n = 5 at every even "
        "deviation 2 through 8)" % [f[d].get(1) for d in (2, 4, 6, 8)])
    rtd = [max(x) for x in P["rtmax"]]
    row("n=5", rtd[1] == 16 and all(r < 16 for i, r in enumerate(rtd) if i != 1),
        "max rt = %d = (n-1)^2, attained at d=2 only (Appendix A: 16, at d=2 only)"
        % max(rtd))
    tots = [sum(x) for x in P["cnt"]]
    row("n=5", sum(tots) == 32588 and tots[0] == 954,
        "all deviations: %d synchronizing strongly connected automata, %d Eulerian "
        "(Appendix A: 32,588; Section 5.2: 954)" % (sum(tots), tots[0]))
    m4 = max(max(v for k, v in f[2 * i].items() if k >= 2) for i in range(3))
    row("n=5", sum(tots[:3]) == 28968 and m4 == 2 * 5 - 1,
        "{d<=4}: %d automata; max minext over subsets of size >= 2 = %d = 2n-1 "
        "(Appendix E: 28,968 automata, one unit of slack below 2n = 10)"
        % (sum(tots[:3]), m4))
    e = P["extra"]
    row("n=5", e[5] == 0 and e[0] == 0 and e[4] == 11042,
        "all deviations: Theorem 1 violations (stuck S with B(S)>=0) %d over %d automata "
        "and %d stuck subsets; never-extendable subsets %d (Appendix A: 0 violations, "
        "11,042 stuck subsets, no never-extendable subset)" % (e[5], e[8], e[4], e[0]))
    row("n=5", e[6] == 0 and e[7] == 11042,
        "complementary pairs stuck on both sides %d against %d one-sided "
        "(Corollary 2; Appendix A: 0 against 11,042)" % (e[6], e[7]))
    row("n=5", e[1] == 954 and e[2] == 0 and e[3] == 0,
        "beta*=0 on %d automata; beta*=0 with d>0: %d; d=0 with beta*!=0: %d "
        "(Appendix A: 954, no disagreement)" % (e[1], e[2], e[3]))
    print("leg A %.1fs" % (time.time() - t), flush=True)


def leg_B():
    t = time.time()
    n = 6
    reps, tot, po = census(n, 2 * n)
    _data["n6_all"] = P = pack(n, tot, po, reps)
    row("n=6", len(reps) == A001372[n],
        "%d conjugacy classes of endofunctions (A001372: %d; Appendix A.1)"
        % (len(reps), A001372[n]))
    d0 = sum(P["cnt"][0])
    d2 = sum(P["cnt"][1])
    row("n=6", (d2, d0) == (248233, 12228),
        "synchronizing strongly connected: %d at d=2 (Table A.1: 248,233 non-Eulerian "
        "automata on {d<=2}), %d at d=0 (Section 5.2: 12,228)" % (d2, d0))
    f = P["f"]
    row("n=6", f[0] == {1: 5, 2: 4, 3: 4, 4: 4, 5: 5},
        "Eulerian automata (d=0, where B=0): max minext by subset size %s "
        "(Section 5.2: 5,4,4,4,5; n-1 = 5 is attained inside {B>=0})" % f[0])
    tots = [sum(x) for x in P["cnt"]]
    row("n=6", sum(tots) == 1122529 and tots[0] == 12228,
        "all deviations: %d synchronizing strongly connected automata, %d Eulerian "
        "(Appendix A: 1,122,529; Section 5.2: 12,228)" % (sum(tots), tots[0]))
    m4 = max(max(v for k, v in f[2 * i].items() if k >= 2) for i in range(3))
    row("n=6", sum(tots[:3]) == 808403 and m4 == 2 * n,
        "{d<=4}: %d automata; max minext over subsets of size >= 2 = %d = 2n "
        "(Appendix E: 808,403 automata, no slack below 2n = 12)" % (sum(tots[:3]), m4))
    rtd = [max(x) for x in P["rtmax"]]
    row("n=6", rtd[1] == 25 and all(r < 25 for i, r in enumerate(rtd) if i != 1),
        "max rt = %d = (n-1)^2, attained at d=2 only (Appendix A: at d=2 only; "
        "Appendix E: 25)" % max(rtd))
    e = P["extra"]
    row("n=6", e[5] == 0 and e[0] == 0 and e[4] == 186497,
        "all deviations: Theorem 1 violations (stuck S with B(S)>=0) %d over %d automata "
        "and %d stuck subsets; never-extendable subsets %d (Appendix A: 0 violations, "
        "186,497 stuck subsets, no never-extendable subset)" % (e[5], e[8], e[4], e[0]))
    row("n=6", e[6] == 0 and e[7] == 186497,
        "complementary pairs stuck on both sides %d against %d one-sided "
        "(Corollary 2; Appendix A: 0 against 186,497)" % (e[6], e[7]))
    row("n=6", e[1] == 12228 and e[2] == 0 and e[3] == 0,
        "beta*=0 on %d automata; disagreements with d=0 in either direction %d "
        "(Appendix A: 12,228, no disagreement)" % (e[1], e[2] + e[3]))
    print("leg B %.1fs" % (time.time() - t), flush=True)


def leg_C(shard=None):
    t = time.time()
    n = 7
    reps = endofunction_class_reps(n)
    nclasses = len(reps)
    IB = indeg_table(n)
    if shard is not None:
        i, K = shard
        reps = [c for j, c in enumerate(reps) if j % K == i]
    state = {}

    def prog(ai, c, tot):
        state.update(dict(
            done=ai + 1, ntot=len(reps), shard=shard,
            cand=[int(x) for x in tot["cand"]],
            cnt=[[int(y) for y in x] for x in tot["cnt"]],
            fmax=tot["fmax"].tolist(), rtmax=tot["rtmax"].tolist(),
            extra=[int(x) for x in tot["extra"]],
            wit_val=tot["wit_val"].tolist(), wit_b=tot["wit_b"].tolist(),
            wit_k=tot["wit_k"].tolist(), wit_a=tot["wit_a"].tolist(),
            elapsed_s=round(time.time() - t, 1)))
        if CKPT is not None:
            with open(CKPT, "w") as fh:
                json.dump(state, fh)
        if ai % 10 == 0 or ai < 3:
            print("  a-class %d/%d  cand=%s cnt=%s max=%s  %.1fs"
                  % (ai + 1, len(reps), [int(x) for x in tot["cand"]],
                     [int(x) for x in tot["cnt"].sum(axis=1)],
                     [int(x) for x in tot["wit_val"].max(axis=1)],
                     time.time() - t), flush=True)

    _, tot, po = census(n, 4, progress=prog, reps=reps, IB=IB)
    _data["n7_d4"] = P = pack(n, tot, po, reps)
    P["shard"] = shard
    row("n=7", nclasses == A001372[n],
        "%d conjugacy classes of endofunctions (A001372: %d; Appendix A.1)"
        % (nclasses, A001372[n]))
    d0 = sum(P["cnt"][0])
    d2 = sum(P["cnt"][1])
    full = shard is None
    row("n=7 {d<=4}", (not full) or (d2, d0) == (4873053, 192582),
        "synchronizing strongly connected: %d at d=2 (Table A.1: 4,873,053 non-Eulerian "
        "automata on {d<=2}), %d at d=0 (Section 5.2: 192,582)" % (d2, d0))
    f = P["f"]
    row("n=7 {d<=4}", (not full) or f[0] == {k: 6 for k in range(1, 7)},
        "Eulerian automata (d=0, where B=0): max minext by subset size %s "
        "(Section 5.2: 6,6,6,6,6,6; n-1 = 6 is attained inside {B>=0})" % f[0])
    tots = [sum(x) for x in P["cnt"]]
    row("n=7 {d<=4}", (not full) or (sum(tots) == 22079307 and tots[0] == 192582),
        "%d synchronizing strongly connected automata, %d Eulerian "
        "(Appendix A and E: 22,079,307)" % (sum(tots), tots[0]))
    mall = max(max(v for k, v in f[2 * i].items() if k >= 2)
               for i in range(3) if len(f[2 * i]) > 1)
    row("n=7 {d<=4}", (not full) or mall == 14,
        "max minext over subsets of size >= 2 over the whole class = %d against 2n = 14 "
        "(Appendix E: 14 = 2n)" % mall)
    row("n=7 {d<=4}", (not full) or (f[4].get(6, -1)
                                     > max(f[0].get(6, -1), f[2].get(6, -1))),
        "max minext over subsets of size n-1 = 6: %s on d=4 against %s on {d<=2} "
        "(Appendix E: larger on d=4 than on {d<=2})"
        % (f[4].get(6), max(f[0].get(6, -1), f[2].get(6, -1))))
    rtd = [max(x) for x in P["rtmax"]]
    row("n=7 {d<=4}", (not full) or (rtd[1] == 36 and max(rtd[0], rtd[2]) < 36),
        "max rt = %d = (n-1)^2, attained at d=2 only (Appendix A and E: 36 on {d<=4}, "
        "attained at d=2 only)" % max(rtd))
    e = P["extra"]
    row("n=7 {d<=4}", e[5] == 0 and e[0] == 0 and ((not full) or e[4] == 1853891),
        "Theorem 1 violations (stuck S with B(S)>=0) %d over %d automata and %d stuck "
        "subsets; never-extendable subsets %d (Appendix A: 0 violations, 1,853,891 stuck "
        "subsets, no never-extendable subset)" % (e[5], e[8], e[4], e[0]))
    row("n=7 {d<=4}", e[6] == 0 and ((not full) or e[7] == 1853891),
        "complementary pairs stuck on both sides %d against %d one-sided "
        "(Corollary 2; Appendix A: 0 against 1,853,891)" % (e[6], e[7]))
    row("n=7 {d<=4}", e[2] == 0 and e[3] == 0 and ((not full) or e[1] == 192582),
        "beta*=0 on %d automata; disagreements with d=0 in either direction %d "
        "(Theorem 3; Appendix A: 192,582, no disagreement)" % (e[1], e[2] + e[3]))
    print("leg C %.1fs" % (time.time() - t), flush=True)


def leg_E():
    worst = None
    for k in range(1, 7):
        for n in range(3, 41):
            co = [(n - 1 - j) * k ** (n - 2 - j) for j in range(n - 1)]
            r = np.roots([float(x) for x in reversed(co)])
            if len(r) == 0:
                continue
            m = float(np.min(np.abs(r))) / k
            if worst is None or m < worst[0]:
                worst = (m, n, k)
    row("roots", worst[0] > 1.0 + 1e-9,
        "p(z) = sum_{j<=n-2} (n-1-j) k^{n-2-j} z^j has min |root|/k = %.6f > 1 over "
        "3<=n<=40, 1<=k<=6 (smallest at n=%d, k=%d).  M is non-negative with every row "
        "sum k, so rho(M) = k and no eigenvalue of M is a root of p; p(M) is invertible, "
        "and beta* = w^T p(M) = 0 forces w = 0 (Theorem 5 at the weights of Theorem 3, where q_c = p)"
        % (worst[0], worst[1], worst[2]))
    per_n = {}
    for n in range(3, 41):
        vals = []
        for k in range(1, 7):
            co = [(n - 1 - j) * k ** (n - 2 - j) for j in range(n - 1)]
            r = np.roots([float(x) for x in reversed(co)])
            vals.append(float(np.min(np.abs(r))) / k)
        per_n[n] = vals
    spread = max(max(v) - min(v) for v in per_n.values())
    seq = [min(per_n[n]) for n in range(3, 41)]
    falls = all(seq[i + 1] < seq[i] for i in range(len(seq) - 1))
    row("roots", spread < 1e-9 and falls and abs(seq[0] - 2.0) < 1e-9
        and round(seq[-1], 5) == 1.05427 and min(seq) > 1.0,
        "min |root|/k at each n=3..40: largest difference across k=1..6 %.1e; %.6f at "
        "n=3, %.6f at n=40, strictly decreasing in n: %s (Appendix A: independent of k, "
        "falls strictly from 2 at n=3 to 1.05427 at n=40, above 1 throughout)"
        % (spread, seq[0], seq[-1], falls))
    tot = bad = 0
    keys = []
    for key in ("n4_all", "n5_all", "n6_all", "n7_d4"):
        if key in _data:
            tot += _data[key]["extra"][1]
            bad += _data[key]["extra"][2] + _data[key]["extra"][3]
            keys.append(key)
    all_four = len(keys) == 4 and _data["n7_d4"].get("shard") is None
    row("n=4..7", bad == 0 and tot > 0 and ((not all_four) or tot == 205836),
        "over the populations swept in this run (%s): %d automata with beta* = 0, %d "
        "disagreements with d = 0 in either direction (Appendix A: 205,836 over "
        "n=4, 5, 6 and n=7 on {d<=4}, no disagreement)"
        % (", ".join(keys), tot, bad))


def main():
    global JSON, CKPT
    args = []
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        if argv[i] == "--json" and i + 1 < len(argv):
            JSON = argv[i + 1]
            i += 2
        elif argv[i] == "--checkpoint" and i + 1 < len(argv):
            CKPT = argv[i + 1]
            i += 2
        else:
            args.append(argv[i])
            i += 1
    legs = args[0] if args else "ABCE"
    shard = None
    if len(args) > 2:
        shard = (int(args[1]), int(args[2]))
    print("legs=%s shard=%s" % (legs, shard), flush=True)
    if "A" in legs:
        leg_A()
        flush()
    if "B" in legs:
        leg_B()
        flush()
    if "C" in legs:
        leg_C(shard)
        flush()
    if "E" in legs:
        leg_E()
        flush()
    nf = sum(1 for r in _rows if not r["ok"])
    print("\n%d rows, %d FAILED, %.1fs"
          % (len(_rows), nf, time.time() - _t0), flush=True)
    flush()
    return min(nf, 255)


if __name__ == "__main__":
    sys.exit(main())
