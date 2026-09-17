"""grading.py -- grading of the strict half by length: where sigma_t first becomes positive,
the truncated certificates B_T, and the attainment of minext = t.

Supports, in "Certificates for short extending words in a finite automaton":
  Section 6.4, on the exhaustive synchronizing strongly connected population at n=5
  (32,588 automata; 977,640 proper-subset instances):
    the certificate fires at t=1 on 314,393 instances, and a further 12,064 fire only at
      the full length t=n-1;
    the union of {sigma_t>0}, t<=T, is larger than {B_T>0} by 12,644 instances at T=2 and
      29,396 at T=4;
    against {B_T>=0} neither region contains the other: the union holds 9,108 instances
      at T=2 and 26,826 at T=4 that {B_T>=0} misses (and {B_T>=0} holds 129,294 at T=2 and
      48,976 at T=4 outside the union);
    sigma_t(S)>0 together with minext(S)=t occurs on 314,393, 74,052, 9,338 and 808
      instances at t=1, 2, 3, 4.
  (The boundary-half counts 402, 2,428, 8,528 of Section 6.4 are printed by census.py.)

Definitions: sigma_t(S) = indeg_t(S) - k^t |S| and B_T(S) = sum_{t<=T} k^(T-t) sigma_t(S)
(Section 3), k = 2; minext(S) = least |u| with |S u^-1| > |S|.

Population / convention: as census.py (default filter: synchronizing and strongly
  connected, quotient convention of Appendix A.1); counts are over proper nonempty
  subsets S (instances = population x (2^n - 2)).

Usage:    python grading.py N [--dmax D] [--out FILE]
          The run behind the paper:  python grading.py 5
          (census.py must be importable: keep both files in one directory.)

Output:   one JSON dict on stdout (also written to FILE with --out); lists are indexed
          by t or T (index 0 unused).
            pos_by_t[t]              #{S : sigma_t(S) > 0}
            first_pos[t]             #{S : t = least t' with sigma_t'(S) > 0};
                                     first_pos[1] = 314,393 (fires at t=1)
            none_pos                 #{S : no sigma_t(S) > 0}
            only_full                #{S : sigma_{n-1}(S) > 0, sigma_t(S) <= 0 for t < n-1}
                                     (12,064: fire only at the full length)
            BT_pos[T]                #{S : B_T(S) > 0}
            union_minus_BTpos[T]     #{S in the union of {sigma_t>0}, t<=T, with B_T(S) <= 0}
                                     (T=2: 12,644; T=4: 29,396)
            BTpos_minus_union[T]     #{S with B_T(S) > 0 outside that union} (always 0)
            union_minus_BTge0[T]     #{S in the union with B_T(S) < 0} (T=2: 9,108; T=4: 26,826)
            BTge0_minus_union[T]     #{S with B_T(S) >= 0 outside the union}
                                     (T=2: 129,294; T=4: 48,976)
            gain_first[t]            #{S in C# with B(S) < 0 whose first positive sigma is at t}
            slack[t][v]              #{S : first positive sigma at t, t - minext(S) = v};
                                     slack[t]["0"] = #{S : sigma_t(S) > 0, minext(S) = t}
                                     = 314,393, 74,052, 9,338, 808 at t = 1..4

Runtime:  about 2 s at n=5 (one core).

Requires: Python 3.8+, numpy; census.py from this directory.
"""
import json
import sys
import time

import numpy as np

import census as E


def run(n, dmax=None, batch=40000):
    t0 = time.time()
    A, B, dev = E.build_corpus(n, dmax, "syncsc")
    N = A.shape[0]
    out = {"n": n, "dmax": dmax, "population": int(N),
           "convention": "quotient (a over one representative per conjugacy class, "
                         "b over all n^n maps)",
           "pos_by_t": [0] * n, "first_pos": [0] * (n + 1), "none_pos": 0,
           "only_full": 0, "BT_pos": [0] * n,
           "union_minus_BTpos": [0] * n, "BTpos_minus_union": [0] * n,
           "union_minus_BTge0": [0] * n, "BTge0_minus_union": [0] * n,
           "gain_first": [0] * n, "slack": {}}
    for st in range(0, N, batch):
        en = min(N, st + batch)
        bt = E.Batch(n, A[st:en], B[st:en])
        M = bt.M
        sig, Bs = bt.sigmas()
        pc = bt.pc
        proper = (pc > 0) & (pc < n)
        pr = proper[None, :]
        # minext for every proper subset
        minext = np.full((bt.N, M), E.INF, dtype=np.int64)
        for s in range(1, n):
            tg = np.zeros((bt.N, M), dtype=bool)
            tg[:, pc > s] = True
            minext = np.where((pc == s)[None, :], bt.dists(tg, cap=4 * n), minext)
        first = np.full((bt.N, M), 0, dtype=np.int64)     # 0 == never positive
        for t in range(n - 1, 0, -1):
            first = np.where((sig[t - 1] > 0), t, first)
        for t in range(1, n):
            out["pos_by_t"][t] += int(((sig[t - 1] > 0) & pr).sum())
            out["first_pos"][t] += int(((first == t) & pr).sum())
        out["none_pos"] += int(((first == 0) & pr).sum())
        onlyfull = (sig[n - 2] > 0)
        for t in range(1, n - 1):
            onlyfull &= (sig[t - 1] <= 0)
        out["only_full"] += int((onlyfull & pr).sum())
        # truncated certificates, and their comparison with the union of the strict
        # half-spaces {sigma_t > 0}, t <= T
        for T in range(1, n):
            BT = np.zeros((bt.N, M), dtype=np.int64)
            for t in range(1, T + 1):
                BT += (2 ** (T - t)) * sig[t - 1]
            out["BT_pos"][T] += int(((BT > 0) & pr).sum())
            uni = (sig[:T] > 0).any(axis=0)
            out["union_minus_BTpos"][T] += int((uni & ~(BT > 0) & pr).sum())
            out["BTpos_minus_union"][T] += int(((BT > 0) & ~uni & pr).sum())
            out["union_minus_BTge0"][T] += int((uni & ~(BT >= 0) & pr).sum())
            out["BTge0_minus_union"][T] += int(((BT >= 0) & ~uni & pr).sum())
        # where C# gains on {B>=0}, by the first positive sigma
        anypos = (sig > 0).any(axis=0)
        allzero = (sig == 0).all(axis=0)
        gain = (anypos | allzero) & (Bs < 0)
        for t in range(1, n):
            out["gain_first"][t] += int((gain & (first == t) & pr).sum())
        # slack of the certificate: t - minext(S) over S whose first positive sigma is at t
        for t in range(1, n):
            sel = (first == t) & pr & (minext < E.INF)
            if sel.any():
                sl = (t - minext[sel])
                h = out["slack"].setdefault(str(t), {})
                for v, c in zip(*np.unique(sl, return_counts=True)):
                    h[str(int(v))] = h.get(str(int(v)), 0) + int(c)
    out["seconds"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":
    n = int(sys.argv[1])
    dmax = None
    outpath = None
    a = sys.argv[2:]
    for i, v in enumerate(a):
        if v == "--dmax":
            dmax = int(a[i + 1])
        if v == "--out":
            outpath = a[i + 1]
    r = run(n, dmax)
    if outpath is not None:
        with open(outpath, "w") as f:
            json.dump(r, f, indent=1)
    print(json.dumps(r, indent=1))
