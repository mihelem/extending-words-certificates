"""run.py -- run the Python implementation (engine.py) on one population, write its JSON file

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: the Python side of "two implementations, one in C and one in
    Python, ... agreeing on 96 of 96 compared integer fields across four
    populations in both counting conventions": binary n=3, 4, 5 and ternary n=4,
    all deviations, compared field by field by ../compare_engines.py.  Of the
    subset counts below, those compared are Hsharp, Hsharp_qcert,
    Hsharp_qcertplus, stuck, stuck_qcert, stuck_qcertplus,
    gain_Csharp_minus_Bge0, Blt0, Bge0, Csharp, sigma_zero, boundary_nograde
    (the quantities of Sections 6.3 to 6.6).
Population / convention: see engine.py.  Stored populations: "syncSC"
  (synchronizing and strongly connected: the one the paper uses) and further
  "unfiltered", "syncSC_nonEuler", "syncSC_d2", "syncSC_d2_nonEuler",
  "sync_notSC", "notsync", "eulerian_syncSC"; each with "q" (quotient) and "l"
  (labelled) weights.
Usage:    python run.py n k tag outdir [--reps i j] [--nocheck] [--maxbatch B]
          writes outdir/tag.json.  The runs compared with the C program:
            python run.py 3 2 n3_all OUT
            python run.py 4 2 n4_all OUT
            python run.py 5 2 n5_all OUT
          and the ternary n=4 population in three pieces (first-letter class
          representatives 0-6, 7-12 and 13-18 of the 19), then merged:
            python run.py 4 3 n4k3_part0 OUT --reps 0 7
            python run.py 4 3 n4k3_part1 OUT --reps 7 13
            python run.py 4 3 n4k3_part2 OUT --reps 13 19
            python merge.py OUT n4k3_all n4k3_part0 n4k3_part1 n4k3_part2
          --reps i j   use only the first-letter representatives i..j-1
          --nocheck    skip the pair-automaton computation of sum x_u^2
          --maxbatch B automata per numpy batch
Output:   outdir/tag.json with n, k, tag, wall_seconds,
          automata_enumerated_quotient, repslice, identity_instances_checked and
          identity_disagreements (the two computations of sum x_u^2), and
          populations -> name -> q|l -> {aut, sub, prof, hor}: "aut" automaton
          counts (n_aut, n_nonEuler, n_euler, n_devD), "sub" counts of proper
          nonempty subsets, "prof" maxima per subset size j (keys "name|j"),
          "hor" counts per length t (keys "name|t").  Subset counts: n_sub,
          Csharp, Hsharp, sigma_zero, anypos (some sigma_t > 0), Bge0, Bgt0, Beq0,
          Blt0, gain_Csharp_minus_Bge0 (in C# with B < 0), stuck (minext > n-1),
          Hsharp_qcert / Hsharp_qcertplus (in H#, (Q-CERT) / (Q-CERT+) fires at
          some t <= n-1), hardcore_Blt0_qcert(plus), stuck_qcert(plus),
          qcert_any, qcertplus_any, minext_infinite, boundary_nograde
          (sigma_t = 0 for t <= n-2 and minext > n-2), doubly_stuck_pairs2x
          (S and its complement both stuck, each pair counted twice), and the
          per-size counts *_size{j}.
          One line on stdout with the file name, wall time and automata count.
Runtime:  one core: n=3 and n=4 under 2 s each; n=5 2 to 4 minutes and each
          ternary n=4 piece 2 to 4.5 minutes (lower figures on an idle machine,
          higher ones measured with other jobs running).
Requires: Python 3 (tested with 3.10) and numpy (tested with 2.2).
"""
import json
import os
import sys
import time
from math import factorial

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from engine import (conj_reps, indeg1_fast, is_strongly_connected,
                    is_synchronizing, subset_stats, population,
                    popcount_table)

BIG = 10 ** 6


class Acc:
    """weighted accumulator for one named population"""

    def __init__(self, n):
        self.n = n
        self.aut = {}          # key -> weight
        self.sub = {}          # key -> weight
        self.prof = {}         # (name, j) -> max
        self.profcnt = {}      # (name, j) -> weight of witnesses at the max
        self.hor = {}          # (name, t) -> weight

    def a(self, key, w):
        self.aut[key] = self.aut.get(key, 0) + int(w)

    def s(self, key, w):
        self.sub[key] = self.sub.get(key, 0) + int(w)

    def h(self, key, t, w):
        self.hor[(key, int(t))] = self.hor.get((key, int(t)), 0) + int(w)

    def p(self, name, j, v):
        k = (name, int(j))
        if k not in self.prof or v > self.prof[k]:
            self.prof[k] = int(v)

    def dump(self):
        return dict(
            aut=self.aut, sub=self.sub,
            prof={f"{a}|{b}": v for (a, b), v in sorted(self.prof.items())},
            hor={f"{a}|{b}": v for (a, b), v in sorted(self.hor.items())},
        )


def qthresholds(sig, sz, k, t):
    """returns (thr_QCERT, thr_QCERTplus) as int64 arrays.
    m = -sigma_t, c = |S|.  m<0 -> threshold -1 (certificate fires, correctly:
    sigma_t>0 already implies some x_u>0)."""
    m = -sig
    c = sz
    thr = c * m
    q = np.where(m >= 0, m // np.maximum(c, 1), 0)
    r = np.where(m >= 0, m - q * c, 0)
    thrp = q * c * c + r * r
    thr = np.where(m >= 0, thr, -1)
    thrp = np.where(m >= 0, thrp, -1)
    return thr, thrp


def run(n, k, tag, outdir, do_check=True, maxbatch=None, repslice=None):
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()
    NS = 1 << n
    pc = popcount_table(n).astype(np.int64)
    proper = np.array([0 < pc[m] < n for m in range(NS)])
    pidx = np.where(proper)[0]
    szv = pc[pidx]                                   # (P,)
    nf = factorial(n)
    pos = {int(m): i for i, m in enumerate(pidx)}
    compidx = np.array([pos[(NS - 1) ^ int(m)] for m in pidx])

    pops = {}
    for name in ["unfiltered", "syncSC", "syncSC_nonEuler", "syncSC_d2",
                 "syncSC_d2_nonEuler", "sync_notSC", "notsync", "eulerian_syncSC"]:
        pops[name] = {"q": Acc(n), "l": Acc(n)}

    ident_bad = 0
    ident_seen = 0
    naut_seen = 0

    tmax_ext = 6 * n + 8
    for delta, wl in population(n, k, batch=maxbatch, repslice=repslice):
        B = delta.shape[0]
        naut_seen += B
        d1 = indeg1_fast(delta, n)
        w = d1 - k
        dev = np.abs(w).sum(axis=1)
        sc = is_strongly_connected(delta, n)
        sy = is_synchronizing(delta, n)
        st = subset_stats(delta, n, k, tmax_ext, want_identity_check=do_check)

        sig = np.rint(st["sig"]).astype(np.int64)        # (n-1,B,NS)
        ssq = np.rint(st["ssq"]).astype(np.int64)
        minext = st["minext"]
        if do_check:
            ssq_p = np.rint(st["ssq_pair"]).astype(np.int64)
            ident_bad += int((ssq_p != ssq).sum())
            ident_seen += int(ssq.size)

        sig = sig[:, :, pidx]
        ssq = ssq[:, :, pidx]
        minext = minext[:, pidx]
        P = pidx.size
        szM = szv[None, :]                                # (1,P)

        # B(S) and the graded family B_T
        Bv = np.zeros((B, P), dtype=np.int64)
        BT = np.zeros((n - 1, B, P), dtype=np.int64)
        for t in range(1, n):
            Bv += (k ** (n - 1 - t)) * sig[t - 1]
        for T in range(1, n):
            acc = np.zeros((B, P), dtype=np.int64)
            for t in range(1, T + 1):
                acc += (k ** (T - t)) * sig[t - 1]
            BT[T - 1] = acc

        anypos = (sig > 0).any(axis=0)
        allzero = (sig == 0).all(axis=0)
        Csharp = anypos | allzero
        Hsharp = (~anypos) & (~allzero)
        stuck = minext > (n - 1)
        # boundary half of Section 6.4: sigma_t == 0 for every t <= n-2 AND minext > n-2
        if n >= 3:
            bnd_nograde = (sig[: n - 2] == 0).all(axis=0) & (minext > (n - 2))
        else:
            bnd_nograde = np.zeros_like(stuck)

        # first length at which sigma_t>0
        g1h = np.full((B, P), BIG, dtype=np.int64)
        for t in range(n - 1, 0, -1):
            g1h[sig[t - 1] > 0] = t

        qfire = np.zeros((n - 1, B, P), dtype=bool)
        qpfire = np.zeros((n - 1, B, P), dtype=bool)
        for t in range(1, n):
            thr, thrp = qthresholds(sig[t - 1], szM, k, t)
            qfire[t - 1] = ssq[t - 1] > thr
            qpfire[t - 1] = ssq[t - 1] > thrp
        qany = qfire.any(axis=0)
        qpany = qpfire.any(axis=0)
        g2h = np.full((B, P), BIG, dtype=np.int64)
        g2ph = np.full((B, P), BIG, dtype=np.int64)
        for t in range(n - 1, 0, -1):
            g2h[qfire[t - 1]] = t
            g2ph[qpfire[t - 1]] = t

        # ---------------- population masks ----------------
        euler = dev == 0
        masks = {
            "unfiltered": np.ones(B, dtype=bool),
            "syncSC": sy & sc,
            "syncSC_nonEuler": sy & sc & (~euler),
            "syncSC_d2": sy & sc & (dev <= 2),
            "syncSC_d2_nonEuler": sy & sc & (dev <= 2) & (~euler),
            "sync_notSC": sy & (~sc),
            "notsync": ~sy,
            "eulerian_syncSC": sy & sc & euler,
        }

        for name, m in masks.items():
            if not m.any():
                continue
            for conv, wt in (("q", np.ones(B, dtype=np.int64)), ("l", wl)):
                A = pops[name][conv]
                ww = np.where(m, wt, 0)
                A.a("n_aut", ww.sum())
                A.a("n_nonEuler", np.where(m & (~euler), wt, 0).sum())
                A.a("n_euler", np.where(m & euler, wt, 0).sum())
                for dd in range(0, 2 * k * n + 1):
                    c = np.where(m & (dev == dd), wt, 0).sum()
                    if c:
                        A.a(f"n_dev{dd}", c)
                W = ww[:, None]
                A.s("n_sub", (W * np.ones((1, P), dtype=np.int64)).sum())
                A.s("Csharp", (W * Csharp).sum())
                A.s("Hsharp", (W * Hsharp).sum())
                A.s("sigma_zero", (W * allzero).sum())
                A.s("anypos", (W * anypos).sum())
                A.s("Bge0", (W * (Bv >= 0)).sum())
                A.s("Bgt0", (W * (Bv > 0)).sum())
                A.s("Beq0", (W * (Bv == 0)).sum())
                A.s("Blt0", (W * (Bv < 0)).sum())
                A.s("gain_Csharp_minus_Bge0", (W * (Csharp & (Bv < 0))).sum())
                A.s("stuck", (W * stuck).sum())
                A.s("Hsharp_qcert", (W * (Hsharp & qany)).sum())
                A.s("Hsharp_qcertplus", (W * (Hsharp & qpany)).sum())
                A.s("hardcore_Blt0_qcert", (W * ((Bv < 0) & qany)).sum())
                A.s("hardcore_Blt0_qcertplus", (W * ((Bv < 0) & qpany)).sum())
                A.s("stuck_qcert", (W * (stuck & qany)).sum())
                A.s("stuck_qcertplus", (W * (stuck & qpany)).sum())
                A.s("qcert_any", (W * qany).sum())
                A.s("qcertplus_any", (W * qpany).sum())
                A.s("minext_infinite", (W * (minext >= BIG)).sum())
                # further counts
                A.s("boundary_nograde", (W * bnd_nograde).sum())
                A.s("doubly_stuck_pairs2x", (W * (stuck & stuck[:, compidx])).sum())
                if (m[:, None] & stuck).any():
                    A.p("maxB_on_stuck", 0, np.where(m[:, None] & stuck, Bv, -10 ** 9).max())
                if (m[:, None] & (~stuck)).any():
                    A.p("minB_on_nonstuck", 0, -np.where(m[:, None] & (~stuck), Bv, 10 ** 9).min())
                for j in range(1, n):
                    sj = (szM == j)
                    A.s(f"Hsharp_size{j}", (W * (Hsharp & sj)).sum())
                    A.s(f"Hsharp_qcert_size{j}", (W * (Hsharp & qany & sj)).sum())
                    A.s(f"Hsharp_qcertplus_size{j}", (W * (Hsharp & qpany & sj)).sum())
                    A.s(f"stuck_size{j}", (W * (stuck & sj)).sum())
                for t in range(1, n):
                    A.h("sigpos", t, (W * (sig[t - 1] > 0)).sum())
                    A.h("firstsigpos", t, (W * (g1h == t)).sum())
                    A.h("BTpos", t, (W * (BT[t - 1] > 0)).sum())
                    A.h("existsig_le", t, (W * (sig[:t] > 0).any(axis=0)).sum())
                    A.h("qcert_t", t, (W * qfire[t - 1]).sum())
                    A.h("qcertplus_t", t, (W * qpfire[t - 1]).sum())
                    A.h("firstqcert", t, (W * (g2h == t)).sum())
                    A.h("firstqcertplus", t, (W * (g2ph == t)).sum())
                    A.h("firstqcert_Hsharp", t, (W * ((g2h == t) & Hsharp)).sum())
                    A.h("firstqcertplus_Hsharp", t, (W * ((g2ph == t) & Hsharp)).sum())
                # profiles per subset size
                mm = m[:, None]
                for j in range(1, n):
                    sel = (szM == j) & mm
                    if not sel.any():
                        continue
                    v = np.where(sel & (minext < BIG), minext, -1).max()
                    A.p("f_all", j, v)
                    v = np.where(sel & Csharp & (minext < BIG), minext, -1).max()
                    A.p("f_Csharp", j, v)
                    v = np.where(sel & (g1h < BIG), g1h, -1).max()
                    A.p("g1", j, v)
                    v = np.where(sel & (g2h < BIG), g2h, -1).max()
                    A.p("g2", j, v)
                    v = np.where(sel & (g2ph < BIG), g2ph, -1).max()
                    A.p("g2plus", j, v)
                    v = np.where(sel & Hsharp & (minext < BIG), minext, -1).max()
                    A.p("f_Hsharp", j, v)

    wall = time.time() - t0
    res = dict(n=n, k=k, tag=tag,
               language="Python + numpy " + np.__version__,
               wall_seconds=round(wall, 2),
               automata_enumerated_quotient=int(naut_seen),
               repslice=repslice,
               identity_instances_checked=ident_seen,
               identity_disagreements=ident_bad,
               populations={name: {c: pops[name][c].dump() for c in ("q", "l")}
                            for name in pops})
    fn = os.path.join(outdir, f"{tag}.json")
    with open(fn, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
    print(f"wrote {fn}  ({wall:.1f}s, {naut_seen} automata)")
    return res


if __name__ == "__main__":
    if len(sys.argv) < 5:
        sys.exit("usage: python run.py n k tag outdir [--reps i j] [--nocheck] [--maxbatch B]")
    n = int(sys.argv[1]); k = int(sys.argv[2]); tag = sys.argv[3]; outdir = sys.argv[4]
    do_check = "--nocheck" not in sys.argv
    mb = None
    if "--maxbatch" in sys.argv:
        mb = int(sys.argv[sys.argv.index("--maxbatch") + 1])
    rs = None
    if "--reps" in sys.argv:
        i = sys.argv.index("--reps")
        rs = (int(sys.argv[i + 1]), int(sys.argv[i + 2]))
    run(n, k, tag, outdir, do_check, mb, repslice=rs)
