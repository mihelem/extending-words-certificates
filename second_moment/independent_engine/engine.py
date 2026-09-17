"""engine.py -- Python implementation of the per-subset quantities of Sections 3, 6.5 and 6.6

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: "The counts of Section 6.6 and Appendix D come from two
    implementations, one in C and one in Python, ... agreeing on 96 of 96
    compared integer fields across four populations in both counting
    conventions".  This module is the Python implementation (numpy); run.py
    drives it, and ../compare_engines.py compares its JSON files with those of
    ../census_engine.c.
Population / convention: letter 0 ranges over one representative of each
  conjugacy class of endofunctions of Q = {0,...,n-1}, every other letter over
  all n^n maps (at k=3 the two letters after the first form ordered pairs).
  Each automaton carries the quotient weight 1 and the labelled weight n!/|C(a)|
  (Appendix A.1).

Definitions implemented (Sections 2, 3, 6.5 and 6.6):

  complete DFA A = (Q, Sigma, delta), |Q| = n, k = |Sigma|.
  S u^{-1} = { q : q.u in S }
  x_u      = |S u^{-1}| - |S|
  minext(S)= min { |u| : |S u^{-1}| > |S| }
  indeg_t(q) = #{ (p,u) : |u| = t, p.u = q }
  sigma_t(S) = indeg_t(S) - k^t |S| = sum_{|u|=t} x_u
  w = indeg_1 - k*1,  d = sum_q |w_q|
  B(S) = sum_{t=1}^{n-1} k^{n-1-t} sigma_t(S)
  Csharp = { exists t<=n-1 : sigma_t > 0 } union { sigma == 0 }
  Hsharp = { sigma_t <= 0 for all t<=n-1, sigma not== 0 }

  (Q-CERT) fires at length t iff   sum_{|u|=t} x_u^2  >  |S| * (-sigma_t(S)).

Method.
  Since S(xu)^{-1} = (S u^{-1}) x^{-1}, the multiset { S u^{-1} : |u| = t }
  is obtained by t steps of the branching map  T |-> { T x^{-1} : x in Sigma }
  starting from T = S.  So with the 2^n x 2^n integer matrix
      R[T][T x^{-1}] += 1   (one increment per letter x)
  the row S of R^t is exactly the multiplicity vector of { S u^{-1} : |u|=t }.
  Hence, with pc(T) = |T|:
      indeg_t(S)          = (R^t pc)[S]
      sigma_t(S)          = (R^t pc)[S] - k^t |S|
      sum_{|u|=t} x_u^2   = (R^t pc^2)[S] - 2|S| (R^t pc)[S] + k^t |S|^2
      max_{|u|=t} x_u > 0 iff  max{ |T| : R^t[S][T] > 0 } > |S|
  This path never uses the pair automaton.

Second path for sum x_u^2, used as a check (the pair count of Appendix D):
      sum_u |S u^{-1}|^2 = sum_{p,q in S} pairdeg_t(p,q) =: P_t(S)
  with pairdeg_t the t-step in-degree of (p,q) in the pair automaton on QxQ,
      (r,r').x = (r.x, r'.x),
  so   sum_{|u|=t} x_u^2 = P_t(S) - 2|S| indeg_t(S) + k^t |S|^2.
  Both paths are computed and compared elementwise (run.py counts the
  disagreements).
  minext(S) is searched beyond n-1 on the 0/1-clipped matrix, up to tmax_ext.

Usage:    imported by run.py.
Output:   none (library module).
Runtime:  see run.py.
Requires: Python 3 (tested with 3.10) and numpy (tested with 2.2).
"""

import itertools
import json
import os
import sys
import time
from math import factorial

import numpy as np


# ----------------------------------------------------------------------
# 1.  endofunction conjugacy classes of [n] -> [n]   (A001372 count)
# ----------------------------------------------------------------------
def conj_reps(n):
    """One representative per conjugacy class of maps [n]->[n] under
    f ~ p f p^{-1}.  Returns (reps, centraliser_order) where the
    representative is the lexicographic minimum of its orbit."""
    perms = list(itertools.permutations(range(n)))
    reps = {}
    seen = set()
    for f in itertools.product(range(n), repeat=n):
        if f in seen:
            continue
        orbit = set()
        cent = 0
        for p in perms:
            g = [0] * n
            for i in range(n):
                g[p[i]] = p[f[i]]
            g = tuple(g)
            orbit.add(g)
            if g == f:
                cent += 1
        seen |= orbit
        r = min(orbit)
        # centraliser order is a class invariant: |C| = n!/|orbit|
        reps[r] = factorial(n) // len(orbit)
    return sorted(reps), reps


# ----------------------------------------------------------------------
# 2.  automaton-level predicates, vectorised over a batch
#     delta : (B, n, k) int array,  delta[b,q,x] = q.x
# ----------------------------------------------------------------------
def indeg1(delta, n):
    B = delta.shape[0]
    out = np.zeros((B, n), dtype=np.int64)
    for x in range(delta.shape[2]):
        for q in range(n):
            np.add.at(out, (np.arange(B), delta[:, q, x]), 1)
    return out


def indeg1_fast(delta, n):
    B, _, k = delta.shape
    flat = (np.arange(B)[:, None, None] * n + delta).reshape(-1)
    return np.bincount(flat, minlength=B * n).reshape(B, n)


def is_strongly_connected(delta, n):
    B, _, k = delta.shape
    adj = np.zeros((B, n, n), dtype=np.uint8)
    bi = np.repeat(np.arange(B), n * k)
    qi = np.tile(np.repeat(np.arange(n), k), B)
    ti = delta.reshape(-1)
    adj[bi, qi, ti] = 1
    R = adj | np.eye(n, dtype=np.uint8)[None, :, :]
    for _ in range(int(np.ceil(np.log2(max(n, 2)))) + 1):
        R = (np.matmul(R.astype(np.int32), R.astype(np.int32)) > 0).astype(np.uint8)
    return R.reshape(B, -1).all(axis=1)


def is_synchronizing(delta, n):
    """A complete DFA is synchronizing iff every pair {p,q} can be merged.
    Backward-closure on ordered pairs from the diagonal."""
    B, _, k = delta.shape
    npair = n * n
    # idx[x][b, p*n+q] = index of (p.x, q.x)
    idx = np.empty((k, B, npair), dtype=np.int64)
    for x in range(k):
        a = delta[:, :, x]                      # (B,n)
        idx[x] = (a[:, :, None] * n + a[:, None, :]).reshape(B, npair)
    marked = np.zeros((B, npair), dtype=bool)
    diag = np.arange(n) * n + np.arange(n)
    marked[:, diag] = True
    for _ in range(npair):
        new = marked.copy()
        for x in range(k):
            new |= np.take_along_axis(marked, idx[x], axis=1)
        if np.array_equal(new, marked):
            break
        marked = new
    return marked.all(axis=1)


# ----------------------------------------------------------------------
# 3.  the subset engine
# ----------------------------------------------------------------------
def popcount_table(n):
    NS = 1 << n
    return np.array([bin(m).count("1") for m in range(NS)], dtype=np.float64)


def subset_stats(delta, n, k, tmax_ext, want_identity_check=True):
    """Returns a dict of (B, 2^n) arrays.  Lengths t = 1..n-1 exact;
    minext searched out to tmax_ext."""
    B = delta.shape[0]
    NS = 1 << n
    masks = np.arange(NS, dtype=np.int64)
    pc = popcount_table(n)
    pc2 = pc * pc
    pow2 = (np.int64(1) << np.arange(n))

    # preimage table: pre[b, T, x] = T x^{-1}
    bitsel = (np.int64(1) << delta)                                  # (B,n,k)
    inT = (masks[None, :, None, None] & bitsel[:, None, :, :]) != 0  # (B,NS,n,k)
    pre = (inT * pow2[None, None, :, None]).sum(axis=2)              # (B,NS,k)
    del inT

    bidx = np.repeat(np.arange(B, dtype=np.int64), NS * k)
    tidx = np.tile(np.repeat(masks, k), B)
    flat = (bidx * NS + tidx) * NS + pre.reshape(-1)
    Rm = np.bincount(flat, minlength=B * NS * NS).astype(np.float64).reshape(B, NS, NS)
    del flat, bidx, tidx

    szS = pc[None, :]                                                # (1,NS)
    sig = np.zeros((n - 1, B, NS))
    ssq = np.zeros((n - 1, B, NS))
    ssq_pair = np.zeros((n - 1, B, NS)) if want_identity_check else None
    grows = np.zeros((n - 1, B, NS), dtype=bool)
    indeg_t = np.zeros((n - 1, B, NS))

    # pair automaton, for the second computation of sum x_u^2
    if want_identity_check:
        npair = n * n
        Npair = np.zeros((B, npair, npair), dtype=np.float64)
        for x in range(k):
            a = delta[:, :, x]
            src = (np.arange(n)[:, None] * n + np.arange(n)[None, :]).reshape(-1)
            dst = (a[:, :, None] * n + a[:, None, :]).reshape(B, npair)
            bb = np.repeat(np.arange(B), npair)
            Npair[bb, np.tile(src, B), dst.reshape(-1)] += 1
        vpair = np.ones((B, npair), dtype=np.float64)
        Mind = np.array([[(m >> q) & 1 for q in range(n)] for m in range(NS)],
                        dtype=np.float64)                            # (NS,n)

    Rt = Rm.copy()
    for t in range(1, n):
        S1 = Rt @ pc
        S2 = Rt @ pc2
        indeg_t[t - 1] = S1
        sig[t - 1] = S1 - (k ** t) * szS
        ssq[t - 1] = S2 - 2.0 * szS * S1 + (k ** t) * szS * szS
        grows[t - 1] = np.max(np.where(Rt > 0, pc[None, None, :], -1.0), axis=2) > szS
        if want_identity_check:
            if t == 1:
                vpair = np.einsum('bij->bj', Npair)
            else:
                vpair = np.einsum('bi,bij->bj', vpair, Npair)
            A = vpair.reshape(B, n, n)
            P = np.einsum('sp,bpq,sq->bs', Mind, A, Mind)
            ssq_pair[t - 1] = P - 2.0 * szS * S1 + (k ** t) * szS * szS
        if t < n - 1:
            Rt = Rt @ Rm

    # minext, continued past n-1 on the clipped (reachability) matrix
    BIG = 10 ** 6
    minext = np.full((B, NS), BIG, dtype=np.int64)
    for t in range(n - 1, 0, -1):
        minext[grows[t - 1]] = t
    cur = np.minimum(Rt, 1.0)
    t = n - 1
    while t < tmax_ext:
        cur = np.minimum(cur @ Rm, 1.0)
        t += 1
        g = np.max(np.where(cur > 0, pc[None, None, :], -1.0), axis=2) > szS
        upd = g & (minext == BIG)
        minext[upd] = t
        if not (minext[:, 1:NS - 1] == BIG).any():
            break

    out = dict(sig=sig, ssq=ssq, grows=grows, minext=minext, indeg_t=indeg_t)
    if want_identity_check:
        out["ssq_pair"] = ssq_pair
    return out


# ----------------------------------------------------------------------
# 4.  population generation
# ----------------------------------------------------------------------
def population(n, k, batch=None, repslice=None):
    """Yield (delta (B,n,k), labelled_weight (B,)) over the quotient
    convention:  letter 0 over one representative of each endofunction
    conjugacy class, all other letters over all n^n maps.  With
    repslice = (i, j) only the representatives of index i <= ri < j are used."""
    reps, cent = conj_reps(n)
    allm = np.array(list(itertools.product(range(n), repeat=n)), dtype=np.int64)
    nm = allm.shape[0]
    nf = factorial(n)
    if batch is None:
        batch = max(1, 4_000_000 // ((1 << n) * (1 << n)))
    others = nm ** (k - 1)
    for ri, r in enumerate(reps):
        if repslice is not None and not (repslice[0] <= ri < repslice[1]):
            continue
        wt = nf // cent[r]
        r_arr = np.array(r, dtype=np.int64)
        start = 0
        while start < others:
            stop = min(others, start + batch)
            idxs = np.arange(start, stop)
            B = stop - start
            delta = np.empty((B, n, k), dtype=np.int64)
            delta[:, :, 0] = r_arr[None, :]
            rem = idxs
            for j in range(k - 1):
                delta[:, :, k - 1 - j] = allm[rem % nm]
                rem = rem // nm
            yield delta, np.full(B, wt, dtype=np.int64)
            start = stop
