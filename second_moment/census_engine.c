/* census_engine.c -- exhaustive per-subset counts of the certificate B, the
 * region C#, and the second-moment tests (Q-CERT) and (Q-CERT+)
 *
 * Supports, in "Certificates for short extending words in a finite automaton"
 * (names below are fields of the "acc" object of the output; each counter is a
 * pair [quotient, labelled]; the paper's shares are ratios of quotient values):
 *   Section 4.1 and Table A.1: non-Eulerian automata (autos_nonEul) and those
 *     with no proper nonempty subset having sigma_t = 0 for every t <= n-1
 *     (autos_noSigZeroSub): 51 and 36 at n=3, 1,168 and 923 at n=4, 31,634 and
 *     29,508 at n=5, 12,509 and 11,104 at n=5 on {d<=2}, 1,110,301 and 719,484
 *     at n=6, 248,233 and 137,301 at n=6 on {d<=2}, 4,873,053 and 4,359,891 at
 *     n=7 on {d<=2}.
 *   Appendix A.1: the same fractions in both conventions (93.28 against 93.16
 *     at n=5, 55.31 against 54.27 at n=6 on {d<=2}, 70.59 against 68.75 at
 *     n=3, 79.02 against 76.54 at n=4).
 *   Section 6.3: {B<0} (Bneg) among the proper-subset instances
 *     (rows): 138 of 354, 7,724 of 17,360, 463,047 of 977,640 and 33,481,397 of
 *     69,596,798 at n=3,4,5,6.
 *   Section 6.4, n=5: sigma_1 > 0 on 314,393 instances (sig_pos[1]); 12,064
 *     whose only positive sigma_t is at t=n-1 (sig_first[4]); the union of the
 *     {sigma_t>0}, t<=T, exceeds {B_T>0} by exists_sig_le[T] - BT_pos[T] =
 *     12,644 at T=2 and 29,396 at T=4.  Boundary half (boundary_nograde): 402,
 *     2,428 and 8,528 at n=4,5,6.
 *   Section 6.5 and Table D.1, row C#: {B<0} shrinks by the share
 *     Csharp_minus_Bge0 / Bneg.
 *   Section 6.6 and Table D.1, rows (Q-CERT) and (Q-CERT+): the shares
 *     (Csharp_minus_Bge0 + Hsharp_qcert) / Bneg and
 *     (Csharp_minus_Bge0 + Hsharp_qplus) / Bneg; 0 stuck subsets certified
 *     (stuck_qcert, stuck_qplus); per subset size j, the largest length at which
 *     sigma_t > 0, (Q-CERT), (Q-CERT+) first fires (byj_g1, byj_g2, byj_g2p) and
 *     the largest minext <= n-1 (byj_f) are all n-1.
 *   Appendix D: rows extending within t but at no length exactly t (ex_gap,
 *     ex_gap_any); none on the {d<=2} populations.
 *   Appendix A: the population sizes (autos).
 *   tables.py checks each of these numbers against the JSON files.
 * Population / convention: states Q = {0,...,n-1}.  Letter a ranges over one
 *   representative of each conjugacy class of endofunctions of Q, every further
 *   letter over all n^n maps independently; an automaton is kept if it is
 *   strongly connected, synchronizing and of deviation d <= dmax.  At k=2 this
 *   is the quotient convention of Appendix A.1.  At k=3 the pair (b,c) is
 *   ORDERED here, whereas Appendix A.1 takes the letters after the first as a
 *   multiset.  Every counter is kept twice: [0] quotient, weight 1 per
 *   enumerated automaton; [1] labelled, weight n!/|C(a)| (the size of the
 *   conjugacy class of a), which gives the count over all transition tables.
 * Usage:    gcc -O2 -o census_engine census_engine.c
 *           census_engine n k dmax out.json      (2 <= n <= 7, 1 <= k <= 3;
 *                                                  dmax = -1: every deviation)
 *           The eleven populations of Section 6.6: see run_populations.py.
 * Output:   out.json with n, k, dmax, a_classes (7, 19, 47, 130, 343 classes at
 *           n=3..7), candidates_after_dfilter, passed_filters (= autos), wall_s,
 *           and "acc", the counters described at struct ACC below; one summary
 *           line on stdout.
 * Runtime:  one core per run, gcc -O2, measured on a shared 8-core machine:
 *           n=7 {d<=2} 466 s, k=3 n=5 {d<=2} 821 s, n=6 all d 44 s,
 *           n=6 {d<=2} 8 s, k=3 n=4 all d 4 s, every other population of
 *           Section 6.6 under 2 s.
 * Requires: an ISO C compiler (tested with gcc 16).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NMAX 7
#define KMAX 3
#define NSMAX (1 << NMAX)
#define MAXPHI 1024

typedef long long i64;
typedef struct { i64 q, l; } C2;   /* quotient and labelled weight */

/* The counters.  A row is one proper nonempty subset S of one kept automaton.
 * Arrays indexed by a length t have entries t = 0..n-1 (entry 0 unused);
 * arrays indexed by a size j = |S| have entries j = 0..n.
 *   autos, autos_nonEul    kept automata; of which non-Eulerian
 *   autos_noSigZeroSub     non-Eulerian kept automata with no proper nonempty S
 *                          having sigma_t(S) = 0 for every t <= n-1
 *   rows                   rows
 *   sig_pos[t]             rows with sigma_t(S) > 0
 *   sig_first[t]           rows whose smallest t with sigma_t(S) > 0 is t
 *                          (t = n: no such t)
 *   BT_pos[T]              rows with B_T(S) > 0
 *   exists_sig_le[T]       rows with sigma_t(S) > 0 for some t <= T
 *   Csharp, Bge0, Bneg     rows in C#; rows with B(S) >= 0; with B(S) < 0
 *   Csharp_minus_Bge0      rows in C# with B(S) < 0
 *   Hsharp                 rows in H#
 *   Hsharp_qcert, _qplus   rows in H# on which (Q-CERT), (Q-CERT+) fires at
 *                          some t <= n-1
 *   sigma_zero             rows with sigma_t(S) = 0 for every t <= n-1
 *   stuck                  rows with minext(S) > n-1
 *   stuck_qcert, _qplus    stuck rows on which the test fires at some t <= n-1
 *   qcert_pos[t], qplus_pos[t]      rows on which the test fires at t
 *   qcert_first[t], qplus_first[t]  rows whose smallest firing length is t
 *                                   (t = n: the test never fires)
 *   qcert_lower, qplus_lower  rows whose smallest firing length is below the
 *                          smallest t with sigma_t(S) > 0 (n if none)
 *   qplus_lower_than_q     rows on which (Q-CERT+) first fires before (Q-CERT)
 *   qplus_beats_q          rows on which (Q-CERT+) fires at some t <= n-1 and
 *                          (Q-CERT) at none
 *   boundary_nograde       rows with sigma_t(S) = 0 for every t <= n-2 and
 *                          minext(S) > n-2
 *   viol_*                 implementation checks, all 0 when correct:
 *                          _ex: pairs (row, t) at which the test fires but no
 *                          word of length exactly t extends S; _minext: rows
 *                          with minext(S) above the smallest firing length;
 *                          viol_qsum_neg: pairs (row, t) with a negative second
 *                          moment; viol_qplus_ge_qcert: pairs (row, t) at which
 *                          (Q-CERT) fires and (Q-CERT+) does not
 *   ex_gap[t]              rows with minext(S) <= t such that no word of length
 *                          exactly t extends S; ex_gap_any: rows with such a t
 *   byj_rows, byj_stuck, byj_Hsharp, byj_Hsharp_qcert, byj_Hsharp_qplus [j]
 *                          the same counts restricted to |S| = j
 *   byj_f[j]               largest minext(S) <= n-1 over |S| = j
 *   byj_g1[j], byj_g2[j], byj_g2p[j]
 *                          largest smallest-firing-length of sigma_t > 0,
 *                          (Q-CERT), (Q-CERT+) over the subsets of size j on
 *                          which that test fires at some t <= n-1 (0: none)
 * The integer maxima byj_f and byj_g* are the same in both conventions.
 */
typedef struct {
    C2 autos, autos_nonEul, autos_noSigZeroSub, rows;
    C2 sig_pos[NMAX + 1], sig_first[NMAX + 2], BT_pos[NMAX + 1], exists_sig_le[NMAX + 1];
    C2 Csharp, Bge0, Bneg, Csharp_minus_Bge0;
    C2 Hsharp, Hsharp_qcert, Hsharp_qplus, sigma_zero;
    C2 stuck, stuck_qcert, stuck_qplus;
    C2 qcert_pos[NMAX + 1], qcert_first[NMAX + 2];
    C2 qplus_pos[NMAX + 1], qplus_first[NMAX + 2];
    C2 qcert_lower, qplus_lower, qplus_lower_than_q, qplus_beats_q;
    C2 boundary_nograde;
    C2 viol_qcert_ex, viol_qplus_ex, viol_sig_ex;
    C2 viol_qcert_minext, viol_qplus_minext, viol_sig_minext;
    C2 viol_qsum_neg, viol_qplus_ge_qcert;
    C2 ex_gap[NMAX + 1], ex_gap_any;   /* within t, but not at length exactly t */
    C2 byj_rows[NMAX + 2], byj_stuck[NMAX + 2];
    C2 byj_Hsharp[NMAX + 2], byj_Hsharp_qcert[NMAX + 2], byj_Hsharp_qplus[NMAX + 2];
    int byj_f[NMAX + 2], byj_g1[NMAX + 2], byj_g2[NMAX + 2], byj_g2p[NMAX + 2];
} ACC;

static ACC acc;
static int N, K, DMAX;
static int NS, FULL;
static int pc_[NSMAX], lowidx[NSMAX];
static int L[KMAX][NMAX];
static int ind_[NMAX];
static int excess_;
static i64 WL;                 /* labelled weight of the current a-class */
static unsigned char *seenmap; /* size n^n, for phi dedup                */
static i64 ncand = 0, npass = 0;

static void die(const char *m) { fprintf(stderr, "FATAL: %s\n", m); exit(2); }
#define ADD(c) do { (c).q += 1; (c).l += WL; } while (0)

/* ------------------------------------------------------- conjugacy classes */
static int *ufpar;
static int uffind(int x) {
    int r = x, t;
    while (ufpar[r] != r) r = ufpar[r];
    while (ufpar[x] != r) { t = ufpar[x]; ufpar[x] = r; x = t; }
    return r;
}
static int nreps;
static int repmap[400][NMAX];
static i64 reporb[400];

static void build_classes(int n) {
    int Nn = 1, i, q, g, code, pw[NMAX + 1];
    for (i = 0; i < n; i++) { pw[i] = Nn; Nn *= n; }
    ufpar = (int *)malloc(sizeof(int) * Nn);
    if (!ufpar) die("oom ufpar");
    for (i = 0; i < Nn; i++) ufpar[i] = i;
    for (code = 0; code < Nn; code++) {
        int f[NMAX];
        for (i = 0; i < n; i++) f[i] = (code / pw[i]) % n;
        for (g = 0; g + 1 < n; g++) {          /* adjacent transposition (g,g+1) */
            int p[NMAX], c2 = 0, ra, rb;
            for (i = 0; i < n; i++) p[i] = i;
            p[g] = g + 1; p[g + 1] = g;
            for (q = 0; q < n; q++) c2 += p[f[q]] * pw[p[q]];
            ra = uffind(code); rb = uffind(c2);
            if (ra != rb) { if (ra < rb) ufpar[rb] = ra; else ufpar[ra] = rb; }
        }
    }
    {
        i64 *sz = (i64 *)calloc(Nn, sizeof(i64));
        if (!sz) die("oom sz");
        for (code = 0; code < Nn; code++) sz[uffind(code)]++;
        nreps = 0;
        for (code = 0; code < Nn; code++) if (sz[code]) {
            if (nreps >= 400) die("too many classes");
            for (i = 0; i < n; i++) repmap[nreps][i] = (code / pw[i]) % n;
            reporb[nreps] = sz[code];
            nreps++;
        }
        free(sz);
    }
    free(ufpar);
}

/* ------------------------------------------------------------- the filters */
static int is_sc(int n) {
    int seen = 1, st[NMAX], sp = 0, q, x, r;
    st[sp++] = 0;
    while (sp) { q = st[--sp];
        for (x = 0; x < K; x++) { r = L[x][q];
            if (!((seen >> r) & 1)) { seen |= 1 << r; st[sp++] = r; } } }
    if (seen != (1 << n) - 1) return 0;
    seen = 1; sp = 0; st[sp++] = 0;
    while (sp) { q = st[--sp];
        for (x = 0; x < K; x++) for (r = 0; r < n; r++)
            if (L[x][r] == q && !((seen >> r) & 1)) { seen |= 1 << r; st[sp++] = r; } }
    return seen == (1 << n) - 1;
}

static int is_sync(int n) {
    unsigned char vis[NMAX * NMAX];
    int st[NMAX * NMAX][2], sp = 0, cnt = 0, q, x, r, s, p;
    memset(vis, 0, sizeof(vis));
    for (q = 0; q < n; q++) { vis[q * n + q] = 1; cnt++; st[sp][0] = q; st[sp][1] = q; sp++; }
    while (sp) {
        p = st[--sp][0]; q = st[sp][1];
        for (x = 0; x < K; x++)
            for (r = 0; r < n; r++) if (L[x][r] == p)
                for (s = 0; s < n; s++) if (L[x][s] == q)
                    if (!vis[r * n + s]) { vis[r * n + s] = 1; cnt++;
                        st[sp][0] = r; st[sp][1] = s; sp++; }
    }
    return cnt == n * n;
}

/* ---------------------------------------------------------------- analysis */
static void analyze(int n, int k) {
    int v[NMAX + 1][NMAX], A[NMAX + 1][NMAX][NMAX];
    static int idg[NMAX + 1][NSMAX], P[NMAX + 1][NSMAX], col[NMAX][NSMAX];
    static unsigned char exg[NMAX + 1][NSMAX];
    int kt[NMAX + 1], kp[NMAX + 1];
    int t, q, r, s, x, S, i, j;
    int phis[MAXPHI][NMAX], nphi, phis2[MAXPHI][NMAX], nphi2;
    int codes[MAXPHI], ncodes;
    int pwn[NMAX + 1];
    int nonEul = 0, has_sigzero = 0;

    for (i = 0, pwn[0] = 1; i < n; i++) pwn[i + 1] = pwn[i] * n;

    /* v_t = 1^T M^t */
    for (q = 0; q < n; q++) v[0][q] = 1;
    for (t = 1; t < n; t++) {
        for (q = 0; q < n; q++) v[t][q] = 0;
        for (x = 0; x < k; x++) for (q = 0; q < n; q++) v[t][L[x][q]] += v[t - 1][q];
    }
    for (q = 0; q < n; q++) if (v[1][q] != k) nonEul = 1;

    /* A_t[p][q] = #{(r,s,u): |u|=t, r.u=p, s.u=q}  (pair-automaton in-degree) */
    for (r = 0; r < n; r++) for (s = 0; s < n; s++) A[0][r][s] = 1;
    for (t = 1; t < n; t++) {
        for (r = 0; r < n; r++) for (s = 0; s < n; s++) A[t][r][s] = 0;
        for (x = 0; x < k; x++) for (r = 0; r < n; r++) {
            int fr = L[x][r];
            for (s = 0; s < n; s++) A[t][fr][L[x][s]] += A[t - 1][r][s];
        }
    }

    kt[0] = 1; for (t = 1; t < n; t++) kt[t] = kt[t - 1] * k;
    kp[0] = 1; for (t = 1; t < n; t++) { kp[t] = 1; for (i = 0; i < n - 1 - t; i++) kp[t] *= k; }

    /* subset sums by lowest-bit recursion: idg[t][S] = indeg_t(S), and
       P[t][S] = sum over p,q in S of A_t[p][q] = pairdeg_t(S) (Appendix D) */
    for (t = 1; t < n; t++) {
        idg[t][0] = 0;
        for (S = 1; S < NS; S++) { int lb = S & (-S); idg[t][S] = idg[t][S ^ lb] + v[t][lowidx[lb]]; }
    }
    for (t = 1; t < n; t++) {
        for (q = 0; q < n; q++) col[q][0] = 0;
        for (S = 1; S < NS; S++) {
            int lb = S & (-S), ii = lowidx[lb], S2 = S ^ lb;
            for (q = 0; q < n; q++) col[q][S] = col[q][S2] + A[t][ii][q];
        }
        P[t][0] = 0;
        for (S = 1; S < NS; S++) {
            int lb = S & (-S), ii = lowidx[lb], S2 = S ^ lb;
            P[t][S] = P[t][S2] + 2 * col[ii][S2] + A[t][ii][ii];
        }
    }

    /* exg[t][S] = 1 iff some word of length EXACTLY t has |S u^{-1}| > |S|;
       phis holds the distinct maps q -> q.u over the words u of length t */
    nphi = 1; for (q = 0; q < n; q++) phis[0][q] = q;
    for (t = 1; t < n; t++) {
        ncodes = 0; nphi2 = 0;
        for (i = 0; i < nphi; i++) for (x = 0; x < k; x++) {
            int g[NMAX], code = 0;
            for (q = 0; q < n; q++) { g[q] = L[x][phis[i][q]]; code += g[q] * pwn[q]; }
            if (!seenmap[code]) {
                if (nphi2 >= MAXPHI || ncodes >= MAXPHI) die("MAXPHI exceeded");
                seenmap[code] = 1; codes[ncodes++] = code;
                for (q = 0; q < n; q++) phis2[nphi2][q] = g[q];
                nphi2++;
            }
        }
        for (i = 0; i < ncodes; i++) seenmap[codes[i]] = 0;
        nphi = nphi2;
        for (i = 0; i < nphi; i++) for (q = 0; q < n; q++) phis[i][q] = phis2[i][q];

        memset(exg[t], 0, (size_t)NS);
        for (i = 0; i < nphi; i++) {
            int pmask[NMAX], pre[NSMAX];
            for (q = 0; q < n; q++) pmask[q] = 0;
            for (r = 0; r < n; r++) pmask[phis[i][r]] |= 1 << r;
            pre[0] = 0;
            for (S = 1; S < NS; S++) { int lb = S & (-S); pre[S] = pre[S ^ lb] | pmask[lowidx[lb]]; }
            for (S = 1; S < FULL; S++) if (pc_[pre[S]] > pc_[S]) exg[t][S] = 1;
        }
    }

    ADD(acc.autos);
    if (nonEul) ADD(acc.autos_nonEul);

    /* ------------------------------------------------------- the row loop */
    for (S = 1; S < FULL; S++) {
        int sig[NMAX + 1], Bv = 0, anypos = 0, first_sig = n, sigzero = 1;
        int BT = 0, seen_pos = 0, cq = n, cqp = n, me = n, stuck;
        j = pc_[S];
        for (t = 1; t < n; t++) {
            sig[t] = idg[t][S] - kt[t] * j;
            Bv += kp[t] * sig[t];
            if (sig[t] != 0) sigzero = 0;
        }
        for (t = 1; t < n; t++) if (sig[t] > 0) {
            if (!anypos) first_sig = t;
            anypos = 1; ADD(acc.sig_pos[t]);
        }
        ADD(acc.sig_first[first_sig]);
        for (t = 1; t < n; t++) {
            BT = BT * k + sig[t];
            if (BT > 0) ADD(acc.BT_pos[t]);
            if (sig[t] > 0) seen_pos = 1;
            if (seen_pos) ADD(acc.exists_sig_le[t]);
        }
        if (sigzero) { has_sigzero = 1; ADD(acc.sigma_zero); }

        for (t = 1; t < n; t++) {
            /* qs = sum over |u|=t of x_u^2 = pairdeg_t(S) - 2|S| indeg_t(S) + k^t |S|^2 */
            int qs = P[t][S] - 2 * j * idg[t][S] + kt[t] * j * j;
            int m = -sig[t], fire_q, fire_p;
            if (qs < 0) ADD(acc.viol_qsum_neg);
            fire_q = (qs > j * m);                      /* (Q-CERT), Proposition 3 */
            /* (Q-CERT+), Proposition 4: qs > q|S|^2 + r^2, q = floor(m/|S|), r = m - q|S| */
            if (m < 0) fire_p = 1;                      /* sigma_t>0: Corollary 1 */
            else { int qq = m / j, rr = m - (m / j) * j; /* j>=1, m>=0 */
                   fire_p = (qs > qq * j * j + rr * rr); }
            if (fire_q && !fire_p) ADD(acc.viol_qplus_ge_qcert);
            if (fire_q) { ADD(acc.qcert_pos[t]); if (cq == n) cq = t;
                          if (!exg[t][S]) ADD(acc.viol_qcert_ex); }
            if (fire_p) { ADD(acc.qplus_pos[t]); if (cqp == n) cqp = t;
                          if (!exg[t][S]) ADD(acc.viol_qplus_ex); }
            if (sig[t] > 0 && !exg[t][S]) ADD(acc.viol_sig_ex);
        }
        ADD(acc.qcert_first[cq]);
        ADD(acc.qplus_first[cqp]);

        for (t = 1; t < n; t++) if (exg[t][S]) { me = t; break; }
        stuck = (me == n);
        { int gapany = 0;
          for (t = 1; t < n; t++) if (me <= t && !exg[t][S]) { ADD(acc.ex_gap[t]); gapany = 1; }
          if (gapany) ADD(acc.ex_gap_any); }

        ADD(acc.rows); ADD(acc.byj_rows[j]);
        if (stuck) {
            ADD(acc.stuck); ADD(acc.byj_stuck[j]);
            if (cq < n) ADD(acc.stuck_qcert);
            if (cqp < n) ADD(acc.stuck_qplus);
        } else if (me > acc.byj_f[j]) acc.byj_f[j] = me;

        if (anypos || sigzero) ADD(acc.Csharp);
        if (Bv >= 0) ADD(acc.Bge0);
        else { ADD(acc.Bneg); if (anypos) ADD(acc.Csharp_minus_Bge0); }
        if (!anypos && !sigzero) {
            ADD(acc.Hsharp); ADD(acc.byj_Hsharp[j]);
            if (cq < n) { ADD(acc.Hsharp_qcert); ADD(acc.byj_Hsharp_qcert[j]); }
            if (cqp < n) { ADD(acc.Hsharp_qplus); ADD(acc.byj_Hsharp_qplus[j]); }
        }
        if (cq < first_sig) ADD(acc.qcert_lower);
        if (cqp < first_sig) ADD(acc.qplus_lower);
        if (cqp < cq) ADD(acc.qplus_lower_than_q);
        if (cqp < n && cq == n) ADD(acc.qplus_beats_q);
        if (first_sig < n && first_sig > acc.byj_g1[j]) acc.byj_g1[j] = first_sig;
        if (cq < n && cq > acc.byj_g2[j]) acc.byj_g2[j] = cq;
        if (cqp < n && cqp > acc.byj_g2p[j]) acc.byj_g2p[j] = cqp;
        if (cq < n && me > cq) ADD(acc.viol_qcert_minext);
        if (cqp < n && me > cqp) ADD(acc.viol_qplus_minext);
        if (first_sig < n && me > first_sig) ADD(acc.viol_sig_minext);
        if (n >= 3) { int ok = 1;
            for (t = 1; t <= n - 2; t++) if (sig[t] != 0) { ok = 0; break; }
            if (ok && me > n - 2) ADD(acc.boundary_nograde); }
    }
    if (nonEul && !has_sigzero) ADD(acc.autos_noSigZeroSub);
}

/* --------------------------------------------------------- the enumeration */
static void enum_rec(int li, int pos) {
    int r;
    if (li == K) {
        int d = 0, q;
        for (q = 0; q < N; q++) d += (ind_[q] > K ? ind_[q] - K : K - ind_[q]);
        if (DMAX >= 0 && d > DMAX) return;
        ncand++;
        if (!is_sc(N)) return;
        if (!is_sync(N)) return;
        npass++;
        analyze(N, K);
        return;
    }
    if (pos == N) { enum_rec(li + 1, 0); return; }
    for (r = 0; r < N; r++) {
        int bump;
        L[li][pos] = r; ind_[r]++;
        bump = (ind_[r] > K) ? 1 : 0;
        excess_ += bump;
        if (!(DMAX >= 0 && 2 * excess_ > DMAX)) enum_rec(li, pos + 1);
        excess_ -= bump;
        ind_[r]--;
    }
}

/* -------------------------------------------------------------- JSON output */
static void pc2(FILE *f, const char *nm, C2 c, int comma) {
    fprintf(f, "  \"%s\": [\n   %lld,\n   %lld\n  ]%s\n", nm, c.q, c.l, comma ? "," : "");
}
static void pcv(FILE *f, const char *nm, C2 *c, int m, int comma) {
    int i; fprintf(f, "  \"%s\": [\n", nm);
    for (i = 0; i < m; i++)
        fprintf(f, "   [\n    %lld,\n    %lld\n   ]%s\n", c[i].q, c[i].l, i + 1 < m ? "," : "");
    fprintf(f, "  ]%s\n", comma ? "," : "");
}
static void piv(FILE *f, const char *nm, int *c, int m, int comma) {
    int i; fprintf(f, "  \"%s\": [\n", nm);
    for (i = 0; i < m; i++) fprintf(f, "   %d%s\n", c[i], i + 1 < m ? "," : "");
    fprintf(f, "  ]%s\n", comma ? "," : "");
}

int main(int argc, char **argv) {
    int i, n, k;
    double t0, wall;
    FILE *f;
    i64 nfact = 1;
    if (argc < 5) { fprintf(stderr, "usage: census_engine n k dmax out.json   (dmax = -1: every deviation)\n"); return 1; }
    N = n = atoi(argv[1]); K = k = atoi(argv[2]); DMAX = atoi(argv[3]);
    if (n < 2 || n > NMAX || k < 1 || k > KMAX) die("bad n/k");
    NS = 1 << n; FULL = NS - 1;
    for (i = 0; i < NS; i++) { int b = i, c = 0; while (b) { c += b & 1; b >>= 1; } pc_[i] = c; }
    for (i = 0; i < n; i++) lowidx[1 << i] = i;
    for (i = 2; i <= n; i++) nfact *= i;
    memset(&acc, 0, sizeof(acc));
    t0 = (double)clock() / CLOCKS_PER_SEC;
    build_classes(n);
    { i64 nn = 1; for (i = 0; i < n; i++) nn *= n;
      seenmap = (unsigned char *)calloc((size_t)nn, 1); if (!seenmap) die("oom seenmap"); }

    for (i = 0; i < nreps; i++) {
        int q;
        WL = reporb[i];
        for (q = 0; q < n; q++) { L[0][q] = repmap[i][q]; }
        memset(ind_, 0, sizeof(ind_));
        for (q = 0; q < n; q++) ind_[L[0][q]]++;
        excess_ = 0;
        for (q = 0; q < n; q++) if (ind_[q] > k) excess_ += ind_[q] - k;
        if (DMAX >= 0 && 2 * excess_ > DMAX) continue;
        enum_rec(1, 0);
    }
    wall = (double)clock() / CLOCKS_PER_SEC - t0;

    f = fopen(argv[4], "w"); if (!f) die("cannot open output");
    fprintf(f, "{\n \"engine\": \"c\",\n \"n\": %d,\n \"k\": %d,\n", n, k);
    if (DMAX < 0) fprintf(f, " \"dmax\": null,\n"); else fprintf(f, " \"dmax\": %d,\n", DMAX);
    fprintf(f, " \"a_classes\": %d,\n \"n_factorial\": %lld,\n", nreps, nfact);
    fprintf(f, " \"candidates_after_dfilter\": %lld,\n \"passed_filters\": %lld,\n", ncand, npass);
    fprintf(f, " \"wall_s\": %.3f,\n \"acc\": {\n", wall);
    pcv(f, "BT_pos", acc.BT_pos, n, 1);
    pc2(f, "Bge0", acc.Bge0, 1);
    pc2(f, "Bneg", acc.Bneg, 1);
    pc2(f, "Csharp", acc.Csharp, 1);
    pc2(f, "Csharp_minus_Bge0", acc.Csharp_minus_Bge0, 1);
    pc2(f, "Hsharp", acc.Hsharp, 1);
    pc2(f, "Hsharp_qcert", acc.Hsharp_qcert, 1);
    pc2(f, "Hsharp_qplus", acc.Hsharp_qplus, 1);
    pc2(f, "autos", acc.autos, 1);
    pc2(f, "autos_noSigZeroSub", acc.autos_noSigZeroSub, 1);
    pc2(f, "autos_nonEul", acc.autos_nonEul, 1);
    pc2(f, "boundary_nograde", acc.boundary_nograde, 1);
    pcv(f, "byj_Hsharp", acc.byj_Hsharp, n + 1, 1);
    pcv(f, "byj_Hsharp_qcert", acc.byj_Hsharp_qcert, n + 1, 1);
    pcv(f, "byj_Hsharp_qplus", acc.byj_Hsharp_qplus, n + 1, 1);
    piv(f, "byj_f", acc.byj_f, n + 1, 1);
    piv(f, "byj_g1", acc.byj_g1, n + 1, 1);
    piv(f, "byj_g2", acc.byj_g2, n + 1, 1);
    piv(f, "byj_g2p", acc.byj_g2p, n + 1, 1);
    pcv(f, "byj_rows", acc.byj_rows, n + 1, 1);
    pcv(f, "byj_stuck", acc.byj_stuck, n + 1, 1);
    pcv(f, "ex_gap", acc.ex_gap, n, 1);
    pc2(f, "ex_gap_any", acc.ex_gap_any, 1);
    pcv(f, "exists_sig_le", acc.exists_sig_le, n, 1);
    pcv(f, "qcert_first", acc.qcert_first, n + 1, 1);
    pc2(f, "qcert_lower", acc.qcert_lower, 1);
    pcv(f, "qcert_pos", acc.qcert_pos, n, 1);
    pc2(f, "qplus_beats_q", acc.qplus_beats_q, 1);
    pcv(f, "qplus_first", acc.qplus_first, n + 1, 1);
    pc2(f, "qplus_lower", acc.qplus_lower, 1);
    pc2(f, "qplus_lower_than_q", acc.qplus_lower_than_q, 1);
    pcv(f, "qplus_pos", acc.qplus_pos, n, 1);
    pc2(f, "rows", acc.rows, 1);
    pcv(f, "sig_first", acc.sig_first, n + 1, 1);
    pcv(f, "sig_pos", acc.sig_pos, n, 1);
    pc2(f, "sigma_zero", acc.sigma_zero, 1);
    pc2(f, "stuck", acc.stuck, 1);
    pc2(f, "stuck_qcert", acc.stuck_qcert, 1);
    pc2(f, "stuck_qplus", acc.stuck_qplus, 1);
    pc2(f, "viol_qcert_ex", acc.viol_qcert_ex, 1);
    pc2(f, "viol_qcert_minext", acc.viol_qcert_minext, 1);
    pc2(f, "viol_qplus_ex", acc.viol_qplus_ex, 1);
    pc2(f, "viol_qplus_ge_qcert", acc.viol_qplus_ge_qcert, 1);
    pc2(f, "viol_qplus_minext", acc.viol_qplus_minext, 1);
    pc2(f, "viol_qsum_neg", acc.viol_qsum_neg, 1);
    pc2(f, "viol_sig_ex", acc.viol_sig_ex, 1);
    pc2(f, "viol_sig_minext", acc.viol_sig_minext, 0);
    fprintf(f, " }\n}\n");
    fclose(f);
    printf("n=%d k=%d dmax=%d  automata q=%lld l=%lld (nonEul q=%lld) rows q=%lld  %.2fs\n",
           n, k, DMAX, acc.autos.q, acc.autos.l, acc.autos_nonEul.q, acc.rows.q, wall);
    free(seenmap);
    return 0;
}
