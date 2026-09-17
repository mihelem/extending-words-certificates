/* bias_census_exact.c -- the bias census with an exact certificate: integer matrix-tree polynomial of the stationary
 * vector of t pi(x) + (1-t) pi(y), exact sign of n e_t(S) - |S| e_t(Q) on the whole interval [1/2, 2/3], and the
 * grid thresholds of bias_census.c computed from the same polynomial
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Appendix A: "The bias census of Appendix C at n <= 7 was produced by two implementations on a grid of step 1/400,
 *     agreeing on every histogram bin" -- this program and bias_census.c (compare_histograms.py compares the two).
 *     Here moreover every (stuck subset, letter order) pair at n = 5, 6, 7 is certified exactly to satisfy
 *     n e_t(S) <= |S| e_t(Q) on all of [1/2, 2/3], with equality at t = 2/3 for exactly the 9, 8 and 116 pairs of
 *     the 2/3 bin: no pair has t* in (1/2, 2/3), and none is heavy at t = 1/2.
 *   Appendix C: on the stratum of the binary n = 8 population whose first letter is a permutation (the 22 cycle types
 *     as first letter, all 8^8 second letters): 123,014,054 automata, 18,609,570 stuck subsets, 416 pairs below 2/3
 *     (grid bins 35: 384 pairs, 42: 32 pairs), 32 pairs at 2/3 (bin 67), none heavy at t = 1/2.  The 448 BOUNDARY
 *     lines of that run are the input of exact_n8.py, which re-verifies each threshold exactly (384 at 2 - sqrt 2,
 *     32 at the root 0.603 of 2t^3 - 4t^2 + 5t - 2, 32 at 2/3).
 *
 * Population / convention: binary synchronizing strongly connected complete automata in the quotient convention of
 *   Appendix A.1: first letter over the representatives file, second letter over all n^n maps.  With the file of all
 *   conjugacy classes of endofunctions (class_reps.c) this is the exhaustive population; with the file of the
 *   permutation cycle types (permutation_reps.py 8) it is the permutation-first stratum.
 *
 * For every stuck subset S (minext(S) > n-1) and each of the two letter orders (the biased letter carries weight t,
 * the other 1-t, t in [1/2,1]) it reports
 *   (a) the least grid t (step 1/400) with n e_t(S) >= m e_t(Q)          -- same convention as bias_census.c
 *   (b) an EXACT integer certificate of  n e_t(S) - m e_t(Q) <= 0  on the WHOLE interval [1/2,2/3]
 *   (c) the exact integer values of that quantity at t = 1/2 and t = 2/3.
 *
 * Stationary vector by the Markov chain tree theorem (exact, integer):
 *   w_q(t) = sum_j C[q][j] t^j (1-t)^{d-j},  d = n-1,
 * C[q][j] = number of spanning in-trees rooted at q that use j edges of the first letter.
 * Enumeration: over all 2^n letter-choice functions c: Q -> {0,1}; the functional graph
 * g_c(p) = p.c(p) has exactly one cycle iff, for each q on that cycle, deleting q's out-edge leaves
 * an in-tree rooted at q.  Fixing c(q) = 0 makes the correspondence a bijection with in-trees.
 * e_t \propto w, so n e_t(S) >= m e_t(Q)  <=>  F(t) := n w_S(t) - m w_Q(t) >= 0  (w_Q(t) > 0 on (0,1)).
 *
 * Exact certificate.  F(t) = sum_j A_j t^j (1-t)^{d-j}, A_j = n C_S[j] - m C_Q[j] integer.
 * Put t = (3+s)/6, so s in [0,1] <=> t in [1/2,2/3], and
 *     H(s) := 6^d F(t) = sum_j A_j (3+s)^j (3-s)^{d-j} = sum_i h_i s^i = sum_k c_k s^k (1-s)^{d-k},
 *     h_i = sum_j A_j TPOW[j][i],   c_k = sum_{i<=k} binom(d-i, k-i) h_i     (all integers).
 * All c_k <= 0  ==>  F <= 0 on [1/2,2/3]  (Bernstein / convex-hull property).  Moreover
 *     c_0 = H(0) = 6^d F(1/2)   and   c_d = H(1) = 6^d F(2/3),
 * so c_d == 0 is the exact statement "S is exactly at the boundary at t = 2/3".
 * For the second letter order the same code is used with the coefficient array A reversed
 * (weight t on letter 1 = weight 1-t on letter 0).
 *
 * Usage:    gcc -O2 -o bias_census_exact bias_census_exact.c -lm
 *           bias_census_exact n repsfile [part nparts]      parts take the representatives with r % nparts == part
 *           python sum_parts.py OUT_0 ... OUT_{nparts-1}
 *
 * Output:   BOUNDARY n= a=[..] b=[..] S={..} biased=x bin= grid_t= exact6dF_half= exact6dF_23= cert=
 *                    every pair whose grid bin is <= 67 (t <= 0.6675, the bin that holds 2/3)
 *           UNCERT   pairs without the certificate (at most 2000 lines)
 *           DONE bias_census_exact n= part= automata= stuck_subsets= automata_with_stuck= pairs= min_t*= (refined )
 *                bin23_pairs= below23_pairs= heavy_at_half= exact_zero_at_23= exact_pos_at_23=
 *                certified_le0_on_[1/2,2/3]= uncertified= max_excess_below_bin23= attained by ...
 *           WORSTBELOW  the pair with the largest n e_t(S) - m over the grid bins below 67
 *           HIST (threshold grid 0.5+i/400; last bin = never): [i:count] ...
 *   pairs = 2 x stuck_subsets; bin23_pairs / below23_pairs = pairs in bin 67 / in bins 0..66; heavy_at_half = pairs
 *   with F(1/2) > 0; exact_zero_at_23 = pairs with F(2/3) = 0; exact6dF_half = 6^d F(1/2), exact6dF_23 = 6^d F(2/3);
 *   HIST bins as in bias_census.c (t = 0.5 + i/400; bin 201 = never).  Progress lines go to stderr.
 *
 * Runtime:  n = 5, 6 under 6 seconds; n = 7 about 4.5 minutes wall in 2 parts on 2 cores; n = 8 stratum about 51 minutes
 *           wall in 2 parts on 2 cores.
 * Requires: gcc or clang (the code uses __builtin_popcount and __builtin_ctz), libm; n <= 8.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXN 8
#define MAXS (1 << MAXN)
#define G 201            /* grid t = 0.5 + i/400, i = 0..200 */
#define BIN23 67         /* grid bin 0.6675: the "2/3 bin" of bias_census.c */
#define MAXPRINT 200000  /* cap on printed BOUNDARY lines */
#define MAXUNC   2000    /* cap on printed UNCERT lines */

static int n, d; static const int k = 2;
static int let[2][MAXN];
static int npow, nreps; static int reps[4000][MAXN];

/* ---------------- automaton tests (identical to bias_census.c / uniform_weights.c) ---------------- */
static int strongly_connected(void) {
    int full = (1 << n) - 1, reach = 1, prev;
    do { prev = reach; for (int p = 0; p < n; p++) if (reach >> p & 1)
            for (int x = 0; x < k; x++) reach |= 1 << let[x][p]; } while (reach != prev);
    if (reach != full) return 0;
    int co = 1;
    do { prev = co; for (int p = 0; p < n; p++) if (!(co >> p & 1))
            for (int x = 0; x < k; x++) if (co >> let[x][p] & 1) { co |= 1 << p; break; } } while (co != prev);
    return co == full;
}
static int synchronizing(void) {
    static unsigned char merge[MAXN][MAXN]; int changed;
    for (int p = 0; p < n; p++) for (int q = 0; q < n; q++) merge[p][q] = (p == q);
    do { changed = 0;
        for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++) if (!merge[p][q])
            for (int x = 0; x < k; x++) { int a = let[x][p], b = let[x][q];
                if (merge[a][b] || merge[b][a]) { merge[p][q] = merge[q][p] = 1; changed = 1; break; } }
    } while (changed);
    for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++) if (!merge[p][q]) return 0;
    return 1;
}
static int pre[2][MAXS];
static void build_pre(void) {
    int pre1[2][MAXN];
    for (int x = 0; x < k; x++) { for (int q = 0; q < n; q++) pre1[x][q] = 0;
        for (int p = 0; p < n; p++) pre1[x][let[x][p]] |= 1 << p; }
    int N = 1 << n;
    for (int x = 0; x < k; x++) { pre[x][0] = 0;
        for (int S = 1; S < N; S++) { int low = S & -S; pre[x][S] = pre[x][S ^ low] | pre1[x][__builtin_ctz(low)]; } }
}
/* minext(S) capped at n; stamped visited array (no memset per call) */
static unsigned int seenstamp[MAXS]; static unsigned int stampctr = 0;
static int minext_capped(int S) {
    static int cur[MAXS], nxt[MAXS];
    int m = __builtin_popcount(S);
    if (++stampctr == 0) { memset(seenstamp, 0, sizeof seenstamp); stampctr = 1; }
    unsigned int st = stampctr;
    seenstamp[S] = st; cur[0] = S; int nc = 1;
    for (int t = 1; t <= n - 1; t++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) for (int x = 0; x < k; x++) {
            int T = pre[x][cur[i]];
            if (__builtin_popcount(T) > m) return t;
            if (seenstamp[T] != st) { seenstamp[T] = st; nxt[nn++] = T; }
        }
        if (nn == 0) return n;
        memcpy(cur, nxt, sizeof(int) * nn); nc = nn;
    }
    return n;
}

/* ---------------- Markov chain tree theorem: integer coefficients C[q][j] ---------------- */
static long long C[MAXN][MAXN], CQ[MAXN];
static void tree_poly(void) {
    memset(C, 0, sizeof C);
    int N = 1 << n;
    for (int mask = 0; mask < N; mask++) {
        int color[MAXN]; for (int i = 0; i < n; i++) color[i] = 0;
        int cyclecount = 0, cyclemask = 0;
        for (int s = 0; s < n; s++) {
            if (color[s]) continue;
            int p = s;
            while (color[p] == 0) { color[p] = 1; p = let[(mask >> p) & 1][p]; }
            if (color[p] == 1) {                 /* new cycle, entered at p */
                if (++cyclecount >= 2) break;
                int cm = 0, r = p;
                do { cm |= 1 << r; r = let[(mask >> r) & 1][r]; } while (r != p);
                cyclemask = cm;
            }
            int r = s; while (color[r] == 1) { color[r] = 2; r = let[(mask >> r) & 1][r]; }
        }
        if (cyclecount != 1) continue;
        int z = __builtin_popcount(mask);        /* # states using letter 1 */
        int j = n - z - 1;                       /* # states != q using letter 0, given c(q) = 0 */
        if (j < 0) continue;
        int rest = cyclemask & ~mask;            /* roots on the cycle with c(q) = 0 */
        while (rest) { int q = __builtin_ctz(rest); rest &= rest - 1; C[q][j]++; }
    }
    for (int j = 0; j < n; j++) { long long s = 0; for (int q = 0; q < n; q++) s += C[q][j]; CQ[j] = s; }
}

/* ---------------- precomputed tables ---------------- */
static double BAS[2][G][MAXN];       /* BAS[order][i][j] = u^j (1-u)^{d-j}, u = 0.5 + (order?-1:1)*i/400 */
static long long TPOW[MAXN][MAXN];   /* TPOW[j][i] = coeff of s^i in (3+s)^j (3-s)^{d-j} */
static long long BINOM[MAXN + 1][MAXN + 1];
static void build_tables(void) {
    for (int x = 0; x < 2; x++) for (int i = 0; i < G; i++) {
        double u = x == 0 ? 0.5 + i / 400.0 : 0.5 - i / 400.0;
        double v = 1.0 - u;
        for (int j = 0; j <= d; j++) { double b = 1; for (int r = 0; r < j; r++) b *= u; for (int r = 0; r < d - j; r++) b *= v; BAS[x][i][j] = b; }
    }
    for (int a = 0; a <= n; a++) { BINOM[a][0] = 1; for (int b = 1; b <= a; b++) BINOM[a][b] = BINOM[a-1][b-1] + (b <= a-1 ? BINOM[a-1][b] : 0); }
    for (int j = 0; j <= d; j++) {
        long long poly[2 * MAXN]; memset(poly, 0, sizeof poly); poly[0] = 1; int deg = 0;
        for (int r = 0; r < j; r++) {            /* multiply by (3 + s) */
            for (int i = deg + 1; i >= 1; i--) poly[i] = poly[i - 1] + 3 * poly[i];
            poly[0] = 3 * poly[0]; deg++;
        }
        for (int r = 0; r < d - j; r++) {        /* multiply by (3 - s) */
            for (int i = deg + 1; i >= 1; i--) poly[i] = -poly[i - 1] + 3 * poly[i];
            poly[0] = 3 * poly[0]; deg++;
        }
        for (int i = 0; i <= d; i++) TPOW[j][i] = poly[i];
    }
}

static void print_aut(FILE *f) {
    for (int x = 0; x < k; x++) { fprintf(f, "%c=[", 'a' + x); for (int p = 0; p < n; p++) fprintf(f, "%d%s", let[x][p], p + 1 < n ? "," : ""); fprintf(f, "] "); }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: bias_census_exact n repsfile [part nparts]\n"); return 1; }
    n = atoi(argv[1]); d = n - 1;
    int part = 0, nparts = 1; if (argc >= 5) { part = atoi(argv[3]); nparts = atoi(argv[4]); }
    npow = 1; for (int i = 0; i < n; i++) npow *= n;
    const char *repfile = argv[2];
    FILE *f = fopen(repfile, "r"); if (!f) { fprintf(stderr, "no %s\n", repfile); return 1; }
    nreps = 0; while (1) { int ok = 1; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &reps[nreps][i]) != 1) { ok = 0; break; } if (!ok) break; nreps++; }
    fclose(f);
    build_tables();

    int N = 1 << n;
    long long n_aut = 0, n_stuck = 0, n_stuck_aut = 0, n_pairs = 0;
    long long n_cert = 0, n_uncert = 0, n_zero23 = 0, n_pos23 = 0, n_pos_half = 0, n_bin23 = 0, n_below23 = 0;
    long long n_printed = 0, n_uprinted = 0;
    double best_t = 2; int best_S = 0, best_x = 0; int best_let[2][MAXN]; memset(best_let, 0, sizeof best_let);
    /* worst (= largest) normalised excess n e_t(S) - m over the grid bins strictly below the 2/3 bin */
    double worst_below = -1e300; int wb_S = 0, wb_x = 0, wb_i = 0; int wb_let[2][MAXN]; memset(wb_let, 0, sizeof wb_let);
    long long hist[G + 1]; memset(hist, 0, sizeof hist);
    static double WG[2][G][MAXN]; static double WT[2][G];

    for (int r = 0; r < nreps; r++) {
        if (r % nparts != part) continue;
        memcpy(let[0], reps[r], sizeof(int) * n);
        for (int i = 0; i < n; i++) let[1][i] = 0;                /* odometer for the second letter */
        for (int bcode = 0; bcode < npow; bcode++) {
            if (bcode) { int i = n - 1; while (i >= 0 && ++let[1][i] == n) { let[1][i] = 0; i--; } }
            if (!strongly_connected() || !synchronizing()) continue;
            n_aut++;
            build_pre();
            int stuck[MAXS]; int ns = 0;
            for (int S = 1; S < N - 1; S++) if (minext_capped(S) >= n) stuck[ns++] = S;
            if (!ns) continue;
            n_stuck += ns; n_stuck_aut++;
            tree_poly();
            for (int x = 0; x < 2; x++) for (int i = 0; i < G; i++) {
                double tot = 0;
                for (int q = 0; q < n; q++) { double s = 0; const double *B = BAS[x][i];
                    for (int j = 0; j <= d; j++) s += (double)C[q][j] * B[j];
                    WG[x][i][q] = s; tot += s; }
                WT[x][i] = tot;
            }
            for (int si = 0; si < ns; si++) {
                int S = stuck[si]; int m = __builtin_popcount(S);
                long long CS[MAXN]; for (int j = 0; j <= d; j++) { long long s = 0;
                    for (int q = 0; q < n; q++) if (S >> q & 1) s += C[q][j]; CS[j] = s; }
                for (int x = 0; x < 2; x++) {
                    n_pairs++;
                    /* ---- exact certificate on [1/2, 2/3] ---- */
                    long long A[MAXN];
                    for (int j = 0; j <= d; j++) { long long v = (long long)n * CS[j] - (long long)m * CQ[j];
                        A[x == 0 ? j : d - j] = v; }
                    long long h[MAXN], c[MAXN];
                    for (int i = 0; i <= d; i++) { long long s = 0; for (int j = 0; j <= d; j++) s += A[j] * TPOW[j][i]; h[i] = s; }
                    int allle0 = 1; long long cmax = -0x7fffffffffffffffLL;
                    for (int kk = 0; kk <= d; kk++) { long long s = 0;
                        for (int i = 0; i <= kk; i++) s += BINOM[d - i][kk - i] * h[i];
                        c[kk] = s; if (s > 0) allle0 = 0; if (s > cmax) cmax = s; }
                    if (allle0) n_cert++; else n_uncert++;
                    if (c[d] == 0) n_zero23++; else if (c[d] > 0) n_pos23++;
                    if (c[0] > 0) n_pos_half++;
                    /* ---- grid scan (bias_census.c convention) ---- */
                    int found = G;
                    for (int i = 0; i < G; i++) {
                        if (found != G && i >= BIN23) break;      /* worst_below only needs i < BIN23 */
                        double tot = WT[x][i]; if (!(tot > 0)) continue;
                        double v = 0; for (int q = 0; q < n; q++) if (S >> q & 1) v += WG[x][i][q];
                        double ex = (double)n * v / tot - (double)m;      /* = n e_t(S) - m */
                        if (i < BIN23 && ex > worst_below) { worst_below = ex; wb_S = S; wb_x = x; wb_i = i; memcpy(wb_let, let, sizeof wb_let); }
                        if (found == G && ex >= -1e-9 * n) { found = i; }
                    }
                    hist[found]++;
                    if (found <= BIN23) {
                        if (found == BIN23) n_bin23++; else n_below23++;
                        if (n_printed < MAXPRINT) { n_printed++;
                            printf("BOUNDARY n=%d ", n); print_aut(stdout);
                            printf("S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q);
                            printf("} biased=%c bin=%d grid_t=%.4f exact6dF_half=%lld exact6dF_23=%lld cert=%d\n",
                                   'a' + x, found, 0.5 + found / 400.0, c[0], c[d], allle0); fflush(stdout); }
                    }
                    if (!allle0 && n_uprinted < MAXUNC) { n_uprinted++;
                        printf("UNCERT n=%d ", n); print_aut(stdout);
                        printf("S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q);
                        printf("} biased=%c bin=%d cmax=%lld c0=%lld cd=%lld\n", 'a' + x, found, cmax, c[0], c[d]); fflush(stdout); }
                    if (found < G) { double tg = 0.5 + found / 400.0;
                        if (tg < best_t - 1e-12) { best_t = tg; best_S = S; best_x = x; memcpy(best_let, let, sizeof best_let); } }
                }
            }
        }
        fprintf(stderr, "[part %d/%d] rep %d/%d automata=%lld stuck=%lld best_t=%.4f bin23=%lld below23=%lld uncert=%lld\n",
                part, nparts, r + 1, nreps, n_aut, n_stuck, best_t, n_bin23, n_below23, n_uncert); fflush(stderr);
    }
    /* bisection refinement of the best pair, on the exact tree polynomial */
    double lo = best_t - 1 / 400.0, hi = best_t; if (lo < 0.5) lo = 0.5;
    if (best_t < 2) {
        memcpy(let, best_let, sizeof let); tree_poly();
        int m = __builtin_popcount(best_S);
        long long CS[MAXN]; for (int j = 0; j <= d; j++) { long long s = 0;
            for (int q = 0; q < n; q++) if (best_S >> q & 1) s += C[q][j]; CS[j] = s; }
        long long A[MAXN];
        for (int j = 0; j <= d; j++) A[best_x == 0 ? j : d - j] = (long long)n * CS[j] - (long long)m * CQ[j];
        for (int it = 0; it < 60; it++) { double mid = 0.5 * (lo + hi);
            double F = 0; for (int j = 0; j <= d; j++) { double b = 1;
                for (int rr = 0; rr < j; rr++) b *= mid; for (int rr = 0; rr < d - j; rr++) b *= 1 - mid; F += (double)A[j] * b; }
            if (F >= 0) hi = mid; else lo = mid; }
    }
    printf("DONE bias_census_exact n=%d part=%d/%d automata=%lld stuck_subsets=%lld automata_with_stuck=%lld pairs=%lld"
           " min_t*=%.6f (refined %.6f) bin23_pairs=%lld below23_pairs=%lld heavy_at_half=%lld"
           " exact_zero_at_23=%lld exact_pos_at_23=%lld certified_le0_on_[1/2,2/3]=%lld uncertified=%lld"
           " max_excess_below_bin23=%.12g attained by ",
           n, part, nparts, n_aut, n_stuck, n_stuck_aut, n_pairs, best_t, hi, n_bin23, n_below23,
           n_pos_half, n_zero23, n_pos23, n_cert, n_uncert, worst_below);
    if (best_t < 2) { memcpy(let, best_let, sizeof let); print_aut(stdout); printf("S={");
        for (int q = 0; q < n; q++) if (best_S >> q & 1) printf("%d,", q); printf("} biased letter=%c", 'a' + best_x); }
    printf("\n");
    if (worst_below > -1e299) { memcpy(let, wb_let, sizeof let);
        printf("WORSTBELOW n=%d ", n); print_aut(stdout); printf("S={");
        for (int q = 0; q < n; q++) if (wb_S >> q & 1) printf("%d,", q);
        printf("} biased=%c bin=%d grid_t=%.4f  n e_t(S) - m = %.12g\n", 'a' + wb_x, wb_i, 0.5 + wb_i / 400.0, worst_below); }
    printf("HIST (threshold grid 0.5+i/400; last bin = never): ");
    for (int i = 0; i <= G; i++) if (hist[i]) printf(" [%d:%lld]", i, hist[i]);
    printf("\n");
    return 0;
}
