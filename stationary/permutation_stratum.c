/* permutation_stratum.c -- uniform-weight census and bias census of binary automata, with orbit reduction under the
 * centraliser of a permutation first letter (built for the permutation-first strata at n = 8 and n = 9)
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Appendix C: on the stratum of the binary n = 9 population whose first letter is a permutation (30 cycle types, all
 *     9^9 second letters): 3,761,587,885 automata, 278,959,029 stuck subsets, no stuck subset with B_e(S) >= 0 at
 *     uniform weights, the largest value of B_e on a stuck subset being -1 (none heavy at t = 1/2); the least bias
 *     threshold is below 2/3 for 384 + 32 pairs (grid bins 38 and 58) and equals 2/3 for 1,568 pairs (bin 67).  The
 *     14 distinct BOUNDARY orbits of these 1,984 pairs are the input of exact_thresholds.py, which gives the roots
 *     0.594 of 11t^2 - 20t + 8 (384 pairs), 0.643 of t^3 + 8t^2 - 18t + 8 (32) and 2/3 (1,568).
 *   Appendix A: the n = 9 stratum "was produced by a further implementation, which enumerates one second letter per
 *     orbit of the centraliser of the first and weights by the orbit size, after reproducing the n = 8 stratum digit
 *     for digit": 123,014,054 automata, 18,609,570 stuck subsets, 7,484,632 automata with a stuck subset, maximum of
 *     B_e on stuck subsets -1, threshold bins {35: 384, 42: 32, 67: 32}.  With the file of all conjugacy classes it
 *     is also the second implementation of the uniform-weight maxima of B_e (-1) on the binary populations n = 5, 6, 7
 *     (32,588 / 11,042, 1,122,529 / 186,497, 42,605,958 / 2,827,614 automata / stuck subsets) and of the bias
 *     histogram bins <= 67 there (9, 8 and 116 pairs at bin 67, none below).
 *
 * Population / convention: binary synchronizing strongly connected complete automata in the quotient convention of
 *   Appendix A.1: first letter over the representatives file (permutation_reps.py n: one permutation per cycle type,
 *   the permutation-first stratum; or class_reps.c: all conjugacy classes of endofunctions), second letter over all
 *   n^n maps.
 *
 * Method:   stuck subsets of every size at once by n-1 reverse multi-source breadth-first searches over the preimage
 *   graph of subsets.  At t = 1/2 the stationary vector is the in-tree count, e_q proportional to T_q (the number of
 *   spanning in-trees rooted at q), so "S heavy" is the exact integer test n T(S) >= |S| T(Q), and
 *   B_e(S) = (n T(S) - |S| T(Q)) / gcd_q T_q; a HIT is a stuck subset that is heavy at t = 1/2.  T_q = sum_j C[q][j],
 *   C[q][j] = number of in-trees rooted at q with j first-letter edges, by the enumeration of the 2^n letter-choice
 *   functions of bias_census_exact.c.  Orbit reduction: when the first letter a is a permutation, only the
 *   lexicographically least conjugate of b under the centraliser C(a) is kept and every counter is weighted by the
 *   orbit size |C(a)| / |Stab(b)|, so that the weighted counters equal the quotient-convention counts (no reduction when
 *   a is not a permutation or |C(a)| > 1024).  Mode thr: for every stuck subset S and each letter order x (weight t on
 *   letter x, 1-t on the other, t on the grid 1/2 + i/400, i = 0..200), the least grid t with n e_t(S) >= |S| e_t(Q),
 *   computed from the polynomial w_q(t) = sum_j C[q][j] t^j (1-t)^{n-1-j} with the grid, tolerance and BOUNDARY
 *   convention of bias_census_exact.c, so that the weighted histogram reproduces that program's pair histogram.
 *
 * Usage:    gcc -O2 -o permutation_stratum permutation_stratum.c
 *           python permutation_reps.py 9 reps_perm_9.txt           (30 cycle types; 22 at n = 8)
 *           permutation_stratum n repsfile [part nparts] [census] [thr]
 *             census: stuck-subset counts and the maximum and histogram of B_e on stuck subsets; thr: bias thresholds;
 *             parts take the representatives with index r % nparts == part.  The paper's runs use census thr:
 *             n = 9 and n = 8 on the permutation cycle types (n = 9 in 4 parts, n = 8 in 1 or 2), n = 5, 6, 7 on all
 *             classes (n = 7 in 2 parts).
 *           python sum_parts.py OUT_0 ... OUT_{nparts-1}              totals of the parts
 *           python exact_thresholds.py OUT_0 ... OUT_{nparts-1}       exact thresholds of the BOUNDARY lines
 *
 * Output:   HIT n= a=[..] b=[..] S={..} m= e=[..] Be= orbit=            a stuck subset with B_e >= 0 (never printed on
 *                                                                        the populations above)
 *           BOUNDARY n= a=[..] b=[..] S={..} biased=x bin= grid_t= orbit=   a canonical pair with grid bin <= 67; it
 *                                                                        stands for `orbit` pairs of the population
 *           DONE permutation_stratum n= part= census= thr= automata= canonical_reps= stuck_subsets=
 *                automata_with_stuck= hits_heavy_and_stuck= hits_weighted= automata_with_hit= automata_with_hit_weighted=
 *                max_Be_on_stuck= hist_Be_on_stuck={value:count,...}                                    (with census)
 *                pairs= min_grid_t= bin23_pairs= below23_pairs= attained_by ... hist_bins<=67={bin:count,...} (with thr)
 *   automata, stuck_subsets, automata_with_stuck, hits_weighted, automata_with_hit_weighted, the B_e histogram and all
 *   thr counters are orbit-weighted (quotient-convention counts); canonical_reps, hits_heavy_and_stuck and
 *   automata_with_hit count canonical representatives.  hist_Be_on_stuck clamps values below -32 to -32 (and above 31
 *   to 31).  Progress lines go to stderr.
 *
 * Runtime:  n = 5, 6 under 6 seconds; n = 7 (all classes) about 8 minutes wall in 2 parts on 2 cores; n = 8 stratum
 *           about 7 minutes in 2 parts (263 s and 163 s on one core each); n = 9 stratum between about 1 and 4 hours per
 *           part, 4 parts on 4 cores.
 * Requires: gcc or clang (the code uses __builtin_popcount and __builtin_ctz); n <= 10.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 10
#define MAXS (1 << MAXN)
#define MAXREPS 6000
#define CMAX 1024
#define G 201
#define BIN23 67
#define MAXPRINT 400000

static int n, d; static const int k = 2;
static int let[2][MAXN];
static int nreps; static int reps[MAXREPS][MAXN];

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
static int rev_head[MAXS], rev_next[2 * MAXS], rev_node[2 * MAXS];
static void build_rev(void) {
    int N = 1 << n, idx = 0;
    for (int T = 0; T < N; T++) rev_head[T] = -1;
    for (int S = 1; S < N; S++) for (int x = 0; x < k; x++) {
        int T = pre[x][S];
        rev_node[idx] = S; rev_next[idx] = rev_head[T]; rev_head[T] = idx; idx++;
    }
}
static int dist_[MAXS], queue_[MAXS];
static int stuck_of_size(int m, int *out) {
    int N = 1 << n, qh = 0, qt = 0;
    for (int S = 0; S < N; S++) dist_[S] = -1;
    for (int T = 1; T < N; T++) if (__builtin_popcount(T) > m) { dist_[T] = 0; queue_[qt++] = T; }
    while (qh < qt) {
        int T = queue_[qh++], dd = dist_[T];
        if (dd >= n - 1) continue;
        for (int e = rev_head[T]; e != -1; e = rev_next[e]) { int S = rev_node[e];
            if (dist_[S] < 0) { dist_[S] = dd + 1; queue_[qt++] = S; } }
    }
    int cnt = 0;
    for (int S = 1; S < N - 1; S++) if (dist_[S] < 0 && __builtin_popcount(S) == m) out[cnt++] = S;
    return cnt;
}
/* tree polynomial coefficients C[q][j] (j = number of first-letter edges), T_q = sum_j C[q][j] */
static long long C[MAXN][MAXN], CQ[MAXN], T[MAXN], TQ, TS[MAXS];
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
            if (color[p] == 1) {
                if (++cyclecount >= 2) break;
                int cm = 0, r = p;
                do { cm |= 1 << r; r = let[(mask >> r) & 1][r]; } while (r != p);
                cyclemask = cm;
            }
            int r = s; while (color[r] == 1) { color[r] = 2; r = let[(mask >> r) & 1][r]; }
        }
        if (cyclecount != 1) continue;
        int z = __builtin_popcount(mask);        /* # states using letter 1 */
        int j = n - z - 1;                       /* # states != root using letter 0, given c(root) = 0 */
        if (j < 0) continue;
        int rest = cyclemask & ~mask;            /* roots on the cycle with c(q) = 0 */
        while (rest) { int q = __builtin_ctz(rest); rest &= rest - 1; C[q][j]++; }
    }
    for (int j = 0; j <= d; j++) { long long s = 0; for (int q = 0; q < n; q++) s += C[q][j]; CQ[j] = s; }
    TQ = 0; for (int q = 0; q < n; q++) { long long s = 0; for (int j = 0; j <= d; j++) s += C[q][j]; T[q] = s; TQ += s; }
    TS[0] = 0;
    for (int S = 1; S < N; S++) { int low = S & -S; TS[S] = TS[S ^ low] + T[__builtin_ctz(low)]; }
}
static double BAS[2][G][MAXN];
static void build_tables(void) {
    for (int x = 0; x < 2; x++) for (int i = 0; i < G; i++) {
        double u = x == 0 ? 0.5 + i / 400.0 : 0.5 - i / 400.0, v = 1.0 - u;
        for (int j = 0; j <= d; j++) { double b = 1; for (int r = 0; r < j; r++) b *= u; for (int r = 0; r < d - j; r++) b *= v; BAS[x][i][j] = b; }
    }
}
static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }
static void print_aut(FILE *f) {
    for (int x = 0; x < k; x++) { fprintf(f, "%c=[", 'a' + x); for (int p = 0; p < n; p++) fprintf(f, "%d%s", let[x][p], p + 1 < n ? "," : ""); fprintf(f, "] "); }
}
/* ---------------- centralizer of the first letter (a permutation) ---------------- */
static int cent[CMAX][MAXN], centinv[CMAX][MAXN], ncent, cent_ok;
static int cyc[MAXN][MAXN], clen[MAXN], ncyc;
static int cur_pi[MAXN], used[MAXN];
static void cent_rec(int j) {
    if (!cent_ok) return;
    if (j == ncyc) {
        if (ncent >= CMAX) { cent_ok = 0; return; }
        memcpy(cent[ncent], cur_pi, sizeof(int) * n);
        for (int p = 0; p < n; p++) centinv[ncent][cur_pi[p]] = p;
        ncent++; return;
    }
    for (int t = 0; t < ncyc; t++) if (!used[t] && clen[t] == clen[j]) {
        used[t] = 1;
        for (int r = 0; r < clen[j]; r++) {
            for (int i = 0; i < clen[j]; i++) cur_pi[cyc[j][i]] = cyc[t][(i + r) % clen[j]];
            cent_rec(j + 1);
            if (!cent_ok) { used[t] = 0; return; }
        }
        used[t] = 0;
    }
}
static void build_centralizer(void) {
    const int *a = let[0]; int seen = 0;
    for (int p = 0; p < n; p++) seen |= 1 << a[p];
    ncent = 0; cent_ok = 0;
    if (seen != (1 << n) - 1) return;
    int vis = 0; ncyc = 0;
    for (int s = 0; s < n; s++) if (!(vis >> s & 1)) { int p = s, l = 0;
        do { cyc[ncyc][l++] = p; vis |= 1 << p; p = a[p]; } while (p != s); clen[ncyc++] = l; }
    for (int t = 0; t < ncyc; t++) used[t] = 0;
    cent_ok = 1; cent_rec(0);
    if (!cent_ok) ncent = 0;
}
static int canonical(int *stab) {
    const int *b = let[1]; int st = 1;
    for (int c = 1; c < ncent; c++) {
        const int *pi = cent[c], *pinv = centinv[c];
        int cmp = 0;
        for (int q = 0; q < n; q++) { int v = pi[b[pinv[q]]];
            if (v < b[q]) { cmp = -1; break; } if (v > b[q]) { cmp = 1; break; } }
        if (cmp < 0) return 0;
        if (cmp == 0) st++;
    }
    *stab = st; return 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: permutation_stratum n repsfile [part nparts] [census] [thr]\n"); return 1; }
    n = atoi(argv[1]); d = n - 1;
    if (n < 2 || n > MAXN) { fprintf(stderr, "n out of range\n"); return 1; }
    int part = 0, nparts = 1, census = 0, thr = 0;
    for (int i = 3; i < argc; i++) { if (!strcmp(argv[i], "census")) census = 1; if (!strcmp(argv[i], "thr")) thr = 1; }
    if (argc >= 5 && strcmp(argv[3], "census") != 0 && strcmp(argv[3], "thr") != 0) { part = atoi(argv[3]); nparts = atoi(argv[4]); }
    const char *repfile = argv[2];
    FILE *f = fopen(repfile, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", repfile); return 1; }
    nreps = 0;
    while (nreps < MAXREPS) { int ok = 1; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &reps[nreps][i]) != 1) { ok = 0; break; } if (!ok) break; nreps++; }
    fclose(f);
    build_tables();
    long long npow = 1; for (int i = 0; i < n; i++) npow *= n;
    long long n_reps_aut = 0, w_aut = 0, w_stuck_aut = 0, w_stuck = 0, n_hits = 0, w_hits = 0, n_hit_aut = 0, w_hit_aut = 0;
    long long maxBe_stuck = -(1LL << 60); long long hist_be[64]; memset(hist_be, 0, sizeof hist_be);
    long long hist[G + 1]; memset(hist, 0, sizeof hist); long long w_pairs = 0, w_bin23 = 0, w_below23 = 0, n_printed = 0;
    double best_t = 2; int best_S = 0, best_x = 0; int best_let[2][MAXN];
    static int stuck[MAXS];
    static double WG[2][G][MAXN], WT[2][G];
    fprintf(stderr, "permutation_stratum n=%d reps=%d part=%d/%d census=%d thr=%d\n", n, nreps, part, nparts, census, thr);
    for (int r = 0; r < nreps; r++) {
        if (r % nparts != part) continue;
        memcpy(let[0], reps[r], sizeof(int) * n);
        build_centralizer();
        for (int i = 0; i < n; i++) let[1][i] = 0;
        for (long long bcode = 0; bcode < npow; bcode++) {
            if (bcode) { int i = n - 1; while (i >= 0 && ++let[1][i] == n) { let[1][i] = 0; i--; } }
            long long orbit = 1; int stab = 1;
            if (ncent > 1 && ncent <= 64 && !canonical(&stab)) continue;
            if (!strongly_connected() || !synchronizing()) continue;
            if (ncent > 64 && !canonical(&stab)) continue;
            if (ncent > 1) orbit = ncent / stab;
            n_reps_aut++; w_aut += orbit;
            build_pre(); build_rev();
            int ns = 0;
            for (int m = 1; m <= n - 1; m++) ns += stuck_of_size(m, stuck + ns);
            if (!ns) continue;
            w_stuck_aut += orbit; w_stuck += (long long)ns * orbit;
            tree_poly();
            long long g = 0; for (int q = 0; q < n; q++) g = gcdll(g, T[q]);
            if (thr) for (int x = 0; x < 2; x++) for (int i = 0; i < G; i++) {
                double tot = 0;
                for (int q = 0; q < n; q++) { double s = 0; const double *B = BAS[x][i];
                    for (int j = 0; j <= d; j++) s += (double)C[q][j] * B[j];
                    WG[x][i][q] = s; tot += s; }
                WT[x][i] = tot;
            }
            int aut_hit = 0;
            for (int si = 0; si < ns; si++) {
                int S = stuck[si], m = __builtin_popcount(S);
                long long num = (long long)n * TS[S] - (long long)m * TQ;
                long long be = num / g;
                if (census) { if (be > maxBe_stuck) maxBe_stuck = be;
                    int bi = (int)(be + 32); if (bi < 0) bi = 0; if (bi > 63) bi = 63; hist_be[bi] += orbit; }
                if (num >= 0) {
                    n_hits++; w_hits += orbit; aut_hit = 1;
                    printf("HIT n=%d ", n); print_aut(stdout);
                    printf("S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q);
                    printf("} m=%d e=[", m); for (int q = 0; q < n; q++) printf("%lld%s", T[q] / g, q + 1 < n ? "," : "");
                    printf("] Be=%lld orbit=%lld\n", be, orbit); fflush(stdout);
                }
                if (thr) for (int x = 0; x < 2; x++) {
                    w_pairs += orbit;
                    int found = G;
                    for (int i = 0; i < G; i++) {
                        double tot = WT[x][i]; if (!(tot > 0)) continue;
                        double v = 0; for (int q = 0; q < n; q++) if (S >> q & 1) v += WG[x][i][q];
                        double ex = (double)n * v / tot - (double)m;
                        if (ex >= -1e-9 * n) { found = i; break; }
                    }
                    hist[found] += orbit;
                    if (found <= BIN23) {
                        if (found == BIN23) w_bin23 += orbit; else w_below23 += orbit;
                        if (n_printed < MAXPRINT) { n_printed++;
                            printf("BOUNDARY n=%d ", n); print_aut(stdout);
                            printf("S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q);
                            printf("} biased=%c bin=%d grid_t=%.4f orbit=%lld\n", 'a' + x, found, 0.5 + found / 400.0, orbit); fflush(stdout); }
                    }
                    if (found < G) { double tg = 0.5 + found / 400.0;
                        if (tg < best_t - 1e-12) { best_t = tg; best_S = S; best_x = x; memcpy(best_let, let, sizeof best_let); } }
                }
            }
            if (aut_hit) { n_hit_aut++; w_hit_aut += orbit; }
        }
        fprintf(stderr, "[part %d/%d] rep %d/%d |C(a)|=%d automata_w=%lld reps=%lld stuck_w=%lld hits=%lld best_t=%.4f below23_w=%lld bin23_w=%lld\n",
                part, nparts, r + 1, nreps, ncent, w_aut, n_reps_aut, w_stuck, n_hits, best_t, w_below23, w_bin23); fflush(stderr);
    }
    printf("DONE permutation_stratum n=%d part=%d/%d census=%d thr=%d automata=%lld canonical_reps=%lld stuck_subsets=%lld automata_with_stuck=%lld hits_heavy_and_stuck=%lld hits_weighted=%lld automata_with_hit=%lld automata_with_hit_weighted=%lld",
           n, part, nparts, census, thr, w_aut, n_reps_aut, w_stuck, w_stuck_aut, n_hits, w_hits, n_hit_aut, w_hit_aut);
    if (census) { printf(" max_Be_on_stuck=%lld hist_Be_on_stuck={", maxBe_stuck);
        for (int bi = 0; bi < 64; bi++) if (hist_be[bi]) printf("%d:%lld,", bi - 32, hist_be[bi]); printf("}"); }
    if (thr) { printf(" pairs=%lld min_grid_t=%.4f bin23_pairs=%lld below23_pairs=%lld", w_pairs, best_t, w_bin23, w_below23);
        if (best_t < 2) { printf(" attained_by "); memcpy(let, best_let, sizeof let); print_aut(stdout);
            printf("S={"); for (int q = 0; q < n; q++) if (best_S >> q & 1) printf("%d,", q); printf("} biased=%c", 'a' + best_x); }
        printf(" hist_bins<=%d={", BIN23); for (int i = 0; i <= BIN23; i++) if (hist[i]) printf("%d:%lld,", i, hist[i]); printf("}"); }
    printf("\n"); fflush(stdout);
    return 0;
}
