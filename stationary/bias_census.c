/* bias_census.c -- the bias a stuck subset needs: least letter weight t >= 1/2 at which it carries its share of the
 * stationary vector, over every stuck subset of every binary automaton of a population (floating point, grid 1/400)
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Section 7.3 and Appendix C: give the letters the weights (t, 1-t) and let t*(S) be the least t >= 1/2 with
 *   n e_t(S) >= |S| e_t(Q), either letter carrying t.  Over every stuck subset of every synchronizing strongly connected
 *   binary automaton in the quotient convention: min t* = 1 at n = 4 (1,240 automata); exhaustively at n = 5, 6, 7
 *   (32,588, 1,122,529 and 42,605,958 automata with 11,042, 186,497 and 2,827,614 stuck subsets) the minimum of t* is
 *   2/3, attained by 9, 8 and 116 pairs (automaton, subset, biased letter), and no pair has t* in (1/2, 2/3).
 *   Appendix A: the bias census at n <= 7 was produced by two implementations on a grid of step 1/400, agreeing on
 *   every histogram bin (this program and bias_census_exact.c; compare with compare_histograms.py).
 *   The EXTREMAL lines are the input of boundary_classes.py (the 133 attaining pairs, their exact threshold 2/3 and
 *   their isomorphism classes).
 *
 * Method:   for each stuck subset S (minext(S) > n-1, breadth-first search over preimage sets) and each letter order x
 *   (weight t on letter x, 1-t on the other), the stationary vector e_t of t pi(x) + (1-t) pi(y), normalised to sum 1,
 *   is computed by Gaussian elimination with partial pivoting at every grid point t = 1/2 + i/400, i = 0..200;
 *   the pair's grid threshold is the least i with e_t(S) >= |S|/n - 1e-9 (bin 201 = never, not even at t = 1).
 *   The smallest grid threshold is then refined by 40 bisection steps on [t - 1/400, t].
 *
 * Population / convention: first letter over the representatives file (class_reps.c: all conjugacy classes of
 *   endofunctions, Appendix A.1), second letter over all n^n maps; synchronizing and strongly connected automata only.
 *
 * Usage:    gcc -O2 -o bias_census bias_census.c -lm
 *           bias_census n repsfile [part nparts]      parts take the representatives with index r % nparts == part
 *           python sum_parts.py OUT_0 ... OUT_{nparts-1}
 *
 * Output:   EXTREMAL n= a=[..] b=[..]  S={..} biased=x grid_t=     every pair with grid threshold <= bin 67 (t <= 0.6675,
 *                                                                 the bin that contains 2/3)
 *           DONE bias_census n= part= automata= stuck_subsets= automata_with_stuck= min_t*= (refined ) attained by ...
 *           HIST (threshold grid 0.5+i/400; last bin = never):  [i:count] ...
 *           automata and stuck_subsets are the population and stuck-subset counts; HIST counts (subset, order) pairs by
 *           grid bin i (t = 0.5 + i/400; bin 67 = (0.665, 0.6675] holds 2/3; bin 200 = t = 1; bin 201 = never), so
 *           "nothing in (1/2, 2/3)" reads as: no bin 0..66.  Progress lines go to stderr.
 *
 * Runtime:  n = 4, 5 under a second; n = 6 about 10 seconds; n = 7 about 5.5 minutes wall in 2 parts on 2 cores.
 * Requires: gcc or clang (the code uses __builtin_popcount and __builtin_ctz), libm; n <= 8.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXN 8
#define MAXS (1 << MAXN)
static int n; static const int k = 2;
static int let[2][MAXN];
static int npow, nreps; static int reps[4000][MAXN];
static void decode(int code, int *f) { for (int i = n - 1; i >= 0; i--) { f[i] = code % n; code /= n; } }
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
/* minext(S) capped at n: returns t <= n-1 if some |S u^{-1}| > |S| with |u| = t, else n (stuck) */
static int minext_capped(int S) {
    static unsigned char seen[MAXS]; static int cur[MAXS], nxt[MAXS];
    int N = 1 << n, m = __builtin_popcount(S);
    memset(seen, 0, N); seen[S] = 1; cur[0] = S; int nc = 1;
    for (int t = 1; t <= n - 1; t++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) for (int x = 0; x < k; x++) {
            int T = pre[x][cur[i]];
            if (__builtin_popcount(T) > m) return t;
            if (!seen[T]) { seen[T] = 1; nxt[nn++] = T; }
        }
        if (nn == 0) return n;
        memcpy(cur, nxt, sizeof(int) * nn); nc = nn;
    }
    return n;
}
/* stationary vector (sum 1) of t*pi(x) + (1-t)*pi(y), x = first letter index, by Gaussian elimination */
static int stationary(int x, double t, double *e) {
    int y = 1 - x; double A[MAXN][MAXN + 1]; memset(A, 0, sizeof A);
    /* equations: for each q: sum_p e_p (t[p.x=q] + (1-t)[p.y=q]) - e_q = 0 ; replace last with sum e = 1 */
    for (int p = 0; p < n; p++) { A[let[x][p]][p] += t; A[let[y][p]][p] += 1 - t; }
    for (int q = 0; q < n; q++) A[q][q] -= 1;
    for (int p = 0; p < n; p++) A[n - 1][p] = 1; A[n - 1][n] = 1;
    for (int c = 0; c < n; c++) {
        int piv = c; for (int r = c + 1; r < n; r++) if (fabs(A[r][c]) > fabs(A[piv][c])) piv = r;
        if (fabs(A[piv][c]) < 1e-12) return 0;
        if (piv != c) for (int j = 0; j <= n; j++) { double tmp = A[c][j]; A[c][j] = A[piv][j]; A[piv][j] = tmp; }
        for (int r = 0; r < n; r++) if (r != c) { double f = A[r][c] / A[c][c]; if (f != 0) for (int j = c; j <= n; j++) A[r][j] -= f * A[c][j]; }
    }
    for (int c = 0; c < n; c++) e[c] = A[c][n] / A[c][c];
    return 1;
}
static void print_aut(FILE *f) {
    for (int x = 0; x < k; x++) { fprintf(f, "%c=[", 'a' + x); for (int p = 0; p < n; p++) fprintf(f, "%d%s", let[x][p], p + 1 < n ? "," : ""); fprintf(f, "] "); }
}
#define G 201     /* grid t = 0.5 + i/400 */
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: bias_census n repsfile [part nparts]\n"); return 1; }
    n = atoi(argv[1]); int part = 0, nparts = 1; if (argc >= 5) { part = atoi(argv[3]); nparts = atoi(argv[4]); }
    npow = 1; for (int i = 0; i < n; i++) npow *= n;
    const char *repfile = argv[2];
    FILE *f = fopen(repfile, "r"); if (!f) { fprintf(stderr, "no %s\n", repfile); return 1; }
    nreps = 0; while (1) { int ok = 1; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &reps[nreps][i]) != 1) { ok = 0; break; } if (!ok) break; nreps++; }
    fclose(f);
    int N = 1 << n; long long n_aut = 0, n_stuck = 0, n_stuck_aut = 0;
    double best_t = 2; int best_S = 0, best_x = 0; int best_let[2][MAXN];
    long long hist[G + 1]; memset(hist, 0, sizeof hist);   /* histogram of per-(S,order) thresholds (grid index), G = never */
    static double et[2][G][MAXN]; static unsigned char valid[2][G];
    for (int r = 0; r < nreps; r++) {
        if (r % nparts != part) continue;
        memcpy(let[0], reps[r], sizeof(int) * n);
        for (int bcode = 0; bcode < npow; bcode++) {
            decode(bcode, let[1]);
            if (!strongly_connected() || !synchronizing()) continue;
            n_aut++;
            build_pre();
            int stuck[MAXS]; int ns = 0;
            for (int S = 1; S < N - 1; S++) if (minext_capped(S) >= n) stuck[ns++] = S;
            if (!ns) continue;
            n_stuck += ns; n_stuck_aut++;
            for (int x = 0; x < 2; x++) for (int i = 0; i < G; i++) valid[x][i] = stationary(x, 0.5 + i / 400.0, et[x][i]);
            for (int s = 0; s < ns; s++) { int S = stuck[s]; int m = __builtin_popcount(S); double need = (double)m / n - 1e-9;
                for (int x = 0; x < 2; x++) {
                    int found = G;
                    for (int i = 0; i < G; i++) { if (!valid[x][i]) continue; double v = 0; for (int q = 0; q < n; q++) if (S >> q & 1) v += et[x][i][q];
                        if (v >= need) { found = i; break; } }
                    hist[found]++;
                    if (found <= 67) { printf("EXTREMAL n=%d ", n); print_aut(stdout); printf(" S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q); printf("} biased=%c grid_t=%.4f\n", 'a' + x, 0.5 + found / 400.0); fflush(stdout); }
                    if (found < G) { double tg = 0.5 + found / 400.0;
                        if (tg < best_t - 1e-12) { best_t = tg; best_S = S; best_x = x; memcpy(best_let, let, sizeof best_let); } }
                }
            }
        }
        fprintf(stderr, "[part %d/%d] rep %d/%d automata=%lld stuck=%lld best_t=%.4f\n", part, nparts, r + 1, nreps, n_aut, n_stuck, best_t); fflush(stderr);
    }
    /* refine best by bisection */
    double lo = best_t - 1 / 400.0, hi = best_t; if (lo < 0.5) lo = 0.5;
    if (best_t < 2) { memcpy(let, best_let, sizeof let); int m = __builtin_popcount(best_S); double need = (double)m / n;
        for (int it = 0; it < 40; it++) { double mid = 0.5 * (lo + hi); double e[MAXN]; stationary(best_x, mid, e); double v = 0; for (int q = 0; q < n; q++) if (best_S >> q & 1) v += e[q];
            if (v >= need - 1e-12) hi = mid; else lo = mid; } }
    printf("DONE bias_census n=%d part=%d/%d automata=%lld stuck_subsets=%lld automata_with_stuck=%lld min_t*=%.6f (refined %.6f) attained by ", n, part, nparts, n_aut, n_stuck, n_stuck_aut, best_t, hi);
    if (best_t < 2) { memcpy(let, best_let, sizeof let); print_aut(stdout); printf("S={"); for (int q = 0; q < n; q++) if (best_S >> q & 1) printf("%d,", q); printf("} biased letter=%c", 'a' + best_x); }
    printf("\nHIST (threshold grid 0.5+i/400; last bin = never): ");
    for (int i = 0; i <= G; i++) if (hist[i]) printf(" [%d:%lld]", i, hist[i]);
    printf("\n");
    return 0;
}
