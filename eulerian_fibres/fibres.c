/* fibres.c -- the Eulerian fibre: synchronizing Eulerian binary automata and the maximum of minext per subset size
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Section 5.2 (and Appendix A): over all synchronizing Eulerian binary automata at n = 4 through n = 9
 *   (72, 954, 12,228, 192,582, 3,212,088 and 59,605,126 automata in the quotient convention), the maximum of
 *   minext over the subsets of size m is n-1 when gcd(m,n) = 1 and n-2 otherwise; by subset size the maxima run
 *   3,2,3; 4,4,4,4; 5,4,4,4,5; 6,6,6,6,6,6; 7,6,7,6,7,6,7 and 8,8,7,8,8,7,8,8.
 *
 * Population / convention: binary automata on Q = {0,...,n-1} in the quotient convention of Appendix A.1.  An
 *   automaton is Eulerian when every state has exactly two incoming edges, counting both letters.  The first
 *   letter a ranges over one representative of each conjugacy class of endofunctions (the file written by
 *   class_reps.c), the second letter b over ALL maps with the complementary in-degree profile
 *   |b^{-1}(q)| = 2 - |a^{-1}(q)| (enumerated as the distinct arrangements of the multiset of targets), followed by
 *   the synchronization filter (a synchronizing Eulerian automaton is strongly connected; this is checked anyway).
 *   For every automaton, minext(S) is computed for EVERY proper nonempty subset S by a reverse multi-source
 *   breadth-first search per size m (distance to a subset of size > m, capped at n), and the census reports, per
 *   subset size m, the maximum of minext over all (automaton, subset) pairs, the number of pairs attaining n-1,
 *   the number beyond n-1, and the histogram of minext values.
 *
 * Usage:    gcc -O2 -o fibres fibres.c
 *           gcc -O2 -o class_reps class_reps.c
 *           class_reps n reps_n.txt
 *           fibres n reps_n.txt                       whole population
 *           fibres n reps_n.txt part nparts           the representatives with index r % nparts == part
 *           python stationary/sum_parts.py OUT_0 ... OUT_{nparts-1}      adds up the DONE lines of the parts
 *
 * Output:   one line (stdout)
 *             DONE fibres n= part=p/nparts candidates= eulerian_sync_automata= per_size_max_minext=[m=1..n-1]
 *                  pairs_at_n-1_by_size=[...] pairs_beyond_n-1_by_size=[...] hist={m<size>:d<minext>:<count>,...}
 *           eulerian_sync_automata is the fibre size, per_size_max_minext the maxima quoted in Section 5.2
 *           (d = n in hist and pairs_beyond_n-1_by_size means no extension within n-1); candidates counts the
 *           Eulerian pairs (a,b) before the synchronization filter.  Progress lines go to stderr.
 *
 * Runtime:  n <= 7 under 3 seconds; n = 8 about 2 minutes on one core; n = 9 about 80 minutes wall in 4 parts on 4 cores.
 * Requires: gcc or clang (the code uses __builtin_popcount and __builtin_ctz).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 10
#define MAXS (1 << MAXN)
#define MAXREPS 20000

static int n; static const int k = 2;
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
/* pre[x][S] = S x^{-1} = {p : p.x in S}, as bit masks */
static int pre[2][MAXS];
static void build_pre(void) {
    int pre1[2][MAXN];
    for (int x = 0; x < k; x++) { for (int q = 0; q < n; q++) pre1[x][q] = 0;
        for (int p = 0; p < n; p++) pre1[x][let[x][p]] |= 1 << p; }
    int N = 1 << n;
    for (int x = 0; x < k; x++) { pre[x][0] = 0;
        for (int S = 1; S < N; S++) { int low = S & -S; pre[x][S] = pre[x][S ^ low] | pre1[x][__builtin_ctz(low)]; } }
}
/* reverse adjacency of the preimage graph: for each T, the list of S with S x^{-1} = T for some letter x */
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
/* minext for all subsets of size m: dist_[S] = least word length with |S u^{-1}| > m, capped at n (= no growth within n-1) */
static void minext_of_size(int m) {
    int N = 1 << n, qh = 0, qt = 0;
    for (int S = 0; S < N; S++) dist_[S] = -1;
    for (int T = 1; T < N; T++) if (__builtin_popcount(T) > m) { dist_[T] = 0; queue_[qt++] = T; }
    while (qh < qt) {
        int T = queue_[qh++], dd = dist_[T];
        if (dd >= n - 1) continue;
        for (int e = rev_head[T]; e != -1; e = rev_next[e]) { int S = rev_node[e];
            if (dist_[S] < 0) { dist_[S] = dd + 1; queue_[qt++] = S; } }
    }
}

/* ---------- enumeration of b with in-degree c[q] = 2 - |a^{-1}(q)| ---------- */
static int cnt_[MAXN];                       /* remaining multiplicity of each target */
static long long n_aut = 0, n_cand = 0;
static long long hist[MAXN + 1][MAXN + 1];   /* hist[m][d]: pairs with |S| = m and minext = d (d = n means > n-1) */
static void process(void) {
    n_cand++;
    if (!synchronizing() || !strongly_connected()) return;
    n_aut++;
    build_pre(); build_rev();
    int N = 1 << n;
    for (int m = 1; m <= n - 1; m++) {
        minext_of_size(m);
        for (int S = 1; S < N - 1; S++) if (__builtin_popcount(S) == m) {
            int d = dist_[S] < 0 ? n : dist_[S];
            hist[m][d]++;
        }
    }
}
static void assign(int p) {
    if (p == n) { process(); return; }
    for (int q = 0; q < n; q++) if (cnt_[q] > 0) { cnt_[q]--; let[1][p] = q; assign(p + 1); cnt_[q]++; }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: fibres n repsfile [part nparts]\n"); return 1; }
    n = atoi(argv[1]);
    if (n < 2 || n > MAXN) { fprintf(stderr, "n out of range\n"); return 1; }
    int part = 0, nparts = 1; if (argc >= 5) { part = atoi(argv[3]); nparts = atoi(argv[4]); }
    FILE *f = fopen(argv[2], "r"); if (!f) { fprintf(stderr, "cannot open %s\n", argv[2]); return 1; }
    nreps = 0;
    while (nreps < MAXREPS) { int ok = 1; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &reps[nreps][i]) != 1) { ok = 0; break; } if (!ok) break; nreps++; }
    fclose(f);
    memset(hist, 0, sizeof hist);
    fprintf(stderr, "fibres n=%d reps=%d part=%d/%d\n", n, nreps, part, nparts);
    for (int r = 0; r < nreps; r++) {
        if (r % nparts != part) continue;
        memcpy(let[0], reps[r], sizeof(int) * n);
        int indeg[MAXN]; for (int q = 0; q < n; q++) indeg[q] = 0;
        for (int p = 0; p < n; p++) indeg[let[0][p]]++;
        int ok = 1; for (int q = 0; q < n; q++) { if (indeg[q] > 2) ok = 0; cnt_[q] = 2 - indeg[q]; }
        if (!ok) continue;                                  /* a alone already exceeds in-degree 2 somewhere */
        assign(0);
        if (((r / nparts) & 63) == 0) { fprintf(stderr, "[part %d/%d] rep %d/%d candidates=%lld eulerian_sync=%lld\n", part, nparts, r + 1, nreps, n_cand, n_aut); fflush(stderr); }
    }
    printf("DONE fibres n=%d part=%d/%d candidates=%lld eulerian_sync_automata=%lld", n, part, nparts, n_cand, n_aut);
    printf(" per_size_max_minext=[");
    for (int m = 1; m <= n - 1; m++) { int mx = 0; for (int d = 0; d <= n; d++) if (hist[m][d]) mx = d; printf("%d%s", mx, m < n - 1 ? "," : ""); }
    printf("] pairs_at_n-1_by_size=[");
    for (int m = 1; m <= n - 1; m++) printf("%lld%s", hist[m][n - 1], m < n - 1 ? "," : "");
    printf("] pairs_beyond_n-1_by_size=[");
    for (int m = 1; m <= n - 1; m++) printf("%lld%s", hist[m][n], m < n - 1 ? "," : "");
    printf("] hist={");
    for (int m = 1; m <= n - 1; m++) for (int d = 0; d <= n; d++) if (hist[m][d]) printf("m%d:d%d:%lld,", m, d, hist[m][d]);
    printf("}\n"); fflush(stdout);
    return 0;
}
