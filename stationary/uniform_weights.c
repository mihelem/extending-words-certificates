/* uniform_weights.c -- the stationary-vector functional B_e at uniform letter weights on stuck subsets, and the
 * comparison of the regions {B_e >= 0} and {B >= 0}
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Appendix C: with uniform weights no stuck subset has B_e(S) >= 0 and the largest value of B_e on a stuck subset
 *     is -1 on the exhaustive binary populations n = 5 (32,588 automata, 11,042 stuck subsets), n = 6 (1,122,529 /
 *     186,497), n = 7 (42,605,958 / 2,827,614), on the stratum of the binary n = 8 population whose first letter is
 *     a permutation (22 cycle types, all 8^8 second letters: 123,014,054 / 18,609,570), and, with pairwise distinct
 *     letters, on the exhaustive ternary n = 5 population in the multiset convention (138,540,502 automata).
 *   Section 7.3: "Exhaustively there is no such subset at n <= 7" (a stuck subset with B_e(S) >= 0 in a two-letter
 *     automaton at equal letter weights).
 *   Appendix C (incomparability): at n = 5, {B_e >= 0} holds 17,037 proper-subset instances that {B >= 0} misses and
 *     misses 9,793 that it holds; at n = 4, 115 of the 7,460 proper-subset instances in H# have B_e >= 0, none of them
 *     stuck; the populations n = 4, 5, 6 binary and n = 4 ternary have 17,360 + 977,640 + 69,596,798 + 5,534,186 =
 *     76,125,984 proper-subset instances.
 *
 * Definitions: e is the positive left eigenvector of M = sum_x pi(x) with e^T M = k e^T, scaled to coprime positive
 *   integers (computed exactly as a row of cofactors of (M - kI)^T, Bareiss determinants); B_e(S) = n e(S) - |S| e(Q).
 *   S is stuck when minext(S) > n-1 (breadth-first search over preimage sets, cap n-1).  In mode `regions` also
 *   sigma_t(S) = sum_q in S indeg_t(q) - k^t |S| (indeg_t(q) = number of words of length t leading into q),
 *   B(S) = sum_{t=1}^{n-1} k^{n-1-t} sigma_t(S), and H# = {S : sigma_t(S) <= 0 for all t <= n-1, not all = 0}.
 *
 * Population / convention: synchronizing strongly connected complete automata with k = 2 or 3 letters in the
 *   quotient convention of Appendix A.1: the first letter over the representatives file (class_reps.c for all
 *   endofunction classes; permutation_reps.py for the permutation cycle types of the n = 8 stratum), the second
 *   letter over all n^n maps, and at k = 3 the third letter c over all maps with code(c) >= code(b) (multisets).
 *
 * Usage:    gcc -O2 -o uniform_weights uniform_weights.c
 *           uniform_weights search  n k repsfile [part nparts]   stuck subsets and the maxima of B_e on them
 *           uniform_weights regions n k repsfile [part nparts]   the same, plus the REGIONS line (every subset)
 *           Parts take the representatives with index r % nparts == part; add them up with
 *           python sum_parts.py OUT_0 ... OUT_{nparts-1}
 *           Paper runs: regions 4 2, regions 5 2, regions 6 2 and regions 4 3; search n 2 for n = 2, ..., 7 (n = 7 in
 *           4 parts); search 5 3 (4 parts); all on the file of all conjugacy classes (class_reps.c); and search 8 2 on
 *           the 22 permutation cycle types (permutation_reps.py 8; 3 parts).
 *
 * Output:   DONE uniform_weights n= k= part= automata= instances= stuck= max_Be_on_stuck= max_e= counterexamples=
 *                max_Be_on_stuck_distinct_letters=
 *           automata = population size; instances = automata x (2^n - 2) proper nonempty subsets; stuck = number of
 *           stuck subsets; max_Be_on_stuck = the largest B_e on a stuck subset over all automata of the population;
 *           max_Be_on_stuck_distinct_letters = the same over the automata whose letters are pairwise distinct (at k = 2
 *           every automaton of the population has a != b, so the two coincide); counterexamples = number of stuck
 *           subsets with B_e >= 0, each printed on a COUNTEREXAMPLE line.  In mode regions:
 *           REGIONS Be>=0&B<0= (in {B_e >= 0} but not {B >= 0})  B>=0&Be<0= (the converse)  Hsharp= (instances in H#)
 *           Hsharp&Be>=0= (those with B_e >= 0).  A value -9223372036854775808 means "no stuck subset".
 *           Progress lines go to stderr.
 *
 * Runtime (one core per process): n <= 5 at k = 2 and regions 4 3 under a second; regions 6 2 about 11 seconds, search
 *   6 2 about 4 seconds; search 7 2 about 6 minutes in total (4 parts of 73 to 100 seconds); search 5 3 about 5 minutes
 *   in total (4 parts of 1 to 1.5 minutes); search 8 2 on the stratum roughly an hour in total (the 8-cycle alone,
 *   16,596,608 automata, takes 6 minutes).
 * Requires: gcc or clang (the code uses __builtin_popcount and __builtin_ctz); n <= 8, k <= 3.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>

#define MAXN 8
#define MAXK 3
#define MAXS (1 << MAXN)

static int n, k;
static int let[MAXK][MAXN];          /* let[x][p] = p.x */
static int npow;                     /* n^n */
static int nreps; static int reps[4000][MAXN];

static void decode(int code, int *f) { for (int i = n - 1; i >= 0; i--) { f[i] = code % n; code /= n; } }

/* ---------- automaton tests ---------- */
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
/* pair criterion: every pair of states is merged by some word */
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

/* ---------- preimage tables and stuck subsets ---------- */
static int pre[MAXK][MAXS];          /* pre[x][S] = S x^{-1} as a bit mask */
static void build_pre(void) {
    int pre1[MAXK][MAXN];
    for (int x = 0; x < k; x++) { for (int q = 0; q < n; q++) pre1[x][q] = 0;
        for (int p = 0; p < n; p++) pre1[x][let[x][p]] |= 1 << p; }
    int N = 1 << n;
    for (int x = 0; x < k; x++) { pre[x][0] = 0;
        for (int S = 1; S < N; S++) { int low = S & -S; pre[x][S] = pre[x][S ^ low] | pre1[x][__builtin_ctz(low)]; } }
}
/* minext(S) capped at n: returns t<=n-1 if some |Su^-1|>|S| with |u|=t, else n (stuck) */
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
        if (nn == 0) return n;               /* every branch dead: never extends */
        memcpy(cur, nxt, sizeof(int) * nn); nc = nn;
    }
    return n;
}

/* ---------- integer left eigenvector e^T M = k e^T ---------- */
static int64_t gcd64(int64_t a, int64_t b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { int64_t t = a % b; a = b; b = t; } return a; }
static int64_t det_bareiss(int64_t a[MAXN][MAXN], int m) {
    int64_t prev = 1; int sign = 1;
    for (int i = 0; i < m - 1; i++) {
        if (a[i][i] == 0) { int r = -1; for (int j = i + 1; j < m; j++) if (a[j][i]) { r = j; break; }
            if (r < 0) return 0; for (int c = 0; c < m; c++) { int64_t t = a[i][c]; a[i][c] = a[r][c]; a[r][c] = t; } sign = -sign; }
        for (int j = i + 1; j < m; j++) for (int c = i + 1; c < m; c++)
            a[j][c] = (a[j][c] * a[i][i] - a[j][i] * a[i][c]) / prev;
        prev = a[i][i];
    }
    return sign * a[m - 1][m - 1];
}
static int64_t ev[MAXN];
static int eigenvector(void) {
    /* A = (M - kI)^T ; kernel vector = a nonzero column of adj(A) = cofactors along a row */
    int64_t A[MAXN][MAXN]; memset(A, 0, sizeof A);
    for (int p = 0; p < n; p++) for (int x = 0; x < k; x++) A[let[x][p]][p] += 1;   /* A[q][p] = M[p][q] */
    for (int p = 0; p < n; p++) A[p][p] -= k;
    for (int row = 0; row < n; row++) {
        int nonzero = 0;
        for (int col = 0; col < n; col++) {
            int64_t B[MAXN][MAXN]; int ri = 0;
            for (int i = 0; i < n; i++) { if (i == row) continue; int ci = 0;
                for (int j = 0; j < n; j++) { if (j == col) continue; B[ri][ci++] = A[i][j]; } ri++; }
            int64_t d = det_bareiss(B, n - 1);
            ev[col] = ((row + col) & 1) ? -d : d;
            if (d) nonzero = 1;
        }
        if (!nonzero) continue;
        int64_t g = 0; for (int i = 0; i < n; i++) g = gcd64(g, ev[i]);
        int neg = 0, pos = 0;
        for (int i = 0; i < n; i++) { ev[i] /= g; if (ev[i] < 0) neg = 1; if (ev[i] > 0) pos = 1; }
        if (neg && pos) return 0;                       /* not a positive vector: should not happen on SC */
        if (neg) for (int i = 0; i < n; i++) ev[i] = -ev[i];
        for (int i = 0; i < n; i++) if (ev[i] == 0) return 0;
        return 1;
    }
    return 0;
}

/* ---------- beta^* and sigma_t ---------- */
static int64_t indeg_t[MAXN][MAXN];   /* indeg_t[t][q], t = 0..n-1: number of words of length t leading into q */
static void build_indeg(void) {
    for (int q = 0; q < n; q++) indeg_t[0][q] = 1;
    for (int t = 1; t <= n - 1; t++) { for (int q = 0; q < n; q++) indeg_t[t][q] = 0;
        for (int p = 0; p < n; p++) for (int x = 0; x < k; x++) indeg_t[t][let[x][p]] += indeg_t[t - 1][p]; }
}
static int64_t kpow[MAXN + 1];

static void print_aut(FILE *f) {
    for (int x = 0; x < k; x++) { fprintf(f, "%c=[", 'a' + x); for (int p = 0; p < n; p++) fprintf(f, "%d%s", let[x][p], p + 1 < n ? "," : ""); fprintf(f, "] "); }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: uniform_weights search|regions n k repsfile [part nparts]\n"); return 1; }
    const char *mode = argv[1]; n = atoi(argv[2]);
    npow = 1; for (int i = 0; i < n; i++) npow *= n;
    const char *repfile = argv[4];
    k = atoi(argv[3]); int part = 0, nparts = 1;
    if (argc >= 7) { part = atoi(argv[5]); nparts = atoi(argv[6]); }
    FILE *f = fopen(repfile, "r"); if (!f) { fprintf(stderr, "no %s\n", repfile); return 1; }
    nreps = 0; while (1) { int ok = 1; for (int i = 0; i < n; i++) if (fscanf(f, "%d", &reps[nreps][i]) != 1) { ok = 0; break; } if (!ok) break; nreps++; }
    fclose(f);
    int regions = !strcmp(mode, "regions");
    kpow[0] = 1; for (int t = 1; t <= n; t++) kpow[t] = kpow[t - 1] * k;
    int N = 1 << n;
    long long n_aut = 0, n_stuck = 0, c_be_ge0_b_lt0 = 0, c_b_ge0_be_lt0 = 0, c_hsharp = 0, c_hsharp_be_ge0 = 0, n_counter = 0;
    long long max_be_stuck = LLONG_MIN; int64_t max_e = 0;
    long long max_be_stuck_distinct = LLONG_MIN;        /* the same maximum over automata with pairwise distinct letters */
    for (int r = 0; r < nreps; r++) {
        if (r % nparts != part) continue;
        memcpy(let[0], reps[r], sizeof(int) * n);
        for (int bcode = 0; bcode < npow; bcode++) {
            decode(bcode, let[1]);
            int cstart = (k == 3) ? bcode : 0, cend = (k == 3) ? npow - 1 : 0;
            for (int ccode = cstart; ccode <= cend; ccode++) {
                if (k == 3) decode(ccode, let[2]);
                if (!strongly_connected()) continue;
                if (!synchronizing()) continue;
                n_aut++;
                build_pre();
                int stuck[MAXS]; int ns = 0;
                for (int S = 1; S < N - 1; S++) if (minext_capped(S) >= n) stuck[ns++] = S;
                n_stuck += ns;
                if (ns == 0 && !regions) continue;
                if (!eigenvector()) { fprintf(stderr, "eigenvector failure: "); print_aut(stderr); fprintf(stderr, "\n"); continue; }
                int64_t eQ = 0; for (int q = 0; q < n; q++) eQ += ev[q];
                for (int q = 0; q < n; q++) if (ev[q] > max_e) max_e = ev[q];
                if (regions) {
                    build_indeg();
                    for (int S = 1; S < N - 1; S++) {
                        int m = __builtin_popcount(S); int64_t eS = 0, B = 0; int allle0 = 1, allzero = 1;
                        for (int q = 0; q < n; q++) if (S >> q & 1) eS += ev[q];
                        for (int t = 1; t <= n - 1; t++) { int64_t s = 0; for (int q = 0; q < n; q++) if (S >> q & 1) s += indeg_t[t][q];
                            s -= kpow[t] * m; if (s > 0) allle0 = 0; if (s != 0) allzero = 0; B += kpow[n - 1 - t] * s; }
                        int64_t Be = (int64_t)n * eS - (int64_t)m * eQ;
                        if (Be >= 0 && B < 0) c_be_ge0_b_lt0++;
                        if (B >= 0 && Be < 0) c_b_ge0_be_lt0++;
                        if (allle0 && !allzero) { c_hsharp++; if (Be >= 0) c_hsharp_be_ge0++; }
                    }
                }
                int distinct = 1;                               /* are the k letters pairwise distinct? */
                for (int x = 0; x < k; x++) for (int y = x + 1; y < k; y++) if (!memcmp(let[x], let[y], sizeof(int) * n)) distinct = 0;
                for (int i = 0; i < ns; i++) { int S = stuck[i]; int m = __builtin_popcount(S); int64_t eS = 0;
                    for (int q = 0; q < n; q++) if (S >> q & 1) eS += ev[q];
                    int64_t Be = (int64_t)n * eS - (int64_t)m * eQ;
                    if (Be > max_be_stuck) max_be_stuck = Be;
                    if (distinct && Be > max_be_stuck_distinct) max_be_stuck_distinct = Be;
                    if (Be >= 0) { n_counter++; printf("COUNTEREXAMPLE n=%d k=%d ", n, k); print_aut(stdout);
                        printf(" S={"); for (int q = 0; q < n; q++) if (S >> q & 1) printf("%d,", q);
                        printf("} e=("); for (int q = 0; q < n; q++) printf("%lld%s", (long long)ev[q], q + 1 < n ? "," : ""); printf(") B_e=%lld\n", (long long)Be); fflush(stdout); }
                }
            }
        }
        fprintf(stderr, "[part %d/%d] rep %d/%d done: automata=%lld stuck=%lld maxBe_stuck=%lld counterexamples=%lld\n",
                part, nparts, r + 1, nreps, n_aut, n_stuck, max_be_stuck, n_counter); fflush(stderr);
    }
    printf("DONE uniform_weights n=%d k=%d part=%d/%d automata=%lld instances=%lld stuck=%lld max_Be_on_stuck=%lld max_e=%lld counterexamples=%lld max_Be_on_stuck_distinct_letters=%lld\n",
           n, k, part, nparts, n_aut, n_aut * (long long)(N - 2), n_stuck, max_be_stuck, (long long)max_e, n_counter, max_be_stuck_distinct);
    if (regions) printf("REGIONS Be>=0&B<0=%lld  B>=0&Be<0=%lld  Hsharp=%lld  Hsharp&Be>=0=%lld\n", c_be_ge0_b_lt0, c_b_ge0_be_lt0, c_hsharp, c_hsharp_be_ge0);
    return 0;
}
