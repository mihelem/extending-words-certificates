/* class_reps.c -- one representative per conjugacy class of endofunctions of {0,...,n-1}
 *
 * Supports, in "Certificates for short extending words in a finite automaton":
 *   Appendix A.1: the first letter of a binary automaton ranges over one representative of each conjugacy class of
 *   endofunctions of an n-element set (19, 47, 130 and 343 classes at n = 4, 5, 6, 7; sequence A001372), which is
 *   the input of every quotient-convention enumeration: fibres.c (Section 5.2, n = 4..9) and, in stationary/,
 *   uniform_weights.c, bias_census.c, bias_census_exact.c and permutation_stratum.c at n <= 7.
 *
 * Method:   classes of functional graphs up to isomorphism, by a canonical string: every node's rooted tree of
 *   non-cycle preimages is encoded recursively (sorted children), every cycle by the lexicographically least
 *   rotation of its nodes' tree strings, and the components sorted.  All n^n maps are enumerated in lexicographic
 *   order and the first map of each class (its lexicographically least member) is written, one per line, as the
 *   list of images of 0..n-1.  The class counts must be A001372: 1, 3, 7, 19, 47, 130, 343, 951, 2615 for n = 1..9.
 *
 * Usage:    gcc -O2 -o class_reps class_reps.c
 *           class_reps n reps_n.txt       writes the representatives to reps_n.txt, summary line on stdout
 *           class_reps n > reps_n.txt     without a file name the representatives go to stdout, the summary to stderr
 *
 * Output:   the representatives, then the line  DONE class_reps n= classes= file=  (classes = the A001372 term).
 * Runtime:  n <= 8 under 10 seconds; n = 9 (387,420,489 maps) about 6 minutes on one core.
 * Requires: a C compiler (gcc or clang).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 10
#define HBITS 20
#define HSIZE (1 << HBITS)

static int n, f[MAXN];
static int oncycle[MAXN], color[MAXN];
static char tstr[MAXN][4 * MAXN + 4];        /* tree string of each node */
static int tlen[MAXN];

static int cmp_str(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

/* rooted tree string of node p: "(" + sorted children strings + ")", children = non-cycle preimages */
static void tree_string(int p) {
    char *ch[MAXN]; int nc = 0;
    for (int q = 0; q < n; q++) if (f[q] == p && !oncycle[q] && q != p) { tree_string(q); ch[nc++] = tstr[q]; }
    qsort(ch, nc, sizeof(char *), cmp_str);
    int L = 0; tstr[p][L++] = '(';
    for (int i = 0; i < nc; i++) { int l = strlen(ch[i]); memcpy(tstr[p] + L, ch[i], l); L += l; }
    tstr[p][L++] = ')'; tstr[p][L] = 0; tlen[p] = L;
}

static char canon[8 * MAXN * MAXN];
static void canonical(void) {
    /* find cycle nodes */
    for (int i = 0; i < n; i++) { color[i] = 0; oncycle[i] = 0; }
    for (int s = 0; s < n; s++) {
        if (color[s]) continue;
        int p = s; while (color[p] == 0) { color[p] = 1; p = f[p]; }
        if (color[p] == 1) { int r = p; do { oncycle[r] = 1; r = f[r]; } while (r != p); }
        int r = s; while (color[r] == 1) { color[r] = 2; r = f[r]; }
    }
    for (int p = 0; p < n; p++) if (oncycle[p]) tree_string(p);
    /* cycles: least rotation of the sequence of tree strings */
    char *comps[MAXN]; static char cbuf[MAXN][8 * MAXN * MAXN / MAXN]; int ncomp = 0; int done[MAXN] = {0};
    for (int s = 0; s < n; s++) if (oncycle[s] && !done[s]) {
        int cyc[MAXN], L = 0; int r = s; do { cyc[L++] = r; done[r] = 1; r = f[r]; } while (r != s);
        char best[8 * MAXN * MAXN / MAXN]; best[0] = 0; int have = 0;
        for (int rot = 0; rot < L; rot++) {
            char cand[8 * MAXN * MAXN / MAXN]; int C = 0; cand[C++] = '[';
            for (int i = 0; i < L; i++) { int node = cyc[(rot + i) % L]; memcpy(cand + C, tstr[node], tlen[node]); C += tlen[node]; }
            cand[C++] = ']'; cand[C] = 0;
            if (!have || strcmp(cand, best) < 0) { strcpy(best, cand); have = 1; }
        }
        strcpy(cbuf[ncomp], best); comps[ncomp] = cbuf[ncomp]; ncomp++;
    }
    qsort(comps, ncomp, sizeof(char *), cmp_str);
    int C = 0; for (int i = 0; i < ncomp; i++) { int l = strlen(comps[i]); memcpy(canon + C, comps[i], l); C += l; } canon[C] = 0;
}

/* hash set of canonical strings */
static char *htab[HSIZE]; static int hcount = 0;
static uint64_t hstr(const char *s) { uint64_t h = 1469598103934665603ULL; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ULL; } return h; }
static int insert(const char *s) {          /* 1 if new */
    uint64_t h = hstr(s) & (HSIZE - 1);
    while (htab[h]) { if (!strcmp(htab[h], s)) return 0; h = (h + 1) & (HSIZE - 1); }
    htab[h] = strdup(s); hcount++; return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: class_reps n [outfile]\n"); return 1; }
    n = atoi(argv[1]); if (n < 1 || n > MAXN) return 1;
    int to_file = argc >= 3; const char *fname = to_file ? argv[2] : "(stdout)";
    FILE *out = to_file ? fopen(fname, "w") : stdout; if (!out) return 1;
    long long npow = 1; for (int i = 0; i < n; i++) npow *= n;
    for (int i = 0; i < n; i++) f[i] = 0;
    for (long long code = 0; code < npow; code++) {
        if (code) { int i = n - 1; while (i >= 0 && ++f[i] == n) { f[i] = 0; i--; } }
        canonical();
        if (insert(canon)) { for (int i = 0; i < n; i++) fprintf(out, "%d ", f[i]); fprintf(out, "\n"); }
    }
    if (to_file) fclose(out); else fflush(out);
    fprintf(to_file ? stdout : stderr, "DONE class_reps n=%d classes=%d file=%s\n", n, hcount, fname);
    return 0;
}
