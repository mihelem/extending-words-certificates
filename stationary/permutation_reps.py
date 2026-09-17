"""permutation_reps.py -- one permutation per cycle type on {0,...,n-1}: the first letters of a permutation-first stratum

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A and Appendix C: the stratum of the binary n = 8 population whose first letter is a permutation takes the
  22 cycle types as first letter and all 8^8 second letters; its analogue at n = 9 the 30 cycle types and all 9^9
  second letters.  This program writes those first letters, the representatives file read by uniform_weights.c and
  bias_census_exact.c (n = 8) and by permutation_stratum.c (n = 8 and n = 9).
Population / convention: the partitions of n in decreasing lexicographic order, each part a cycle on consecutive states
  i -> i+1 (last -> first of the block); one line per permutation, the images of 0..n-1 separated by spaces.
Usage:    python permutation_reps.py n                    permutations to stdout, summary line to stderr
          python permutation_reps.py n reps_perm_n.txt    permutations to the file, summary line to stdout
Output:   the permutations, then  wrote <file>: <count> cycle types   (22 at n = 8, 30 at n = 9).
Runtime:  instantaneous.
Requires: Python 3.
"""
import sys

def partitions(m, mx=None):
    if mx is None: mx = m
    if m == 0:
        yield []; return
    for f in range(min(m, mx), 0, -1):
        for rest in partitions(m - f, f): yield [f] + rest

n = int(sys.argv[1]); out = sys.argv[2] if len(sys.argv) > 2 else None
lines = []
for lam in partitions(n):
    perm = list(range(n)); pos = 0
    for f in lam:
        for i in range(f): perm[pos + i] = pos + (i + 1) % f
        pos += f
    lines.append(" ".join(str(x) for x in perm) + " ")
if out is None:
    sys.stdout.write("\n".join(lines) + "\n")
    print("wrote %s: %d cycle types" % ("stdout", len(lines)), file=sys.stderr)
else:
    with open(out, "w", newline="\n") as fh:
        fh.write("\n".join(lines) + "\n")
    print("wrote %s: %d cycle types" % (out, len(lines)))
