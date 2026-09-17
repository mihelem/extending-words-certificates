"""compare_histograms.py -- do the two bias-census implementations agree on every histogram bin?

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix C: no pair has t* in (1/2, 2/3) at n = 5, 6, 7 (every pair is certified on the whole interval).
  Appendix A: "The bias census of Appendix C at n <= 7 was produced by two implementations on a grid of step 1/400,
  agreeing on every histogram bin": bias_census.c (floating-point stationary vector by Gaussian elimination) against
  bias_census_exact.c (integer matrix-tree polynomial), at n = 5, 6, 7.
Method:   adds up the parts of each run (sum_parts.py) and compares the population, the stuck subsets, the automata with
  a stuck subset, the least grid threshold and the threshold histogram bin by bin.
Usage:    python compare_histograms.py --a BC_part0.out [BC_part1.out ...] --b BCE_part0.out [BCE_part1.out ...]
Output:   one [PASS]/[FAIL] line per compared quantity; last line "N rows, M FAILED"; exit status = number of failed rows.
Runtime:  instantaneous.
Requires: Python 3 (standard library only); sum_parts.py in the same directory.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sum_parts import read_run, combine  # noqa: E402


def main(argv):
    if "--a" not in argv or "--b" not in argv:
        print(__doc__)
        return 1
    ia, ib = argv.index("--a"), argv.index("--b")
    side_a = argv[ia + 1:ib] if ia < ib else argv[ia + 1:]
    side_b = argv[ib + 1:] if ia < ib else argv[ib + 1:ia]
    ta, pa = combine([read_run(p) for p in side_a])
    tb, pb = combine([read_run(p) for p in side_b])
    rows = []
    rows.append(("parts of run A complete and consistent (%s, n=%s)" % (ta["kind"], ta.get("n")), not pa))
    rows.append(("parts of run B complete and consistent (%s, n=%s)" % (tb["kind"], tb.get("n")), not pb))
    rows.append(("same n: %s and %s" % (ta.get("n"), tb.get("n")), ta.get("n") == tb.get("n")))
    for field in ("automata", "stuck_subsets", "automata_with_stuck", "min_t*"):
        rows.append(("same %s: %s and %s" % (field, ta.get(field), tb.get(field)), ta.get(field) == tb.get(field)))
    ha, hb = ta["HIST"], tb["HIST"]
    bins = sorted(set(ha) | set(hb))
    differing = [i for i in bins if ha.get(i, 0) != hb.get(i, 0)]
    rows.append(("every histogram bin agrees (%d non-empty bins, %d pairs in A, %d in B; differing bins: %s)"
                 % (len(bins), sum(ha.values()), sum(hb.values()), differing or "none"), not differing and bool(bins)))
    if "uncertified" in tb:
        rows.append(("run B certifies n e_t(S) - |S| e_t(Q) <= 0 on the whole interval [1/2, 2/3] for all %s pairs "
                     "(uncertified: %s), so no pair has its threshold below 2/3 between grid points"
                     % (tb.get("pairs"), tb.get("uncertified")), tb.get("uncertified") == 0))
    below = sum(c for i, c in ha.items() if i < 67)
    print("run A: %s" % " ".join(os.path.basename(p) for p in side_a))
    print("run B: %s" % " ".join(os.path.basename(p) for p in side_b))
    print("bins <= 67 in A: %s;  pairs below bin 67: %d" % ({i: c for i, c in sorted(ha.items()) if i <= 67}, below))
    failed = 0
    for label, ok in rows:
        print(("[PASS] " if ok else "[FAIL] ") + label)
        failed += 0 if ok else 1
    print("%d rows, %d FAILED" % (len(rows), failed))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
