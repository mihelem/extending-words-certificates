"""compare_engines.py -- compare the C and the Python implementations on integer counts

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: "The counts of Section 6.6 and Appendix D come from two
    implementations, one in C and one in Python, ... agreeing on 96 of 96
    compared integer fields across four populations in both counting
    conventions": 12 subset counts x 2 conventions (quotient, labelled) x 4
    populations (binary n=3, 4, 5 and ternary n=4, all deviations, synchronizing
    and strongly connected; ternary pairs of letters ordered).
  Only raw integer counts are compared, never percentages: rounding can hide a
  disagreement and can also produce one.  The C program (census_engine.c) and
  the Python program (independent_engine/) name their fields differently; the
  map is FIELDS below.  If the map were wrong, rows would silently drop out
  rather than fail, so fewer than MIN_ROWS compared rows is itself a failure.
Population / convention: see census_engine.c and independent_engine/engine.py.
Usage:    python compare_engines.py C_DIR PY_DIR
          C_DIR:  n3_all.json n4_all.json n5_all.json n4k3_all.json written by
                  python run_populations.py ./census_engine C_DIR
                     --only n3_all n4_all n5_all n4k3_all
          PY_DIR: the same four file names written by independent_engine/run.py
                  (and merge.py for n4k3_all), see the usage in run.py
Output:   one row per compared field, then
          "compared 96 integer fields, 96 matched, 0 MISMATCHED" (Appendix A's
          "96 of 96").  Exit status 0 if every compared field matches, 1 on a
          mismatch, 2 if fewer than MIN_ROWS fields were compared.
Runtime:  under a second (producing the inputs takes about 5 s in C and 7 to
          17 minutes in Python, one core, depending on machine load).
Requires: Python 3 (standard library only).
"""
import io
import json
import os
import sys

# (C field, Python field)
FIELDS = [
    ("Hsharp",            "Hsharp"),
    ("Hsharp_qcert",      "Hsharp_qcert"),
    ("Hsharp_qplus",      "Hsharp_qcertplus"),
    ("stuck",             "stuck"),
    ("stuck_qcert",       "stuck_qcert"),
    ("stuck_qplus",       "stuck_qcertplus"),
    ("Csharp_minus_Bge0", "gain_Csharp_minus_Bge0"),
    ("Bneg",              "Blt0"),
    ("Bge0",              "Bge0"),
    ("Csharp",            "Csharp"),
    ("sigma_zero",        "sigma_zero"),
    ("boundary_nograde",  "boundary_nograde"),
]

POPS = [
    ("n=3 k=2 all d", "n3_all.json",   "n3_all.json"),
    ("n=4 k=2 all d", "n4_all.json",   "n4_all.json"),
    ("n=5 k=2 all d", "n5_all.json",   "n5_all.json"),
    ("n=4 k=3 all d", "n4k3_all.json", "n4k3_all.json"),
]

MIN_ROWS = 60          # fewer compared rows than this is a failure


def load(p):
    return json.load(io.open(p, encoding="utf-8"))


def main(c_dir, py_dir):
    compared = matched = 0
    mismatches = []
    for tag, ef, vf in POPS:
        eacc = load(os.path.join(c_dir, ef))["acc"]
        vpop = load(os.path.join(py_dir, vf))["populations"]["syncSC"]
        print("=" * 72)
        print(tag)
        for conv, idx in (("quotient", 0), ("labelled", 1)):
            vsub = vpop[conv[0]]["sub"]
            for ek, vk in FIELDS:
                ev = eacc.get(ek)
                if not isinstance(ev, list) or len(ev) <= idx:
                    continue
                ev = ev[idx]
                if vk not in vsub:
                    continue
                vv = vsub[vk]
                compared += 1
                same = (ev == vv)
                matched += same
                if not same:
                    mismatches.append((tag, conv, ek, vk, ev, vv))
                print("  %-9s %-20s C=%-12d Python=%-12d %s"
                      % (conv, ek, ev, vv, "[PASS]" if same else "[FAIL]"))
    print("=" * 72)
    print("compared %d integer fields, %d matched, %d MISMATCHED"
          % (compared, matched, len(mismatches)))
    for m in mismatches:
        print("  MISMATCH %s" % (m,))
    if compared < MIN_ROWS:
        print("FAILED: only %d fields compared, at least %d expected -- the "
              "field map or the input files are wrong"
              % (compared, MIN_ROWS))
        return 2
    print("RESULT: %s"
          % ("the two implementations agree on every compared integer"
             if not mismatches else "the two implementations DISAGREE"))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit("usage: python compare_engines.py C_DIR PY_DIR")
    raise SystemExit(main(sys.argv[1], sys.argv[2]))
