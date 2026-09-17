"""run_populations.py -- run census_engine on the eleven populations of Section 6.6

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: "The eleven populations of Section 6.6": the seven binary
    populations and strata of Section 4.1 (n=3, 4, 5, 6 over all deviations;
    {d<=2} at n=5, 6, 7), the binary {d<=2} stratum at n=4, the exhaustive
    ternary population at n=4 and the ternary {d<=2} strata at n=4 and n=5.
  This program only produces the JSON files; tables.py checks the numbers of
  Sections 4.1, 6.3-6.6 and Appendices A and D against them.
Population / convention: as in census_engine.c (quotient convention of
  Appendix A.1; at k=3 the two letters after the first are ordered pairs).
Usage:    gcc -O2 -o census_engine census_engine.c
          python run_populations.py ./census_engine OUTDIR [--jobs J] [--only NAME ...]
          python tables.py OUTDIR
Output:   OUTDIR/NAME.json for each NAME in POPULATIONS below (engine arguments
          n k dmax, dmax = -1 meaning every deviation); one line per finished
          run with the engine's summary and the wall time; exit status = number
          of failed runs.
Runtime:  one core per run (gcc -O2, shared machine): n5k3_d2 821 s, n7_d2
          466 s, n6_all 44 s, n6_d2 8 s, n4k3_all 4 s, the others under 2 s;
          about 23 minutes serially, about 14 minutes with --jobs 2.
Requires: Python 3.7 or later (standard library only).
"""
import argparse
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

POPULATIONS = [
    # name        n  k  dmax
    ("n3_all",    3, 2, -1),
    ("n4_all",    4, 2, -1),
    ("n5_all",    5, 2, -1),
    ("n6_all",    6, 2, -1),
    ("n4_d2",     4, 2, 2),
    ("n5_d2",     5, 2, 2),
    ("n6_d2",     6, 2, 2),
    ("n7_d2",     7, 2, 2),
    ("n4k3_all",  4, 3, -1),
    ("n4k3_d2",   4, 3, 2),
    ("n5k3_d2",   5, 3, 2),
]


def run_one(engine, outdir, name, n, k, dmax):
    out = os.path.join(outdir, name + ".json")
    t0 = time.time()
    p = subprocess.run([engine, str(n), str(k), str(dmax), out],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    return name, p.returncode, (p.stdout + p.stderr).strip(), time.time() - t0


def main():
    ap = argparse.ArgumentParser(description="Run census_engine on the eleven populations.")
    ap.add_argument("engine", help="path of the compiled census_engine")
    ap.add_argument("outdir", help="directory for the JSON files (created if missing)")
    ap.add_argument("--jobs", type=int, default=1, help="runs at once (default 1)")
    ap.add_argument("--only", nargs="+", metavar="NAME", help="run only these populations")
    a = ap.parse_args()
    names = [p[0] for p in POPULATIONS]
    if a.only:
        bad = [x for x in a.only if x not in names]
        if bad:
            ap.error("unknown population(s) %s; known: %s" % (", ".join(bad), " ".join(names)))
    todo = [p for p in POPULATIONS if not a.only or p[0] in a.only]
    os.makedirs(a.outdir, exist_ok=True)
    failed = 0
    t0 = time.time()
    with ThreadPoolExecutor(max(1, a.jobs)) as pool:
        futures = [pool.submit(run_one, a.engine, a.outdir, *p) for p in todo]
        for fut in futures:
            name, rc, text, wall = fut.result()
            failed += rc != 0
            print("%-9s %s  [%s, %.1f s]" % (name, text, "ok" if rc == 0 else "FAILED rc=%d" % rc, wall))
            sys.stdout.flush()
    print("%d runs, %d FAILED, total wall %.1f s" % (len(todo), failed, time.time() - t0))
    return min(failed, 255)


if __name__ == "__main__":
    sys.exit(main())
