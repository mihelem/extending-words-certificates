"""merge.py -- merge the JSON files of run.py pieces of one (n, k) population into one file

Supports, in "Certificates for short extending words in a finite automaton":
  Appendix A: the exhaustive ternary n=4 population (789,358 automata with the
    two letters after the first ordered), one of the four populations on which
    the C and Python implementations are compared, is run by run.py in three
    pieces over the first-letter class representatives and merged here.
Population / convention: see engine.py.  Counts add; the per-size maxima
  ("prof") take the maximum over the pieces.
Usage:    python merge.py outdir out_tag tag1 tag2 ...
          reads outdir/tag1.json, outdir/tag2.json, ... and writes
          outdir/out_tag.json, e.g.
            python merge.py OUT n4k3_all n4k3_part0 n4k3_part1 n4k3_part2
Output:   the merged JSON file (same layout as run.py's, plus merged_from and
          max_single_run_seconds); one line on stdout.
Runtime:  under a second.
Requires: Python 3 (standard library only).
"""
import json
import os
import sys


def merge(outdir, tags, out_tag):
    rs = [json.load(open(os.path.join(outdir, f"{t}.json"))) for t in tags]
    base = rs[0]
    m = dict(base)
    m["tag"] = out_tag
    m["merged_from"] = tags
    m["repslice"] = [r.get("repslice") for r in rs]
    m["wall_seconds"] = round(sum(r["wall_seconds"] for r in rs), 2)
    m["max_single_run_seconds"] = max(r["wall_seconds"] for r in rs)
    m["automata_enumerated_quotient"] = sum(r["automata_enumerated_quotient"] for r in rs)
    m["identity_instances_checked"] = sum(r["identity_instances_checked"] for r in rs)
    m["identity_disagreements"] = sum(r["identity_disagreements"] for r in rs)
    pops = {}
    for name in base["populations"]:
        pops[name] = {}
        for c in ("q", "l"):
            acc = {"aut": {}, "sub": {}, "prof": {}, "hor": {}}
            for r in rs:
                d = r["populations"][name][c]
                for sec in ("aut", "sub", "hor"):
                    for k2, v in d[sec].items():
                        acc[sec][k2] = acc[sec].get(k2, 0) + v
                for k2, v in d["prof"].items():
                    if k2 not in acc["prof"] or v > acc["prof"][k2]:
                        acc["prof"][k2] = v
            pops[name][c] = acc
    m["populations"] = pops
    fn = os.path.join(outdir, f"{out_tag}.json")
    json.dump(m, open(fn, "w"), indent=1, sort_keys=True)
    print("wrote", fn, "| runs:", [r["wall_seconds"] for r in rs],
          "| max single run", m["max_single_run_seconds"], "s")


if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit("usage: python merge.py outdir out_tag tag1 tag2 ...")
    merge(sys.argv[1], sys.argv[3:], sys.argv[2])
