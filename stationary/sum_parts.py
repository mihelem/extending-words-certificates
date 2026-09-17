"""sum_parts.py -- add up the part outputs of a census run and print the totals the paper quotes

Supports, in "Certificates for short extending words in a finite automaton" (every total below is a sum over parts):
  Section 5.2: the fibre sizes 3,212,088 (n = 8) and 59,605,126 (n = 9, four parts) and the per-size maxima of minext
    8,8,7,8,8,7,8,8 at n = 9, with the gcd law (n-1 exactly at the sizes m with gcd(m,n) = 1, n-2 otherwise)
    -- outputs of eulerian_fibres/fibres.c.
  Appendix C: 42,605,958 automata and 2,827,614 stuck subsets at n = 7; 123,014,054 / 18,609,570 on the n = 8 stratum;
    138,540,502 ternary automata at n = 5; maximum of B_e on stuck subsets -1 -- outputs of uniform_weights.c;
    the bias census totals at n = 6, 7 (8 and 116 pairs at 2/3, none below) -- outputs of bias_census.c and
    bias_census_exact.c; the n = 8 stratum census (416 pairs below 2/3 in bins 35 and 42, 32 at bin 67, none heavy at
    t = 1/2) -- bias_census_exact.c; the n = 9 stratum (3,761,587,885 automata, 278,959,029 stuck subsets, maximum of
    B_e -1, bins 38: 384, 58: 32, 67: 1,568) -- permutation_stratum.c.
  Appendix C, with --populations: 17,360 + 977,640 + 69,596,798 + 5,534,186 = 76,125,984 proper-subset instances on
    the populations n = 4, 5, 6 binary and n = 4 ternary (uniform_weights.c regions runs).
Method:   reads the DONE line (and the REGIONS and HIST lines) of every output.  Counts are summed, fields named
  max_* are maximised, min_* and the refined threshold minimised, per_size_max_minext maximised entry by entry, the
  other lists summed entry by entry, histograms merged bin by bin.  The program that wrote a line is recognised by its
  fields.  The parts must come from one run: equal n (and k, census, thr), and every part index 0..nparts-1 exactly once.
Usage:    python sum_parts.py OUT_0 OUT_1 ... OUT_{nparts-1}
          python sum_parts.py --populations RUN [RUN ...]    runs on different populations (each run given by all its
                                                           parts): totals per population and the sum of the counts
Output:   parts: <found> of <nparts> ... ; TOTAL <field>=<value> ...; the merged histograms; then the derived lines
  of the program (fibre size and gcd law; population, stuck subsets and maxima of B_e; pairs by threshold bin).
  Exit status 0, or 1 when the parts are inconsistent or incomplete.
Runtime:  instantaneous.
Requires: Python 3 (standard library only).
"""
import math
import re
import sys

DICT_FIELD = re.compile(r"\b(hist(?:_Be_on_stuck|_bins<=\d+)?)=\{([^}]*)\}")
REFINED = re.compile(r"\(refined (-?[0-9.]+)\)")
ATTAINED = re.compile(r"\battained[ _]by\b(.*)$")
HIST_BIN = re.compile(r"\[(\d+):(\d+)\]")
SAME = ("n", "k", "census", "thr")


def number(s):
    try:
        return int(s)
    except ValueError:
        return float(s)


def parse_fields(text, rec):
    for tok in text.split():
        if "=" not in tok:
            continue
        key, val = tok.rsplit("=", 1)
        if not key or not val:
            continue
        if val.startswith("["):
            rec[key] = [int(x) for x in val.strip("[]").split(",") if x != ""]
        elif key == "part":
            p, np_ = val.split("/")
            rec[key] = (int(p), int(np_))
        else:
            try:
                rec[key] = number(val)
            except ValueError:
                pass


def parse_done(line):
    rec = {}
    for key, body in DICT_FIELD.findall(line):
        d = {}
        for item in body.split(","):
            if item:
                k, v = item.rsplit(":", 1)
                d[k] = d.get(k, 0) + int(v)
        rec[key] = d
    line = DICT_FIELD.sub(" ", line)
    m = REFINED.search(line)
    if m:
        rec["refined"] = float(m.group(1))
        line = REFINED.sub(" ", line)
    m = ATTAINED.search(line)
    rec["attained"] = m.group(1).strip() if m else ""
    if m:
        line = line[:m.start()]
    parse_fields(line, rec)
    return rec


def read_run(path):
    """the DONE record of one output file, with its REGIONS fields and HIST bins"""
    done, regions, hist = None, {}, {}
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.rstrip("\r\n")
            if line.startswith("DONE "):
                done = parse_done(line)
            elif line.startswith("REGIONS "):
                parse_fields(line, regions)
            elif line.startswith("HIST "):
                for i, c in HIST_BIN.findall(line):
                    hist[int(i)] = hist.get(int(i), 0) + int(c)
    if done is None:
        raise SystemExit("no DONE line in %s" % path)
    done["REGIONS"] = regions
    done["HIST"] = hist
    return done


def kind(rec):
    if "eulerian_sync_automata" in rec:
        return "fibres"
    if "canonical_reps" in rec:
        return "permutation_stratum"
    if "certified_le0_on_[1/2,2/3]" in rec:
        return "bias_census_exact"
    if "min_t*" in rec:
        return "bias_census"
    if "instances" in rec:
        return "uniform_weights"
    return "unknown"


def combine(recs):
    """sum the part records; returns (total, problems)"""
    problems = []
    tot = {"REGIONS": {}, "HIST": {}}
    kinds = {kind(r) for r in recs}
    if len(kinds) != 1:
        problems.append("outputs of different programs: %s" % sorted(kinds))
    for key in SAME:
        vals = {r[key] for r in recs if key in r}
        if len(vals) > 1:
            problems.append("parts disagree on %s: %s" % (key, sorted(vals)))
    parts = [r["part"] for r in recs if "part" in r]
    nparts = {np_ for _, np_ in parts}
    if len(nparts) != 1:
        problems.append("parts disagree on the number of parts: %s" % sorted(nparts))
    else:
        np_ = nparts.pop()
        idx = sorted(p for p, _ in parts)
        if idx != list(range(np_)):
            problems.append("part indices %s, expected each of 0..%d exactly once" % (idx, np_ - 1))
        tot["nparts"] = np_
    tot["parts_found"] = len(parts)
    best_attained = {}
    for r in recs:
        for key, val in r.items():
            if key in ("part", "attained", "REGIONS", "HIST"):
                continue
            if key in SAME:
                tot[key] = val
            elif isinstance(val, dict):
                d = tot.setdefault(key, {})
                for k, v in val.items():
                    d[k] = d.get(k, 0) + v
            elif isinstance(val, list):
                if key not in tot:
                    tot[key] = list(val)
                elif key == "per_size_max_minext":
                    tot[key] = [max(a, b) for a, b in zip(tot[key], val)]
                else:
                    tot[key] = [a + b for a, b in zip(tot[key], val)]
            elif key.startswith("max_"):
                tot[key] = max(tot.get(key, val), val)
            elif key.startswith("min_") or key == "refined":
                if key not in tot or val < tot[key]:
                    tot[key] = val
                    if key.startswith("min_"):
                        best_attained[key] = r.get("attained", "")
            else:
                tot[key] = tot.get(key, 0) + val
        for key, val in r["REGIONS"].items():
            tot["REGIONS"][key] = tot["REGIONS"].get(key, 0) + val
        for i, c in r["HIST"].items():
            tot["HIST"][i] = tot["HIST"].get(i, 0) + c
    tot["attained"] = best_attained
    tot["kind"] = kinds.pop() if len(kinds) == 1 else "mixed"
    return tot, problems


def fmt(v):
    if isinstance(v, float):
        return "%.12g" % v
    if isinstance(v, dict):
        keys = sorted(v, key=lambda s: int(s) if re.fullmatch(r"-?\d+", str(s)) else str(s))
        return "{" + ",".join("%s:%d" % (k, v[k]) for k in keys) + "}"
    if isinstance(v, list):
        return "[" + ",".join(str(x) for x in v) + "]"
    return str(v)


def report(tot, problems, label="TOTAL"):
    k = tot["kind"]
    head = "parts: %d of %s  program: %s  n=%s" % (tot["parts_found"], tot.get("nparts", "?"), k, tot.get("n", "?"))
    if "k" in tot:
        head += " k=%s" % tot["k"]
    print(head)
    for p in problems:
        print("PROBLEM: " + p)
    skip = {"REGIONS", "HIST", "attained", "kind", "nparts", "parts_found"} | set(SAME)
    fields = [(key, val) for key, val in tot.items() if key not in skip]
    print(label + " " + " ".join("%s=%s" % (key, fmt(val)) for key, val in fields if not isinstance(val, (list, dict))))
    for key, val in fields:
        if isinstance(val, (list, dict)):
            print("  %s=%s" % (key, fmt(val)))
    for key, tail in tot["attained"].items():
        if tail:
            print("  %s attained by %s" % (key, tail))
    if tot["REGIONS"]:
        print("REGIONS " + "  ".join("%s=%d" % kv for kv in tot["REGIONS"].items()))
    if tot["HIST"]:
        print("HIST " + " ".join("[%d:%d]" % (i, tot["HIST"][i]) for i in sorted(tot["HIST"])))
    n = tot.get("n")
    if k == "fibres":
        mx = tot["per_size_max_minext"]
        law = all(mx[m - 1] == (n - 1 if math.gcd(m, n) == 1 else n - 2) for m in range(1, n))
        print("fibre size (synchronizing Eulerian binary automata): %d" % tot["eulerian_sync_automata"])
        print("maximum of minext over the subsets of size m = 1..%d: %s" % (n - 1, ",".join(map(str, mx))))
        print("gcd law (maximum n-1 exactly at the sizes m with gcd(m,n) = 1, n-2 otherwise): %s"
              % ("holds" if law else "FAILS"))
        print("subsets not extending within n-1: %d" % sum(tot["pairs_beyond_n-1_by_size"]))
    elif k == "uniform_weights":
        print("population: %d automata, %d proper-subset instances, %d stuck subsets; largest B_e on a stuck subset: %d "
              "(%s over automata with pairwise distinct letters); stuck subsets with B_e >= 0: %d"
              % (tot["automata"], tot["instances"], tot["stuck"], tot["max_Be_on_stuck"],
                 tot.get("max_Be_on_stuck_distinct_letters", "not printed"), tot["counterexamples"]))
    elif k in ("bias_census", "bias_census_exact"):
        h = tot["HIST"]
        below = sum(c for i, c in h.items() if i < 67)
        print("population: %d automata, %d stuck subsets; (subset, letter) pairs in the histogram: %d (= 2 x stuck "
              "subsets: %s)" % (tot["automata"], tot["stuck_subsets"], sum(h.values()),
                                sum(h.values()) == 2 * tot["stuck_subsets"]))
        print("pairs with grid threshold below the 2/3 bin (bins 0..66): %d;  at the 2/3 bin (67): %d;  bins <= 67: %s"
              % (below, h.get(67, 0), fmt({i: c for i, c in h.items() if i <= 67})))
        print("least grid threshold: %.6f (refined %.6f)" % (tot["min_t*"], tot.get("refined", float("nan"))))
    elif k == "permutation_stratum":
        print("population: %d automata (%d canonical representatives), %d stuck subsets, %d automata with a stuck subset"
              % (tot["automata"], tot["canonical_reps"], tot["stuck_subsets"], tot["automata_with_stuck"]))
        if "max_Be_on_stuck" in tot:
            hb = tot["hist_Be_on_stuck"]
            print("largest B_e on a stuck subset: %d (attained by %d stuck subsets); stuck subsets heavy at t = 1/2: %d; "
                  "B_e histogram total = stuck subsets: %s" % (tot["max_Be_on_stuck"], hb.get(str(tot["max_Be_on_stuck"]), 0),
                                                              tot["hits_weighted"], sum(hb.values()) == tot["stuck_subsets"]))
        if "pairs" in tot:
            hb = {int(i): c for i, c in tot["hist_bins<=67"].items()}
            print("(subset, letter) pairs: %d; below the 2/3 bin: %d; at the 2/3 bin (67): %d; bins <= 67: %s"
                  % (tot["pairs"], sum(c for i, c in hb.items() if i < 67), hb.get(67, 0), fmt(hb)))


def main(argv):
    populations = "--populations" in argv
    paths = [a for a in argv if a != "--populations"]
    if not paths:
        print(__doc__)
        return 1
    recs = [(p, read_run(p)) for p in paths]
    if not populations:
        tot, problems = combine([r for _, r in recs])
        report(tot, problems)
        return 1 if problems else 0
    groups = {}
    for p, r in recs:
        groups.setdefault((kind(r), r.get("n"), r.get("k"), r.get("census"), r.get("thr")), []).append(r)
    status = 0
    grand = {}
    for key in sorted(groups, key=str):
        tot, problems = combine(groups[key])
        report(tot, problems, label="POPULATION")
        status |= 1 if problems else 0
        for field in ("automata", "instances", "stuck", "stuck_subsets"):
            if field in tot:
                grand[field] = grand.get(field, 0) + tot[field]
        print()
    print("SUM OVER %d POPULATIONS " % len(groups) + " ".join("%s=%d" % kv for kv in grand.items()))
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
