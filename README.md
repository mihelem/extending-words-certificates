# Certificates for short extending words in a finite automaton — programs

This repository holds the programs behind the computed statements of the paper

> M. Miccinesi, *Certificates for short extending words in a finite automaton*.

The paper proves its theorems by hand. The programs compute what the paper *reports*:

* the numbers in its examples and witnesses;
* the exhaustive censuses of Sections 4–8 and Appendices A, C, D and E;
* three comparisons that Appendix A reports as agreements between two programs:
  * the C census engine against an independent Python engine, 96 of 96 integer fields;
  * the two bias-census programs, every histogram bin;
  * the exact re-verification of the pairs attaining the least bias thresholds.

Section, theorem and table numbers below are those of the paper.

Nothing here is stored output. Each program either checks the paper's statements itself, printing one
`[PASS]`/`[FAIL]` line per statement and exiting with the number of failures, or prints counts that
[the map below](#map-from-the-paper-to-the-programs) ties to the paper's numbers.


> [!WARNING]
> **One-off Scripts** The code in this repository was mostly generated and served the purpose of exploring automata to extract specific characterizations. It is not meant to be a library. Please do not build on top of it or extend it.

## Contents

| directory | what it computes | paper |
|---|---|---|
| `examples/` | the explicit small automata and witnesses; the flat-walk strengthening; root location | Sections 3, 5.2–5.4, 6.1–6.4, 6.6, 8.1–8.3; Appendices A, C, D |
| `ks_family/` | the Kisielewicz–Szykuła family | Appendix E (Table E.1), Appendix C |
| `census/` | exhaustive binary censuses at n = 3,…,7 (Python); identity (2) against word enumeration | Sections 5.4, 6.1–6.5, 8.1; Appendices A, A.1, E |
| `second_moment/` | the census engine in C behind Table A.1, Section 6 and Table D.1, an independent Python engine, the membership test | Sections 4.1, 6.3–6.6; Appendices A, A.1, A.2, D |
| `ternary/` | the ternary populations | Sections 6.2, 6.3, 6.5; Appendices A, A.1, D |
| `eulerian_fibres/` | the synchronizing Eulerian binary automata at n = 4,…,9; conjugacy-class representatives | Section 5.2; Appendices A, A.1 |
| `stationary/` | the stationary-vector functional B_e: witnesses, the family on every n ≥ 5, bias census, uniform-weight censuses, exact re-verification, Berlinkov's L | Section 7.3; Appendices A, C |

## Requirements

* **Python 3.** The code uses nothing newer than Python 3.8, and was run with 3.10. Standard library only, except:
  * `numpy`: `census/census.py`, `census/grading.py`, `census/census_d4.py`,
    `census/quotient_vs_labelled.py`, `second_moment/independent_engine/`, `examples/root_location.py`;
  * `mpmath`: `examples/root_location.py`;
  * `sympy`: `stationary/witnesses.py`, `equal_weight_witnesses.py`, `boundary_classes.py`, `exact_n8.py`,
    `exact_thresholds.py`;
  * `numba`: `census/census_d4.py`.

  `pip install -r requirements.txt` installs all four.
* **A C compiler**, gcc or clang, for the `.c` files. Several programs use `__builtin_popcount` and
  `__builtin_ctz`.
* **`rustc`**, for `second_moment/membership.rs`.

Versions used: Python 3.10, numpy 2.2, mpmath 1.3, sympy 1.14, gcc 16, rustc 1.97.

## Conventions

* **Automata.** An automaton on Q = {0,…,n−1} is given by its letters, each written as the list of images of
  0,…,n−1. Words act on the right: q·(uv) = (q·u)·v, so `ba` applies b first.
* **Notation** is the paper's: σ_t, β\*, B, B_T, minext, stuck (minext(S) > n−1), deviation d, the regions C♯
  and H♯, (Q-CERT) and (Q-CERT+), B_e. A census "instance" is a pair (automaton, S), with S a proper
  nonempty subset.
* **Quotient convention** (Appendix A.1).
  * The first letter ranges over one representative of each conjugacy class of maps of Q: 3, 7, 19, 47, 130,
    343 classes at n = 2,…,7 (sequence A001372). The second letter ranges over all n^n maps.
  * Since the second letter is arbitrary, no count depends on which map represents a class, and the programs
    choose representatives independently.
  * The exception is the ternary n = 5 sub-population of Appendix A: its third letter ranges over class
    representatives only, so its size depends on that choice and on the permutation chosen for each cycle
    type. `ternary/ternary.py` states both choices: the lexicographically least map of each class, and the
    cycles on consecutive states.
* **Ternary automata.** At k = 3 the paper counts the two letters after the first as a multiset; that is how
  `ternary/ternary.py` counts. The census engine in `second_moment/` enumerates them as ordered pairs.
  `second_moment/tables.py` also derives the multiset automaton counts.
* **Parts.** A long run can be split into parts. Part `i` of `K` takes the first-letter representatives whose
  index r satisfies r ≡ i (mod K). `stationary/sum_parts.py` adds up the parts of a run, including runs of
  `eulerian_fibres/`.
* **Inputs.** Files of class representatives are generated, never shipped:
  * `eulerian_fibres/class_reps.c` writes all conjugacy classes;
  * `stationary/permutation_reps.py` writes one permutation per cycle type.

## Quick checks (about 6 minutes)

```bash
cd examples
python examples_and_figures.py     # 47 rows, 0 FAILED   (about a second)
python flat_walks.py               #  7 rows, 0 FAILED   (under a minute)
python root_location.py            #  9 rows, 0 FAILED   (about a minute)
cd ../ks_family
python ks_family.py                # 11 rows, 0 FAILED   (about a second)
cd ../census
python single_length.py            #  4 rows, 0 FAILED   (about a second)
cd ../ternary
python ternary.py --procs 2        # 20 rows, 0 FAILED   (2 to 3 minutes on 2 processes)
cd ../stationary
python witnesses.py                # 39 rows, 0 FAILED   (a few seconds)
python equal_weight_witnesses.py   # 35 rows, 0 FAILED   (about 20 s)
python family_witnesses.py 5 40    # 288 rows, 0 FAILED  (two seconds)
python berlinkov_L.py              #  4 rows, 0 FAILED   (under a minute)
cd ../second_moment
python membership.py 5             #  6 rows, 0 FAILED   (under a minute)
cd ../eulerian_fibres
python ternary_converse_n4.py      #  9 rows, 0 FAILED   (about a minute)
```

The runtimes in this file were measured on an 8-core machine shared with other work. Every program is
single-threaded; "cores" means separate processes.

## Reproducing everything

### `examples/` and `ks_family/`

Run the commands in [Quick checks](#quick-checks-about-6-minutes). Each program's docstring lists the statements
it checks.

### `census/`

```bash
python single_length.py                     # Section 5.4                                     1 s
python census.py 3 ; python census.py 4 ; python census.py 5                      # a few seconds
python census.py 5 --nosync ; python census.py 5 --syncnotsc    # Section 6.1       a few seconds
python census.py 6                          # n = 6                                     about 4 min
python grading.py 5                         # Section 6.4                                     2 s
python quotient_vs_labelled.py 4 d2         # Appendix A: 811                                 1 s
python quotient_vs_labelled.py 6 d2         # Appendix A.1: 76.18 / 91.37             under a minute
python quotient_vs_labelled.py 6 unfiltered # Appendix A.1: 90.13 / 96.94             about a minute
python identity_check.py --procs 2          # Appendix A, identity (2); 16 rows         about 4 min
python census_d4.py ABCE                    # n = 4..6, and n = 7 on {d<=4}; numba      about 14 min
```

`census.py` and `grading.py` print a JSON dictionary, and their docstrings describe every field. The paper's
numbers come from these fields:

* `census.py N`:
  * `population`, with `dev_strata["0"]` for the Eulerian automata;
  * `stuck` and `stuck_maxB` (−1);
  * `Bneg`, the instances with B < 0 (Section 6.3);
  * `Csharp_minus_Bge0` / `Bneg` (Section 6.5);
  * `grade_boundary_fail[n-2]` (Section 6.4: 402, 2,428, 8,528);
  * `violations_Beq0` (Section 6.1: 58,060 with `--nosync`, 0 with `--syncnotsc`);
  * `grade_strict_fail` (0 in all three runs at n = 5);
  * `never_ext`;
  * `chain_np1_B` (Section 8.1: 23,965);
  * `maxrt` (9 and 16).
* `grading.py 5`:
  * `first_pos[1]` (314,393) and `only_full` (12,064);
  * `union_minus_BTpos[2]` and `[4]` (12,644, 29,396);
  * `union_minus_BTge0[2]` and `[4]` (9,108, 26,826), with `BTge0_minus_union` nonzero at T = 2 and 4;
  * `slack[t]["0"]` (314,393, 74,052, 9,338, 808).

`census_d4.py`, `single_length.py`, `quotient_vs_labelled.py` and `identity_check.py` print `[PASS]`/`[FAIL]`
rows. `census_d4.py` leg C can be run in parts (`python census_d4.py C I K`) and can write its tables with
`--json FILE`; the rows that need the whole population are checked only in a run without parts.

### `second_moment/`

```bash
gcc -O2 -o census_engine census_engine.c
python run_populations.py ./census_engine OUT --jobs 2     # the eleven populations of Section 6.6, 10-15 min
python tables.py OUT                                       # 90 rows, 0 FAILED
python membership.py 3 ; python membership.py 4 ; python membership.py 5    # Appendix D, n <= 5
rustc -O membership.rs && ./membership 6 filter                             # Appendix D, n = 6, 1-3 min
```

`tables.py` checks the following from the engine's integer counters:

* Table A.1 and the range quoted in Section 4.1;
* the quotient and labelled shares of Appendix A.1;
* the counts of Sections 6.3, 6.4, 6.5 and 6.6;
* the 21 cells of Table D.1, and the ratios of Appendix D over the populations of Table D.1;
* "0 stuck subsets certified" and "n−1 at every size" on the eleven populations;
* the binary gap statement of Appendix D;
* the population sizes of Appendix A.

`membership 6 filter` prints `memonly_rows_syncsc=2083316` and `rows_syncsc=347983990`.

The independent Python engine (numpy) recomputes four of the populations. `compare_engines.py` compares
12 integer fields in both counting conventions, 96 comparisons in all (Appendix A):

```bash
python independent_engine/run.py 3 2 n3_all PYOUT
python independent_engine/run.py 4 2 n4_all PYOUT
python independent_engine/run.py 5 2 n5_all PYOUT                          # 2-4 min
python independent_engine/run.py 4 3 n4k3_part0 PYOUT --reps 0 7          # the ternary n = 4 population
python independent_engine/run.py 4 3 n4k3_part1 PYOUT --reps 7 13          # in three pieces, 2-4 min each
python independent_engine/run.py 4 3 n4k3_part2 PYOUT --reps 13 19
python independent_engine/merge.py PYOUT n4k3_all n4k3_part0 n4k3_part1 n4k3_part2
python compare_engines.py OUT PYOUT            # compared 96 integer fields, 96 matched, 0 MISMATCHED
```

### `ternary/`

```bash
python ternary.py --procs 2                    # 20 rows, 0 FAILED; 2-3 min on 2 processes
```

### `eulerian_fibres/`

```bash
gcc -O2 -o class_reps class_reps.c
gcc -O2 -o fibres fibres.c
for n in 4 5 6 7 8; do ./class_reps $n reps_$n.txt; ./fibres $n reps_$n.txt; done     # n = 8: about 2 min
./class_reps 9 reps_9.txt                                                              # about 6 min
for i in 0 1 2 3; do ./fibres 9 reps_9.txt $i 4 > fibres9_$i.out & done; wait         # about 80 min on 4 cores
python ../stationary/sum_parts.py fibres9_0.out fibres9_1.out fibres9_2.out fibres9_3.out
```

Each run ends with a `DONE` line carrying `eulerian_sync_automata=` and `per_size_max_minext=[...]`.
`sum_parts.py` adds up the parts and reports whether the gcd law holds: the maximum is n−1 at the sizes m
with gcd(m, n) = 1, and n−2 otherwise.

### `stationary/`

Build and generate the inputs:

```bash
gcc -O2 -o uniform_weights uniform_weights.c
gcc -O2 -o bias_census bias_census.c -lm
gcc -O2 -o bias_census_exact bias_census_exact.c -lm
gcc -O2 -o permutation_stratum permutation_stratum.c
gcc -O2 -o class_reps ../eulerian_fibres/class_reps.c
for n in 2 3 4 5 6 7; do ./class_reps $n reps_$n.txt; done
python permutation_reps.py 8 reps_perm_8.txt       # 22 cycle types
python permutation_reps.py 9 reps_perm_9.txt       # 30 cycle types
```

Witnesses and Berlinkov's L (`[PASS]`/`[FAIL]` rows):

```bash
python witnesses.py                 # Proposition 8 and the mechanism paragraph of Appendix C
python equal_weight_witnesses.py    # Proposition 9 and its verification in Appendix C
python family_witnesses.py 5 40     # the family of Appendix C: a witness on every n >= 5 (exact, n = 5..40)
python berlinkov_L.py               # Section 7.3: L = 135, 666, maximum reset threshold 25
```

Uniform weights (Appendix C; Section 7.3, "no such subset at n ≤ 7"):

```bash
./uniform_weights regions 4 2 reps_4.txt > r42.out     # 115 of the 7,460 instances of H# have B_e >= 0
./uniform_weights regions 5 2 reps_5.txt > r52.out     # REGIONS Be>=0&B<0=17037  B>=0&Be<0=9793
./uniform_weights regions 6 2 reps_6.txt > r62.out     # about 15 s
./uniform_weights regions 4 3 reps_4.txt > r43.out
python sum_parts.py --populations r42.out r52.out r62.out r43.out    # 76,125,984 instances
for n in 2 3 4 5 6; do ./uniform_weights search $n 2 reps_$n.txt; done   # max_Be_on_stuck=-1 at every n
for i in 0 1 2 3; do ./uniform_weights search 7 2 reps_7.txt $i 4 > s7_$i.out & done; wait    # about 6 min of CPU
python sum_parts.py s7_*.out                           # 42,605,958 automata, 2,827,614 stuck subsets, max -1
for i in 0 1 2 3; do ./uniform_weights search 5 3 reps_5.txt $i 4 > t5_$i.out & done; wait    # about 5 min of CPU
python sum_parts.py t5_*.out                           # 138,540,502 automata; max_Be_on_stuck_distinct_letters=-1
for i in 0 1 2; do ./uniform_weights search 8 2 reps_perm_8.txt $i 3 > s8_$i.out & done; wait  # about 1 h of CPU
python sum_parts.py s8_*.out                           # 123,014,054 automata, 18,609,570 stuck subsets, max -1
```

The same maxima from the second program (`census`: stuck subsets and B_e only):

```bash
./permutation_stratum 5 reps_5.txt census ; ./permutation_stratum 6 reps_6.txt census       # seconds
for i in 0 1; do ./permutation_stratum 7 reps_7.txt $i 2 census > p7_$i.out & done; wait     # a few minutes
python sum_parts.py p7_0.out p7_1.out
```

Bias census (Appendix C, and the statements of Appendix A on how it was checked):

```bash
./bias_census 4 reps_4.txt                              # min_t*=1.000000
./bias_census 5 reps_5.txt > bc5.out ; ./bias_census 6 reps_6.txt > bc6.out
for i in 0 1; do ./bias_census 7 reps_7.txt $i 2 > bc7_$i.out & done; wait                  # about 6 min on 2 cores
./bias_census_exact 5 reps_5.txt > bce5.out ; ./bias_census_exact 6 reps_6.txt > bce6.out
for i in 0 1; do ./bias_census_exact 7 reps_7.txt $i 2 > bce7_$i.out & done; wait            # about 5 min on 2 cores
python sum_parts.py bc7_0.out bc7_1.out                 # 116 pairs at the 2/3 bin, none below
python compare_histograms.py --a bc5.out --b bce5.out
python compare_histograms.py --a bc6.out --b bce6.out
python compare_histograms.py --a bc7_0.out bc7_1.out --b bce7_0.out bce7_1.out    # every bin agrees; every pair certified
python boundary_classes.py bc5.out bc6.out bc7_0.out bc7_1.out                   # 39 rows: exactly 2/3; 1, 1, 4 classes
```

The two permutation-first strata:

```bash
for i in 0 1; do ./bias_census_exact 8 reps_perm_8.txt $i 2 > bce8_$i.out & done; wait       # about 51 min on 2 cores
python sum_parts.py bce8_0.out bce8_1.out                # 416 pairs below 2/3 (bins 35: 384, 42: 32), 32 at 2/3
python exact_n8.py bce8_0.out bce8_1.out                 # 21 rows: 2 - sqrt 2, 0.603, 2/3 exactly
for i in 0 1; do ./permutation_stratum 8 reps_perm_8.txt $i 2 census thr > ps8_$i.out & done; wait   # about 5 min
python sum_parts.py ps8_0.out ps8_1.out                  # the n = 8 stratum again, by centraliser orbits
for i in 0 1 2 3; do ./permutation_stratum 9 reps_perm_9.txt $i 4 census thr > ps9_$i.out & done; wait  # 1-4 h per part
python sum_parts.py ps9_*.out                            # 3,761,587,885 automata, 278,959,029 stuck subsets, max -1
python exact_thresholds.py ps9_*.out                     # 0.594 (384 pairs), 0.643 (32), 2/3 (1,568)
```

At n ≤ 8, `bias_census_exact.c` certifies over the whole interval [1/2, 2/3] that the excess of every pair
not re-verified exactly is non-positive. `compare_histograms.py` and `exact_n8.py` check this. At n = 9,
`permutation_stratum.c` evaluates the thresholds on the grid of step 1/400; `exact_thresholds.py` then
determines exactly the thresholds of the pairs at or below the 2/3 bin.

`sum_parts.py` and the census programs print `DONE` lines with named fields. Each program's docstring lists
them.

## Map from the paper to the programs

| paper | statement | program |
|---|---|---|
| Example 1, Figures 1–2 | C_3: in-degrees, w, β\* = (−4,3,1), B on the eight subsets, minext, the two stuck subsets | `examples/examples_and_figures.py` |
| Section 4.1, Table A.1 | the share of non-Eulerian automata with no proper nonempty subset in K⊥ ∩ {0,1}^Q: 55.3 to 93.3 percent, not monotone | `second_moment/tables.py` |
| Section 5.2 | group automata: β\* = 0, nothing extends, not synchronizing | `examples/examples_and_figures.py` |
| Section 5.2 | fibre sizes 72, 954, 12,228, 192,582, 3,212,088, 59,605,126 and the maxima of minext by subset size, n = 4,…,9 | `eulerian_fibres/fibres.c` (and `stationary/sum_parts.py` at n = 9); `census/census_d4.py` (n ≤ 7) |
| Section 5.2 | the coprimality conjecture is binary: with three letters, on the 24,606 Eulerian synchronizing strongly connected ternary automata on 4 states, the maximum of minext is 3 at every subset size and 832 subsets of size 2 attain it; the example a = [0,0,2,2], b = [0,1,3,2], c = [3,1,1,3], S = {0,1}, word cbc | `eulerian_fibres/ternary_converse_n4.py` |
| Section 5.4, Example 2, Figure 3 | w = (2,−1,−1), w^T M = −2w^T, σ_2 ≡ 0, the bipartition, strongly connected and not synchronizing; the roots of h_t on \|z\| = k | `examples/examples_and_figures.py`, `examples/root_location.py` |
| Section 5.4 | 6 of 639, 48 of 63,016, 0 of 18,003 | `census/single_length.py` |
| Section 6.1 | 146,875 = 31,895 + 82,392 + 32,588; the strict half on all three; no boundary violation on the 82,392; 58,060 on the 31,895 | `census/census.py 5` (with `--nosync`, `--syncnotsc`); `examples/flat_walks.py` |
| Section 6.2 | C_3: B({0,1}) = −1, minext 3, the words of length ≤ 2, baa | `examples/examples_and_figures.py` |
| Section 6.2 | largest B on a stuck subset −1 on binary n = 3, 4, 5 and ternary n = 4; −1, −2, −6, −4, −50, −68 by deviation | `census/census.py`, `ternary/ternary.py` |
| Section 6.3 | {B < 0}: 138/354, 7,724/17,360, 463,047/977,640, 33,481,397/69,596,798 | `second_moment/tables.py`, `census/census.py` |
| Section 6.3 | {2} on C_3; n−1 attained inside {B ≥ 0} | `examples/examples_and_figures.py`, `census/census_d4.py`, `ternary/ternary.py` |
| Section 6.4 | 314,393; 12,064; 12,644 and 29,396; 9,108 and 26,826; 314,393, 74,052, 9,338, 808; the witness family; 402, 2,428, 8,528 | `census/grading.py 5`, `census/census.py`, `second_moment/tables.py`, `examples/examples_and_figures.py` |
| Section 6.5 | C♯ shrinks {B < 0} by 3.4, 5.8, 9.1 percent; 0 on the 59 automata at n = 3; 3.06 at ternary n = 4 against 3.42 | `second_moment/tables.py`, `census/census.py`, `ternary/ternary.py` |
| Section 6.6 | the shares of (Q-CERT) and (Q-CERT+) over the populations of Table D.1; 0 stuck subsets certified and n−1 at every size, on the eleven populations; the multiset −1,−1,0,0 | `second_moment/tables.py`, `examples/examples_and_figures.py` |
| Section 7.3 | L reaches 135 on the permutation-first stratum at n = 6; 666; maximum reset threshold 25 | `stationary/berlinkov_L.py` |
| Proposition 8, Appendix C | the four witnesses, the chain, the stationary vectors at weights (t, 1−t), the letters invisible to e | `stationary/witnesses.py` |
| Section 7.3, Appendix C | bias thresholds 1 (n = 4), 2/3 (n = 5, 6, 7), 2−√2 (n = 8 stratum), 0.594 (n = 9 stratum) | `stationary/bias_census.c`, `bias_census_exact.c`, `permutation_stratum.c`, `boundary_classes.py`, `exact_n8.py`, `exact_thresholds.py`, `compare_histograms.py`, `sum_parts.py` |
| Proposition 9, Appendix C | the witnesses at n = 9 and n = 10, reset words, the words giving 5, the blocks Y and Z, the depth profiles | `stationary/equal_weight_witnesses.py` |
| Appendix C, the family proposition | for every n ≥ 5 the automaton A_n on the states γ_1..γ_L, h_1, h_2, z_1..z_r: synchronizing, strongly connected, minext({γ_L, h_2}) = 2L+2 ≥ n, the closed-form stationary vector at weights (t, 1−t), n e(S) − 2 e(Q) = (n−2L) − (1−t)(3n−8), the threshold 1 − (n−2L)/(3n−8) | `stationary/family_witnesses.py` |
| Section 7.3 | no such subset at n ≤ 7 | `stationary/uniform_weights.c`, `permutation_stratum.c` |
| Section 8.1 | 23,965 of 32,588 automata admit a growth chain in {B ≥ 0}; C_n: {1}b⁻¹ = {0,1}, rt(C_n) = (n−1)² | `census/census.py 5`, `examples/examples_and_figures.py` |
| Section 8.2 | the two flat moves on C_3 | `examples/examples_and_figures.py` |
| Section 8.3 | the witness at n = 5; the statement holds at n = 3, 4 (largest B −1) and fails on 49 subsets at n = 5 (largest B +5) | `examples/flat_walks.py` |
| Appendix A | population sizes | `census/census.py`, `census/census_d4.py`, `second_moment/tables.py`, `ternary/ternary.py`, `stationary/sum_parts.py` |
| Appendix A | Theorem 1 with 0 violations on 23,234,424 binary automata (32,588 + 1,122,529 + 22,079,307) and on the two ternary populations (395,299 + 580,893), 24,210,616 in all; the stuck subsets 11,042, 186,497 and 1,853,891; no never-extendable subset; Corollary 2 | `census/census_d4.py`, `census/census.py`, `ternary/ternary.py` |
| Appendix A | identity (2) against word enumeration: 0 disagreements of 977,640 at n = 5, and 0 at k = 3 | `census/identity_check.py` |
| Appendix A | {β\* = 0} is the Eulerian locus: 72, 954, 12,228, 192,582 (205,836); the ternary populations agree | `census/census_d4.py`, `ternary/ternary.py` |
| Appendix A | min\|root(p)\|/k from 2 (n = 3) to 1.05427 (n = 40); 1,760 random weightings, smallest ratio 1.00075; 1.00000004 at ε = 10⁻⁶ | `examples/root_location.py`; `census/census_d4.py` leg E |
| Appendix A | 11,385 and 9,698 attaining subsets; the singleton maximum n at d = 2,…,8 (n = 5); rt maxima 9 and 16; (n−1)² at d = 2 only; #{B > 0} = #{B < 0} = 463,047 | `ternary/ternary.py`, `census/census_d4.py`, `census/census.py`, `examples/flat_walks.py` |
| Appendix A | the C and Python programs agree on 96 of 96 integer fields | `second_moment/compare_engines.py` |
| Appendix A | the bias census at n ≤ 7 by two programs agreeing on every bin; the 133, 448 and 1,984 pairs re-verified exactly; the n = 9 program reproduces the n = 8 stratum | `stationary/compare_histograms.py`, `boundary_classes.py`, `exact_n8.py`, `exact_thresholds.py`, `permutation_stratum.c`, `sum_parts.py` |
| Appendix A | the uniform-weight maxima by two programs on the binary populations up to n = 8 | `stationary/uniform_weights.c`, `permutation_stratum.c` |
| Appendix A.1 | 19, 47, 130, 343 classes; 395,299 against 789,358 | `eulerian_fibres/class_reps.c`, `census/census_d4.py`, `ternary/ternary.py`, `second_moment/tables.py` |
| Appendix A.1 | no permutation letter: 76.18 against 91.37, and 90.13 against 96.94 | `census/quotient_vs_labelled.py` |
| Appendix A.1, A.2 | the fractions of Table A.1 in both conventions; the shift is under 2.5 points | `second_moment/tables.py` |
| Appendix C | t\* at n = 5, 6, 7: 9, 8 and 116 attaining pairs in 1, 1 and 4 classes, none in (1/2, 2/3), the light letter a permutation, the heavy letter of deficiency 1 or 2, (3t−2)·c·t^i(1−t)^j | `stationary/bias_census.c`, `compare_histograms.py`, `boundary_classes.py` |
| Appendix C | uniform weights: no stuck subset with B_e ≥ 0 and maximum −1 at n ≤ 7, on the n = 8 and n = 9 strata, and on ternary n = 5 with pairwise distinct letters | `stationary/uniform_weights.c`, `permutation_stratum.c`, `sum_parts.py` |
| Appendix C | the n = 8 example with threshold 2−√2; 416 pairs below 2/3 (384 + 32); none heavy at t = 1/2 | `stationary/exact_n8.py`, `bias_census_exact.c`, `permutation_stratum.c` |
| Appendix C | n = 9: 384 pairs at 0.594, 32 at 0.643, 1,568 at 2/3 | `stationary/permutation_stratum.c`, `exact_thresholds.py` |
| Appendix C | {B_e ≥ 0} and {B ≥ 0} incomparable: 17,037 and 9,793 at n = 5; 76,125,984 instances; the four-state witness; 115 of 7,460 in H♯ at n = 4 | `stationary/uniform_weights.c regions`, `sum_parts.py --populations`, `examples/examples_and_figures.py` |
| Appendix C | on the Kisielewicz–Szykuła family the maximising subsets have B_e = −13 at n = 5, falling with n | `ks_family/ks_family.py` |
| Appendix D | the attainable second moments 3, 5, 9 and the observation 7 | `examples/examples_and_figures.py`, `second_moment/membership.py` |
| Appendix D | the membership test: 0 of 708, 80 of 52,080, 15,053 of 3,910,560, 2,083,316 of 347,983,990 | `second_moment/membership.py`, `membership.rs` |
| Appendix D, Table D.1 | the 21 cells; the ratio of (Q-CERT) to C♯; the ternary shares 90.04 and 90.64 | `second_moment/tables.py`, `ternary/ternary.py` |
| Appendix D | the gap witness; gap instances 1,952, 1,157, 125 at d = 6, 8, 10 on ternary n = 4; no gap on the binary {d ≤ 2} populations | `examples/examples_and_figures.py`, `ternary/ternary.py`, `second_moment/tables.py` |
| Appendix E, Table E.1 | d = n−3; 8, 14, 22, 31, 44, 56 at a single subset of size m−1; the closed forms; the budget 2n | `ks_family/ks_family.py` |
| Appendix E | {d ≤ 4}: 14 = 2n at n = 7 (22,079,307 automata); 28,968 and 808,403 automata at n = 5, 6; rt maxima 9, 16, 25, 36 at d = 2; the comparisons at subset sizes 3 and n−1 | `census/census_d4.py` |
