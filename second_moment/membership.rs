// membership.rs -- the exact membership test on (|S|, sigma_t(S), sum x_u^2)
// against the (Q-CERT+) threshold, binary automata, any n (used at n = 6)
//
// Supports, in "Certificates for short extending words in a finite automaton":
//   Appendix D: the membership test "certifies ... 2,083,316 of 347,983,990 at
//     n=6, that is ... 0.60 percent" (rows of the exhaustive synchronizing
//     strongly connected binary population, one per proper nonempty subset and
//     length t <= n-1, on which the membership test fires and the (Q-CERT+)
//     threshold does not).  The same computation as membership.py, which covers
//     n = 3, 4, 5 (0 of 708, 80 of 52,080, 15,053 of 3,910,560); at those sizes
//     the two programs print identical counters.
// Population / convention: letter a over one representative of each conjugacy
//   class of endofunctions of Q = {0,...,n-1} (130 classes at n=6), letter b
//   over all n^n maps; with "filter" only synchronizing strongly connected
//   automata get rows (1,122,529 at n=6: quotient convention, Appendix A.1).
//   Row (S, t): x_u = |S u^{-1}| - |S| over the 2^t words of length t,
//   m = -sigma_t(S), c = |S|.  The threshold fires iff sum x_u^2 > q c^2 + r^2
//   with q = floor(m/c), r = m - qc (always when m < 0); membership fires iff
//   sum x_u^2 is not attainable as sum y_u^2 with 2^t integers y_u in [0, c]
//   summing to m.
// Usage:    rustc -O membership.rs            (produces ./membership)
//           ./membership 6 filter             ("nofilter": rows for every automaton)
// Output:   one KEY=VALUE per line: n, classes, autos (enumerated), syncsc,
//           eul, rows, thr, mem, memonly, memonly_sync, rows_syncsc, thr_syncsc,
//           memonly_rows_syncsc.  Appendix D's n=6 figures are
//           memonly_rows_syncsc=2083316 and rows_syncsc=347983990.
// Runtime:  one core: n=6 filter 2 to 3 minutes (167 s measured on a shared
//           machine); n <= 5 under 2 s.
// Requires: rustc (tested with 1.97), standard library only.

use std::collections::HashMap;
use std::env;

fn perms(n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut p: Vec<usize> = (0..n).collect();
    loop {
        out.push(p.clone());
        // next permutation
        let mut i = n as isize - 2;
        while i >= 0 && p[i as usize] >= p[i as usize + 1] {
            i -= 1;
        }
        if i < 0 {
            break;
        }
        let i = i as usize;
        let mut j = n - 1;
        while p[j] <= p[i] {
            j -= 1;
        }
        p.swap(i, j);
        p[i + 1..].reverse();
    }
    out
}

/// canonical form of an endofunction under simultaneous conjugation
fn canon(f: &[usize], n: usize, ps: &[Vec<usize>]) -> Vec<usize> {
    let mut best: Option<Vec<usize>> = None;
    let mut inv = vec![0usize; n];
    for p in ps {
        for i in 0..n {
            inv[p[i]] = i;
        }
        let g: Vec<usize> = (0..n).map(|i| p[f[inv[i]]]).collect();
        if best.is_none() || g < *best.as_ref().unwrap() {
            best = Some(g);
        }
    }
    best.unwrap()
}

fn classes(n: usize) -> Vec<Vec<usize>> {
    let ps = perms(n);
    let total = (n as u64).pow(n as u32);
    let mut seen = std::collections::HashSet::new();
    let mut reps = Vec::new();
    for code in 0..total {
        let mut f = vec![0usize; n];
        let mut c = code;
        for i in 0..n {
            f[i] = (c % n as u64) as usize;
            c /= n as u64;
        }
        let k = canon(&f, n, &ps);
        if seen.insert(k) {
            reps.push(f);
        }
    }
    reps
}

fn is_sync(a: &[usize], b: &[usize], n: usize) -> bool {
    // every unordered pair must reach the diagonal
    for p0 in 0..n {
        for q0 in (p0 + 1)..n {
            let mut seen = vec![false; n * n];
            let mut stack = vec![(p0, q0)];
            seen[p0 * n + q0] = true;
            let mut ok = false;
            while let Some((p, q)) = stack.pop() {
                if p == q {
                    ok = true;
                    break;
                }
                for f in [a, b] {
                    let (mut x, mut y) = (f[p], f[q]);
                    if x > y {
                        std::mem::swap(&mut x, &mut y);
                    }
                    if !seen[x * n + y] {
                        seen[x * n + y] = true;
                        stack.push((x, y));
                    }
                }
            }
            if !ok {
                return false;
            }
        }
    }
    true
}

fn is_sc(a: &[usize], b: &[usize], n: usize) -> bool {
    let mut fwd = vec![Vec::new(); n];
    let mut rev = vec![Vec::new(); n];
    for q in 0..n {
        for f in [a, b] {
            fwd[q].push(f[q]);
            rev[f[q]].push(q);
        }
    }
    let reach = |g: &Vec<Vec<usize>>| -> usize {
        let mut seen = vec![false; n];
        let mut st = vec![0usize];
        seen[0] = true;
        let mut c = 1;
        while let Some(x) = st.pop() {
            for &y in &g[x] {
                if !seen[y] {
                    seen[y] = true;
                    c += 1;
                    st.push(y);
                }
            }
        }
        c
    };
    reach(&fwd) == n && reach(&rev) == n
}

/// table[m][sq] = true iff sum(y^2)=sq is attainable with N terms in [0,c]
/// summing to m.  Built once per (N,c).
fn attain_table(nw: usize, c: usize) -> Vec<Vec<bool>> {
    let maxm = nw * c;
    let maxsq = nw * c * c;
    let mut cur = vec![vec![false; maxsq + 1]; maxm + 1];
    cur[0][0] = true;
    for _ in 0..nw {
        let mut nxt = vec![vec![false; maxsq + 1]; maxm + 1];
        for s in 0..=maxm {
            for sq in 0..=maxsq {
                if !cur[s][sq] {
                    continue;
                }
                for y in 0..=c {
                    let s2 = s + y;
                    let q2 = sq + y * y;
                    if s2 > maxm || q2 > maxsq {
                        break;
                    }
                    nxt[s2][q2] = true;
                }
            }
        }
        cur = nxt;
    }
    cur
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let want_filter = args.get(2).map(|s| s == "filter").unwrap_or(true);
    let tmax = n - 1;

    let reps = classes(n);
    let nsub = 1usize << n;

    // proper nonempty subsets as bitmasks
    let subsets: Vec<usize> = (1..nsub - 1).collect();

    let mut cache: HashMap<(usize, usize), Vec<Vec<bool>>> = HashMap::new();
    for t in 1..=tmax {
        let nw = 1usize << t;
        for c in 1..n {
            cache.entry((nw, c)).or_insert_with(|| attain_table(nw, c));
        }
    }

    let mut autos: u64 = 0;
    let mut syncsc: u64 = 0;
    let mut eul: u64 = 0;
    let mut rows: u64 = 0;
    let mut thr: u64 = 0;
    let mut mem: u64 = 0;
    let mut memonly: u64 = 0;
    let mut memonly_sync: u64 = 0;
    let mut rows_syncsc: u64 = 0;
    let mut thr_syncsc: u64 = 0;
    let mut memonly_syncsc: u64 = 0;

    let total_b = (n as u64).pow(n as u32);
    let mut b = vec![0usize; n];
    for a in &reps {
        for code in 0..total_b {
            let mut c = code;
            for i in 0..n {
                b[i] = (c % n as u64) as usize;
                c /= n as u64;
            }
            autos += 1;
            let sy = is_sync(a, &b, n);
            let sc = is_sc(a, &b, n);
            let keep = sy && sc;
            if keep {
                syncsc += 1;
                let mut indeg = vec![0usize; n];
                for q in 0..n {
                    indeg[a[q]] += 1;
                    indeg[b[q]] += 1;
                }
                if indeg.iter().all(|&d| d == 2) {
                    eul += 1;
                }
            }
            if want_filter && !keep {
                continue;
            }
            for t in 1..=tmax {
                let nw = 1usize << t;
                // per-word preimage-count vectors, then subset sums over masks
                // sums[w][mask] = |S u^{-1}| for the w-th word of length t
                let mut sums: Vec<Vec<i64>> = Vec::with_capacity(nw);
                for w in 0..nw {
                    let mut v = vec![0i64; n];
                    for q in 0..n {
                        let mut x = q;
                        let mut ww = w;
                        for _ in 0..t {
                            x = if ww & 1 == 0 { a[x] } else { b[x] };
                            ww >>= 1;
                        }
                        v[x] += 1;
                    }
                    // subset-sum over masks
                    let mut s = vec![0i64; nsub];
                    for mask in 1..nsub {
                        let low = mask.trailing_zeros() as usize;
                        s[mask] = s[mask & (mask - 1)] + v[low];
                    }
                    sums.push(s);
                }
                for &mask in &subsets {
                    let cs = mask.count_ones() as i64;
                    let mut sig: i64 = 0;
                    let mut sq: i64 = 0;
                    for w in 0..nw {
                        let x = sums[w][mask] - cs;
                        sig += x;
                        sq += x * x;
                    }
                    rows += 1;
                    if keep {
                        rows_syncsc += 1;
                    }
                    let m = -sig;
                    let fires_thr = if m < 0 {
                        true
                    } else {
                        let q_ = m / cs;
                        let r_ = m - q_ * cs;
                        sq > q_ * cs * cs + r_ * r_
                    };
                    let tab = &cache[&(nw, cs as usize)];
                    let fires_mem = if m < 0 || (m as usize) >= tab.len() {
                        true
                    } else {
                        let row = &tab[m as usize];
                        let s = sq as usize;
                        !(s < row.len() && row[s])
                    };
                    if fires_thr {
                        thr += 1;
                        if keep {
                            thr_syncsc += 1;
                        }
                    }
                    if fires_mem {
                        mem += 1;
                    }
                    if fires_mem && !fires_thr {
                        memonly += 1;
                        if sy {
                            memonly_sync += 1;
                        }
                        if keep {
                            memonly_syncsc += 1;
                        }
                    }
                }
            }
        }
    }

    println!("n={}", n);
    println!("classes={}", reps.len());
    println!("autos={}", autos);
    println!("syncsc={}", syncsc);
    println!("eul={}", eul);
    println!("rows={}", rows);
    println!("thr={}", thr);
    println!("mem={}", mem);
    println!("memonly={}", memonly);
    println!("memonly_sync={}", memonly_sync);
    println!("rows_syncsc={}", rows_syncsc);
    println!("thr_syncsc={}", thr_syncsc);
    println!("memonly_rows_syncsc={}", memonly_syncsc);
}
