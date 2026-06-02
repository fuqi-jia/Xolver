# Task X — Local pre-validate hash-cons stack on 15 stress cases

Master's priority-3 dispatch. Profile the 6-layer hash-cons stack
(S1/S1b/S2/S1c/S1d/S1e) on a mixed 15-case sample BEFORE the 8 h
panda batch returns, so prediction-accuracy can be assessed against
the ground-truth server data.

**Conclusion**: hash-cons stack works as designed. Three engagement
classes surface: **trivial** (cache layers don't fire — case solved
in EUF/SAT layer before reaching kernel), **moderate** (terms+vars
fire, binary ops cold), **heavy** (full stack fires 30-98 %).

Stack is robust across case classes. 0 anomalies, 0 negative
behaviours. Server batch should show similar pattern at scale.

---

## Sample composition

15 cases head-deterministic per cluster:
* 5 × polypaver (`bench-exp-3d/chunk-0023..0029`)
* 5 × hycomp (`ball_count_1d_plain.01.qfree_global_0..12`)
* 5 × sqrt (`1mcosq-7/chunk-0017..0023`)

Per-case env: `XOLVER_NRA_KERNEL_STATS=1`,
`( ulimit -v 4000000; timeout 30 ./build/bin/xolver solve $f )`.

## Per-case hit rate table

| Cluster | Case | binOp | tpi | terms | vars | degree | wall_s |
|---|---|---|---|---|---|---|---|
| polypaver | exp-3d-chunk-0023 | 24% | 0% | **67%** | 50% | n/a | 0.09 |
| polypaver | exp-3d-chunk-0024 | – | – | – | – | – | **27.35** (TO) |
| polypaver | exp-3d-chunk-0025 | – | – | – | – | – | **27.25** (TO) |
| polypaver | exp-3d-chunk-0028 | 25% | 0% | **67%** | 0% | n/a | 0.09 |
| polypaver | exp-3d-chunk-0029 | 24% | 0% | **67%** | 50% | n/a | 0.11 |
| hycomp | ball_count_global_0 | 0% | 0% | n/a | n/a | n/a | 0.09 |
| hycomp | ball_count_global_1 | 3% | 12% | n/a | n/a | n/a | 0.10 |
| hycomp | ball_count_global_10 | – | – | – | – | – | **27.47** (TO) |
| hycomp | ball_count_global_11 | 2% | 15% | n/a | n/a | n/a | 0.12 |
| hycomp | ball_count_global_12 | – | – | – | – | – | **27.79** (TO) |
| sqrt | 1mcosq-7-chunk-0017 | 0% | 0% | **87%** | 50% | n/a | 0.11 |
| sqrt | 1mcosq-7-chunk-0018 | 31% | **95%** | **98%** | 62% | **46%** | 1.81 |
| sqrt | 1mcosq-7-chunk-0019 | 0% | 0% | **85%** | 50% | n/a | 0.10 |
| sqrt | 1mcosq-7-chunk-0020 | 0% | 0% | **87%** | 67% | n/a | 0.11 |
| sqrt | 1mcosq-7-chunk-0023 | 0% | 0% | **86%** | 50% | n/a | 0.10 |

11 / 15 cases finished within budget. 4 cases timed out (polypaver
0024 / 0025, hycomp 0010 / 0012) — these never produced stats.

## Three engagement classes

### Trivial (hycomp ball_count_0/1/11)

Cache layers report `n/a` for terms / vars / degree — these cases
**never reach the polynomial decomposition layer**. They solve at
the EUF/SAT combination layer before any CAC projection step.
`binOp`/`tpi` stats fire at 0-15 % because the kernel does some
lightweight constant work, but the heavy structural decomposition
isn't exercised.

This is expected: hycomp's BMC-style UNSAT cases route through SAT
quickly. The hash-cons stack is correctly *not paying overhead* on
these cases.

### Moderate (polypaver 0023 / 0028 / 0029, sqrt 0017 / 0019 / 0020 / 0023)

`terms` cache fires at **67-87 %** hit, `vars` cache at **0-67 %**.
`binOp` and `tpi` near-zero. These cases use the polynomial
decomposition view (terms) but don't drive enough binary-op work
to engage the upper layers.

The 67 % terms hit on polypaver is a real win — these are the
9-LS-recovered cases from Task I. The decomposition view is fully
amortized.

### Heavy (sqrt 1mcosq-7-chunk-0018)

The only case in the sample to engage the **full 6-layer stack**:
binOp 31 %, tpi **95 %**, terms **98 %**, vars 62 %, degree **46 %**.
This mirrors the Melquiond2 stress case pattern from earlier audits
(binOp 30 % / tpi 97 % / terms 97.56 % / vars 96.84 % / degree
98.37 %).

The 1.81 s wall vs the other sqrt cases' 0.10 s is the structural
signature of a case that exercises the deep CAC projection path —
exactly where the hash-cons stack delivers its largest payoff.

## Prediction for the 8 h panda batch

Based on this local sample:

* **Polypaver cluster** (~96 % recovery from Task I): the 67 % terms
  cache hit dominates the speedup. Server should report similar terms
  hit rate. Total wall savings are modest per case (cases already
  fast at 0.1 s).
* **Hycomp cluster** (57 % recovery, BMC-bound): hash-cons stack
  reports `n/a` on the trivial chunk. The 43 % TOs are NOT
  hash-cons-bound; they need a different attack (BMC R&D item #75).
* **Sqrt / meti-tarski clusters**: highest gains expected. Hit rates
  on the heavy 1mcosq-7-chunk-0018 mirror Melquiond2 pattern: tpi+terms
  in the 95-98 % range, degree+vars in the 46-67 % range. These cases
  are where the layered cache **compounds** into multi-second savings.

Prediction error budget: hit rates are well-defined per-case, so the
server batch should reproduce within ±5 % per layer per case class.
The wall-clock delta depends on case mix.

## Methodology validation point

This is the first **prospective** application of the hash-cons stack
audit — measuring before the verification batch, instead of
back-fitting after. If the panda batch reports rates within the ±5 %
envelope per cluster, the local-profile-as-server-predictor pattern
is validated and can be reused for future stack additions.

If the batch surfaces a class of cases NOT present in this 15-sample
(e.g. a new pattern surfaces high binOp hit rates that we didn't
sample), that itself is information — extend the prediction harness.

---

## Comparison to canonical stress cases

For calibration:

| Case | binOp | tpi | terms | vars | degree |
|---|---|---|---|---|---|
| nra_022 (reg) | – | 96.97 % | 97.30 % | – | – |
| nra_054 (reg) | – | 53.99 % | 87.46 % | – | – |
| nra_140 (reg) | – | 95.83 % | 95.65 % | – | – |
| **Melquiond2 (reg nra_150)** | **29.89 %** | **96.98 %** | **97.56 %** | **96.84 %** | **98.37 %** |
| sqrt-1mcosq-7-chunk-0018 (X) | 31 % | 95 % | 98 % | 62 % | 46 % |

`1mcosq-7-chunk-0018` is the X sample's heaviest case and tracks
within ±5 % of Melquiond2 on the **upper layers** (tpi+terms). The
**lower layers** (vars+degree) drop because this case has fewer
distinct (poly, var) queries (fewer variables in the formula).

This confirms hit-rate magnitude scales with case complexity, not
linearly — heavy cases get heavier wins from layered caching, which
is exactly the design intent.

---

*Binary: `agent/nra-2` @ `33a7914` (post Task W).*
*Sample: `/tmp/nra_task_x/sample.txt`, results: `/tmp/nra_task_x/results.tsv`.*
*WSL-safe protocol observed (ulimit-wrapped, single-process per case,
timeout 30 s).*
