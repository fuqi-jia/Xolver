# SMT benchmark comparisons

`select_public_sample.py` freezes a deterministic family-stratified sample from
an existing SMT-LIB directory. It records member names, sizes, expected statuses
and SHA-256 hashes. Selection uses neither solver outcomes nor file-size cutoffs.
Use the shared immutable SMT-LIB archives for provenance checks; benchmarks do
not need a project-specific copy.

`compare_fixed_sample.py` compares two standard Xolver executables and Z3 on
identical hash-checked inputs. A manifest contains a `cases` array with `path`,
`sha256`, `family`, `logic`, `expected`, and optional `repetitions` fields.
Choose inputs and repetition counts before observing results. Every execution is
a fresh process, with solver order rotated across cases and repetitions.

Follow-up selection accepts `--seed` and repeatable `--exclude previous.json`
arguments. Exclusion applies to member names; content hashes allow additional
overlap checks. A different file is not necessarily a different semantic template.

```bash
python3 tools/regression/select_public_sample.py --root /datasets/non-incremental \
  --output selected.json
python3 tools/regression/compare_fixed_sample.py --manifest selected.json \
  --baseline /validation/baseline/xolver --candidate /validation/candidate/xolver \
  --z3 /oracles/z3 --timeout 3 --output comparison
```

Reports retain verdicts, unknowns, timeouts and errors. A decisive disagreement
with Z3 or the embedded status fails the comparison. All inputs contribute to
coverage and PAR-2; unsolved executions cost twice the timeout. Latency ratios
use medians only where all solvers consistently decide the same verdict, then
weight benchmark families equally. Family bootstrap intervals describe sampling
variation within that sample, not all SMT workloads. Raw observations remain in
`report.json`. Common-case speedups alone cannot establish overall superiority.

The default sample spans QF_LIA, QF_NIA, QF_LRA and QF_NRA. It does not represent
bitvectors, floating point, strings, arrays, quantifiers or incremental solving.
Broader claims require explicit samples from those populations and separate
model/proof validation. Agreement with a reference is differential evidence, not
a formal correctness proof.

`tools/fuzz/fuzz_integer_partial.py` separately checks integer div/mod cases with
Z3 and cvc5. Exported SAT models are replayed with their chosen zero-divisor
interpretations pinned under fresh function names. Unspecified table entries
use the model's explicit zero default. Both oracles must reject negative controls
with missing or incorrect zero-divisor values. These generated checks measure
semantic correctness, not public-benchmark performance.

`tools/fuzz/fuzz_linear_arithmetic.py` checks signed rational linear formulas,
strict inequalities and Boolean contexts with Z3 and cvc5. SAT cases have an
independently constructed rational witness; UNSAT cases contain a Boolean
contradiction between linear predicates. Both references also check the fully
pinned exported SAT models. These checks complement the propagation unit tests
that replay returned explanations using only their original premises.

Algebraic SAT models using `root-of-with-interval` are replayed through the
shared model serializer. An exact rational Sturm count must establish one real
root in each open isolating interval. Fresh Real witnesses then retain the
polynomial, interval, original model expressions and every original assertion;
the replay uses `ALL` to express witness polynomials. Independent solvers check
the resulting formula. Ambiguous intervals, constructor-name collisions and
unsupported values remain unverified. This supplements truth evidence and does
not count as a new timed solver decision.
