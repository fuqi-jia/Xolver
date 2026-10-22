# Independent PA result replay

`tools/proof/isabelle_pa.py` translates a single original SMT-LIB query into
an Isabelle/HOL theorem. SAT closes the original assertions existentially over
their free symbols; UNSAT negates that closure. Supplying a complete model
instead substitutes its free-variable assignments into the original quantified
formula. This checks more than satisfaction of the solver's projected formula.

`tools/proof/replay_pa.py` checks generated theories with the pinned
Isabelle2025-2 distribution. Each theorem uses `presburger`; its transitive
oracle dependencies must be empty. `quick_and_dirty` is disabled. The script
only marks claims `kernel-checked` after a successful build and a second hash
check of the original input copy and generated theory. Generation alone is
explicitly recorded as `generated-unchecked`.

Supported terms include Int/Bool free variables, integer and Boolean
quantifiers, linear arithmetic, constant nonzero `div/mod`, Boolean operators,
chained comparisons, distinctness, `ite`, `abs`, simultaneous `let` bindings,
and `:named` annotations. Every binder receives a fresh HOL identifier.
User-supplied identifiers never appear in Isabelle identifiers or ML code.
Negative divisors use a positive absolute divisor internally, with quotient
sign adjustment, preserving SMT-LIB's nonnegative remainder.

Unsupported commands or semantics produce an explicit error: incremental
sessions, nonconstant/zero divisors, nonlinear products, user-defined functions,
nonzero-arity functions, and sorts other than Int/Bool. This is an expanding
verification interface, not a claim that all solver inputs are already covered.

The trust boundary includes the Python SMT-LIB-to-HOL translator, HOL's integer
and Boolean semantics, and the Isabelle distribution. The generated proofs
are independent of Xolver search and of its elimination trail. They do **not**
prove that the C++ implementation refines these semantics, nor do they yet
provide a native elimination certificate for every PA decision.

## Server execution

The official archive is pinned by SHA256 in `tools/remote/install_isabelle.sh`.
The installation lives in `dependencies/isabelle/Isabelle2025-2` on Panda1.
All runs reuse one locked session/cache at `build/isabelle`; only source,
theorem, configuration and log evidence is archived per run.

A manifest is a JSON list:

```json
[
  {"input": "query.smt2", "verdict": "unsat"},
  {"input": "another.smt2", "verdict": "sat", "model": {"x": -6, "p": true}}
]
```

Replay it on the server through ExperimentOS:

```bash
python3 tools/proof/replay_pa.py \
  --manifest claims.json \
  --isabelle dependencies/isabelle/Isabelle2025-2/bin/isabelle \
  --cache build/isabelle \
  --output validation/pa-claims
```

Output directories must be new so failed or earlier evidence cannot be silently
reused. Manifest verdicts are claims to be checked, not evidence.

The server acceptance harness combines targeted scope/division cases, existing
PA differential inputs, a quantified model, a deliberately false verdict and a
deliberately false model. Infrastructure errors and timeouts do not count as
successful rejection of false claims.

R1 failed during JVM startup under the 16 GB address-space limit. The default
distribution enabled ZGC and used a 256-core host's worker count. R2 configures
two JVM workers and serial GC while keeping the same memory limit. The R1
failure is retained; neither installing Isabelle nor starting a replay counts
as a verified theorem.

R2 reached Poly/ML startup but its compressed-pointer runtime reserves
16 GiB for the heap, 4 GiB for stacks and 2 GiB for code before use
(`contrib/polyml-5.9.2-2/src/libpolyml/memmgr.cpp`, `MemMgr::Initialise`).
R3 therefore allows 32 GiB of virtual address space for the proof task; the
actual ML heap remains capped at 2 GiB. This does not change Xolver's limits.

The new targeted cases exposed three wrong SAT answers in frozen Native R12:
simultaneous `let`, n-ary Boolean equality and chained strict comparison.
R13 changes the parser's binding registration to occur after all right-hand
sides are parsed, expands n-ary equality into adjacent binary equalities, and
dispatches comparisons to the existing vector constructors. Public API
construction also preserves every chained comparison operand.
R13's preflight passed the let/equality checks but exposed a second comparison
dispatcher in the ordinary-expression fast path. R14 removes that duplicate
dispatcher and routes ordinary and indexed operators through the shared entry.
The preserved R12 observations and the new regression files prevent the old
820/820 result from being mistaken for evidence covering these new cases.

R3 and R4 did not complete their 37-claim batches: a quantified stress formula
kept the batch open for minutes. They were stopped explicitly and their logs
are retained. R4's solver observations match all 12 targeted expected verdicts,
but its unfinished batch marks no theorem as checked.

R5 checks 13 targeted claims (including a supplied model), then the false
verdict/model controls, then all 24 differential claims. Aggregate success
still requires all 37 claims. Successful targeted artifacts are retained
independently if a stress claim later exhausts its budget.

Timeout cleanup now traverses the owned process tree, including children
forked by Java threads and detached Poly/ML process groups. It stops the tree
before killing it and checks process start times before sending termination
signals. A test with a child in a separate session verifies that it cannot
survive cleanup. This fixes a process-control issue, not proof validity.

R5's generic simplifier composition failed on the successor statement and a
free-Boolean formula. R6 instead supplies HOL's `all_bool_eq` and `ex_bool_eq`
lemmas directly to the proof-producing Presburger method.

**R6 accepted all 13 targeted claims**, with no oracle dependencies, and rejected
both the false verdict and false model through proof-method failure (return
code 1, not timeout or infrastructure failure). The separate 24-claim stress
batch timed out at 900 seconds (return code 124); this is not a passing
37-claim run. The timed-out batch does not certify any of its 24 claims.

The [acceptance manifest](evidence/pa-isabelle-r6-acceptance-evidence.tar.manifest.json)
binds 97 records, verified after download. Archive SHA256:
`c646e5d1f537c115855be172ff868c3791b4e3a93dc6a796289a5ad7e9d5fdcd`.
It includes the original inputs, generated theories, translator and checker
sources, successful kernel logs, false-claim failures and progress snapshot.
It deliberately excludes the unfinished stress batch.

The later [terminal R6 manifest](evidence/pa-isabelle-r6-final-evidence.tar.manifest.json)
contains 214 records, including the stress timeout and final EOS failure,
plus the completed R14 performance/Python runs. Every archived member and the
archive hash were checked after download. Archive SHA256:
`6d1fecc87a2f903900b038ebfb7d797ef65f6c3765226a763b76c0685678febc`.

R7 adds affine normalization hints as separate proved lemmas. For example,
`3*x + 3*y = 10` is proved equivalent to `False` before elimination of an
enclosing alternating-quantifier formula. Integer bounds use ceiling division
of the constant after coefficient reduction, including negative constants.
Every hint is itself proved with `presburger`; the original query theorem is
unchanged. The transitive oracle check includes all helper lemmas, even unused
ones. A Python normalization error therefore creates a proof obligation that
must fail, rather than silently changing the theorem being checked.
The R7 server replay also includes a false verdict for a query requiring
normalization. **All 37 claims passed**, including all 24 previously timed-out
stress claims (80.66 seconds for that batch). All three false-claim controls
were rejected by proof failure. This is a result for this exact corpus and
checker configuration; it does not establish native QE certificate coverage
or C++ refinement.

The [R7 evidence manifest](evidence/pa-isabelle-r7-evidence.tar.manifest.json)
binds 575 verified records, including the complete proof run and the separate
R15 differential failure. Archive SHA256:
`0e0a6139a819c05f25b53ba147006aead47dcb478190ea8df232b0b027ef7ef3`.

R8 extends the targeted corpus to Boolean/integer quantifier alternation,
piecewise integers, quantified conditions, and both `distinct` fixes. All
20 ordinary theories finish, but the supplied model theorem with nested HOL
`let` assignments fails the proof method; the 21-claim batch is unverified.
The failure is preserved in the
[R16 semantics archive](evidence/pa-r16-semantic-evidence.tar.manifest.json).

R9 adds HOL's proved `Let_def` rule to the method. Its 21 targeted claims now
pass, including the model. All four negative controls are rejected through
proof failure: wrong verdict, wrong model, wrong verdict with normalization,
and a deliberately false normalization helper while retaining a correct
original SAT theorem. The last mutation exists only in the audit harness;
its driver, generated false theorem and `mutation.json` record the test.
The unchanged 24-claim stress batch also passes. **All 45 claims are
kernel-checked**, and all four negative controls fail through proof rejection,
not timeout or infrastructure error. This still establishes per-query
mathematical results rather than a proof that the C++ implementation refines
the PA semantics.

The [terminal R9/R16 manifest](evidence/native-r16-final-evidence.tar.manifest.json)
contains 1200 records, all hash-verified after download, archive SHA256
`5f3658adefc7ba4ddd3408f60c4127568e2154cb98b5b54fa9bd408b8953f712`.
The corrupted-hint log fails at `normalize_0` itself, before the correct
original SAT theorem: the checker rejects the false equivalence
`(3*x = 3000000000000000000000000000003) = False`.

## Native QE obligations (R23 implementation)

PA now consumes SOMTParser nodes directly. It does not include `NativeTerms`,
`TermExpr`, `Kind` or `ExprId`; only theory-specific affine/divisibility data
crosses from decision to evidence. Native declarations are mapped by node
identity to PA variable numbers, including shadowed binders. Let aliases are
resolved through binding nodes. The public runtime passes native DAG handles.

`solve input.smt2 --produce-pa-certificate certificate.json` requests the PA
backend and exports a completed SAT or UNSAT decision's QE obligations. An
unsupported theory or exhausted budget yields no certificate. Output creation
is exclusive: existing evidence is never overwritten or counted as a new result.
A multi-query script cannot reuse one certificate destination. The C++ API uses
`setOption("produce-pa-certificate", true)` and
`getProof().presburger()`; assertion/scope mutation and a new query invalidate
previous evidence. This export is separate from ground Alethe/DRAT production.

The `xolver-pa-qe-obligations/1` JSON format records every completed existential
elimination, including inner user binders and local division/piecewise witnesses.
Each step contains its eliminated variable and exact before/after DNFs. Integers
and variable IDs are decimal strings; a zero divisor denotes an inequality,
and a positive divisor denotes (possibly negated) divisibility. The final DNF
must be the claimed Boolean constant. Recording consumes the solve work budget;
a partial trace is never published as a completed certificate.

To replay an artifact, add `"certificate": "certificate.json"` to its original
input/verdict entry in the manifest shown above. The replay checks the schema,
exact types, completed step count, eliminated-variable absence and absence of
fresh output variables. Isabelle then proves **every supplied QE equivalence**
and, separately, the original query verdict or complete supplied model.
The oracle dependency check includes all QE lemmas, even if the original-query
proof does not use them. Bundle hashes cover the certificate, source, generated
theory and both translators; generation is labeled `generated-unchecked`.

This is not yet a compositional proof of native input lowering. Removing a step
and changing its count could still leave individually valid obligations; the
independent original-query theorem protects the result, not trace completeness
relative to execution. Native Boolean/quantifier composition, parser refinement,
and C++ implementation refinement remain unproved. The schema deliberately calls
these objects obligations. A successful replay must not be reported as a C++
end-to-end proof.

Native-certificate R1 runs against the frozen Native R25 CLI
`f3faf2a04dcb69b67dc94d85d27e9844b03c942e885ddd804efc90627f25e972`.
All 23 query claims, their 46 native elimination equations and three supplied
native models pass Isabelle replay. The corrupted inner QE step and wrong free
model both fail proof checking. The audit driver is
`tools/remote/test_pa_certificates.py`; it obtains actual CLI artifacts and models.
Timeout or infrastructure failure does not count as rejection. This is optional
solver evidence checking, not a requirement to formally verify the C++ program.

Task scope clarification (2026-10-21): the user requests an SMT solver, and no
longer requires a C++ end-to-end refinement proof or a formally proved input
translator. These are not release blockers. SMT semantics, correct verdicts and
models remain requirements; independent certificate checks are optional solver
validation, alongside differential and regression tests.
