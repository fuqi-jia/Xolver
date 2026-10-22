# Gate cleanup closeout — 2026-10-23

The final scan found one additional unused build switch, `XOLVER_ENABLE_TRACING`. Its CMake option and compile definition were removed. The obsolete `tools/tuning/autotune.py` default-flip proposer was also removed, and comments that described deleted switches were corrected. MCSAT/NLSAT implementations and their direct tests remain.

The original 171-item batch list is removed, plus eight controls found outside that list. No active legacy algorithm gate remains in the reviewed scope. This is a source audit, not a formal exhaustiveness proof.

The review covered named environment readers, internal Boolean members/parameters, CMake options and preprocessor branches, CLI/Solver options, and retired-name references in tests and tools. The remaining 161 controls at 237 read sites comprise 88 diagnostics, 66 resource controls and seven strategy parameters. Resource-scaling policy, input applicability, solver state, proof/model validation and supported build/package options are retained. Boolean runtime readers all belong to diagnostics. Dynamic reads are confined to the configuration adapters and external proof-checker executable resolution.

SOMTParser is pinned to main merge `ac3efd64c1b6ac88fd00803f8edf33a44e499194` (PR #62), whose tree is identical to tested head `8248739a04e57481f2bd636c080d89d3f5ba1bc4`. No local third-party source patch is included.

## Validation and open issue

The final batch12 server suite passed 833 relevant unit cases / 243658 assertions. Its 902 paired cases had zero wrong answers, errors or new verdict regressions, with 103 dual-oracle checks. Of 77 model checks, 76 passed and one timed out. Therefore the strict suite **failed**. The case `nra_194_sat_metitarski_sqrt-1mcosq-8-chunk-0290.smt2` also has unstable solve time on the old baseline; 13 of 15 frozen-binary repetitions timed out. No invalid model was reported. The cause is unresolved; see [deferred bugs](DEFERRED-BUGS.md). This cleanup does not claim a speedup or completion of full PA/SL.

Batch12 experiment `6448777d785e`, run `f728115343ae`; timeout probe `7a16ff4b02d4`, run `e259ce545b2b`. The final solver SHA256 is `ad847f38920967abf8ada8b1846f557ff78ac4b8a60bbb083aa0fcf74295cee2`. The complete results archive SHA256 is `6227d1e624b001d50a46dbd7f615829682c1912a9142299ec55c96d63c1d3970` (4598 individually verified members).

The closeout experiment `7da3c959bb36`, run `2d66d951cae6`, passed: source comparison confirmed that all 13 C++ edits change only comments; the shared-directory rebuild and 833 relevant unit tests / 243658 assertions passed (666 unrelated tests were not selected). Both rebuilt binaries are byte-identical to batch12 r4, so its broader differential evidence and unresolved strict model-check timeout still apply. All compilation/solver tests used Panda1/ExperimentOS and the single locked incremental build directory `/pub/data/jiafq/xolver/build`. See the [structured validation record](GATE-CLOSEOUT-VALIDATION.json) and [final scan](GATE-CLOSEOUT-SCAN.json).

## Evidence storage

Concise reports, audit inventories and experiment protocols are versioned here. Full archives and frozen input copies remain in local `docs/audit/evidence/` and server `validation/`, excluded from Git to avoid committing repeated source/test copies. Historical links to these local archives retain their original provenance. No evidence was deleted.

Closeout results archive: `gate-closeout-results.tar.gz`, SHA256 `c0141bf88f01bb7a2b0e8b711efdcc396a60e5e2eeffa116f8789e6ab91bf28e`; all 1042 members verified.
