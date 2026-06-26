#include "theory/arith/logics/nia/NiaSolver.h"
#include "theory/arith/logics/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/logics/dl/DifferenceGraph.h"
#include "theory/arith/logics/dl/BellmanFord.h"
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/logics/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/logics/nia/search/NiaIcpAdapter.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/logics/nra/core/CdcacCore.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "theory/arith/logics/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"
#include "theory/arith/logics/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/kernel/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/logics/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/logics/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/kernel/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/logics/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/logics/nia/farkas/FarkasOrModelAssembler.h"
#include "util/MpqUtils.h"
#include <chrono>
#include <iostream>

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheoryCheckResult> NiaSolver::stageBoundedEarly(TheoryLemmaStorage&, TheoryEffort) {
    // Phase 3b: early-pipeline placement of the partial bounded
    // enumerator. Reads its own flag XOLVER_NIA_BOUNDED_PARTIAL_EARLY
    // (separate from the late-stage XOLVER_NIA_BOUNDED_PARTIAL — former
    // controls placement, latter algorithm). Sound SAT-finding only;
    // never returns UnsatComplete. On failure, falls through to the
    // rest of the pipeline (so the standard reasoners still get to run).
    static const bool earlyEnabled = [] {
        return xolver::env::flag("XOLVER_NIA_BOUNDED_PARTIAL_EARLY");
    }();
    if (!earlyEnabled) return std::nullopt;
    // Reuse the same algorithm; differs only in pipeline position.
    // Phase L1 step 3 — LS feedback hint (XOLVER_NIA_LS_FEEDBACK=1,
    // default-OFF). The LS context's bestAssignment (when present) is
    // tried as the FIRST candidate before cartesian enumeration. Sound:
    // validator-gated like every other candidate.
    static const bool lsFeedback = [] {
        return xolver::env::flag("XOLVER_NIA_LS_FEEDBACK");
    }();
    const IntegerModel* hint = nullptr;
    if (lsFeedback) {
        const auto& ctx = localSearch_.lsContext();
        if (!ctx.bestAssignment.empty()) hint = &ctx.bestAssignment;
    }
    auto br = bounded_.solvePartialWithHint(normalized_, domains_, validator_, hint);
    if (br.status == BoundedSolveStatus::Sat) {
        currentModel_ = br.model;
        return TheoryCheckResult::consistent();
    }
    // Any other status — fall through to the regular pipeline.
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBounded(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto allVars = collectVars(normalized_, *kernel_);
    bool allFinite = domains_.allFinite(allVars);
    if (allFinite) {
        // Domain is finite: bounded solver is authoritative; skip linear lemmas
        pendingLinLemmas_.clear();
        auto br = bounded_.solve(normalized_, domains_, validator_, lemmaDb);
        if (br.status == BoundedSolveStatus::Sat) {
            currentModel_ = br.model;
            return TheoryCheckResult::consistent();
        }
        if (br.status == BoundedSolveStatus::UnsatComplete) {
            return TheoryCheckResult::mkConflict(*br.conflict);
        }
        // UnknownBudget / UnknownUnsupported: continue pipeline
    } else {
        // Phase 3a (XOLVER_NIA_BOUNDED_PARTIAL, default-OFF). When the full
        // domain isn't finite (some unbounded vars), try the partial
        // enumerator: enumerate the tightly-bounded subset × small guess
        // sets for unbounded vars, validate each candidate against the
        // ORIGINAL constraints. Sound SAT-finding only — UnsatComplete is
        // never returned from this path (unbounded search space is not
        // exhausted).
        static const bool partialEnabled = [] {
            return xolver::env::flag("XOLVER_NIA_BOUNDED_PARTIAL");
        }();
        if (partialEnabled) {
            // Phase L1 step 3 — LS feedback hint (XOLVER_NIA_LS_FEEDBACK=1,
    // default-OFF). The LS context's bestAssignment (when present) is
    // tried as the FIRST candidate before cartesian enumeration. Sound:
    // validator-gated like every other candidate.
    static const bool lsFeedback = [] {
        return xolver::env::flag("XOLVER_NIA_LS_FEEDBACK");
    }();
    const IntegerModel* hint = nullptr;
    if (lsFeedback) {
        const auto& ctx = localSearch_.lsContext();
        if (!ctx.bestAssignment.empty()) hint = &ctx.bestAssignment;
    }
    auto br = bounded_.solvePartialWithHint(normalized_, domains_, validator_, hint);
            if (br.status == BoundedSolveStatus::Sat) {
                currentModel_ = br.model;
                return TheoryCheckResult::consistent();
            }
            // Any other status (UnknownUnsupported / UnknownBudget) — fall
            // through to the next pipeline stage.
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBitBlastEarly(TheoryLemmaStorage&, TheoryEffort) {
    // DEFAULT-ON (2026-06-05): run the WHOLE-problem bit-blast early — while the
    // variable box is still free — instead of leaving it to the FULL-effort
    // nia.bit-blast which fires once the SAT search has PINNED the small bounded
    // vars to a specific (often wrong) branch. On a box-INCOMPLETE pinned branch
    // (unbounded beta/gamma, e.g. the GrandProduct prime-field grand product) the
    // late per-branch path cannot prove the branch UNSAT, so it escalates width
    // K=2→128 and allocates ~3.3 GB before the firewall — a real OOM bug, NOT a
    // resource wall (z3 solves the same case instantly). Searching the whole free
    // problem once keeps the encoding bounded (~0.6 GB) and lets the SAT solver
    // explore all branches together. This is an ALGORITHMIC fix (search strategy),
    // not a width/budget cap. The >=50 active-constraint gate below preserves the
    // small-case behavior (BB_EARLY's per-call cost regressed tiny UNSAT cases
    // before that gate). Opt-out: XOLVER_NIA_BB_EARLY=0.
    static const bool earlyEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_BB_EARLY");
        return !e || (*e && *e != '0');   // default ON; only "0" disables
    }();
    if (!earlyEnabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
    // Array-combination gate: when the problem contains array terms (Store/Select),
    // the array-read results are EUF-managed shared terms abstracted into the NIA
    // constraints as opaque vars. Bit-blasting those constraints is wasteful (it
    // was the ~1s/call hot stage on the array-combination GrandProduct, confirmed
    // via ARITH_STAGE_PROF) and can mislead (the bit-blast model ignores the EUF
    // array axioms). The combination + other reasoner stages own these. Opt-out
    // XOLVER_NIA_BB_ARRAY=1. (Verified: sum10 etc. still solve without bit-blast.)
    if (bbArrayGate_ < 0) {
        bbArrayGate_ = 0;
        if (coreIr_ && !std::getenv("XOLVER_NIA_BB_ARRAY")) {
            ExprId n = static_cast<ExprId>(coreIr_->size());
            for (ExprId e = 0; e < n; ++e) {
                Kind k = coreIr_->get(e).kind;
                if (k == Kind::Store || k == Kind::Select) { bbArrayGate_ = 1; break; }
            }
        }
    }
    if (bbArrayGate_ == 1) return std::nullopt;
    // H3 size-gate: BB_EARLY's per-call encoding+SAT cost is heavy
    // (~5-6s on SAT14-class with 600+ active polynomial constraints).
    // On small NIA cases (~1-10 active constraints) the upstream
    // reasoning stages decide the verdict for free, and BB_EARLY's
    // overhead pushes them past the per-case timeout. Local NIA reg
    // verified this: BB_EARLY ON regressed 3 small UNSAT cases (nia_025,
    // nia_056, nia_090) from unsat to unknown, and 3 to TIMEOUT.
    // Threshold: require >= 50 active normalized constraints, the
    // SAT14-pattern lower bound. Tunable via XOLVER_NIA_BB_EARLY_MIN_ACTIVE.
    static const size_t minActive = [] {
        if (const char* e = std::getenv("XOLVER_NIA_BB_EARLY_MIN_ACTIVE"))
            return static_cast<size_t>(std::atol(e));
        return static_cast<size_t>(50);
    }();
    if (normalized_.size() < minActive) return std::nullopt;
    static const bool h3Diag = xolver::env::diag("XOLVER_NIA_BB_ENTRY_DIAG");
    if (h3Diag) {
        static thread_local long earlyCount = 0;
        ++earlyCount;
        if ((earlyCount & 0xff) == 1 || earlyCount < 8) {
            std::fprintf(stderr,
                "[BB-EARLY] call=%ld active=%zu normalized=%zu\n",
                earlyCount, active_.size(), normalized_.size());
        }
    }
    // Dedup re-blasts of the same free problem (see bbEarlyUnkSize_). If the last
    // blast at this active-constraint size returned UNKNOWN, the free problem is
    // unchanged and a re-blast just burns seconds (00314 80x/11s; a UFDTNIA
    // 4x/14.6s) — skip it. Opt-out XOLVER_NIA_BB_EARLY_NODEDUP=1.
    static const bool bbEarlyDedup =
        !xolver::env::diag("XOLVER_NIA_BB_EARLY_NODEDUP");
    if (bbEarlyDedup && bbEarlyUnkSize_ == normalized_.size())
        return std::nullopt;
    // The bit-blast solver respects its own gate/iteration env caps
    // (XOLVER_NIA_BITBLAST_MAX_ITERS / MAX_BITWIDTH / GATE_BUDGET /
    // CONFLICTS). For early-stage operation users typically pair this
    // flag with tighter caps so Standard-effort cb_propagate overhead
    // stays bounded — same idiom as XOLVER_NIA_LS_EARLY_BUDGET_MS.
    auto res = bitBlast_.solve(normalized_, domains_, validator_);
    switch (res.status) {
        case bitblast::BitBlastResult::Status::Sat:
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        case bitblast::BitBlastResult::Status::UnsatComplete:
            return TheoryCheckResult::mkConflict(*res.conflict);
        case bitblast::BitBlastResult::Status::Unknown:
            if (bbEarlyDedup) bbEarlyUnkSize_ = normalized_.size();
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;  // diag/A-B: isolate non-bit-blast NIA reasoning
    // PER-BRANCH bit-blast is OFF for PURE QF_NIA (no shared-term registry ⇒
    // single-theory). This stage fires AFTER the SAT search has PINNED the bounded
    // vars to a specific (often wrong) branch and then bit-blasts that pinned
    // subproblem — on a box-incomplete branch it escalates width and OOMs, and does
    // not pay off on pure integer problems. The WHOLE-FORMULA eager bit-blast
    // (stageBitBlastEarly, run while the box is still free) stays ON — that is the
    // validated decider. In a COMBINATION logic (UFNIA/ANIA/AUFNIA/UFNRA/AUFDTNIA,
    // sharedTermRegistry_ set) the per-branch path is KEPT (combination already
    // branches; bit-blast is an acceptable backend there). Opt-in restore for pure
    // NIA: XOLVER_NIA_PER_BRANCH_BB=1.
    if (!sharedTermRegistry_ && !std::getenv("XOLVER_NIA_PER_BRANCH_BB"))
        return std::nullopt;
    // H3 (master 2026-06-01) entry counter: confirm whether bit-blast
    // actually fires on SAT14-class inputs before the run TOs upstream.
    static const bool h3Diag = xolver::env::diag("XOLVER_NIA_BB_ENTRY_DIAG");
    if (h3Diag) {
        static thread_local long bbEntryCount = 0;
        ++bbEntryCount;
        if ((bbEntryCount & 0xff) == 1 || bbEntryCount < 8) {
            std::fprintf(stderr,
                "[BB-ENTRY] call=%ld active=%zu normalized=%zu\n",
                bbEntryCount, active_.size(), normalized_.size());
        }
    }
    auto res = bitBlast_.solve(normalized_, domains_, validator_);
    switch (res.status) {
        case bitblast::BitBlastResult::Status::Sat:
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        case bitblast::BitBlastResult::Status::UnsatComplete:
            return TheoryCheckResult::mkConflict(*res.conflict);
        case bitblast::BitBlastResult::Status::Unknown:
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult>
NiaSolver::stageEscalatingBounded(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    (void)lemmaDb;
    static const bool enabled =
        env::paramInt("XOLVER_NIA_BOUNDED_ESCALATE", 1) != 0;
    if (!enabled) return std::nullopt;
    (void)effort;  // Full-effort-only is enforced by the addFull() registration.
    if (!coreIr_) return std::nullopt;  // need the original formula for AMV.
    if (normalized_.empty()) return std::nullopt;

    // Detect vars with a finite lower bound but no upper bound. These are
    // exactly the inputs BoundedNiaSolver can't enumerate today (it bails to
    // UnknownUnsupported in solve()). Be conservative: if there are vars with
    // no domain info OR unbounded below, skip — those are outside this
    // stage's sound lane.
    auto allVars = collectVars(normalized_, *kernel_);
    std::vector<std::string> vars(allVars.begin(), allVars.end());
    std::sort(vars.begin(), vars.end()); // determinism
    std::vector<std::pair<mpz_class, mpz_class>> ranges; // (lo, hi) per var
    ranges.reserve(vars.size());
    bool anyUnboundedAbove = false;
    for (const auto& v : vars) {
        const IntDomain* d = domains_.getDomain(v);
        if (!d) return std::nullopt;
        if (!d->hasLower) return std::nullopt;   // unbounded below — out of lane
        mpz_class lo = d->lower.value;
        if (d->hasUpper) {
            // already capped — keep the existing window
            ranges.push_back({lo, d->upper.value});
        } else {
            ranges.push_back({lo, lo});          // placeholder; widened per k
            anyUnboundedAbove = true;
        }
    }
    if (!anyUnboundedAbove) return std::nullopt; // nia.bounded covers this.
    (void)effort;

    // Cap on per-iteration enumeration size (autotunable knob, iter#5 hoist).
    // STRUCTURAL bound — no artificial k cap; the loop terminates when the
    // augmented box exceeds this threshold for any k.
    const long enumThreshold =
        env::paramLong("XOLVER_NIA_BOUNDED_ENUM_THRESHOLD", 10000);

    // Collect bool AND array vars referenced in the ORIGINAL formula.
    //   - Bool vars: BoolSubterm Purifier introduces `boolpur_K` fresh bool
    //     vars to name complex subexpressions; AMV cannot evaluate them
    //     without a BoolAssignment, so every candidate goes Indeterminate.
    //     We enumerate ALL polarity combos.
    //   - Array vars: QF_ANIA / QF_AUFNIA cases declare arrays (e.g.
    //     `(declare-fun start () (Array Int Int))`); AMV's Select / Store
    //     return Indeterminate when the base array var has no interp. We
    //     supply each Array var with a baseline ConstArray (default token
    //     "#n:0") so the store-chain accumulates correctly. SOUND: the
    //     baseline is a candidate guess — if the SAT witness needs different
    //     base values, AMV will reject this combo and we miss the witness,
    //     never claim a wrong SAT.
    std::set<std::string> boolVarSet;
    std::set<std::string> arrayVarSet;
    {
        std::vector<ExprId> wstack;
        std::unordered_set<ExprId> wseen;
        for (ExprId a : coreIr_->assertions()) wstack.push_back(a);
        const SortId boolSort = coreIr_->boolSortId();
        while (!wstack.empty()) {
            ExprId e = wstack.back(); wstack.pop_back();
            if (e == NullExpr || e >= coreIr_->size()) continue;
            if (!wseen.insert(e).second) continue;
            const auto& n = coreIr_->get(e);
            if (n.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                    if (n.sort == boolSort) {
                        boolVarSet.insert(*nm);
                    } else if (coreIr_->arraySortParams(n.sort)) {
                        arrayVarSet.insert(*nm);
                    }
                }
            }
            for (ExprId c : n.children) wstack.push_back(c);
        }
    }
    std::vector<std::string> boolVars(boolVarSet.begin(), boolVarSet.end());
    std::sort(boolVars.begin(), boolVars.end());
    const size_t nBoolVars = boolVars.size();
    // STRUCTURAL skip: 2^nBoolVars must fit in long enumeration. With
    // enumThreshold=10000 default, 2^13 = 8192 already eats most of it.
    // We don't add an artificial cap, but skip the bool-enum entirely if
    // 2^nBoolVars exceeds the threshold (sound — bool vars left Indeterminate
    // means more candidates get rejected, not fewer; we miss SAT, we don't
    // claim UNSAT).
    long boolCombo = 1;
    for (size_t i = 0; i < nBoolVars; ++i) {
        if (boolCombo > enumThreshold) { boolCombo = -1; break; }
        boolCombo *= 2;
    }
    if (boolCombo < 0) return std::nullopt;

    // AMV input scaffold reused across candidates (zero-alloc inner loop).
    ArithModelValidator::NumAssignment num;
    num.reserve(vars.size());
    ArithModelValidator::BoolAssignment bools;
    bools.reserve(nBoolVars);
    // Array baseline: each Array var gets a ConstArray with default token
    // "#n:0" (matches AMV's auto-token form for the rational 0; see
    // ArithModelValidator.cpp::asToken at line 80). Built ONCE before the
    // enumeration loop — same baseline for every (int × bool) combo, since
    // the formula's stores accumulate as overrides on top.
    ArithModelValidator::ArrayAssignment arrAsg;
    ArithModelValidator::TokenAssignment tokAsg;  // empty — Number→token auto-converts
    if (!arrayVarSet.empty()) {
        arrAsg.reserve(arrayVarSet.size());
        for (const auto& aname : arrayVarSet) {
            TheorySolver::TheoryModel::ArrayInterp interp;
            interp.defaultVal = "#n:0";
            // entries empty: no overrides on the baseline
            arrAsg.emplace(aname, std::move(interp));
        }
    }

    // Escalate width = 2^k - 1 on UNBOUNDED vars; keep bounded vars' ranges
    // intact. Compute totalSize first; if > threshold, stop escalating.
    for (int k = 1; ; ++k) {
        mpz_class widthMinus1 = (mpz_class(1) << k) - 1; // 2^k - 1

        // Build per-var (lo, hi) for THIS k, and compute totalSize.
        std::vector<std::pair<mpz_class, mpz_class>> kRanges = ranges;
        mpz_class totalSize = 1;
        bool overBudget = false;
        for (size_t i = 0; i < vars.size(); ++i) {
            const IntDomain* d = domains_.getDomain(vars[i]);
            if (d && !d->hasUpper) {
                kRanges[i] = {kRanges[i].first, kRanges[i].first + widthMinus1};
            }
            mpz_class span = kRanges[i].second - kRanges[i].first + 1;
            if (span <= 0) { overBudget = true; break; }
            totalSize *= span;
            if (totalSize > enumThreshold) { overBudget = true; break; }
        }
        if (overBudget) break;
        // Combined per-k cost: int product × 2^nBoolVars. Skip k if combined
        // is over threshold (sound — skipping cases that exhaust budget is
        // not a wrong-UNSAT, just an unrecovered SAT chance).
        if (nBoolVars > 0) {
            mpz_class combined = totalSize * boolCombo;
            if (combined > enumThreshold) break;
        }

        // Cartesian-product enumeration. For each int-candidate × bool-
        // candidate, validate via ArithModelValidator against the ORIGINAL
        // coreIr_ assertions — pattern mirrors stageLocalSearchBoolExtend
        // but extended to ENUMERATE bool var polarities (boolpur_K Tseitin
        // proxies introduced by the purifier). SOUND for SAT: a model that
        // satisfies the ORIGINAL boolean+arith formula is a sound SAT
        // witness regardless of the partial constraint subset in normalized_.
        const size_t N = vars.size();
        std::vector<mpz_class> cur(N);
        for (size_t i = 0; i < N; ++i) cur[i] = kRanges[i].first;
        while (true) {
            // Build NumAssignment from `cur`.
            num.clear();
            for (size_t i = 0; i < N; ++i) {
                num.emplace(vars[i], mpq_class(cur[i]));
            }
            // Iterate all 2^nBoolVars polarity combos. With nBoolVars=0 the
            // loop body runs exactly once with empty BoolAssignment.
            for (long bmask = 0; bmask < boolCombo; ++bmask) {
                bools.clear();
                for (size_t i = 0; i < nBoolVars; ++i) {
                    bools.emplace(boolVars[i], ((bmask >> i) & 1) != 0);
                }
                // Use the array-aware ctor when the formula has Array vars,
                // so AMV's Select / Store paths can evaluate.
                std::unique_ptr<ArithModelValidator> amvPtr;
                if (!arrayVarSet.empty()) {
                    amvPtr = std::make_unique<ArithModelValidator>(
                        *coreIr_, num, bools, arrAsg, tokAsg);
                } else {
                    amvPtr = std::make_unique<ArithModelValidator>(
                        *coreIr_, num, bools);
                }
                if (amvPtr->validate(coreIr_->assertions()) ==
                    ArithModelValidator::Verdict::Satisfied) {
                    // Materialize as NIA's currentModel_ — IntegerModel is
                    // a map<string, mpz_class>, same shape as `cur`. Bool
                    // proxies stay implicit in the model — the solver caller
                    // (Solver::Impl) re-validates the full model via the
                    // boundary validator with the SAT-layer's own bool
                    // assignments, so the eventual SAT verdict is
                    // double-checked.
                    IntegerModel model;
                    for (size_t i = 0; i < N; ++i) model[vars[i]] = cur[i];
                    currentModel_ = std::move(model);
                    return TheoryCheckResult::consistent();
                }
            }
            // Increment cur in odometer order.
            size_t j = 0;
            while (j < N) {
                ++cur[j];
                if (cur[j] <= kRanges[j].second) break;
                cur[j] = kRanges[j].first;
                ++j;
            }
            if (j == N) break; // exhausted
        }
        // No SAT in this k's box; escalate (any unbounded var grows).
    }
    return std::nullopt;
}

// LBBB Phase 2 — stageBoundedBitBlast. After LS has failed (per
// localSearch_.hasFailed()), bit-blast over the box LS visited,
// extended by a buffer. Validate any Sat against the ORIGINAL NIA
// constraints; UNSAT verdict from BB is treated as Unknown (only
// the BOX is searched, not the full integer space). Default-OFF
// (XOLVER_NIA_LBBB), Full-effort only via addFull registration.
std::optional<TheoryCheckResult> NiaSolver::stageBoundedBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NIA_LBBB");
    }();
    if (!enabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;
    // Gate: LS must have run AND failed. Otherwise BB would just be
    // a redundant copy of stageBitBlast — we want LBBB to fire only
    // on the box LS converged toward.
    if (!localSearch_.hasFailed()) return std::nullopt;
    const auto& mins = localSearch_.trackedMin();
    const auto& maxs = localSearch_.trackedMax();
    if (mins.empty() || maxs.empty()) return std::nullopt;

    // Build a fresh DomainStore restricted to the LS-visited box +
    // buffer. For each tracked var v: [min - buffer, max + buffer]
    // where buffer = max(10, range * 0.1).
    DomainStore subset = domains_;  // deep-copy
    SatLit dummyReason = SatLit::positive(0);
    for (const auto& [v, lo] : mins) {
        auto mit = maxs.find(v);
        if (mit == maxs.end()) continue;
        const mpz_class& hi = mit->second;
        mpz_class range = hi - lo;
        mpz_class buffer = range / 10;
        if (buffer < 10) buffer = 10;
        mpz_class bbLo = lo - buffer;
        mpz_class bbHi = hi + buffer;
        // Intersect with any existing DomainStore bounds.
        subset.addLowerBound(v, bbLo, dummyReason);
        subset.addUpperBound(v, bbHi, dummyReason);
    }
    // Run BitBlast on the restricted box.
    auto res = bitBlast_.solve(normalized_, subset, validator_);
    if (res.status == bitblast::BitBlastResult::Status::Sat) {
        // Validate against ORIGINAL constraints (not the box-bounded
        // subset). LBBB soundness gate: the box restriction was
        // heuristic, so a BB-SAT model must satisfy the unrestricted
        // formula to count.
        if (validator_.validate(res.model, normalized_) ==
            IntegerModelValidator::Result::Valid) {
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        }
        // BB found a model in the bounded box, but it doesn't satisfy
        // the original — drop and fall through.
        return std::nullopt;
    }
    // BB returned UNSAT (within the bounded box) or Unknown — both
    // are inconclusive for LBBB. Box might be too small; main pipeline
    // can decide. Never claim UNSAT here.
    return std::nullopt;
}

} // namespace xolver
