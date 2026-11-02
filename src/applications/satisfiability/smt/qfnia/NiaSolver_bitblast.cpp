#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "applications/satisfiability/smt/qfnia/NiaSolverDetail.h"
#include "base/RuntimeConfig.h"
#include "evidence/ArithModelValidator.h"
#include "ir/NativeTerms.h"
#include <algorithm>
#include <cstdio>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>
#include <gmpxx.h>

namespace xolver {

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
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBitBlastEarly(TheoryLemmaStorage&, TheoryEffort) {
    // Run on a complete Boolean candidate, before later integer search stages.
    // Applicability, resource limits and result validation remain below.
    // Array terms belong to the combined EUF/array problem; this bit-blast
    // stage only handles integer constraints without array obligations.
    if (bbArrayGate_ < 0) {
        bbArrayGate_ = 0;
        if (nativeTerms_) {
            ExprId n = static_cast<ExprId>(nativeTerms_->size());
            for (ExprId e = 0; e < n; ++e) {
                Kind k = nativeTerms_->get(e).kind;
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
    const size_t minActive = static_cast<size_t>(std::max(0L,
        xolver::config::read<xolver::config::ReadKind::Long>("XOLVER_NIA_BB_EARLY_MIN_ACTIVE", 50)));
    if (normalized_.size() < minActive) return std::nullopt;
    const bool h3Diag = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_BB_ENTRY_DIAG");
    if (h3Diag) {
        static thread_local long earlyCount = 0;
        ++earlyCount;
        if ((earlyCount & 0xff) == 1 || earlyCount < 8) {
            std::fprintf(stderr,
                "[BB-EARLY] call=%ld active=%zu normalized=%zu\n",
                earlyCount, active_.size(), normalized_.size());
        }
    }
    // The backend reuses definitive answers only for an identical complete
    // query. Retrying Unknown must remain possible after backtracking or a
    // resource-budget change; equal constraint counts do not identify a query.
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

std::optional<TheoryCheckResult> NiaSolver::stageBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    // This late stage handles shared-term arrangements in theory combinations.
    // Pure NIA uses the earlier bit-blast stage and bounded-domain solver;
    // repeating bit-blast after integer branching needlessly expands boxes.
    if (!sharedTermRegistry_) return std::nullopt;
    // H3 (master 2026-06-01) entry counter: confirm whether bit-blast
    // actually fires on SAT14-class inputs before the run TOs upstream.
    const bool h3Diag = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_BB_ENTRY_DIAG");
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
NiaSolver::stageEscalatingBounded(TheoryLemmaStorage&, TheoryEffort) {
    if (!nativeTerms_) return std::nullopt;  // need the original formula for AMV.
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

    // Cap on per-iteration enumeration size (autotunable knob, iter#5 hoist).
    // STRUCTURAL bound — no artificial k cap; the loop terminates when the
    // augmented box exceeds this threshold for any k.
    const long enumThreshold =
        config::read<config::ReadKind::Long>("XOLVER_NIA_BOUNDED_ENUM_THRESHOLD", 10000);

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
        for (ExprId a : nativeTerms_->assertions()) wstack.push_back(a);
        const SortId boolSort = nativeTerms_->boolSortId();
        while (!wstack.empty()) {
            ExprId e = wstack.back(); wstack.pop_back();
            if (e == NullExpr || e >= nativeTerms_->size()) continue;
            if (!wseen.insert(e).second) continue;
            const auto& n = nativeTerms_->get(e);
            if (n.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                    if (n.sort == boolSort) {
                        boolVarSet.insert(*nm);
                    } else if (nativeTerms_->arraySortParams(n.sort)) {
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
    // Count Boolean assignments within the enumeration budget. Check before
    // multiplying so even a LONG_MAX budget cannot overflow the loop bound.
    // Budget exhaustion leaves this candidate search inconclusive.
    long boolCombo = 1;
    for (size_t i = 0; i < nBoolVars; ++i) {
        if (boolCombo > enumThreshold / 2) return std::nullopt;
        boolCombo *= 2;
    }

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
        // nativeTerms_ assertions, including every Boolean polarity combination.
        // This assigns the boolpur_K Tseitin proxies introduced by the purifier.
        // SOUND for SAT: a model that
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
                        *nativeTerms_, num, bools, arrAsg, tokAsg);
                } else {
                    amvPtr = std::make_unique<ArithModelValidator>(
                        *nativeTerms_, num, bools);
                }
                if (amvPtr->validate(nativeTerms_->assertions()) ==
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

} // namespace xolver
