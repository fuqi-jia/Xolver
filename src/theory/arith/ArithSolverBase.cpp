#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/Reasoner.h"
#include "expr/ir.h"
#include "theory/combination/SharedTermRegistry.h"
#include <cassert>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <variant>

namespace xolver {

ArithSolverBase::ArithSolverBase() = default;
ArithSolverBase::~ArithSolverBase() = default;

std::string ArithSolverBase::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = coreIr_->get(st->coreExpr);
    std::string name;
    if (expr.kind == Kind::Variable) {
        if (std::holds_alternative<std::string>(expr.payload.value)) {
            name = std::get<std::string>(expr.payload.value);
        }
    } else if (expr.isConst()) {
        // Constants participate in LIA's interface-equality channel via a
        // synthetic "__const_<sharedName>" var; the LIA simplex pins it to
        // the actual constant value via a bound assertion. Solvers whose
        // DomainStore-equivalent has no entry for such tags (e.g. NIA)
        // naturally skip them in their getDeducedSharedEqualities loop --
        // fine, since EUF merges identical constants by signature without
        // needing an arith propagation.
        name = "__const_" + st->name;
    }
    if (!name.empty()) {
        sharedTermToVarName_[s] = name;
    }
    return name;
}

TheoryCheckResult ArithSolverBase::check(TheoryLemmaStorage& lemmaDb,
                                         TheoryEffort effort) {
    return runReasonerPipeline(lemmaDb, effort);
}

std::vector<std::string> ArithSolverBase::reasonerNames() const {
    std::vector<std::string> names;
    names.reserve(reasoners_.size());
    for (const auto& r : reasoners_) names.push_back(r->name());
    return names;
}

TheoryCheckResult ArithSolverBase::runReasonerPipeline(TheoryLemmaStorage& lemmaDb,
                                                       TheoryEffort effort) {
    if (hasPending()) return drainPending();
    // Per-stage cumulative profiler (ARITH_STAGE_PROF). Dumps periodically to
    // stderr so a timeout-killed run still reveals the per-propagation hot
    // stage (no clean exit / atexit). Zero cost when the env var is unset.
    static const bool stageProf = std::getenv("ARITH_STAGE_PROF") != nullptr;
    struct ProfState {
        std::map<std::string, std::pair<double, long>> acc;  // name -> (ms, calls)
        long pipelineCalls = 0;
        std::chrono::steady_clock::time_point lastDump = std::chrono::steady_clock::now();
        void dump() {
            std::cerr << "[STAGE-PROF] pipeline-calls=" << pipelineCalls << "\n";
            for (const auto& [nm, mc] : acc)
                std::cerr << "  " << nm << "  ms=" << (long)mc.first
                          << " calls=" << mc.second << "\n";
            std::cerr.flush();  // survive SIGKILL on a piped-to-file stderr
        }
    };
    static ProfState prof;
    if (stageProf) {
        ++prof.pipelineCalls;
        auto now = std::chrono::steady_clock::now();
        if (std::chrono::duration_cast<std::chrono::milliseconds>(now - prof.lastDump).count() >= 2000) {
            prof.dump();
            prof.lastDump = now;
        }
    }
    // ARITH_STAGE_ENTER (default-OFF): print every stage-entry to stderr,
    // flushed, so a single-stage hang is pinpoint-visible under timeout-kill.
    // Diagnostic only; identical behavior when env unset.
    static const bool stageEnter = std::getenv("ARITH_STAGE_ENTER") != nullptr;
    for (auto& r : reasoners_) {
        if (!r->runsAt(effort)) continue;
        if (stageEnter) {
            std::cerr << "[STAGE-ENTER] " << r->name() << " effort="
                      << (effort == TheoryEffort::Full ? "F" : "S") << "\n";
            std::cerr.flush();
        }
#ifndef NDEBUG
        size_t trailBefore = state_.trail.size();
#endif
        auto profT0 = stageProf ? std::chrono::steady_clock::now()
                                : std::chrono::steady_clock::time_point{};
        auto res = r->run(lemmaDb, effort);
        if (stageProf) {
            auto& mc = prof.acc[r->name()];
            mc.first += std::chrono::duration<double, std::milli>(
                            std::chrono::steady_clock::now() - profT0).count();
            ++mc.second;
        }
        // Reasoners must not mutate the shared trail; only assertLit does.
        assert(state_.trail.size() == trailBefore && "Reasoner mutated trail");
        // nullopt = continue to next stage; a value = stop with that verdict
        // (Consistent here means "theory state is consistent, stop", NOT
        // "continue").
        if (res.has_value()) {
            static const bool stageDiag = std::getenv("ARITH_STAGE_DIAG") != nullptr;
            if (stageDiag && res->kind == TheoryCheckResult::Kind::Conflict) {
                std::cerr << "[STAGE-CONFLICT] stage=" << r->name()
                          << " size=" << (res->conflictOpt ? res->conflictOpt->clause.size() : 0)
                          << " lits=";
                if (res->conflictOpt) {
                    for (const auto& l : res->conflictOpt->clause)
                        std::cerr << (l.sign ? "" : "-") << l.var << " ";
                }
                std::cerr << "\n";
            }
            return std::move(*res);
        }
    }
    return TheoryCheckResult::consistent();
}

void ArithSolverBase::push() {
    ++state_.scopeLevel;
    onPush();
}

void ArithSolverBase::pop(uint32_t n) {
    if (state_.scopeLevel >= n) state_.scopeLevel -= n;
    else state_.scopeLevel = 0;
    onPop(n);
}

void ArithSolverBase::assertLit(const TheoryAtomRecord& atom, bool value,
                                int level, SatLit assertedLit) {
    // Dedup by satVar: replace an existing assignment for the same SAT
    // variable in place, else append. This reproduces the pre-refactor
    // assertLit body shared by IDL/RDL/NIA/NIRA/LIRA verbatim.
    for (auto& a : state_.trail) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            if (level > state_.currentLevel) state_.currentLevel = level;
            onAssertLit(atom, value, level, assertedLit);
            return;
        }
    }
    state_.trail.push_back({level, assertedLit, atom, value});
    if (level > state_.currentLevel) state_.currentLevel = level;
    onAssertLit(atom, value, level, assertedLit);
}

void ArithSolverBase::backtrackToLevel(int level) {
    auto it = std::remove_if(state_.trail.begin(), state_.trail.end(),
        [level](const ActiveAssignment& a) { return a.level > level; });
    state_.trail.erase(it, state_.trail.end());

    if (state_.pending && state_.pending->level > level) {
        state_.pending.reset();
    }
    state_.currentLevel = level;
    onBacktrack(level);
}

void ArithSolverBase::reset() {
    state_.trail.clear();
    state_.pending.reset();
    state_.currentLevel = 0;
    state_.scopeLevel = 0;
    onReset();
}

} // namespace xolver
