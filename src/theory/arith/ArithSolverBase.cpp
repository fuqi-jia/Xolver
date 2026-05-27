#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/Reasoner.h"
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <chrono>
#include <csignal>
#include <map>
#include <string>
#include <unistd.h>
#include <cstring>

namespace zolver {

// ---------------------------------------------------------------------------
// Per-stage wall-time + invocation-count profiler (default-OFF, env
// ARITH_STAGE_PROFILE). Distinguishes a single pathological stage call (one
// huge total, count small, "currently-in" reports the hung stage) from an
// incrementality gap (a stage called thousands of times at moderate cost).
// Dumps on SIGTERM so a spinning solve killed by `timeout -s TERM` still
// reports. Zero cost when disabled.
// ---------------------------------------------------------------------------
namespace {
struct StageProf { double secs = 0; unsigned long long count = 0; };
std::map<std::string, StageProf>& profMap() {
    static std::map<std::string, StageProf> m; return m;
}
std::string g_curStage;
std::chrono::steady_clock::time_point g_curStart;
std::chrono::steady_clock::time_point g_progStart;
bool g_progStarted = false;
unsigned long long g_pipelineCalls = 0;
void dumpProf() {
    using namespace std::chrono;
    double inCur = duration<double>(steady_clock::now() - g_curStart).count();
    std::cerr << "[STAGE-PROFILE] pipeline_calls=" << g_pipelineCalls
              << " currently-in=" << g_curStage << " for=" << inCur << "s\n";
    for (const auto& kv : profMap()) {
        double avgMs = kv.second.count ? kv.second.secs / kv.second.count * 1000.0 : 0.0;
        std::cerr << "[STAGE-PROFILE] " << kv.first
                  << " calls=" << kv.second.count
                  << " total_s=" << kv.second.secs
                  << " avg_ms=" << avgMs << "\n";
    }
    std::cerr.flush();
}
volatile std::sig_atomic_t g_dumpReq = 0;
// Async-signal-safe dump (raw write). Safe to iterate profMap from the handler
// because inserts happen between stage calls; when SIGALRM fires the solver is
// inside one stage call, so the map is stable.
void wstr(const char* s) { ssize_t r = ::write(2, s, std::strlen(s)); (void)r; }
void wull(unsigned long long v) {
    char b[24]; int i = 23; b[i] = '\0';
    if (v == 0) b[--i] = '0';
    while (v) { b[--i] = static_cast<char>('0' + v % 10); v /= 10; }
    wstr(b + i);
}
void onSig(int) {
    wstr("\n[STAGE-PROFILE] pipeline_calls="); wull(g_pipelineCalls);
    wstr(" currently-in="); wstr(g_curStage.c_str()); wstr("\n");
    for (const auto& kv : profMap()) {
        wstr("[STAGE-PROFILE] "); wstr(kv.first.c_str());
        wstr(" calls="); wull(kv.second.count);
        wstr(" total_ms="); wull(static_cast<unsigned long long>(kv.second.secs * 1000.0));
        wstr("\n");
    }
    std::_Exit(0);
}
bool profEnabled() {
    static bool e = [] {
        bool on = std::getenv("ARITH_STAGE_PROFILE") != nullptr;
        if (on) {
            // SIGALRM fires even while stuck inside one stage call (CaDiCaL does
            // not grab it, unlike SIGTERM). Budget seconds env-tunable.
            std::signal(SIGALRM, onSig);
            std::signal(SIGTERM, onSig);
            unsigned secs = 15;
            if (const char* b = std::getenv("ARITH_STAGE_PROFILE_SECS")) {
                unsigned v = static_cast<unsigned>(std::atoi(b));
                if (v > 0) secs = v;
            }
            alarm(secs);
            std::atexit(dumpProf);
        }
        return on;
    }();
    return e;
}
} // namespace

ArithSolverBase::ArithSolverBase() = default;
ArithSolverBase::~ArithSolverBase() = default;

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
    const bool prof = profEnabled();
    if (prof) {
        ++g_pipelineCalls;
        if (!g_progStarted) { g_progStarted = true; g_progStart = std::chrono::steady_clock::now(); }
        if (g_dumpReq) {         // SIGALRM requested a dump; do it in normal context
            dumpProf();
            std::_Exit(0);
        }
    }
    for (auto& r : reasoners_) {
        if (!r->runsAt(effort)) continue;
#ifndef NDEBUG
        size_t trailBefore = state_.trail.size();
#endif
        std::chrono::steady_clock::time_point t0;
        if (prof) { g_curStage = r->name(); g_curStart = std::chrono::steady_clock::now(); t0 = g_curStart; }
        auto res = r->run(lemmaDb, effort);
        if (prof) {
            auto& p = profMap()[r->name()];
            p.secs += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            ++p.count;
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

} // namespace zolver
