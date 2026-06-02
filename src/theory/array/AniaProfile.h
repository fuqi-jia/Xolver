#pragma once
// ---------------------------------------------------------------------------
// AniaProfile — diagnostic-only, in-lane (array-deep) per-phase wall-clock
// profiler for the QF_ANIA / QF_AUFNIA combination path. Gated by the env var
// XOLVER_ANIA_PROF (off → every hook is a no-op, zero overhead on the hot path
// beyond one relaxed atomic load). NEVER affects a verdict.
//
// Goal (Phase B2-alt): split the QF_ANIA solve wall-clock into
//   - EufSolver::check time (array reasoning + EUF saturation = array-deep lane)
//   - ArrayReasoner sub-phases (eager merges / store-select completion / lemmas)
//   - everything else (NIA + LIA + SAT + combination), inferred as total − euf.
// so we can tell whether the wall is in the array lane or downstream in NIA.
//
// Output survives an external `timeout` SIGTERM: a SIGALRM armed on init fires
// a few seconds before any sane external cap, dumps the accumulators, and
// _exit()s. A normal completion also dumps via atexit.
// ---------------------------------------------------------------------------
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <csignal>
#include <unistd.h>

namespace xolver {
namespace aniaprof {

enum Bucket {
    EUF_CHECK = 0,     // total time inside EufSolver::check
    ARR_EAGER,         // ArrayReasoner::enqueueEagerMerges
    ARR_COMPLETE,      // ArrayReasoner::completeStoreSelects
    ARR_LEMMA,         // ArrayReasoner::instantiateLemma
    EUF_SATURATE,      // EufSolver saturation drain loop
    NUM_BUCKETS
};

struct State {
    std::atomic<bool> enabled{false};
    std::atomic<long long> ns[NUM_BUCKETS];      // time of COMPLETED scopes
    std::atomic<long long> calls[NUM_BUCKETS];
    // In-progress accounting: openStart[b] != 0 means a scope for bucket b is
    // currently on the stack (it began at that steady_clock ns). Lets dump()
    // include the elapsed time of a scope still open when SIGALRM fires mid-run
    // (e.g. a single EufSolver::check that has not returned yet) — otherwise the
    // outer scope contributes 0 and the inferred non-EUF split is bogus.
    std::atomic<long long> openStartNs[NUM_BUCKETS];
    std::atomic<int> depth[NUM_BUCKETS];
    std::chrono::steady_clock::time_point start;
    std::atomic<bool> dumped{false};
};

inline long long nowNs() {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch()).count();
}

inline State& state() { static State s; return s; }

// Hot-path gate: a plain inline global (one definition, C++17) read with zero
// synchronisation or magic-static guard cost. Set true only by init() when
// XOLVER_ANIA_PROF is on, BEFORE the solve worker starts — so the off path
// (every Scope ctor on the EUF hot loop) is a single predictable branch.
inline bool g_on = false;

inline const char* bucketName(int b) {
    switch (b) {
        case EUF_CHECK:    return "euf_check(array+euf)";
        case ARR_EAGER:    return "  arr_eager_merges";
        case ARR_COMPLETE: return "  arr_store_select_complete";
        case ARR_LEMMA:    return "  arr_instantiate_lemma";
        case EUF_SATURATE: return "  euf_saturation_drain";
        default:           return "?";
    }
}

inline void dump() {
    State& s = state();
    bool expected = false;
    if (!s.dumped.compare_exchange_strong(expected, true)) return;
    auto now = std::chrono::steady_clock::now();
    double total = std::chrono::duration<double>(now - s.start).count();
    long long nowN = nowNs();
    // Effective bucket ns = completed time + any in-progress scope's elapsed.
    auto eff = [&](int b) -> double {
        long long v = s.ns[b].load();
        long long os = s.openStartNs[b].load();
        if (os != 0 && nowN > os) v += (nowN - os);
        return v / 1e9;
    };
    std::fprintf(stderr, "\n[ANIA-PROF] total wall = %.2fs\n", total);
    double eufS = eff(EUF_CHECK);
    std::fprintf(stderr, "[ANIA-PROF] %-30s %8.2fs  %5.1f%%  (calls=%lld)\n",
                 bucketName(EUF_CHECK), eufS,
                 total > 0 ? 100.0 * eufS / total : 0.0, s.calls[EUF_CHECK].load());
    for (int b = ARR_EAGER; b < NUM_BUCKETS; ++b) {
        double bs = eff(b);
        std::fprintf(stderr, "[ANIA-PROF] %-30s %8.2fs  %5.1f%%  (calls=%lld)\n",
                     bucketName(b), bs, total > 0 ? 100.0 * bs / total : 0.0,
                     s.calls[b].load());
    }
    double rest = total - eufS;
    if (rest < 0) rest = 0;
    std::fprintf(stderr, "[ANIA-PROF] %-30s %8.2fs  %5.1f%%   <= NIA+LIA+SAT+comb\n",
                 "INFERRED non-EUF", rest, total > 0 ? 100.0 * rest / total : 0.0);
    std::fflush(stderr);
}

inline void onAlarm(int) { dump(); _exit(0); }

inline void init() {
    State& s = state();
    if (s.enabled.load(std::memory_order_relaxed)) return;
    const char* e = std::getenv("XOLVER_ANIA_PROF");
    if (!e || !*e || *e == '0') return;
    for (int b = 0; b < NUM_BUCKETS; ++b) {
        s.ns[b] = 0; s.calls[b] = 0; s.openStartNs[b] = 0; s.depth[b] = 0;
    }
    s.start = std::chrono::steady_clock::now();
    s.enabled.store(true, std::memory_order_relaxed);
    g_on = true;
    std::atexit([]() { dump(); });
    std::signal(SIGALRM, onAlarm);
    // Dump at N seconds, ahead of any external timeout. Override with the value
    // of XOLVER_ANIA_PROF if it is a positive integer (seconds).
    int secs = std::atoi(e);
    if (secs <= 0) secs = 25;
    alarm(static_cast<unsigned>(secs));
}

inline bool on() { return g_on; }

// RAII scope timer. Cheap no-op when profiling is off.
struct Scope {
    int bucket;
    std::chrono::steady_clock::time_point t0;
    bool active;
    explicit Scope(int b) : bucket(b), active(on()) {
        if (!active) return;
        t0 = std::chrono::steady_clock::now();
        State& s = state();
        // Record the outermost open scope start for this bucket (depth 0 -> 1).
        if (s.depth[bucket].fetch_add(1, std::memory_order_relaxed) == 0)
            s.openStartNs[bucket].store(nowNs(), std::memory_order_relaxed);
    }
    ~Scope() {
        if (!active) return;
        auto dt = std::chrono::steady_clock::now() - t0;
        State& s = state();
        s.ns[bucket].fetch_add(
            std::chrono::duration_cast<std::chrono::nanoseconds>(dt).count(),
            std::memory_order_relaxed);
        s.calls[bucket].fetch_add(1, std::memory_order_relaxed);
        if (s.depth[bucket].fetch_sub(1, std::memory_order_relaxed) == 1)
            s.openStartNs[bucket].store(0, std::memory_order_relaxed);
    }
};

}  // namespace aniaprof
}  // namespace xolver
