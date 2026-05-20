#pragma once

#include <nlohmann/json.hpp>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace nlcolver {

/**
 * CaseStats: unified per-case solver statistics.
 *
 * Collected during a single checkSat() call and dumped to JSON
 * for benchmark analysis and regression tracking.
 *
 * Schema version incremented on breaking field changes.
 * activeTheories / enabledStats tell the analyzer which counters
 * were actually collected vs. zero-because-not-enabled.
 */
struct CaseStats {
    static constexpr int SCHEMA_VERSION = 1;

    // --- General result ---
    std::string result;              // "sat" | "unsat" | "unknown" | "timeout" | "error"
    double timeMs = 0.0;
    std::string failureStage;        // "frontend" | "atomizer" | "sat" | "theory" | "postcheck" | "runner"
    std::string unknownCode;         // standardised code, e.g. "FRONTEND_UNSUPPORTED_OPERATOR"
    std::string unknownComponent;    // module name, e.g. "IntDivModLowerer"
    std::string unknownDetail;       // human-readable description
    std::vector<std::string> activeTheories;
    std::vector<std::string> enabledStats;

    // --- Frontend / Atomizer ---
    struct Frontend {
        int64_t numExpr = 0;
        int64_t numAtoms = 0;
        int64_t numBoolAtoms = 0;
        int64_t numArithAtoms = 0;
        int64_t numEufAtoms = 0;
        int64_t numUnsupported = 0;
        std::map<std::string, int64_t> unsupportedHistogram;
    } frontend;

    // --- SAT layer ---
    struct Sat {
        int64_t vars = 0;
        int64_t clauses = 0;
        int64_t conflicts = 0;
        int64_t decisions = 0;
        int64_t propagations = 0;
    } sat;

    // --- TheoryManager ---
    struct Theory {
        int64_t checkCalls = 0;
        int64_t conflicts = 0;
        int64_t lemmas = 0;
        int64_t propagations = 0;
        double avgConflictSize = 0.0;
        int64_t maxConflictSize = 0;
    } theory;

    // --- LRA ---
    struct Lra {
        int64_t simplexPivots = 0;
        int64_t boundUpdates = 0;
        int64_t propagationLemmas = 0;
        int64_t cutLemmas = 0;
    } lra;

    // --- LIA ---
    struct Lia {
        int64_t branchCount = 0;
        int64_t gcdTightening = 0;
        int64_t diseqSplits = 0;
    } lia;

    // --- EUF ---
    struct Euf {
        int64_t terms = 0;
        int64_t merges = 0;
        int64_t disequalities = 0;
        int64_t internFailures = 0;
        int64_t maxExplanationSize = 0;
    } euf;

    // --- NIA ---
    struct Nia {
        int64_t linearizationTerms = 0;
        int64_t linearizationLemmas = 0;
        int64_t divmodLowerings = 0;
        int64_t boundedSearchCalls = 0;
    } nia;

    // --- NRA ---
    struct Nra {
        int64_t numPolynomials = 0;
        int64_t projectionPolynomials = 0;
        int64_t rootIsolationCalls = 0;
        int64_t coveringCells = 0;
    } nra;

    // --- SearchStats (filled from TheorySearchStats) ---
    struct SearchStats {
        int64_t modelCheckCalls = 0;
        int64_t modelCheckConflicts = 0;
        int64_t modelCheckLemmas = 0;
        int64_t modelCheckUnknowns = 0;
        int64_t conflictMinSize = -1;
        int64_t conflictMaxSize = 0;
        double conflictAvgSize = 0.0;
        int64_t propagateCalls = 0;
        int64_t propagateTheoryChecks = 0;
        int64_t propagateConflicts = 0;
        int64_t propagateLemmas = 0;
    } search;

    // --- Runtime stage heartbeat ---
    struct StageInfo {
        std::string currentStage;      // e.g. "frontend", "sat", "theory"
        std::string currentComponent;  // e.g. "LraSolver"
        std::string currentOperation;  // e.g. "conflict_explanation"
    } stage;

    nlohmann::json toJson() const;
    static CaseStats fromJson(const nlohmann::json& j);

    // Atomic write to disk (tmp + rename)
    void dumpToFile(const std::string& path) const;
};

/**
 * HeartbeatWriter: periodically flushes lightweight stage snapshot.
 * Used by the runner to reconstruct stats for timeout'd cases.
 */
class HeartbeatWriter {
public:
    void maybeWrite(const CaseStats& stats, const std::string& basePath);
private:
    int64_t lastWriteMs_ = 0;
};

} // namespace nlcolver
