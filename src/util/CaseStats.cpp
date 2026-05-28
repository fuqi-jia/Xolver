#include "util/CaseStats.h"
#include <fstream>
#include <chrono>

namespace xolver {

// ---------------------------------------------------------------------------
// CaseStats JSON serialization
// ---------------------------------------------------------------------------

nlohmann::json CaseStats::toJson() const {
    nlohmann::json j;
    j["schema_version"] = SCHEMA_VERSION;
    j["result"] = result;
    j["time_ms"] = timeMs;
    j["failure_stage"] = failureStage;
    j["unknown_code"] = unknownCode;
    j["unknown_component"] = unknownComponent;
    j["unknown_detail"] = unknownDetail;
    j["active_theories"] = activeTheories;
    j["enabled_stats"] = enabledStats;

    j["frontend"]["num_expr"] = frontend.numExpr;
    j["frontend"]["num_atoms"] = frontend.numAtoms;
    j["frontend"]["num_bool_atoms"] = frontend.numBoolAtoms;
    j["frontend"]["num_arith_atoms"] = frontend.numArithAtoms;
    j["frontend"]["num_euf_atoms"] = frontend.numEufAtoms;
    j["frontend"]["num_unsupported"] = frontend.numUnsupported;
    j["frontend"]["unsupported_histogram"] = frontend.unsupportedHistogram;

    j["sat"]["vars"] = sat.vars;
    j["sat"]["clauses"] = sat.clauses;
    j["sat"]["conflicts"] = sat.conflicts;
    j["sat"]["decisions"] = sat.decisions;
    j["sat"]["propagations"] = sat.propagations;

    j["theory"]["check_calls"] = theory.checkCalls;
    j["theory"]["conflicts"] = theory.conflicts;
    j["theory"]["lemmas"] = theory.lemmas;
    j["theory"]["propagations"] = theory.propagations;
    j["theory"]["avg_conflict_size"] = theory.avgConflictSize;
    j["theory"]["max_conflict_size"] = theory.maxConflictSize;

    j["lra"]["simplex_pivots"] = lra.simplexPivots;
    j["lra"]["bound_updates"] = lra.boundUpdates;
    j["lra"]["propagation_lemmas"] = lra.propagationLemmas;
    j["lra"]["cut_lemmas"] = lra.cutLemmas;

    j["lia"]["branch_count"] = lia.branchCount;
    j["lia"]["gcd_tightening"] = lia.gcdTightening;
    j["lia"]["diseq_splits"] = lia.diseqSplits;

    j["euf"]["terms"] = euf.terms;
    j["euf"]["merges"] = euf.merges;
    j["euf"]["disequalities"] = euf.disequalities;
    j["euf"]["intern_failures"] = euf.internFailures;
    j["euf"]["max_explanation_size"] = euf.maxExplanationSize;

    j["nia"]["linearization_terms"] = nia.linearizationTerms;
    j["nia"]["linearization_lemmas"] = nia.linearizationLemmas;
    j["nia"]["divmod_lowerings"] = nia.divmodLowerings;
    j["nia"]["bounded_search_calls"] = nia.boundedSearchCalls;

    j["nra"]["num_polynomials"] = nra.numPolynomials;
    j["nra"]["projection_polynomials"] = nra.projectionPolynomials;
    j["nra"]["root_isolation_calls"] = nra.rootIsolationCalls;
    j["nra"]["covering_cells"] = nra.coveringCells;

    j["search"]["model_check_calls"] = search.modelCheckCalls;
    j["search"]["model_check_conflicts"] = search.modelCheckConflicts;
    j["search"]["model_check_lemmas"] = search.modelCheckLemmas;
    j["search"]["model_check_unknowns"] = search.modelCheckUnknowns;
    j["search"]["conflict_min_size"] = search.conflictMinSize;
    j["search"]["conflict_max_size"] = search.conflictMaxSize;
    j["search"]["conflict_avg_size"] = search.conflictAvgSize;
    j["search"]["propagate_calls"] = search.propagateCalls;
    j["search"]["propagate_theory_checks"] = search.propagateTheoryChecks;
    j["search"]["propagate_conflicts"] = search.propagateConflicts;
    j["search"]["propagate_lemmas"] = search.propagateLemmas;

    j["stage"]["current_stage"] = stage.currentStage;
    j["stage"]["current_component"] = stage.currentComponent;
    j["stage"]["current_operation"] = stage.currentOperation;

    return j;
}

CaseStats CaseStats::fromJson(const nlohmann::json& j) {
    CaseStats cs;
    // Minimal deserialization for analyzer use
    if (j.contains("result")) cs.result = j["result"].get<std::string>();
    if (j.contains("time_ms")) cs.timeMs = j["time_ms"].get<double>();
    if (j.contains("failure_stage")) cs.failureStage = j["failure_stage"].get<std::string>();
    if (j.contains("unknown_code")) cs.unknownCode = j["unknown_code"].get<std::string>();
    if (j.contains("unknown_component")) cs.unknownComponent = j["unknown_component"].get<std::string>();
    if (j.contains("unknown_detail")) cs.unknownDetail = j["unknown_detail"].get<std::string>();
    if (j.contains("active_theories")) cs.activeTheories = j["active_theories"].get<std::vector<std::string>>();
    if (j.contains("enabled_stats")) cs.enabledStats = j["enabled_stats"].get<std::vector<std::string>>();

    auto readI64 = [&](const char* obj, const char* key, int64_t& out) {
        if (j.contains(obj) && j[obj].contains(key)) out = j[obj][key].get<int64_t>();
    };
    auto readDbl = [&](const char* obj, const char* key, double& out) {
        if (j.contains(obj) && j[obj].contains(key)) out = j[obj][key].get<double>();
    };

    readI64("frontend", "num_expr", cs.frontend.numExpr);
    readI64("frontend", "num_atoms", cs.frontend.numAtoms);
    readI64("frontend", "num_unsupported", cs.frontend.numUnsupported);

    readI64("sat", "vars", cs.sat.vars);
    readI64("sat", "clauses", cs.sat.clauses);
    readI64("sat", "conflicts", cs.sat.conflicts);
    readI64("sat", "decisions", cs.sat.decisions);
    readI64("sat", "propagations", cs.sat.propagations);

    readI64("theory", "check_calls", cs.theory.checkCalls);
    readI64("theory", "conflicts", cs.theory.conflicts);
    readI64("theory", "lemmas", cs.theory.lemmas);
    readI64("theory", "propagations", cs.theory.propagations);
    readDbl("theory", "avg_conflict_size", cs.theory.avgConflictSize);
    readI64("theory", "max_conflict_size", cs.theory.maxConflictSize);

    readI64("lra", "simplex_pivots", cs.lra.simplexPivots);
    readI64("lra", "bound_updates", cs.lra.boundUpdates);

    readI64("lia", "branch_count", cs.lia.branchCount);
    readI64("lia", "gcd_tightening", cs.lia.gcdTightening);

    readI64("euf", "terms", cs.euf.terms);
    readI64("euf", "merges", cs.euf.merges);
    readI64("euf", "intern_failures", cs.euf.internFailures);

    readI64("nia", "linearization_terms", cs.nia.linearizationTerms);
    readI64("nia", "divmod_lowerings", cs.nia.divmodLowerings);

    readI64("nra", "num_polynomials", cs.nra.numPolynomials);
    readI64("nra", "root_isolation_calls", cs.nra.rootIsolationCalls);

    readI64("search", "model_check_calls", cs.search.modelCheckCalls);
    readI64("search", "model_check_conflicts", cs.search.modelCheckConflicts);
    readI64("search", "propagate_calls", cs.search.propagateCalls);
    readI64("search", "propagate_theory_checks", cs.search.propagateTheoryChecks);
    readI64("search", "propagate_conflicts", cs.search.propagateConflicts);
    readI64("search", "conflict_min_size", cs.search.conflictMinSize);
    readI64("search", "conflict_max_size", cs.search.conflictMaxSize);
    readDbl("search", "conflict_avg_size", cs.search.conflictAvgSize);

    if (j.contains("stage")) {
        if (j["stage"].contains("current_stage")) cs.stage.currentStage = j["stage"]["current_stage"];
        if (j["stage"].contains("current_component")) cs.stage.currentComponent = j["stage"]["current_component"];
        if (j["stage"].contains("current_operation")) cs.stage.currentOperation = j["stage"]["current_operation"];
    }

    return cs;
}

void CaseStats::dumpToFile(const std::string& path) const {
    auto j = toJson();
    j["dumped_at_ms"] = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now().time_since_epoch()).count();

    std::string tmp = path + ".tmp." + std::to_string(
#ifdef _WIN32
        0
#else
        getpid()
#endif
    );
    {
        std::ofstream ofs(tmp);
        if (ofs) ofs << j.dump(2);
    }
    std::rename(tmp.c_str(), path.c_str());
}

// ---------------------------------------------------------------------------
// HeartbeatWriter
// ---------------------------------------------------------------------------

void HeartbeatWriter::maybeWrite(const CaseStats& stats, const std::string& basePath) {
    auto now = std::chrono::steady_clock::now();
    auto elapsedMs = std::chrono::duration_cast<std::chrono::milliseconds>(
        now.time_since_epoch()).count();
    if (elapsedMs - lastWriteMs_ < 1000) return;  // at most once per second

    nlohmann::json j;
    j["current_stage"] = stats.stage.currentStage;
    j["current_component"] = stats.stage.currentComponent;
    j["current_operation"] = stats.stage.currentOperation;
    j["sat_conflicts"] = stats.sat.conflicts;
    j["theory_check_calls"] = stats.theory.checkCalls;
    j["model_checks"] = stats.search.modelCheckCalls;
    j["last_unknown_code"] = stats.unknownCode;
    j["elapsed_ms"] = stats.timeMs;
    j["written_at_ms"] = elapsedMs;

    std::string tmp = basePath + ".heartbeat.tmp";
    {
        std::ofstream ofs(tmp);
        if (ofs) ofs << j.dump();
    }
    std::rename(tmp.c_str(), (basePath + ".heartbeat").c_str());
    lastWriteMs_ = elapsedMs;
}

} // namespace xolver
