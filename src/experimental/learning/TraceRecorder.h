#pragma once

#include "expr/types.h"
#include <nlohmann/json.hpp>
#include <fstream>
#include <string>
#include <vector>

namespace nlcolver {

/**
 * TraceRecorder: captures solver events for learning / replay.
 *
 * Stage A: skeleton only. Records result and timing.
 * Future: SAT decisions, theory checks, cell generation, local-search moves.
 */
class TraceRecorder {
public:
    explicit TraceRecorder(std::string benchmarkId = "");

    void recordResult(const std::string& result);
    void recordTimeMs(double ms);

    // Write trace to JSON file.
    void flush(const std::string& path);

    // Get current trace as JSON object.
    nlohmann::json& data() { return trace_; }

private:
    nlohmann::json trace_;
};

} // namespace nlcolver
