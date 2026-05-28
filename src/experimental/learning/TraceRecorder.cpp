#include "experimental/learning/TraceRecorder.h"

namespace xolver {

TraceRecorder::TraceRecorder(std::string benchmarkId) {
    trace_["benchmark_id"] = benchmarkId;
    trace_["logic"] = "unknown";
    trace_["events"] = nlohmann::json::array();
    trace_["stats"] = nlohmann::json::object();
}

void TraceRecorder::recordResult(const std::string& result) {
    trace_["result"] = result;
}

void TraceRecorder::recordTimeMs(double ms) {
    trace_["time_ms"] = ms;
}

void TraceRecorder::flush(const std::string& path) {
    std::ofstream ofs(path);
    ofs << trace_.dump(2);
}

} // namespace xolver
