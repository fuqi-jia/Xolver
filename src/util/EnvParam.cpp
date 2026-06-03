#include "util/EnvParam.h"

#include <cstdio>
#include <cstdlib>
#include <map>
#include <mutex>
#include <ostream>
#include <sstream>
#include <string>

namespace xolver {
namespace env {
namespace {

struct Record {
    std::string def;
    std::string value;
    bool overridden = false;
};

// Sorted registry so the dump is deterministic (autotuner-friendly).
// Intentionally leaked (heap, never destroyed): the XOLVER_DUMP_PARAMS hook
// runs via atexit, and a function-local static map would be destroyed before
// that handler fires (destructors run in reverse construction order; the hook
// is registered before the map is first built). A never-destroyed singleton
// is the standard fix for state accessed during static teardown.
std::map<std::string, Record>& registry() {
    static std::map<std::string, Record>* r = new std::map<std::string, Record>();
    return *r;
}

std::mutex& registryMutex() {
    static std::mutex* m = new std::mutex();
    return *m;
}

// Exit-time dump via C stdio. We deliberately avoid std::cerr here: the
// atexit hook is registered during early static init, and std::cerr can be
// torn down (its std::ios_base::Init guard destructed) before the hook runs,
// swallowing the output. The C `stderr` FILE* is valid for the entire
// program lifetime including atexit, so it is the robust sink.
void dumpParamsToStderr() {
    std::lock_guard<std::mutex> g(registryMutex());
    std::fprintf(stderr,
                 "# XOLVER tunable parameters: name\tdefault\teffective\toverridden\n");
    for (const auto& kv : registry()) {
        std::fprintf(stderr, "%s\t%s\t%s\t%d\n", kv.first.c_str(),
                     kv.second.def.c_str(), kv.second.value.c_str(),
                     kv.second.overridden ? 1 : 0);
    }
    std::fflush(stderr);
}

// Install the exit-time dump hook exactly once, and only when the user asked
// for it. Cheap to call on every parameter read (call_once is a fast path
// after the first invocation).
void maybeInstallDumpHook() {
    static std::once_flag once;
    std::call_once(once, [] {
        if (std::getenv("XOLVER_DUMP_PARAMS")) {
            std::atexit(dumpParamsToStderr);
        }
    });
}

void record(const char* name, std::string def, std::string value,
            bool overridden) {
    std::lock_guard<std::mutex> g(registryMutex());
    registry()[name] = Record{std::move(def), std::move(value), overridden};
}

} // namespace

long paramLong(const char* name, long def) {
    maybeInstallDumpHook();
    long value = def;
    bool overridden = false;
    if (const char* e = std::getenv(name)) {
        if (*e) {
            char* end = nullptr;
            long parsed = std::strtol(e, &end, 10);
            if (end != e) {
                value = parsed;
                overridden = true;
            }
        }
    }
    record(name, std::to_string(def), std::to_string(value), overridden);
    return value;
}

int paramInt(const char* name, int def) {
    return static_cast<int>(paramLong(name, static_cast<long>(def)));
}

double paramDouble(const char* name, double def) {
    maybeInstallDumpHook();
    double value = def;
    bool overridden = false;
    if (const char* e = std::getenv(name)) {
        if (*e) {
            char* end = nullptr;
            double parsed = std::strtod(e, &end);
            if (end != e) {
                value = parsed;
                overridden = true;
            }
        }
    }
    std::ostringstream dss;
    std::ostringstream vss;
    dss << def;
    vss << value;
    record(name, dss.str(), vss.str(), overridden);
    return value;
}

void dumpParams(std::ostream& os) {
    std::lock_guard<std::mutex> g(registryMutex());
    os << "# XOLVER tunable parameters: name\\tdefault\\teffective\\toverridden\n";
    for (const auto& kv : registry()) {
        os << kv.first << '\t' << kv.second.def << '\t' << kv.second.value
           << '\t' << (kv.second.overridden ? '1' : '0') << '\n';
    }
    os.flush();
}

} // namespace env
} // namespace xolver
