#include "base/EnvParam.h"

#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <cctype>
#include <cmath>
#include <limits>
#include <map>
#include <mutex>
#include <ostream>
#include <sstream>
#include <string>

extern char** environ;

namespace xolver {
namespace env {
namespace {
thread_local const Snapshot* activeSnapshot = nullptr;
}

Snapshot Snapshot::capture(const Parameters& overrides) {
    Snapshot result;
    for (char** entry = environ; entry && *entry; ++entry) {
        const std::string item(*entry);
        const auto equal = item.find('=');
        if (equal != std::string::npos)
            result.values_.emplace(item.substr(0, equal), item.substr(equal + 1));
    }
    for (const auto& [name, value] : overrides) result.values_[name] = value;
    result.recordsReads_ = result.values_.count("XOLVER_DUMP_PARAMS") != 0;
    return result;
}
Snapshot Snapshot::withDefaults(
    const std::vector<std::pair<std::string, std::string>>& defaults) const {
    Snapshot result = *this;
    for (const auto& [name, value] : defaults) result.values_.emplace(name, value);
    result.recordsReads_ = result.values_.count("XOLVER_DUMP_PARAMS") != 0;
    return result;
}
const char* Snapshot::get(const char* name) const {
    auto it = values_.find(name);
    return it == values_.end() ? nullptr : it->second.c_str();
}
Scope::Scope(Snapshot snapshot)
    : snapshot_(std::move(snapshot)), previous_(activeSnapshot) {
    activeSnapshot = &snapshot_;
}
Scope::~Scope() { activeSnapshot = previous_; }
Snapshot currentSnapshot() {
    return activeSnapshot ? *activeSnapshot : Snapshot::capture();
}
const char* get(const char* name) {
    return activeSnapshot ? activeSnapshot->get(name) : std::getenv(name);
}

namespace {

bool recordsReads() {
    return activeSnapshot ? activeSnapshot->recordsReads() : get("XOLVER_DUMP_PARAMS") != nullptr;
}

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
    if (!recordsReads()) return;
    static std::once_flag once;
    std::call_once(once, [] {
        // get() is the non-recording reader; flag()/diag() would recurse here.
        std::atexit(dumpParamsToStderr);
    });
}

void record(const char* name, std::string def, std::string value,
            bool overridden) {
    std::lock_guard<std::mutex> g(registryMutex());
    registry()[name] = Record{std::move(def), std::move(value), overridden};
}

} // namespace

namespace {
bool consumed(const char* end) {
    while (*end && std::isspace(static_cast<unsigned char>(*end))) ++end;
    return *end == '\0';
}

long readLong(const char* name, long def, long minimum, long maximum) {
    maybeInstallDumpHook();
    long value = def;
    bool overridden = false;
    if (const char* e = get(name); e && *e) {
        char* end = nullptr;
        errno = 0;
        long parsed = std::strtol(e, &end, 10);
        if (end != e && consumed(end) && errno != ERANGE &&
            parsed >= minimum && parsed <= maximum) {
            value = parsed;
            overridden = true;
        }
    }
    if (recordsReads())
        record(name, std::to_string(def), std::to_string(value), overridden);
    return value;
}
} // namespace

long paramLong(const char* name, long def) {
    return readLong(name, def, std::numeric_limits<long>::min(),
                    std::numeric_limits<long>::max());
}

int paramInt(const char* name, int def) {
    return static_cast<int>(readLong(name, def, std::numeric_limits<int>::min(),
                                     std::numeric_limits<int>::max()));
}

double paramDouble(const char* name, double def) {
    maybeInstallDumpHook();
    double value = def;
    bool overridden = false;
    if (const char* e = get(name)) {
        if (*e) {
            char* end = nullptr;
            errno = 0;
            double parsed = std::strtod(e, &end);
            if (end != e && consumed(end) && errno != ERANGE && std::isfinite(parsed)) {
                value = parsed;
                overridden = true;
            }
        }
    }
    if (recordsReads()) {
        std::ostringstream dss, vss;
        dss << def;
        vss << value;
        record(name, dss.str(), vss.str(), overridden);
    }
    return value;
}

bool flag(const char* name, bool def) {
    maybeInstallDumpHook();
    bool value = def;
    bool overridden = false;
    if (const char* e = get(name)) {
        if (*e) {
            value = (*e != '0');
            overridden = true;
        }
    }
    if (recordsReads())
        record(name, def ? "1" : "0", value ? "1" : "0", overridden);
    return value;
}

bool diag(const char* name) {
    maybeInstallDumpHook();
    bool present = (get(name) != nullptr);
    // Presence-as-default: a diagnostic is "off" by default, "on" iff set.
    if (recordsReads())
        record(name, "0", present ? "1" : "0", present);
    return present;
}

void dumpParams(std::ostream& os) {
    std::lock_guard<std::mutex> g(registryMutex());
    os << "# XOLVER tunable parameters: name\tdefault\teffective\toverridden\n";
    for (const auto& kv : registry()) {
        os << kv.first << '\t' << kv.second.def << '\t' << kv.second.value
           << '\t' << (kv.second.overridden ? '1' : '0') << '\n';
    }
    os.flush();
}

} // namespace env
} // namespace xolver
