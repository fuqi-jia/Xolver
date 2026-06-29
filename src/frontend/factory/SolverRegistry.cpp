#include "frontend/factory/SolverRegistry.h"

#include <map>
#include <mutex>

namespace xolver {

namespace {

struct Entry {
    int priority = -1;
    LogicBuilder builder;
    const char* label = "";
};

// logic-name → highest-priority builder. Never destroyed (registration may run
// during static init, before main); a function-local static map is the standard
// fix for state touched during static init/teardown ordering.
std::map<std::string, Entry>& table() {
    static std::map<std::string, Entry>* t = new std::map<std::string, Entry>();
    return *t;
}

std::mutex& tableMutex() {
    static std::mutex* m = new std::mutex();
    return *m;
}

} // namespace

void SolverRegistry::registerLogic(std::vector<std::string> logics, int priority,
                                   LogicBuilder builder, const char* label) {
    std::lock_guard<std::mutex> g(tableMutex());
    for (auto& name : logics) {
        auto it = table().find(name);
        if (it == table().end() || priority > it->second.priority) {
            table()[name] = Entry{priority, builder, label};
        }
    }
}

const LogicBuilder* SolverRegistry::builderFor(const std::string& logic) {
    std::lock_guard<std::mutex> g(tableMutex());
    auto it = table().find(logic);
    if (it == table().end()) return nullptr;
    return &it->second.builder;
}

std::size_t SolverRegistry::size() {
    std::lock_guard<std::mutex> g(tableMutex());
    return table().size();
}

} // namespace xolver
