#pragma once
#include "base/ControlKey.h"
#include <utility>
#include <filesystem>
#include <vector>

namespace xolver::config {
// Reader types and conversion semantics are stable across catalog changes.
// Defaults stay explicit because they can depend on a profile or solve time.
bool read(Key<ReadKind::Flag>, bool fallback = false);
bool read(Key<ReadKind::Presence>);
int read(Key<ReadKind::Int>, int fallback);
long read(Key<ReadKind::Long>, long fallback);
double read(Key<ReadKind::Double>, double fallback);
// Semantic controls accept case-insensitive true/false, yes/no, on/off, 1/0.
// Empty or invalid tokens use the explicit caller default.
bool read(Key<ReadKind::Boolean>, bool fallback = false);
std::filesystem::path read(Key<ReadKind::Path>, std::filesystem::path fallback = {});
// A profiling destination: missing/false disables; true or empty uses fallback.
std::filesystem::path read(Key<ReadKind::ProfilePath>, std::filesystem::path fallback);
// Zero disables. A true token selects the default interval/capacity.
long read(Key<ReadKind::Period>, long interval = 2000);
long read(Key<ReadKind::Capacity>, long capacity = 100000);
std::vector<int> read(Key<ReadKind::Moduli>);
enum class Projection { Automatic, Collins, Lazard };
Projection read(Key<ReadKind::Projection>);
// Literal names and explicit modes are checked against controls.json by the
// source audit. Catalog edits no longer change a header imported by all theories.
template<ReadKind Kind, class... Args>
auto read(const char* name, Args&&... args) {
    return read(Key<Kind>{name}, std::forward<Args>(args)...);
}
} // namespace xolver::config
