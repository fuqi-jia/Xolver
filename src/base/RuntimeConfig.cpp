#include "base/RuntimeConfig.h"
#include "base/EnvParam.h"
#include <algorithm>
#include <charconv>
#include <cctype>
#include <optional>
#include <string_view>

namespace xolver::config {
bool read(Key<ReadKind::Flag> key, bool fallback) { return env::flag(key.name(), fallback); }
bool read(Key<ReadKind::Presence> key) { return env::diag(key.name()); }
int read(Key<ReadKind::Int> key, int fallback) { return env::paramInt(key.name(), fallback); }
long read(Key<ReadKind::Long> key, long fallback) { return env::paramLong(key.name(), fallback); }
double read(Key<ReadKind::Double> key, double fallback) { return env::paramDouble(key.name(), fallback); }
namespace {
std::string normalized(const char* value) {
    std::string result(value ? value : "");
    for (char& c : result) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return result;
}
std::optional<bool> boolean(std::string_view value) {
    if (value == "1" || value == "true" || value == "on" || value == "yes") return true;
    if (value == "0" || value == "false" || value == "off" || value == "no") return false;
    return std::nullopt;
}
std::optional<long> integer(std::string_view value) {
    long result = 0;
    auto [end, ec] = std::from_chars(value.data(), value.data() + value.size(), result);
    if (ec != std::errc() || end != value.data() + value.size()) return std::nullopt;
    return result;
}
}
bool read(Key<ReadKind::Boolean> key, bool fallback) {
    return boolean(normalized(env::get(key.name()))).value_or(fallback);
}
std::filesystem::path read(Key<ReadKind::Path> key, std::filesystem::path fallback) {
    const char* value = env::get(key.name());
    return value && *value ? std::filesystem::path(value) : fallback;
}
std::filesystem::path read(Key<ReadKind::ProfilePath> key, std::filesystem::path fallback) {
    const char* value = env::get(key.name());
    if (!value) return {};
    if (!*value) return fallback;
    if (auto enabled = boolean(normalized(value))) return *enabled ? fallback : std::filesystem::path{};
    return std::filesystem::path(value);
}
long read(Key<ReadKind::Period> key, long interval) {
    auto value = normalized(env::get(key.name()));
    if (auto enabled = boolean(value)) return *enabled ? interval : 0;
    return std::max(0L, integer(value).value_or(0));
}
long read(Key<ReadKind::Capacity> key, long capacity) {
    auto value = normalized(env::get(key.name()));
    if (auto number = integer(value)) return std::max(0L, *number);
    return boolean(value).value_or(false) ? capacity : 0;
}
std::vector<int> read(Key<ReadKind::Moduli> key) {
    const std::vector<int> defaults{2, 3, 4, 5, 7, 8, 9, 11};
    const char* raw = env::get(key.name());
    if (!raw || !*raw) return defaults;
    std::string_view value(raw);
    std::vector<int> result;
    while (!value.empty()) {
        auto comma = value.find(',');
        auto token = value.substr(0, comma);
        while (!token.empty() && std::isspace(static_cast<unsigned char>(token.front()))) token.remove_prefix(1);
        while (!token.empty() && std::isspace(static_cast<unsigned char>(token.back()))) token.remove_suffix(1);
        auto number = integer(token);
        if (!number || *number < 2 || *number > 100) return defaults;
        if (std::find(result.begin(), result.end(), *number) == result.end())
            result.push_back(static_cast<int>(*number));
        if (comma == std::string_view::npos) return result;
        value.remove_prefix(comma + 1);
        if (value.empty()) return defaults;
    }
    return defaults;
}
Projection read(Key<ReadKind::Projection> key) {
    auto value = normalized(env::get(key.name()));
    if (value == "collins") return Projection::Collins;
    if (value == "lazard") return Projection::Lazard;
    return Projection::Automatic;
}
} // namespace xolver::config
