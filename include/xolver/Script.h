#pragma once
#include <string>
#include <string_view>
#include <vector>

namespace xolver {
// Standalone query snapshots in source order. Each snapshot replays all prior
// state changes, contains one query and its responses, and scopes assumptions
// to that query. Empty-query scripts have one implicit final-context snapshot.
// This is a correctness fallback for a parser whose command log omits asserts;
// it does not claim to preserve incremental search state between queries.
std::vector<std::string> smtQuerySnapshots(std::string_view source);
}
