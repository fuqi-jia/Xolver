#pragma once
#include "ir/NativeTerms.h"
#include <somtparser/core/kind.h>

namespace xolver {
// Theory-facing operator classification of native nodes; owns no storage.
Kind nativeKind(SOMTParser::NODE_KIND);
}
