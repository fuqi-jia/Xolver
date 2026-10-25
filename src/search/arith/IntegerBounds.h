#pragma once
#include "contracts/DecisionOracle.h"
#include <gmpxx.h>
#include <optional>
#include <string>

namespace xolver::integer_bounds {
// Mathematical integer bounds justified by original mandatory conjuncts.
// Div/mod use SMT-LIB Euclidean semantics. No application or C semantics enter
// this proof calculus; clients lower their source arithmetic before calling it.
struct Bound {
    std::shared_ptr<SOMTParser::DAGNode> symbol;
    std::optional<mpz_class> lower, upper;
    std::shared_ptr<SOMTParser::DAGNode> lowerAssumption, upperAssumption;
};
struct Certificate {
    std::vector<Bound> bounds;
    // Additional bounds on native integer expressions, identified by DAG
    // identity. `bounds` retains its variable-only certificate contract.
    std::vector<Bound> terms{};
};
enum class ProofStatus { Proved, Open, Invalid };
struct ProofResult {
    ProofStatus status = ProofStatus::Open;
    std::optional<Certificate> certificate;
    std::string reason;
    std::size_t work = 0;
};
ProofResult prove(const NativeAssertions &, const std::shared_ptr<SOMTParser::DAGNode> &conclusion,
                  std::size_t workLimit = 2000000);
ProofResult check(const NativeAssertions &, const std::shared_ptr<SOMTParser::DAGNode> &conclusion,
                  const Certificate &, std::size_t workLimit = 2000000);
// Refutation is discovery followed by certificate replay against all original
// assertions. Open means no proof was found, never SAT.
ProofResult refute(const NativeAssertions &, std::size_t workLimit = 2000000);
} // namespace xolver::integer_bounds
