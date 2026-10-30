#include "runtime/SolverImpl.h"

namespace xolver {
SolverAnswer Solver::decide(const NativeAssertions &assertions) {
    // Import transactionally. This owns the index, while every original node
    // remains shared with its caller; no text conversion or DAG rewriting.
    auto terms = std::make_unique<NativeTerms>();
    for (const auto &root : assertions) {
        if (!root || !root->getSort() || !root->getSort()->isBool())
            throw std::invalid_argument("native assertions must be Boolean");
        terms->addAssertion(terms->index(root));
    }
    std::unordered_map<std::string, ExprId> symbols;
    for (ExprId id = 0; id < terms->size(); ++id) {
        const auto expression = terms->get(id);
        if (expression.kind == Kind::Variable)
            if (const auto *name = std::get_if<std::string>(&expression.payload.value))
                symbols.emplace(*name, id);
    }
    pImpl->reset();
    pImpl->logic = "ALL";
    pImpl->boolSortId_ = terms->boolSortId();
    pImpl->intSortId_ = terms->intSortId();
    pImpl->realSortId_ = terms->realSortId();
    pImpl->symbolTerms_ = std::move(symbols);
    pImpl->ir = std::move(terms);
    SolverAnswer answer;
    answer.result = checkSat();
    answer.reason = pImpl->lastUnknownReason_;
    answer.model = pImpl->lastModel_;
    answer.proof = pImpl->lastProof_;
    return answer;
}
} // namespace xolver
