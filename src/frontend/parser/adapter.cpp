#include "frontend/parser/adapter.h"
#include "frontend/parser/rewriter.h"

namespace xolver {
std::unique_ptr<NativeTerms> FrontendAdapter::importProblem(bool rewriteGround) {
    auto terms = std::make_unique<NativeTerms>(parser_.getNodeManager());
    SOMTParser::Rewriter rewriter(parser_.getNodeManager());
    if (rewriteGround) {
        SOMTParser::installDefaultRewriteRules(rewriter);
        installXolverRewriteRules(rewriter);
    }
    for (auto node : parser_.getAssertions()) {
        if (rewriteGround) node = rewriter.rewrite(node);
        terms->addAssertion(terms->index(std::move(node)));
    }
    boolSortId_ = terms->boolSortId();
    return terms;
}
} // namespace xolver
