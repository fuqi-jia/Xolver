#include "ir/NativeFeatures.h"
#include <somtparser/ir/node.h>
#include <unordered_set>

namespace xolver {
NativeFeatures nativeFeatures(const std::vector<SOMTParser::Node> &roots) {
    using K = SOMTParser::NODE_KIND;
    NativeFeatures features;
    auto work = roots;
    std::unordered_set<SOMTParser::Node> visited;
    std::unordered_set<std::shared_ptr<SOMTParser::Sort>> visitedSorts;
    while (!work.empty()) {
        auto node = std::move(work.back());
        work.pop_back();
        if (!node || !visited.insert(node).second)
            continue;
        auto sort = node->getSort();
        if (sort) {
            if (sort->isInt() || sort->isIntOrReal()) {
                const auto kind = node->getKind();
                if (kind == K::NT_MUL) {
                    std::size_t symbolic = 0;
                    for (const auto &c : SOMTParser::children(node))
                        symbolic += c->getKind() != K::NT_CONST;
                    features.nonlinearInteger |= symbolic > 1;
                } else if (kind == K::NT_POW)
                    features.nonlinearInteger = true;
                else if ((kind == K::NT_DIV_INT || kind == K::NT_MOD) &&
                         node->getChildrenSize() == 2)
                    features.nonlinearInteger |= node->getChild(1)->getKind() != K::NT_CONST;
            }
            features.real |= sort->isReal();
            features.integer |= sort->isInt() || sort->isIntOrReal();
            features.integerVariable |=
                (sort->isInt() || sort->isIntOrReal()) &&
                (node->getKind() == K::NT_VAR || node->getKind() == K::NT_QUANT_VAR);
            features.integerValue |=
                (sort->isInt() || sort->isIntOrReal()) && node->getKind() != K::NT_CONST;
            features.realValue |= sort->isReal() && node->getKind() != K::NT_CONST;
            features.bitvector |= sort->isBv();
            features.floatingPoint |= sort->isFp() || sort->isRoundingMode();
            features.strings |= sort->isStr() || sort->isReg();
            features.arrays |= sort->isArray();
            if (sort->isArray()) {
                auto i = sort->getIndexSort(), e = sort->getElemSort();
                features.finiteArray |=
                    i && e && (i->isBool() || i->isBv()) && (e->isBool() || e->isBv());
            }
            features.collections |=
                sort->isSet() || sort->isBag() || sort->isSeq() || sort->isRelation();
            // Finite domains can occur only in a compound sort signature.
            // Those formulas must not enter an infinite-domain abstraction.
            std::vector<std::shared_ptr<SOMTParser::Sort>> sorts{sort};
            while (!sorts.empty()) {
                auto s = sorts.back();
                sorts.pop_back();
                if (!s || !visitedSorts.insert(s).second)
                    continue;
                features.bitvector |= s->isBv();
                features.floatingPoint |= s->isFp() || s->isRoundingMode();
                features.strings |= s->isStr();
                features.collections |= s->isSet() || s->isBag() || s->isSeq() || s->isRelation();
                for (const auto &child : s->children)
                    sorts.push_back(child);
                if (s->dt_constructors)
                    for (const auto &constructor : *s->dt_constructors)
                        for (const auto &selector : constructor.selectors)
                            sorts.push_back(selector.sort);
            }
            features.otherSort |= !sort->isBool() && !sort->isInt() && !sort->isIntOrReal() &&
                                  !sort->isReal() && !sort->isBv();
        }
        switch (node->getKind()) {
        case K::NT_FORALL:
        case K::NT_EXISTS:
            features.quantified = true;
            break;
        case K::NT_SEP_EMP:
        case K::NT_SEP_NIL:
        case K::NT_SEP_PTO:
        case K::NT_SEP_STAR:
        case K::NT_SEP_WAND:
            features.spatial = true;
            break;
        case K::NT_UF_APPLY:
        case K::NT_FUNC_APPLY:
        case K::NT_FUNC_REC_APPLY:
            features.function = true;
            break;
        default:
            break;
        }
        for (auto child : SOMTParser::children(node))
            work.push_back(std::move(child));
    }
    return features;
}
} // namespace xolver
