#include "ir/NativeFeatures.h"
#include <somtparser/ir/node.h>
#include <unordered_set>

namespace xolver {
NativeFeatures nativeFeatures(const std::vector<SOMTParser::Node> &roots) {
    using K = SOMTParser::NODE_KIND;
    NativeFeatures features;
    auto work = roots;
    std::unordered_set<SOMTParser::Node> visited;
    while (!work.empty()) {
        auto node = std::move(work.back());
        work.pop_back();
        if (!node || !visited.insert(node).second)
            continue;
        auto sort = node->getSort();
        if (sort) {
            features.real |= sort->isReal();
            features.integer |= sort->isInt() || sort->isIntOrReal();
            features.integerVariable |=
                (sort->isInt() || sort->isIntOrReal()) &&
                (node->getKind() == K::NT_VAR || node->getKind() == K::NT_QUANT_VAR);
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
            // A BV domain can be present only in an array signature (e.g. a=b).
            // Such formulas must not enter an infinite-domain array abstraction.
            std::vector<std::shared_ptr<SOMTParser::Sort>> sorts{sort};
            std::unordered_set<std::shared_ptr<SOMTParser::Sort>> seenSorts;
            while (!sorts.empty()) {
                auto s = sorts.back();
                sorts.pop_back();
                if (!s || !seenSorts.insert(s).second)
                    continue;
                features.bitvector |= s->isBv();
                features.floatingPoint |= s->isFp();
                features.strings |= s->isStr();
                features.collections |= s->isSet() || s->isBag() || s->isSeq() || s->isRelation();
                if (s->isArray()) {
                    sorts.push_back(s->getIndexSort());
                    sorts.push_back(s->getElemSort());
                }
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
