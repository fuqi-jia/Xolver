#include "theory/arith/linearizer/IncrementalLinearizer.h"
#include "theory/arith/linearizer/BoundStore.h"
#include <unordered_set>

namespace nlcolver {

IncrementalLinearizer::IncrementalLinearizer(PolynomialKernel& kernel,
                                               TheoryAtomRegistry* registry)
    : kernel_(kernel), registry_(registry), abstraction_(kernel) {}

TheoryLemma IncrementalLinearizer::buildAbstractionLemma(SatLit nonlinearReason,
                                                          SatLit linearizedLit) {
    return TheoryLemma{{nonlinearReason.negated(), linearizedLit}};
}

TheoryLemma IncrementalLinearizer::buildCutLemma(SatLit nonlinearReason,
                                                  const std::vector<SatLit>& boundReasons,
                                                  SatLit cutLit) {
    std::vector<SatLit> lits;
    lits.push_back(nonlinearReason.negated());
    for (auto r : boundReasons) lits.push_back(r.negated());
    lits.push_back(cutLit);
    return TheoryLemma{std::move(lits)};
}

void IncrementalLinearizer::markEmitted(const CutCacheKey& key) {
    cache_.markEmitted(key.term, key.nonlinearReason, key.boundValues, key.cutIndex);
}

LinearizationResult IncrementalLinearizer::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const BoundStore& bounds,
    TheoryId owner,
    const LinearizationConfig& config) {

    LinearizationResult result;
    result.status = LinearizationStatus::NoChange;

    TheoryId linearTheory = (owner == TheoryId::NIA) ? TheoryId::LIA : TheoryId::LRA;
    SortKind sort = (owner == TheoryId::NIA) ? SortKind::Int : SortKind::Real;
    std::unordered_set<std::string> processedAuxNames;
    // int cutIndexCounter = 0;  // unused

    for (const auto& c : constraints) {
        auto abstr = abstraction_.abstract(c.poly);
        if (abstr.unsupported) {
            result.status = LinearizationStatus::Unsupported;
            return result;
        }

        // --------------------------------------------------------------
        // Abstraction lemma: ¬C ∨ (p_L rel 0)
        // --------------------------------------------------------------
        if (!abstr.auxTerms.empty()) {
            auto zOpt = LinearConstraintNormalizer::fromPolynomialZero(
                kernel_, abstr.linearizedPoly, c.rel, sort, "abstraction");
            if (zOpt && registry_) {
                SatLit lit = LinearConstraintNormalizer::registerLinearConstraint(
                    *registry_, *zOpt, linearTheory);
                if (lit.var != 0) {
                    result.lemmas.push_back({buildAbstractionLemma(c.reason, lit), std::nullopt});
                    result.status = LinearizationStatus::Lemma;
                    if (result.lemmas.size() >= config.maxLemmas) {
                        return result;
                    }
                }
            }
        }

        // --------------------------------------------------------------
        // Envelope cuts for each unique aux term
        // --------------------------------------------------------------
        for (const auto& aux : abstr.auxTerms) {
            if (processedAuxNames.count(aux.name)) continue;
            processedAuxNames.insert(aux.name);

            if (aux.key.kind == NonlinearKind::Product && aux.key.powers.size() == 2) {
                VarId xVid = aux.key.powers[0].first;
                VarId yVid = aux.key.powers[1].first;
                std::string x = std::string(kernel_.varName(xVid));
                std::string y = std::string(kernel_.varName(yVid));

                auto xBounds = bounds.get(x);
                auto yBounds = bounds.get(y);

                if (!xBounds || !yBounds) continue;

                auto mcCuts = mcGen_.generate(aux, x, y, *xBounds, *yBounds, c.reason);
                int idx = 0;
                for (auto& cut : mcCuts) {
                    if (static_cast<size_t>(idx) >= config.maxCutsPerTerm) break;

                    std::vector<mpq_class> boundVals = {
                        xBounds->lower, xBounds->upper,
                        yBounds->lower, yBounds->upper
                    };

                    if (cache_.hasEmitted(aux.key, c.reason, boundVals, idx)) {
                        ++idx;
                        continue;
                    }

                    SatLit cutLit = LinearConstraintNormalizer::registerLinearConstraint(
                        *registry_, cut.constraint, linearTheory);
                    if (cutLit.var != 0) {
                        auto lemma = buildCutLemma(c.reason, cut.reasons, cutLit);
                        CutCacheKey ck{aux.key, c.reason, boundVals, idx};
                        result.lemmas.push_back({std::move(lemma), ck});
                        result.status = LinearizationStatus::Lemma;

                        if (result.lemmas.size() >= config.maxLemmas) {
                            return result;
                        }
                    }
                    ++idx;
                }

                // Sign lemmas for product: infer sign of x*y from signs of x and y
                if (registry_) {
                    PolyId xPoly = kernel_.mkVar(xVid);
                    PolyId yPoly = kernel_.mkVar(yVid);
                    PolyId tPoly = aux.poly;

                    auto buildSignLemma = [&](Relation xRel, Relation yRel, Relation tRel) -> std::optional<TheoryLemma> {
                        SatLit xLit = registry_->getOrCreatePolynomialAtom(xPoly, xRel, mpq_class(0), linearTheory);
                        SatLit yLit = registry_->getOrCreatePolynomialAtom(yPoly, yRel, mpq_class(0), linearTheory);
                        SatLit tLit = registry_->getOrCreatePolynomialAtom(tPoly, tRel, mpq_class(0), linearTheory);
                        if (xLit.var != 0 && yLit.var != 0 && tLit.var != 0) {
                            return TheoryLemma{{xLit.negated(), yLit.negated(), tLit}};
                        }
                        return std::nullopt;
                    };

                    // x > 0 && y > 0  =>  t > 0
                    if (xBounds->hasLower && xBounds->lower > 0 &&
                        yBounds->hasLower && yBounds->lower > 0) {
                        auto lemma = buildSignLemma(Relation::Gt, Relation::Gt, Relation::Gt);
                        if (lemma) {
                            result.lemmas.push_back({*lemma, std::nullopt});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                    }
                    // x < 0 && y < 0  =>  t > 0
                    if (xBounds->hasUpper && xBounds->upper < 0 &&
                        yBounds->hasUpper && yBounds->upper < 0) {
                        auto lemma = buildSignLemma(Relation::Lt, Relation::Lt, Relation::Gt);
                        if (lemma) {
                            result.lemmas.push_back({*lemma, std::nullopt});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                    }
                    // x > 0 && y < 0  =>  t < 0
                    if (xBounds->hasLower && xBounds->lower > 0 &&
                        yBounds->hasUpper && yBounds->upper < 0) {
                        auto lemma = buildSignLemma(Relation::Gt, Relation::Lt, Relation::Lt);
                        if (lemma) {
                            result.lemmas.push_back({*lemma, std::nullopt});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                    }
                    // x < 0 && y > 0  =>  t < 0
                    if (xBounds->hasUpper && xBounds->upper < 0 &&
                        yBounds->hasLower && yBounds->lower > 0) {
                        auto lemma = buildSignLemma(Relation::Lt, Relation::Gt, Relation::Lt);
                        if (lemma) {
                            result.lemmas.push_back({*lemma, std::nullopt});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                    }
                }
            } else if (aux.key.kind == NonlinearKind::Square && aux.key.powers.size() == 1) {
                VarId xVid = aux.key.powers[0].first;
                std::string x = std::string(kernel_.varName(xVid));
                auto xBounds = bounds.get(x);

                auto sqCuts = sqGen_.generate(
                    aux, x,
                    xBounds ? *xBounds : BoundInfo{},
                    c.reason,
                    std::nullopt,
                    config.emitSquareNonneg,
                    config.emitSquareSecant,
                    config.emitSquareTangent);

                int idx = 0;
                for (auto& cut : sqCuts) {
                    if (static_cast<size_t>(idx) >= config.maxCutsPerTerm) break;

                    std::vector<mpq_class> boundVals;
                    if (xBounds && xBounds->hasFiniteCompleteBounds()) {
                        boundVals = {xBounds->lower, xBounds->upper};
                    }

                    if (cache_.hasEmitted(aux.key, c.reason, boundVals, idx)) {
                        ++idx;
                        continue;
                    }

                    SatLit cutLit = LinearConstraintNormalizer::registerLinearConstraint(
                        *registry_, cut.constraint, linearTheory);
                    if (cutLit.var != 0) {
                        auto lemma = buildCutLemma(c.reason, cut.reasons, cutLit);
                        CutCacheKey ck{aux.key, c.reason, boundVals, idx};
                        result.lemmas.push_back({std::move(lemma), ck});
                        result.status = LinearizationStatus::Lemma;

                        if (result.lemmas.size() >= config.maxLemmas) {
                            return result;
                        }
                    }
                    ++idx;
                }
            }
        }
    }

    return result;
}

} // namespace nlcolver
