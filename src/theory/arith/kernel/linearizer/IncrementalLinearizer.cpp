#include "theory/arith/kernel/linearizer/IncrementalLinearizer.h"
#include "theory/arith/kernel/linearizer/BoundStore.h"
#include <unordered_set>

namespace xolver {

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
    const LinearizationConfig& config,
    const std::unordered_map<std::string, mpq_class>* modelPoints) {

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

                auto mcCuts = mcGen_.generate(aux, x, y, *xBounds, *yBounds, c.reason, sort);
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

                // Model-construction: tangent the square at the current model
                // value of x (if provided) so the cut tightens around the
                // candidate point; else fall back to the bound midpoint.
                std::optional<mpq_class> modelX;
                if (modelPoints) {
                    auto it = modelPoints->find(x);
                    if (it != modelPoints->end()) modelX = it->second;
                }

                auto sqCuts = sqGen_.generate(
                    aux, x,
                    xBounds ? *xBounds : BoundInfo{},
                    c.reason,
                    modelX,
                    config.emitSquareNonneg,
                    config.emitSquareSecant,
                    config.emitSquareTangent,
                    sort);

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
            } else if (aux.key.kind == NonlinearKind::Power && aux.key.powers.size() == 1) {
                // Phase 1: x^N with N >= 3. Convex-envelope cuts via
                // PowerCutGenerator. Gated by XOLVER_NRA_NLEXT_POWER
                // (default OFF until paired-validated).
                //
                // Phase 1c (Bernstein) optionally piggybacks on the same
                // dispatch via XOLVER_NRA_NLEXT_BERNSTEIN; emits the tighter
                // convex-hull bounds on s = x^N. Both can ride together;
                // sound + cumulative.
                static const bool powEnabled = []() {
                    const char* e = std::getenv("XOLVER_NRA_NLEXT_POWER");
                    return e && *e && *e != '0';
                }();
                static const bool bernsteinEnabled = []() {
                    const char* e = std::getenv("XOLVER_NRA_NLEXT_BERNSTEIN");
                    return e && *e && *e != '0';
                }();
                if (!powEnabled && !bernsteinEnabled) continue;
                VarId xVid = aux.key.powers[0].first;
                int exponent = aux.key.powers[0].second;
                std::string x = std::string(kernel_.varName(xVid));
                auto xBounds = bounds.get(x);
                std::optional<mpq_class> modelX;
                if (modelPoints) {
                    auto it = modelPoints->find(x);
                    if (it != modelPoints->end()) modelX = it->second;
                }
                std::vector<mpq_class> boundVals;
                if (xBounds && xBounds->hasFiniteCompleteBounds()) {
                    boundVals = {xBounds->lower, xBounds->upper,
                                 mpq_class(exponent),
                                 modelX ? *modelX : (xBounds->lower + xBounds->upper) / 2};
                }
                if (powEnabled) {
                    auto pwCuts = pwGen_.generate(
                        aux, x, exponent,
                        xBounds ? *xBounds : BoundInfo{},
                        c.reason, modelX,
                        config.emitSquareNonneg,
                        config.emitSquareSecant,
                        config.emitSquareTangent,
                        sort);
                    int idx = 0;
                    for (auto& cut : pwCuts) {
                        if (static_cast<size_t>(idx) >= config.maxCutsPerTerm) break;
                        if (cache_.hasEmitted(aux.key, c.reason, boundVals, idx)) {
                            ++idx; continue;
                        }
                        SatLit cutLit = LinearConstraintNormalizer::registerLinearConstraint(
                            *registry_, cut.constraint, linearTheory);
                        if (cutLit.var != 0) {
                            auto lemma = buildCutLemma(c.reason, cut.reasons, cutLit);
                            CutCacheKey ck{aux.key, c.reason, boundVals, idx};
                            result.lemmas.push_back({std::move(lemma), ck});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                        ++idx;
                    }
                }
                // Phase 1c: Bernstein convex-hull envelope. Uses cache index
                // offset 200+ to stay clear of Power (0..) and MonomialBound
                // (100..) slots.
                if (bernsteinEnabled && xBounds && xBounds->hasFiniteCompleteBounds()) {
                    BernsteinPowerCutGenerator::Options bopt;
                    bopt.maxCutsHere = config.maxCutsPerTerm;
                    auto bCuts = bpGen_.generate(
                        aux, x, exponent, *xBounds, c.reason, bopt, sort);
                    int bIdx = 0;
                    for (auto& cut : bCuts) {
                        if (static_cast<size_t>(bIdx) >= config.maxCutsPerTerm) break;
                        if (cache_.hasEmitted(aux.key, c.reason, boundVals, 200 + bIdx)) {
                            ++bIdx; continue;
                        }
                        SatLit cutLit = LinearConstraintNormalizer::registerLinearConstraint(
                            *registry_, cut.constraint, linearTheory);
                        if (cutLit.var != 0) {
                            auto lemma = buildCutLemma(c.reason, cut.reasons, cutLit);
                            CutCacheKey ck{aux.key, c.reason, boundVals, 200 + bIdx};
                            result.lemmas.push_back({std::move(lemma), ck});
                            result.status = LinearizationStatus::Lemma;
                            if (result.lemmas.size() >= config.maxLemmas) return result;
                        }
                        ++bIdx;
                    }
                }
            } else if (aux.key.kind == NonlinearKind::HigherMixed) {
                // Phase 2 (this block): numeric monomial bounds via
                // MonomialBoundGenerator. Three cut families — interval
                // envelope, pivot-corner secant, multi-variable tangent.
                // Gated by XOLVER_NRA_NLEXT_MONO_BOUND, runs BEFORE the
                // sign-only path (which the previous phase produced). Both
                // are cumulative; the sign lemma is a cheap structural cut
                // even when numeric bounds are produced.
                static const bool monoBoundEnabled = []() {
                    const char* e = std::getenv("XOLVER_NRA_NLEXT_MONO_BOUND");
                    return e && *e && *e != '0';
                }();
                if (monoBoundEnabled && registry_ && aux.key.powers.size() >= 2) {
                    std::vector<MonomialBoundGenerator::Factor> factors;
                    factors.reserve(aux.key.powers.size());
                    // Family 0 (sign-only, NEW) only needs sign-pinned
                    // bounds, not finite ones — so we collect what we can.
                    // Families 1-3 self-decline inside the generator when
                    // ranges are missing. We still require every factor to
                    // have a bound entry so reason tracking holds.
                    bool haveAllBoundEntries = true;
                    for (const auto& [vid, exp] : aux.key.powers) {
                        std::string vn = std::string(kernel_.varName(vid));
                        auto vb = bounds.get(vn);
                        if (!vb) {
                            haveAllBoundEntries = false; break;
                        }
                        MonomialBoundGenerator::Factor f;
                        f.var = vn;
                        f.exponent = exp;
                        f.bounds = *vb;
                        if (modelPoints) {
                            auto it = modelPoints->find(vn);
                            if (it != modelPoints->end()) f.modelVal = it->second;
                        }
                        factors.push_back(std::move(f));
                    }
                    if (haveAllBoundEntries) {
                        MonomialBoundGenerator::Options mbOpt;
                        mbOpt.maxCutsHere = config.maxCutsPerTerm + 4;
                        auto mbCuts = mbGen_.generate(
                            aux, mpq_class(1), factors, c.reason, mbOpt, sort);
                        int idx = 0;
                        std::vector<mpq_class> boundVals;
                        boundVals.reserve(factors.size() * 2 + 1);
                        for (const auto& f : factors) {
                            boundVals.push_back(f.bounds.lower);
                            boundVals.push_back(f.bounds.upper);
                            if (f.modelVal) boundVals.push_back(*f.modelVal);
                        }
                        boundVals.push_back(mpq_class(factors.size()));
                        for (auto& cut : mbCuts) {
                            if (static_cast<size_t>(idx) >= config.maxCutsPerTerm) break;
                            if (cache_.hasEmitted(aux.key, c.reason, boundVals, 100 + idx)) {
                                ++idx; continue;
                            }
                            SatLit cutLit = LinearConstraintNormalizer::registerLinearConstraint(
                                *registry_, cut.constraint, linearTheory);
                            if (cutLit.var != 0) {
                                auto lemma = buildCutLemma(c.reason, cut.reasons, cutLit);
                                CutCacheKey ck{aux.key, c.reason, boundVals, 100 + idx};
                                result.lemmas.push_back({std::move(lemma), ck});
                                result.status = LinearizationStatus::Lemma;
                                if (result.lemmas.size() >= config.maxLemmas) return result;
                            }
                            ++idx;
                        }
                    }
                }

                // MGC-RD Phase 2A: sign-based lemma for high-degree mixed
                // monomials (x^3, x*y*z, theta*vv1*vv3^2, etc.). Walk each
                // factor, derive its sign contribution, combine into a total
                // sign. If definite, emit `aux > 0` (or < 0 etc.) so the SAT
                // layer can propagate. Gated by XOLVER_NRA_NLEXT_HIGHER env
                // var (default OFF until paired-validated).
                static const bool enabled = []() {
                    const char* e = std::getenv("XOLVER_NRA_NLEXT_HIGHER");
                    return e && *e && *e != '0';
                }();
                if (!enabled || !registry_) {
                    continue;
                }
                // Aggregate sign over each (var, exponent) factor.
                // Sign codes: -1 strict-neg, 0 zero, +1 strict-pos, 2 nonneg, -2 nonpos, 0xFF unknown.
                // For an even exponent: factor is nonneg (≥0) at minimum; strict (>0) if var ≠ 0.
                // For an odd exponent: factor inherits the var's sign.
                bool anyStrict = false;
                int totalSign = 1;  // multiplicative accumulator
                bool indeterminate = false;
                for (const auto& [vid, exp] : aux.key.powers) {
                    std::string vn = std::string(kernel_.varName(vid));
                    auto vb = bounds.get(vn);
                    if (!vb) { indeterminate = true; break; }
                    int factorSign;  // -1/0/+1, indeterminate=0xFF
                    bool factorStrict = false;
                    if ((exp % 2) == 0) {
                        // Even: factor ≥ 0; strict iff var bounded away from 0.
                        factorSign = +1;   // nonneg side
                        if ((vb->hasLower && vb->lower > 0) ||
                            (vb->hasUpper && vb->upper < 0)) {
                            factorStrict = true;
                        }
                    } else {
                        // Odd: factor sign = var sign.
                        if (vb->hasLower && vb->lower > 0) {
                            factorSign = +1; factorStrict = true;
                        } else if (vb->hasUpper && vb->upper < 0) {
                            factorSign = -1; factorStrict = true;
                        } else {
                            indeterminate = true; break;
                        }
                    }
                    if (factorSign == -1) totalSign = -totalSign;
                    if (factorStrict) anyStrict = true;
                }
                if (indeterminate || !anyStrict) continue;
                // Total monomial sign is `totalSign` (strict because at least one factor strict
                // AND all factors have known sign in same parity).
                Relation tRel = (totalSign > 0) ? Relation::Gt : Relation::Lt;
                SatLit tLit = registry_->getOrCreatePolynomialAtom(
                    aux.poly, tRel, mpq_class(0), linearTheory);
                if (tLit.var == 0) continue;
                // Conditional: for each factor, the bound condition is its sign
                // assumption; the conclusion is the total sign on the aux. We
                // emit a single clause: (¬cond1 ∨ ¬cond2 ∨ ... ∨ aux<tRel>).
                std::vector<SatLit> clause;
                clause.reserve(aux.key.powers.size() + 1);
                bool litFailed = false;
                for (const auto& [vid, exp] : aux.key.powers) {
                    std::string vn = std::string(kernel_.varName(vid));
                    auto vb = bounds.get(vn);
                    PolyId vp = kernel_.mkVar(vid);
                    if ((exp % 2) == 0) {
                        // Need v != 0 condition; cleanest is `v > 0` OR `v < 0`.
                        // Build whichever side the bound actually proves.
                        Relation vrel;
                        if (vb->hasLower && vb->lower > 0)      vrel = Relation::Gt;
                        else if (vb->hasUpper && vb->upper < 0) vrel = Relation::Lt;
                        else { litFailed = true; break; }
                        SatLit vLit = registry_->getOrCreatePolynomialAtom(
                            vp, vrel, mpq_class(0), linearTheory);
                        if (vLit.var == 0) { litFailed = true; break; }
                        clause.push_back(vLit.negated());
                    } else {
                        Relation vrel = (vb->hasLower && vb->lower > 0)
                                          ? Relation::Gt : Relation::Lt;
                        SatLit vLit = registry_->getOrCreatePolynomialAtom(
                            vp, vrel, mpq_class(0), linearTheory);
                        if (vLit.var == 0) { litFailed = true; break; }
                        clause.push_back(vLit.negated());
                    }
                }
                if (litFailed) continue;
                clause.push_back(tLit);
                TheoryLemma lemma{std::move(clause)};
                result.lemmas.push_back({std::move(lemma), std::nullopt});
                result.status = LinearizationStatus::Lemma;
                if (result.lemmas.size() >= config.maxLemmas) return result;
            }
        }
    }

    return result;
}

} // namespace xolver
