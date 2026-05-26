#include "theory/arith/linear/BoundAxiomGenerator.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/LinearFormKey.h"
#include <unordered_map>
#include <cstdlib>
#include <cstdio>

namespace zolver {

// ---------------------------------------------------------------------------
// Truth-set interval for an atom (L rel c).
// ---------------------------------------------------------------------------
BoundAxiomGenerator::Interval
BoundAxiomGenerator::toInterval(Relation rel, const mpq_class& c) {
    Interval iv;
    switch (rel) {
        case Relation::Leq: iv.valid = true; iv.loInf = true;  iv.hiInf = false; iv.hi = c; iv.hiIncl = true;  break;
        case Relation::Lt:  iv.valid = true; iv.loInf = true;  iv.hiInf = false; iv.hi = c; iv.hiIncl = false; break;
        case Relation::Geq: iv.valid = true; iv.hiInf = true;  iv.loInf = false; iv.lo = c; iv.loIncl = true;  break;
        case Relation::Gt:  iv.valid = true; iv.hiInf = true;  iv.loInf = false; iv.lo = c; iv.loIncl = false; break;
        case Relation::Eq:  iv.valid = true; iv.loInf = false; iv.hiInf = false; iv.lo = c; iv.hi = c; iv.loIncl = true; iv.hiIncl = true; break;
        case Relation::Neq: iv.valid = false; break;  // complement of a point: not a single interval
        default:            iv.valid = false; break;
    }
    return iv;
}

namespace {

Relation flipRel(Relation r) {
    switch (r) {
        case Relation::Leq: return Relation::Geq;
        case Relation::Geq: return Relation::Leq;
        case Relation::Lt:  return Relation::Gt;
        case Relation::Gt:  return Relation::Lt;
        default:            return r;  // Eq, Neq unchanged under negation
    }
}

// Canonicalize (form rel rhs) so the first term's coefficient is positive,
// mapping e.g. (-x <= -5) to the equivalent (x >= 5). Without this, atoms that
// the extractor stored with opposite sign land in different LinearFormKey
// groups and their bound relationship is missed. Negating both sides flips the
// relation and the rhs; the atom's truth set (hence the satVar's meaning) is
// unchanged, so this stays sound.
void canonicalizeForm(LinearFormKey& form, Relation& rel, mpq_class& rhs) {
    if (form.terms.empty()) return;
    if (form.terms.front().second < 0) {
        for (auto& t : form.terms) t.second = -t.second;
        rhs = -rhs;
        rel = flipRel(rel);
    }
}

// {x satisfying a's lower constraint} ⊆ {x satisfying b's lower constraint}
// i.e. b's lower bound is no tighter than a's.
bool lowerWeaker(const BoundAxiomGenerator::Interval& b,
                 const BoundAxiomGenerator::Interval& a) {
    if (b.loInf) return true;          // b unbounded below: implied by anything
    if (a.loInf) return false;         // a unbounded below, b not
    if (b.lo < a.lo) return true;
    if (b.lo > a.lo) return false;
    // equal lower value: ok unless a includes the endpoint and b excludes it
    return b.loIncl || !a.loIncl;
}

// symmetric for the upper side
bool upperWeaker(const BoundAxiomGenerator::Interval& b,
                 const BoundAxiomGenerator::Interval& a) {
    if (b.hiInf) return true;
    if (a.hiInf) return false;
    if (b.hi > a.hi) return true;
    if (b.hi < a.hi) return false;
    return b.hiIncl || !a.hiIncl;
}

// a is entirely to the left of b (a.hi edge below b.lo edge, no shared point).
bool leftOf(const BoundAxiomGenerator::Interval& a,
            const BoundAxiomGenerator::Interval& b) {
    if (a.hiInf) return false;         // a extends to +inf
    if (b.loInf) return false;         // b extends to -inf
    if (a.hi < b.lo) return true;
    if (a.hi > b.lo) return false;
    // touching at the same value: disjoint only if NOT both closed there
    return !(a.hiIncl && b.loIncl);
}

// a is a lower half-line (-inf, hi], b an upper half-line [lo, +inf):
// their union covers ℝ iff there is no gap at the junction.
bool lowerUpperCovers(const BoundAxiomGenerator::Interval& lowerHalf,
                      const BoundAxiomGenerator::Interval& upperHalf) {
    if (!(lowerHalf.loInf && !lowerHalf.hiInf)) return false;
    if (!(upperHalf.hiInf && !upperHalf.loInf)) return false;
    if (lowerHalf.hi > upperHalf.lo) return true;
    if (lowerHalf.hi < upperHalf.lo) return false;
    return lowerHalf.hiIncl || upperHalf.loIncl;  // junction point covered
}

} // namespace

bool BoundAxiomGenerator::subset(const Interval& a, const Interval& b) {
    return lowerWeaker(b, a) && upperWeaker(b, a);
}

bool BoundAxiomGenerator::disjoint(const Interval& a, const Interval& b) {
    return leftOf(a, b) || leftOf(b, a);
}

bool BoundAxiomGenerator::covers(const Interval& a, const Interval& b) {
    return lowerUpperCovers(a, b) || lowerUpperCovers(b, a);
}

std::vector<BoundAxiomGenerator::Shape>
BoundAxiomGenerator::pairShapes(Relation relA, const mpq_class& cA,
                                Relation relB, const mpq_class& cB) {
    std::vector<Shape> shapes;
    Interval a = toInterval(relA, cA);
    Interval b = toInterval(relB, cB);
    if (!a.valid || !b.valid) return shapes;
    if (subset(a, b))   shapes.push_back(Shape::ImpAtoB);
    if (subset(b, a))   shapes.push_back(Shape::ImpBtoA);
    if (disjoint(a, b)) shapes.push_back(Shape::Exclusion);
    if (covers(a, b))   shapes.push_back(Shape::Cover);
    return shapes;
}

bool BoundAxiomGenerator::enabled() {
    static bool e = []() {
        const char* v = std::getenv("ZOLVER_LRA_BOUND_AXIOMS");
        return v && *v && *v != '0';
    }();
    return e;
}

int BoundAxiomGenerator::maxGroupSize() {
    static int m = []() {
        const char* v = std::getenv("ZOLVER_LRA_BOUND_AXIOMS_MAXGROUP");
        return (v && *v) ? std::atoi(v) : 256;
    }();
    return m;
}

int BoundAxiomGenerator::generate(const TheoryAtomRegistry& registry, SatSolver& sat) {
    if (!enabled()) return 0;

    struct AtomLite { Relation rel; mpq_class c; SatVar var; };
    std::unordered_map<LinearFormKey, std::vector<AtomLite>, LinearFormKeyHash> groups;

    for (const auto& rec : registry.records()) {
        if (!std::holds_alternative<LinearAtomPayload>(rec.payload)) continue;
        const auto& p = std::get<LinearAtomPayload>(rec.payload);
        if (p.rel == Relation::Neq) continue;          // complement-of-point: skipped
        if (!p.rhs.isRational()) continue;             // linear atoms are rational
        LinearFormKey form = p.lhs;
        Relation rel = p.rel;
        mpq_class rhs = p.rhs.asRational();
        canonicalizeForm(form, rel, rhs);
        groups[form].push_back({rel, rhs, rec.satVar});
    }

    int emitted = 0;
    int maxGroup = 0, pairedGroups = 0, totalAtoms = 0;
    const int cap = maxGroupSize();
    for (auto& [form, atoms] : groups) {
        (void)form;
        int n = static_cast<int>(atoms.size());
        totalAtoms += n;
        if (n > maxGroup) maxGroup = n;
        if (n < 2 || n > cap) continue;
        ++pairedGroups;
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                SatLit pA = SatLit::positive(atoms[i].var);
                SatLit pB = SatLit::positive(atoms[j].var);
                for (Shape s : pairShapes(atoms[i].rel, atoms[i].c,
                                          atoms[j].rel, atoms[j].c)) {
                    switch (s) {
                        case Shape::ImpAtoB:   sat.addClause({pA.negated(), pB}); break;
                        case Shape::ImpBtoA:   sat.addClause({pB.negated(), pA}); break;
                        case Shape::Exclusion: sat.addClause({pA.negated(), pB.negated()}); break;
                        case Shape::Cover:     sat.addClause({pA, pB}); break;
                    }
                    ++emitted;
                }
            }
        }
    }
    if (const char* d = std::getenv("ZOLVER_LRA_BOUND_AXIOMS_DIAG"); d && *d) {
        std::fprintf(stderr,
            "[BOUND-AX] linAtoms=%d groups=%zu pairedGroups=%d maxGroup=%d clauses=%d\n",
            totalAtoms, groups.size(), pairedGroups, maxGroup, emitted);
    }
    return emitted;
}

} // namespace zolver
