#pragma once
#include "xolver/Result.h"
#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace xolver::sl {
// Location 0 denotes nil. Other ids are existentially interpreted location
// symbols, not integer addresses. String-valued fields are exact integer literals.
using Location = uint32_t;
using Field = std::variant<Location, std::string>;
struct PointsTo { Location address; std::vector<Field> fields; };
struct LocationConstraint { Location left, right; bool equal; };
struct SymbolicHeap {
    std::vector<LocationConstraint> pure;
    std::vector<PointsTo> spatial; // separating conjunction; empty means emp
};
using ConcreteField = std::variant<uint64_t, std::string>;
struct Model {
    std::map<Location, uint64_t> locations;
    std::map<uint64_t, std::vector<ConcreteField>> heap;
};
struct EqualityStep { std::size_t premise; bool reverse = false; };
struct Conflict {
    enum class Kind { PureDisequality, NilAllocation, OverlappingCells };
    Kind kind;
    std::size_t first = 0, second = 0;
    std::vector<EqualityStep> path;
};
struct Outcome {
    Result result = Result::Unknown;
    Model model;
    std::optional<Conflict> conflict;
    std::string reason;
};

// Complete for this existential symbolic-heap fragment: conjunctive location
// (dis)equalities, emp, points-to, star, and ground integer/location fields.
// Lists/SIDs, spatial negation, wand, arithmetic-valued fields and entailment
// are not encoded by SymbolicHeap. Search results are checked before return.
Outcome solve(const SymbolicHeap&);
bool checkModel(const SymbolicHeap&, const Model&);
bool checkConflict(const SymbolicHeap&, const Conflict&);

// Quantifier-free Boolean/spatial formulas over one typed heap. Locations have
// an infinite uninterpreted domain; nil is not allocatable. Integer fields here
// are literals, not arithmetic expressions. This is the SL-specific IR: it does
// not copy the parser's term DAG or define another general expression language.
enum class FieldSort { Location, Integer };
using FormulaId = std::size_t;
struct FormulaNode {
    enum class Kind { Boolean, Relation, Emp, PointsTo, Not, And, Or, Star, Wand };
    Kind kind = Kind::Boolean;
    bool boolean = false;
    LocationConstraint relation{0, 0, true};
    PointsTo cell{};
    std::vector<FormulaId> children;
};
struct Formula {
    explicit Formula(std::vector<FieldSort> fields = {FieldSort::Location})
        : fieldSorts(std::move(fields)) {}
    std::vector<FieldSort> fieldSorts;
    std::vector<FormulaNode> nodes;
    FormulaId root = 0;
    // Appending a node makes it the root. Children must precede their parent.
    FormulaId boolean(bool);
    FormulaId relation(Location, Location, bool equal = true);
    FormulaId emp();
    FormulaId pointsTo(Location, std::vector<Field>);
    FormulaId negate(FormulaId);
    FormulaId conjunction(FormulaId, FormulaId);
    FormulaId disjunction(FormulaId, FormulaId);
    FormulaId star(FormulaId, FormulaId);
    FormulaId wand(FormulaId, FormulaId);
};
struct Limits {
    uint64_t maxSteps = 1000000;
    std::size_t maxDepth = 256;
};
struct Evaluation {
    // Missing means malformed input or an exhausted resource limit, never false.
    std::optional<bool> holds;
    uint64_t steps = 0;
    std::string reason;
};
// Checks classical Boolean connectives, all disjoint partitions for star, and
// all finite extension heaps for wand via a complete finite representative set.
// The evidence implementation does not link the decision/search engines.
Evaluation evaluate(const Formula&, const Model&, Limits = {});
// Exact finite abstraction for this quantifier-free signature, with explicit
// Unknown on limits. General quantified SL, inductive predicates and symbolic
// arithmetic fields require additional theory machinery. Unsat here is an
// exhaustive decision result; it is not a serialized derivation certificate.
Outcome solve(const Formula&, Limits = {});
} // namespace xolver::sl
