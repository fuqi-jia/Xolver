#include "xolver/SeparationLogic.h"
#include "evidence/PresburgerCertificate.h"
#include "evidence/PresburgerModel.h"
#include <iostream>

// This executable deliberately links only xolver_checkers. Search, CaDiCaL,
// SOMTParser and the query runtime must not be needed to replay evidence.
int main() {
    using namespace xolver;
    sl::SymbolicHeap query;
    query.pure = {{1, 2, true}, {2, 3, true}, {1, 3, false}};
    sl::Conflict conflict{sl::Conflict::Kind::PureDisequality, 2, 0,
                          {{0, false}, {1, false}}};
    if (!sl::checkConflict(query, conflict)) return 1;
    conflict.path[1].reverse = true;
    if (sl::checkConflict(query, conflict)) return 2;
    query = {};
    query.spatial = {{1, {sl::Location{0}, std::string("12345678901234567890")}}};
    sl::Model model;
    model.locations = {{0, 0}, {1, 7}};
    model.heap = {{7, {uint64_t{0}, std::string("12345678901234567890")}}};
    if (!sl::checkModel(query, model)) return 3;
    model.heap[8] = {};
    if (sl::checkModel(query, model)) return 4;
    proof::IntegerInequality left{{{1, 2}}, 3}, right{{{1, -2}}, -4};
    if (!proof::checkIntegerLinearContradiction({left, right}, {1, 1})) return 5;
    if (proof::checkIntegerLinearContradiction({left, right}, {1, -1})) return 6;
    sl::Formula spatial({sl::FieldSort::Integer});
    auto empty = spatial.emp();
    auto cell = spatial.pointsTo(1, {std::string("17")});
    auto extension = spatial.wand(cell, cell);
    spatial.conjunction(empty, extension);
    sl::Model emptyModel{{{0, 0}, {1, 23}}, {}};
    if (sl::evaluate(spatial, emptyModel).holds != std::optional<bool>(true)) return 7;
    auto truth = spatial.boolean(true);
    spatial.wand(truth, empty);
    if (sl::evaluate(spatial, emptyModel).holds != std::optional<bool>(false)) return 8;
    pa::ModelEvidence arithmetic;
    arithmetic.symbols.emplace("x", 0);
    arithmetic.values.emplace(0, 1);
    pa::Literal bound;
    bound.affine.coefficients.emplace(0, 2);
    bound.affine.constant = -3;
    arithmetic.formula.insert(pa::Cube{bound});
    if (pa::checkModel(arithmetic).holds != std::optional<bool>(true)) return 9;
    arithmetic.values.at(0) = 2;
    if (pa::checkModel(arithmetic).holds != std::optional<bool>(false)) return 10;
    std::cout << "standalone evidence replay passed\n";
}
