#include "theory/arith/logics/lra/SparseTableau.h"
#include <cassert>

namespace xolver {

// ---------------------------------------------------------------------------
// Row lookup helpers
// ---------------------------------------------------------------------------

int SparseTableau::findRowPos(SparseRow& row, int col) {
    if (row.hasIndex) {
        auto it = row.pos.find(col);
        return it == row.pos.end() ? -1 : it->second;
    }
    for (int i = 0; i < static_cast<int>(row.entries.size()); ++i) {
        if (row.entries[i].col == col) return i;
    }
    return -1;
}

void SparseTableau::maybeBuildRowIndex(SparseRow& row) {
    constexpr int INDEX_THRESHOLD = 32;
    if (row.hasIndex || static_cast<int>(row.entries.size()) < INDEX_THRESHOLD) return;
    row.pos.clear();
    for (int i = 0; i < static_cast<int>(row.entries.size()); ++i) {
        row.pos[row.entries[i].col] = i;
    }
    row.hasIndex = true;
}

// ---------------------------------------------------------------------------
// Coefficient access / mutation
// ---------------------------------------------------------------------------

const mpq_class& SparseTableau::getCoeff(int row, int col) const {
    static const mpq_class kZero(0);
    const auto& r = rows_[row];
    if (r.hasIndex) {
        auto it = r.pos.find(col);
        return it == r.pos.end() ? kZero : r.entries[it->second].coeff;
    }
    for (const auto& e : r.entries) {
        if (e.col == col) return e.coeff;
    }
    return kZero;
}

void SparseTableau::setCoeff(int row, int col, const mpq_class& value) {
    auto& r = rows_[row];
    int rowPos = findRowPos(r, col);

    if (rowPos != -1) {
        if (value == 0) {
            eraseCoeff(row, col);
        } else {
            r.entries[rowPos].coeff = value;
        }
        return;
    }

    if (value == 0) return;

    auto& c = cols_[col];
    int newRowPos = static_cast<int>(r.entries.size());
    int newColPos = static_cast<int>(c.entries.size());

    r.entries.push_back(RowEntry{col, value, newColPos});
    c.entries.push_back(ColEntry{row, newRowPos});

    if (r.hasIndex) {
        r.pos[col] = newRowPos;
    }
    // Promote a row that has grown large to an O(1) col->pos index, so
    // findRowPos/getCoeff stop linear-scanning on every pivot. Small rows stay
    // a plain linear scan (faster than hashing). Once built, the index is
    // maintained incrementally by setCoeff/eraseCoeff.
    maybeBuildRowIndex(r);
}

void SparseTableau::addCoeff(int row, int col, const mpq_class& delta) {
    if (delta == 0) return;
    auto& r = rows_[row];
    // Single findRowPos (vs the old getCoeff+setCoeff double lookup), in the
    // pivot inner loop.
    int rowPos = findRowPos(r, col);
    if (rowPos != -1) {
        r.entries[rowPos].coeff += delta;
        if (r.entries[rowPos].coeff == 0) eraseCoeff(row, col);
        return;
    }
    // Absent: insert delta (mirror setCoeff's insert path).
    auto& c = cols_[col];
    int newRowPos = static_cast<int>(r.entries.size());
    int newColPos = static_cast<int>(c.entries.size());
    r.entries.push_back(RowEntry{col, delta, newColPos});
    c.entries.push_back(ColEntry{row, newRowPos});
    if (r.hasIndex) {
        r.pos[col] = newRowPos;
    }
    maybeBuildRowIndex(r);
}

void SparseTableau::eraseCoeff(int row, int col) {
    auto& r = rows_[row];
    int rowPos = findRowPos(r, col);
    if (rowPos == -1) return;

    int colPos = r.entries[rowPos].colPos;
    auto& c = cols_[col];

    int lastRowPos = static_cast<int>(r.entries.size()) - 1;
    int lastColPos = static_cast<int>(c.entries.size()) - 1;

    // Remove from row by swap-pop
    if (rowPos != lastRowPos) {
        RowEntry moved = r.entries[lastRowPos];
        r.entries[rowPos] = moved;

        // Fix column back-pointer of moved entry
        cols_[moved.col].entries[moved.colPos].rowPos = rowPos;

        if (r.hasIndex) {
            r.pos[moved.col] = rowPos;
        }
    }

    if (r.hasIndex) {
        r.pos.erase(col);
    }
    r.entries.pop_back();

    // Remove from column by swap-pop
    if (colPos != lastColPos) {
        ColEntry moved = c.entries[lastColPos];
        c.entries[colPos] = moved;

        // Fix row back-pointer of moved entry
        rows_[moved.row].entries[moved.rowPos].colPos = colPos;
    }
    c.entries.pop_back();
}

void SparseTableau::replaceRow(int row, int basicVar, const mpq_class& rhs,
                               const std::vector<std::pair<int, mpq_class>>& entries) {
    auto& r = rows_[row];

    // Remove all old entries from columns
    while (!r.entries.empty()) {
        int c = r.entries.back().col;
        eraseCoeff(row, c);
    }

    r.basicVar = basicVar;
    r.rhs = rhs;
    r.version++;

    if (r.hasIndex) {
        r.pos.clear();
        r.hasIndex = false;
    }

    for (const auto& [c, a] : entries) {
        if (a != 0) {
            setCoeff(row, c, a);
        }
    }
}

// ---------------------------------------------------------------------------
// Row / column creation
// ---------------------------------------------------------------------------

int SparseTableau::addEmptyRow() {
    int id = static_cast<int>(rows_.size());
    rows_.push_back(SparseRow());
    return id;
}

int SparseTableau::addEmptyCol() {
    int id = static_cast<int>(cols_.size());
    cols_.push_back(SparseCol());
    return id;
}

// ---------------------------------------------------------------------------
// Invariants (debug only)
// ---------------------------------------------------------------------------

void SparseTableau::checkInvariants(const std::vector<int>& basicRowOfVar) const {
#ifndef NDEBUG
    for (int r = 0; r < static_cast<int>(rows_.size()); ++r) {
        int b = rows_[r].basicVar;
        assert(b >= 0 && b < static_cast<int>(basicRowOfVar.size()));
        assert(basicRowOfVar[b] == r);

        for (int i = 0; i < static_cast<int>(rows_[r].entries.size()); ++i) {
            const auto& e = rows_[r].entries[i];
            assert(e.coeff != 0);
            assert(basicRowOfVar[e.col] == -1);  // non-basic

            const auto& ce = cols_[e.col].entries[e.colPos];
            assert(ce.row == r);
            assert(ce.rowPos == i);
        }
    }

    for (int c = 0; c < static_cast<int>(cols_.size()); ++c) {
        for (int k = 0; k < static_cast<int>(cols_[c].entries.size()); ++k) {
            const auto& ce = cols_[c].entries[k];
            const auto& re = rows_[ce.row].entries[ce.rowPos];
            assert(re.col == c);
            assert(re.colPos == k);
        }

        // Basic variable columns must be empty
        if (c < static_cast<int>(basicRowOfVar.size()) && basicRowOfVar[c] != -1) {
            assert(cols_[c].entries.empty());
        }
    }
#endif
}

} // namespace xolver
