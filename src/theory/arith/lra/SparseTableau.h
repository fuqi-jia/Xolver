#pragma once

#include <gmpxx.h>
#include <vector>
#include <unordered_map>

namespace nlcolver {

// ---------------------------------------------------------------------------
// Sparse Indexed Explicit Tableau
// ---------------------------------------------------------------------------
// Row / column cross-linked storage for Dutertre-de Moura simplex.
// Invariant: every RowEntry references a non-basic variable.
// Invariant: a basic variable's column is always empty.
// ---------------------------------------------------------------------------

struct RowEntry {
    int col;           // variable id (must be non-basic)
    mpq_class coeff;   // coefficient in row
    int colPos;        // position of this row in cols[col].entries
};

struct ColEntry {
    int row;           // row id
    int rowPos;        // position of this col in rows[row].entries
};

struct SparseRow {
    int basicVar = -1;
    mpq_class rhs = 0;
    std::vector<RowEntry> entries;

    // Optional index for large rows (threshold-based)
    bool hasIndex = false;
    std::unordered_map<int, int> pos;  // col -> index in entries

    int version = 0;
};

struct SparseCol {
    std::vector<ColEntry> entries;
};

class SparseTableau {
public:
    // -----------------------------------------------------------------------
    // Row / column access
    // -----------------------------------------------------------------------
    int numRows() const { return static_cast<int>(rows_.size()); }
    int numCols() const { return static_cast<int>(cols_.size()); }

    const SparseRow& row(int r) const { return rows_[r]; }
    SparseRow& row(int r) { return rows_[r]; }

    const SparseCol& col(int c) const { return cols_[c]; }
    SparseCol& col(int c) { return cols_[c]; }

    // -----------------------------------------------------------------------
    // Coefficient access / mutation
    // All structural mutations go through these functions only.
    // Never edit rows_[r].entries or cols_[c].entries directly.
    // -----------------------------------------------------------------------
    mpq_class getCoeff(int row, int col) const;
    void setCoeff(int row, int col, const mpq_class& value);
    void addCoeff(int row, int col, const mpq_class& delta);
    void eraseCoeff(int row, int col);

    // Replace an entire row (clear old entries, insert new ones)
    void replaceRow(int row, int basicVar, const mpq_class& rhs,
                    const std::vector<std::pair<int, mpq_class>>& entries);

    // Add a new empty row. Returns row index.
    int addEmptyRow();

    // Add a new empty column. Returns column index.
    int addEmptyCol();

    // -----------------------------------------------------------------------
    // Diagnostics
    // -----------------------------------------------------------------------
    void checkInvariants(const std::vector<int>& basicRowOfVar) const;

private:
    std::vector<SparseRow> rows_;
    std::vector<SparseCol> cols_;

    // -----------------------------------------------------------------------
    // Row lookup helpers
    // -----------------------------------------------------------------------
    int findRowPos(SparseRow& row, int col);
    void maybeBuildRowIndex(SparseRow& row);
};

} // namespace nlcolver
