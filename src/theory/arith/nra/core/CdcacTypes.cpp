#include "theory/arith/nra/core/CdcacTypes.h"

namespace zolver {

// ------------------------------------------------------------------
// V3: CellCertificate out-of-line destructor and move operations
// Defined here so CoveringCertificate is a complete type when
// unique_ptr's default deleter is instantiated.
// ------------------------------------------------------------------
CellCertificate::CellCertificate() = default;
CellCertificate::~CellCertificate() = default;
CellCertificate::CellCertificate(CellCertificate&&) noexcept = default;
CellCertificate& CellCertificate::operator=(CellCertificate&&) noexcept = default;

} // namespace zolver
