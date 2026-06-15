// SPI v1 contract: the version handshake. A pro module compiled against an
// incompatible XOLVER_SPI_VERSION must be REFUSED by registerProLogic (so a stale
// plugin can never register a builder the core would mis-invoke), while a matching
// version registers. This is the guarantee that makes the open/pro seam stable.

#include <doctest/doctest.h>
#include "xolver/spi/SolverSpi.h"

using namespace xolver;

TEST_CASE("SPI version handshake: matching registers, mismatch is refused") {
    LogicBuilder dummy = [](BuildContext&) {};

    CHECK(SolverRegistry::coreSpiVersion() == XOLVER_SPI_VERSION);

    // A pro module built against the same SPI major registers successfully.
    CHECK(SolverRegistry::registerProLogic(XOLVER_SPI_VERSION,
                                           {"__SPI_TEST_OK__"}, 0, dummy, "spi-test"));
    CHECK(SolverRegistry::builderFor("__SPI_TEST_OK__") != nullptr);

    // A pro module built against a different SPI major is refused — no builder
    // is registered for its logic.
    CHECK_FALSE(SolverRegistry::registerProLogic(XOLVER_SPI_VERSION + 1,
                                                 {"__SPI_TEST_BAD__"}, 0, dummy, "spi-test"));
    CHECK(SolverRegistry::builderFor("__SPI_TEST_BAD__") == nullptr);
}
