# ---------------------------------------------------------------------------
# NLColver core library
# ---------------------------------------------------------------------------

file(GLOB_RECURSE NLCOLVER_SOURCES CONFIGURE_DEPENDS
    "api/*.cpp"
    "parser/*.cpp"
    "expr/*.cpp"
    "sat/*.cpp"
    "theory/*.cpp"
    "theory/**/*.cpp"
    "mcsat/*.cpp"
    "search/*.cpp"
    "omt/*.cpp"
    "proof/*.cpp"
    "learning/*.cpp"
    "util/*.cpp"
)

file(GLOB_RECURSE NLCOLVER_HEADERS CONFIGURE_DEPENDS
    "${CMAKE_SOURCE_DIR}/include/nlcolver/*.h"
    "api/*.h"
    "parser/*.h"
    "expr/*.h"
    "sat/*.h"
    "theory/*.h"
    "theory/**/*.h"
    "mcsat/*.h"
    "search/*.h"
    "omt/*.h"
    "proof/*.h"
    "learning/*.h"
    "util/*.h"
)

add_library(nlcolver_core STATIC
    ${NLCOLVER_SOURCES}
    ${NLCOLVER_HEADERS}
)

set_target_properties(nlcolver_core PROPERTIES
    POSITION_INDEPENDENT_CODE ON
)

if(DEFINED NLCOLVER_CXX_FLAGS)
    target_compile_options(nlcolver_core PRIVATE ${NLCOLVER_CXX_FLAGS})
endif()

target_include_directories(nlcolver_core
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
        ${LIBPOLY_INCLUDE_DIRS}
)

# ---------------------------------------------------------------------------
# CaDiCaL: link the IMPORTED target if available
# ---------------------------------------------------------------------------
if(TARGET cadical)
    target_link_libraries(nlcolver_core PUBLIC cadical)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_HAS_CADICAL)
endif()

# ---------------------------------------------------------------------------
# libpoly: link the static target if available
# ---------------------------------------------------------------------------
if(TARGET static_polyxx)
    target_link_libraries(nlcolver_core PUBLIC static_polyxx)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_HAS_LIBPOLY)
elseif(TARGET polyxx)
    target_link_libraries(nlcolver_core PUBLIC polyxx)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_HAS_LIBPOLY)
elseif(TARGET poly_static)
    target_link_libraries(nlcolver_core PUBLIC poly_static)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_HAS_LIBPOLY)
elseif(TARGET poly)
    target_link_libraries(nlcolver_core PUBLIC poly)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_HAS_LIBPOLY)
endif()

target_link_libraries(nlcolver_core
    PUBLIC
        somtparser
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    PRIVATE
        nlohmann_json::nlohmann_json
)

if(NLCOLVER_ENABLE_PROOFS)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_ENABLE_PROOFS)
endif()

if(NLCOLVER_ENABLE_TRACING)
    target_compile_definitions(nlcolver_core PUBLIC NLCOLVER_ENABLE_TRACING)
endif()
