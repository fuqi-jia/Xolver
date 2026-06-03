# ---------------------------------------------------------------------------
# Xolver core library
# ---------------------------------------------------------------------------

file(GLOB_RECURSE XOLVER_SOURCES CONFIGURE_DEPENDS
    "api/*.cpp"
    "parser/*.cpp"
    "expr/*.cpp"
    "frontend/*.cpp"
    "frontend/**/*.cpp"
    "sat/*.cpp"
    "theory/*.cpp"
    "theory/**/*.cpp"
    "proof/*.cpp"
    "util/*.cpp"
    "experimental/*.cpp"
    "experimental/**/*.cpp"
)

file(GLOB_RECURSE XOLVER_HEADERS CONFIGURE_DEPENDS
    "${CMAKE_SOURCE_DIR}/include/xolver/*.h"
    "api/*.h"
    "parser/*.h"
    "expr/*.h"
    "frontend/*.h"
    "frontend/**/*.h"
    "sat/*.h"
    "theory/*.h"
    "theory/**/*.h"
    "proof/*.h"
    "util/*.h"
    "experimental/*.h"
    "experimental/**/*.h"
)

add_library(xolver_core STATIC
    ${XOLVER_SOURCES}
    ${XOLVER_HEADERS}
)

set_target_properties(xolver_core PROPERTIES
    POSITION_INDEPENDENT_CODE ON
)

if(DEFINED XOLVER_CXX_FLAGS)
    target_compile_options(xolver_core PRIVATE ${XOLVER_CXX_FLAGS})
endif()

target_include_directories(xolver_core
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
# CaDiCaL: required SAT backend
# ---------------------------------------------------------------------------
if(NOT TARGET cadical)
    message(FATAL_ERROR "CaDiCaL SAT solver is required but not found. "
                        "Run: git submodule update --init --recursive && "
                        "cd third_party/cadical && ./configure && make")
endif()
target_link_libraries(xolver_core PUBLIC cadical)
target_compile_definitions(xolver_core PUBLIC XOLVER_HAS_CADICAL)

# ---------------------------------------------------------------------------
# libpoly: link the static target if available
# ---------------------------------------------------------------------------
if(TARGET static_polyxx)
    target_link_libraries(xolver_core PUBLIC static_polyxx)
    target_compile_definitions(xolver_core PUBLIC XOLVER_HAS_LIBPOLY)
elseif(TARGET polyxx)
    target_link_libraries(xolver_core PUBLIC polyxx)
    target_compile_definitions(xolver_core PUBLIC XOLVER_HAS_LIBPOLY)
elseif(TARGET poly_static)
    target_link_libraries(xolver_core PUBLIC poly_static)
    target_compile_definitions(xolver_core PUBLIC XOLVER_HAS_LIBPOLY)
elseif(TARGET poly)
    target_link_libraries(xolver_core PUBLIC poly)
    target_compile_definitions(xolver_core PUBLIC XOLVER_HAS_LIBPOLY)
endif()

target_link_libraries(xolver_core
    PUBLIC
        somtparser
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    PRIVATE
        nlohmann_json::nlohmann_json
)

if(XOLVER_ENABLE_PROOFS)
    target_compile_definitions(xolver_core PUBLIC XOLVER_ENABLE_PROOFS)
endif()

if(XOLVER_ENABLE_TRACING)
    target_compile_definitions(xolver_core PUBLIC XOLVER_ENABLE_TRACING)
endif()

if(XOLVER_ENABLE_LRA_PROFILE)
    target_compile_definitions(xolver_core PUBLIC XOLVER_LRA_PROFILE)
endif()

if(XOLVER_ENABLE_LIA_PROFILE)
    target_compile_definitions(xolver_core PUBLIC XOLVER_LIA_PROFILE)
endif()

# Incremental replay for LiaSolver (disable for baseline comparison)
if(NOT DEFINED XOLVER_LIA_INCREMENTAL OR XOLVER_LIA_INCREMENTAL)
    target_compile_definitions(xolver_core PUBLIC XOLVER_LIA_INCREMENTAL)
endif()

if(XOLVER_ENABLE_CASESTATS)
    target_compile_definitions(xolver_core PUBLIC XOLVER_ENABLE_CASESTATS)
endif()
