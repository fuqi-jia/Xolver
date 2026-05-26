# ---------------------------------------------------------------------------
# Zolver core library
# ---------------------------------------------------------------------------

file(GLOB_RECURSE ZOLVER_SOURCES CONFIGURE_DEPENDS
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
)

file(GLOB_RECURSE ZOLVER_HEADERS CONFIGURE_DEPENDS
    "${CMAKE_SOURCE_DIR}/include/zolver/*.h"
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
)

add_library(zolver_core STATIC
    ${ZOLVER_SOURCES}
    ${ZOLVER_HEADERS}
)

set_target_properties(zolver_core PROPERTIES
    POSITION_INDEPENDENT_CODE ON
)

if(DEFINED ZOLVER_CXX_FLAGS)
    target_compile_options(zolver_core PRIVATE ${ZOLVER_CXX_FLAGS})
endif()

target_include_directories(zolver_core
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
target_link_libraries(zolver_core PUBLIC cadical)
target_compile_definitions(zolver_core PUBLIC ZOLVER_HAS_CADICAL)

# ---------------------------------------------------------------------------
# libpoly: link the static target if available
# ---------------------------------------------------------------------------
if(TARGET static_polyxx)
    target_link_libraries(zolver_core PUBLIC static_polyxx)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_HAS_LIBPOLY)
elseif(TARGET polyxx)
    target_link_libraries(zolver_core PUBLIC polyxx)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_HAS_LIBPOLY)
elseif(TARGET poly_static)
    target_link_libraries(zolver_core PUBLIC poly_static)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_HAS_LIBPOLY)
elseif(TARGET poly)
    target_link_libraries(zolver_core PUBLIC poly)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_HAS_LIBPOLY)
endif()

target_link_libraries(zolver_core
    PUBLIC
        somtparser
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    PRIVATE
        nlohmann_json::nlohmann_json
)

if(ZOLVER_ENABLE_PROOFS)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_ENABLE_PROOFS)
endif()

if(ZOLVER_ENABLE_TRACING)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_ENABLE_TRACING)
endif()

if(ZOLVER_ENABLE_LRA_PROFILE)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_LRA_PROFILE)
endif()

if(ZOLVER_ENABLE_LIA_PROFILE)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_LIA_PROFILE)
endif()

# Incremental replay for LiaSolver (disable for baseline comparison)
if(NOT DEFINED ZOLVER_LIA_INCREMENTAL OR ZOLVER_LIA_INCREMENTAL)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_LIA_INCREMENTAL)
endif()

if(ZOLVER_ENABLE_CASESTATS)
    target_compile_definitions(zolver_core PUBLIC ZOLVER_ENABLE_CASESTATS)
endif()
