cmake_minimum_required(VERSION 3.16)
project(NLColver VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ---------------------------------------------------------------------------
# Build options
# ---------------------------------------------------------------------------
option(NLCOLVER_BUILD_TESTS "Build unit tests and regression suite" ON)
option(NLCOLVER_BUILD_TOOLS "Build CLI tools and utilities" ON)
option(NLCOLVER_ENABLE_PROOFS "Enable proof production infrastructure" ON)
option(NLCOLVER_ENABLE_TRACING "Enable trace/recording for learning" ON)

if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# ---------------------------------------------------------------------------
# Compiler flags
# ---------------------------------------------------------------------------
if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    # Save flags for NLColver targets only (not propagated to submodules)
    set(NLCOLVER_CXX_FLAGS -Wall -Wextra -Wpedantic -Wno-unused-parameter)
    if(CMAKE_BUILD_TYPE STREQUAL "Debug")
        list(APPEND NLCOLVER_CXX_FLAGS -g -O0)
    else()
        list(APPEND NLCOLVER_CXX_FLAGS -O3)
    endif()
endif()

# ---------------------------------------------------------------------------
# Dependencies: GMP / MPFR (required)
# ---------------------------------------------------------------------------
find_package(PkgConfig QUIET)
if(PkgConfig_FOUND)
    pkg_check_modules(GMP QUIET gmp)
    pkg_check_modules(MPFR QUIET mpfr)
endif()

if(NOT GMP_FOUND)
    find_library(GMP_LIBRARIES NAMES gmp libgmp)
    find_path(GMP_INCLUDE_DIRS NAMES gmp.h)
    if(GMP_LIBRARIES AND GMP_INCLUDE_DIRS)
        set(GMP_FOUND TRUE)
    else()
        message(FATAL_ERROR "GMP not found. Install libgmp-dev.")
    endif()
endif()

if(NOT MPFR_FOUND)
    find_library(MPFR_LIBRARIES NAMES mpfr libmpfr)
    find_path(MPFR_INCLUDE_DIRS NAMES mpfr.h)
    if(MPFR_LIBRARIES AND MPFR_INCLUDE_DIRS)
        set(MPFR_FOUND TRUE)
    else()
        message(FATAL_ERROR "MPFR not found. Install libmpfr-dev.")
    endif()
endif()

# ---------------------------------------------------------------------------
# Dependencies: CaDiCaL (SAT backend) — vendored submodule, built via ExternalProject
# ---------------------------------------------------------------------------
include(ExternalProject)

set(CADICAL_SOURCE_DIR "${CMAKE_SOURCE_DIR}/third_party/cadical")
set(CADICAL_BUILD_DIR  "${CMAKE_BINARY_DIR}/third_party/cadical-build")
set(CADICAL_LIB        "${CADICAL_BUILD_DIR}/libcadical.a")
set(CADICAL_INCLUDE    "${CADICAL_SOURCE_DIR}/src")

if(EXISTS "${CADICAL_SOURCE_DIR}/configure")
    ExternalProject_Add(cadical_ext
        SOURCE_DIR    "${CADICAL_SOURCE_DIR}"
        BINARY_DIR    "${CADICAL_BUILD_DIR}"
        CONFIGURE_COMMAND cd "${CADICAL_SOURCE_DIR}" && ./configure -O
        BUILD_COMMAND     cd "${CADICAL_SOURCE_DIR}" && make
        INSTALL_COMMAND   ${CMAKE_COMMAND} -E copy
                          "${CADICAL_SOURCE_DIR}/build/libcadical.a"
                          "${CADICAL_LIB}"
        BUILD_BYPRODUCTS  "${CADICAL_LIB}"
    )
    add_library(cadical STATIC IMPORTED GLOBAL)
    add_dependencies(cadical cadical_ext)
    set_target_properties(cadical PROPERTIES
        IMPORTED_LOCATION "${CADICAL_LIB}"
        INTERFACE_INCLUDE_DIRECTORIES "${CADICAL_INCLUDE}"
    )
    set(CADICAL_FOUND TRUE)
    message(STATUS "CaDiCaL: building from third_party/cadical")
else()
    set(CADICAL_FOUND FALSE)
    message(WARNING "CaDiCaL submodule missing. Run: git submodule update --init --recursive")
endif()

# ---------------------------------------------------------------------------
# Dependencies: libpoly (polynomial kernel) — vendored submodule, add_subdirectory
# ---------------------------------------------------------------------------
set(LIBPOLY_SOURCE_DIR "${CMAKE_SOURCE_DIR}/third_party/libpoly")

if(EXISTS "${LIBPOLY_SOURCE_DIR}/CMakeLists.txt")
    set(LIBPOLY_BUILD_PYTHON_API OFF CACHE BOOL "" FORCE)
    set(LIBPOLY_BUILD_STATIC     ON  CACHE BOOL "" FORCE)
    set(LIBPOLY_BUILD_STATIC_PIC ON  CACHE BOOL "" FORCE)
    # Disable libpoly's own tests to keep ctest output clean
    set(BUILD_TESTING OFF)
    add_subdirectory("${LIBPOLY_SOURCE_DIR}" third_party/libpoly EXCLUDE_FROM_ALL)
    set(BUILD_TESTING ON)  # re-enable for NLColver's own tests
    set(LIBPOLY_FOUND TRUE)
    set(LIBPOLY_INCLUDE_DIRS "${LIBPOLY_SOURCE_DIR}/include")
    message(STATUS "libpoly: building from third_party/libpoly")
else()
    set(LIBPOLY_FOUND FALSE)
    message(WARNING "libpoly submodule missing. Run: git submodule update --init --recursive")
endif()

# ---------------------------------------------------------------------------
# Dependencies: nlohmann/json via FetchContent (for trace/config)
# ---------------------------------------------------------------------------
include(FetchContent)
FetchContent_Declare(
    json
    GIT_REPOSITORY https://github.com/nlohmann/json.git
    GIT_TAG v3.11.3
    GIT_SHALLOW TRUE
)
FetchContent_MakeAvailable(json)

# ---------------------------------------------------------------------------
# Submodules
# ---------------------------------------------------------------------------
add_subdirectory(third_party/SOMTParser)

# ---------------------------------------------------------------------------
# Version macros
# ---------------------------------------------------------------------------
add_compile_definitions(
    NLCOLVER_VERSION_MAJOR=${PROJECT_VERSION_MAJOR}
    NLCOLVER_VERSION_MINOR=${PROJECT_VERSION_MINOR}
    NLCOLVER_VERSION_PATCH=${PROJECT_VERSION_PATCH}
)

# ---------------------------------------------------------------------------
# Main library and tools
# ---------------------------------------------------------------------------
add_subdirectory(src)

if(NLCOLVER_BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()

if(NLCOLVER_BUILD_TOOLS)
    add_subdirectory(tools)
endif()
