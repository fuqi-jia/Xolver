# ---------------------------------------------------------------------------
# Xolver Python extension (_xolver) — pybind11 bindings over the public C++ API.
#
# Built only when XOLVER_BUILD_PYTHON=ON. The wheel build (scikit-build-core)
# sets that and links the already-PIC xolver_core static library into one
# shared object. For a plain `cmake -DXOLVER_BUILD_PYTHON=ON` dev build we
# fetch pybind11 if it is not installed.
# ---------------------------------------------------------------------------

# Prefer an installed pybind11 (provided by scikit-build-core / pip in the wheel
# build via build-system requires); fall back to FetchContent for dev builds.
find_package(pybind11 CONFIG QUIET)
if(NOT pybind11_FOUND)
    message(STATUS "pybind11 not found via find_package; fetching v2.13.6")
    include(FetchContent)
    FetchContent_Declare(
        pybind11
        GIT_REPOSITORY https://github.com/pybind/pybind11.git
        GIT_TAG v2.13.6
        GIT_SHALLOW TRUE
    )
    FetchContent_MakeAvailable(pybind11)
endif()

pybind11_add_module(_xolver
    src/bindings.cpp
)

# Link the core solver. xolver_core already exposes include/ (public headers)
# as a PUBLIC include dir, so <xolver/xolver.h> resolves. The binding also
# touches a few internal headers (the expr Kind enum for mkOp), so add src/ and
# the math include dirs privately — this binding lives inside the repo and is
# compiled against the source tree, exactly like the CLI.
target_link_libraries(_xolver PRIVATE xolver_core)
target_include_directories(_xolver PRIVATE
    ${CMAKE_SOURCE_DIR}/src
    ${GMP_INCLUDE_DIRS}
    ${MPFR_INCLUDE_DIRS}
    ${LIBPOLY_INCLUDE_DIRS}
)

if(DEFINED XOLVER_CXX_FLAGS)
    target_compile_options(_xolver PRIVATE ${XOLVER_CXX_FLAGS})
endif()

# Install the compiled module into the `xolver` package directory of the wheel.
# scikit-build-core picks up install() rules; the pure-Python package alongside
# it is declared in pyproject.toml (tool.scikit-build.wheel.packages).
install(TARGETS _xolver LIBRARY DESTINATION xolver)
