# Source ownership is explicit; configuration rejects undeclared sources and
# reverse dependencies before C++ compilation. No recursive source globbing.
find_package(Python3 REQUIRED COMPONENTS Interpreter)
find_package(Threads REQUIRED)
execute_process(
    COMMAND "${Python3_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/tools/governance/architecture.py"
    RESULT_VARIABLE XOLVER_ARCHITECTURE_STATUS
    OUTPUT_VARIABLE XOLVER_ARCHITECTURE_REPORT)
if(NOT XOLVER_ARCHITECTURE_STATUS EQUAL 0)
    message(FATAL_ERROR "${XOLVER_ARCHITECTURE_REPORT}")
endif()
include(sources.cmake)
execute_process(
    COMMAND "${Python3_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/tools/governance/control_catalog.py"
    RESULT_VARIABLE XOLVER_CONTROL_STATUS)
if(NOT XOLVER_CONTROL_STATUS EQUAL 0)
    message(FATAL_ERROR "Typed runtime control declarations are inconsistent")
endif()

add_library(xolver_build_options INTERFACE)
target_compile_options(xolver_build_options INTERFACE ${XOLVER_CXX_FLAGS})
target_include_directories(xolver_build_options INTERFACE
    $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    ${GMP_INCLUDE_DIRS} ${MPFR_INCLUDE_DIRS} ${LIBPOLY_INCLUDE_DIRS})

# ---------------------------------------------------------------------------
# CaDiCaL: required SAT backend
# ---------------------------------------------------------------------------
if(NOT TARGET cadical)
    message(FATAL_ERROR "CaDiCaL SAT solver is required but not found. "
                        "Run: git submodule update --init --recursive && "
                        "cd third_party/cadical && ./configure && make")
endif()
target_compile_definitions(xolver_build_options INTERFACE XOLVER_HAS_CADICAL)

# ---------------------------------------------------------------------------
# libpoly: link the static target if available
# ---------------------------------------------------------------------------
if(TARGET static_polyxx)
    set(XOLVER_POLY_TARGET static_polyxx)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_HAS_LIBPOLY)
elseif(TARGET polyxx)
    set(XOLVER_POLY_TARGET polyxx)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_HAS_LIBPOLY)
elseif(TARGET poly_static)
    set(XOLVER_POLY_TARGET poly_static)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_HAS_LIBPOLY)
elseif(TARGET poly)
    set(XOLVER_POLY_TARGET poly)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_HAS_LIBPOLY)
endif()

target_link_libraries(xolver_build_options
    INTERFACE
        nlohmann_json::nlohmann_json
)

if(XOLVER_ENABLE_PROOFS)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_ENABLE_PROOFS)
endif()

if(XOLVER_ENABLE_LRA_PROFILE)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_LRA_PROFILE)
endif()

if(XOLVER_ENABLE_LIA_PROFILE)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_LIA_PROFILE)
endif()

if(XOLVER_ENABLE_CASESTATS)
    target_compile_definitions(xolver_build_options INTERFACE XOLVER_ENABLE_CASESTATS)
endif()

# Separate archives can be built/linked without the runtime and search engines.
# Their dependency direction is checked by architecture.py at configure and CI.
set(XOLVER_CORE_OBJECTS)
# Preserve archive member order while automatically including a layer when its
# first compiled source is added.
foreach(layer base parallel ir contracts algebra evidence quantifiers applications frontend search runtime)
    string(TOUPPER "${layer}" upper)
    if(NOT XOLVER_${upper}_SOURCES)
        add_library(xolver_${layer} INTERFACE)
        target_link_libraries(xolver_${layer} INTERFACE xolver_build_options)
        if(layer MATCHES "^(ir|quantifiers|applications)$")
            target_link_libraries(xolver_${layer} INTERFACE somtparser_ir)
        endif()
        continue()
    endif()
    add_library(xolver_${layer} OBJECT ${XOLVER_${upper}_SOURCES})
    list(APPEND XOLVER_CORE_OBJECTS $<TARGET_OBJECTS:xolver_${layer}>)
    set_target_properties(xolver_${layer} PROPERTIES POSITION_INDEPENDENT_CODE ON)
    target_link_libraries(xolver_${layer} PRIVATE xolver_build_options)
    if(layer STREQUAL "parallel")
        target_link_libraries(xolver_${layer} PRIVATE Threads::Threads)
    endif()
    if(layer MATCHES "^(algebra|search|applications|runtime)$")
        target_link_libraries(xolver_${layer} PRIVATE ${XOLVER_POLY_TARGET})
    endif()
    if(layer MATCHES "^(frontend|runtime)$")
        target_link_libraries(xolver_${layer} PRIVATE somtparser)
    endif()
    if(layer MATCHES "^(search|runtime)$")
        target_link_libraries(xolver_${layer} PRIVATE cadical)
    endif()
    if(layer STREQUAL "search")
        # Native graph reasoning consumes the IR bridge, without parser APIs.
        target_link_libraries(xolver_${layer} PRIVATE somtparser_ir)
    endif()
    if(layer MATCHES "^(ir|quantifiers|applications)$")
        # Native node storage consumes only the public IR headers.
        # No frontend/parser headers are visible to this layer.
        target_include_directories(xolver_${layer} PRIVATE
            $<TARGET_PROPERTY:somtparser,INTERFACE_INCLUDE_DIRECTORIES>)
    endif()
endforeach()

add_library(xolver_core STATIC ${XOLVER_CORE_OBJECTS})
target_link_libraries(xolver_core PUBLIC xolver_build_options
    somtparser cadical ${XOLVER_POLY_TARGET} ${MPFR_LIBRARIES} ${GMP_LIBRARIES} Threads::Threads)
set_target_properties(xolver_core PROPERTIES POSITION_INDEPENDENT_CODE ON)
include("${CMAKE_SOURCE_DIR}/cmake/ParallelBackends.cmake")

# Evidence-only archive: no search, parser, SAT, portfolio or decision objects.
add_library(xolver_checkers STATIC
    $<TARGET_OBJECTS:xolver_base> $<TARGET_OBJECTS:xolver_ir>
    $<TARGET_OBJECTS:xolver_contracts> $<TARGET_OBJECTS:xolver_evidence>)
target_link_libraries(xolver_checkers PUBLIC somtparser_ir gmpxx ${MPFR_LIBRARIES} ${GMP_LIBRARIES})
target_include_directories(xolver_checkers PUBLIC
    $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    ${GMP_INCLUDE_DIRS} ${MPFR_INCLUDE_DIRS})
set_target_properties(xolver_checkers PROPERTIES POSITION_INDEPENDENT_CODE ON)
