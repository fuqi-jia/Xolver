cmake_minimum_required(VERSION 3.16)

add_executable(xolver-cli
    main.cpp
)

find_package(Threads REQUIRED)
target_link_libraries(xolver-cli PRIVATE xolver_core Threads::Threads)

set_target_properties(xolver-cli PROPERTIES
    OUTPUT_NAME xolver
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)

add_executable(xolver-sv sv.cpp)
target_link_libraries(xolver-sv PRIVATE xolver_core Threads::Threads)
set_target_properties(xolver-sv PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)

add_executable(xolver-api-examples api_examples.cpp)
target_link_libraries(xolver-api-examples PRIVATE xolver_core gmpxx Threads::Threads)
set_target_properties(xolver-api-examples PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)

foreach(tool parallel-worker parallel-examples)
    string(REPLACE "-" "_" source "${tool}")
    add_executable(xolver-${tool} ${source}.cpp)
    target_link_libraries(xolver-${tool} PRIVATE xolver_core Threads::Threads)
    set_target_properties(xolver-${tool} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
endforeach()

add_executable(xolver-asp asp.cpp)
target_link_libraries(xolver-asp PRIVATE xolver_core gmpxx Threads::Threads)
set_target_properties(xolver-asp PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
