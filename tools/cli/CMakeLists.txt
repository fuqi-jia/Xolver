cmake_minimum_required(VERSION 3.16)

add_executable(nlcolver-cli
    main.cpp
)

target_link_libraries(nlcolver-cli PRIVATE nlcolver_core)

set_target_properties(nlcolver-cli PROPERTIES
    OUTPUT_NAME nlcolver
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)
