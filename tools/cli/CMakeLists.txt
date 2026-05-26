cmake_minimum_required(VERSION 3.16)

add_executable(zolver-cli
    main.cpp
)

target_link_libraries(zolver-cli PRIVATE zolver_core)

set_target_properties(zolver-cli PROPERTIES
    OUTPUT_NAME zolver
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)
