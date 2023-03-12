cmake_minimum_required(VERSION 3.14 FATAL_ERROR)
project(Linearize VERSION 0.3.0 LANGUAGES CXX C)

find_package(LLVM REQUIRED CONFIG)


list(APPEND CMAKE_MODULE_PATH ${LLVM_CMAKE_DIR})
include(AddLLVM)

add_llvm_pass_plugin(Linearize linearize.cpp)

target_include_directories(Linearize PUBLIC ${LLVM_INCLUDE_DIRS})
target_link_directories(Linearize PUBLIC ${LLVM_INCLUDE_DIRS})
target_compile_definitions(Linearize PUBLIC ${LLVM_DEFINITIONS})

if (NOT $(LLVM_ENABLE_RTTI))
	target_compile_options(Linearize PUBLIC "-fno-rtti")
endif()

