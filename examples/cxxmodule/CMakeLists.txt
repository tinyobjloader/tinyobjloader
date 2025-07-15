cmake_minimum_required(VERSION 4.0.0)

project(CppmExample LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)

add_executable(main main.cc)

# The module interface file requires the tiny_obj_loader header file
target_include_directories(main PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/../..")

# Add the tiny_obj_loader module interface file
target_sources(main PRIVATE
	FILE_SET cxx_modules
	TYPE CXX_MODULES
	BASE_DIRS "${CMAKE_CURRENT_SOURCE_DIR}/../.."
	FILES "${CMAKE_CURRENT_SOURCE_DIR}/../../tiny_obj_loader.cppm"
)

