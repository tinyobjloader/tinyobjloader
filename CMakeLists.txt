#Tiny Object Loader Cmake configuration file.
#This configures the Cmake system with multiple properties, depending
#on the platform and configuration it is set to build in.
project(tinyobjloader)
cmake_minimum_required(VERSION 2.8.6)

#Folder Shortcuts
set(TINYOBJLOADEREXAMPLES_DIR ${CMAKE_CURRENT_SOURCE_DIR}/examples)

set(tinyobjloader-Source
	${CMAKE_CURRENT_SOURCE_DIR}/tiny_obj_loader.h
	${CMAKE_CURRENT_SOURCE_DIR}/tiny_obj_loader.cc
	)

set(tinyobjloader-Test-Source
	${CMAKE_CURRENT_SOURCE_DIR}/test.cc
	)

set(tinyobjloader-examples-objsticher
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_writer.h
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_writer.cc
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_sticher.cc
	)

add_library(tinyobjloader
			${tinyobjloader-Source}
	)

add_executable(test ${tinyobjloader-Test-Source})
target_link_libraries(test tinyobjloader)

add_executable(obj_sticher ${tinyobjloader-examples-objsticher})
target_link_libraries(obj_sticher tinyobjloader)