#Tiny Object Loader Cmake configuration file.
#This configures the Cmake system with multiple properties, depending
#on the platform and configuration it is set to build in.
project(tinyobjloader)
cmake_minimum_required(VERSION 2.8.6)
set(TINYOBJLOADER_SOVERSION 1)
set(TINYOBJLOADER_VERSION 1.0.4)

#Folder Shortcuts
set(TINYOBJLOADEREXAMPLES_DIR ${CMAKE_CURRENT_SOURCE_DIR}/examples)

set(tinyobjloader-Source
	${CMAKE_CURRENT_SOURCE_DIR}/tiny_obj_loader.h
	${CMAKE_CURRENT_SOURCE_DIR}/tiny_obj_loader.cc
	)

set(tinyobjloader-Example-Source
	${CMAKE_CURRENT_SOURCE_DIR}/loader_example.cc
	)

set(tinyobjloader-examples-objsticher
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_writer.h
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_writer.cc
	${TINYOBJLOADEREXAMPLES_DIR}/obj_sticher/obj_sticher.cc
	)

#Install destinations
set(TINYOBJLOADER_CMAKE_DIR lib/cmake)
set(TINYOBJLOADER_INCLUDE_DIR include)
set(TINYOBJLOADER_LIBRARY_DIR lib)

option(TINYOBJLOADER_BUILD_TEST_LOADER "Build Example Loader Application" OFF)
option(TINYOBJLOADER_COMPILATION_SHARED "Build as shared library" OFF)

if (TINYOBJLOADER_COMPILATION_SHARED)
	add_library(tinyobjloader SHARED ${tinyobjloader-Source})
	set_target_properties(tinyobjloader PROPERTIES
		SOVERSION ${TINYOBJLOADER_SOVERSION}
	)
else()
	add_library(tinyobjloader STATIC ${tinyobjloader-Source})
endif()

set_target_properties(tinyobjloader PROPERTIES VERSION ${TINYOBJLOADER_VERSION})

target_include_directories(tinyobjloader INTERFACE
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
	$<INSTALL_INTERFACE:${TINYOBJLOADER_INCLUDE_DIR}>
	)

export(TARGETS tinyobjloader FILE ${PROJECT_NAME}-targets.cmake)

if(TINYOBJLOADER_BUILD_TEST_LOADER)
  add_executable(test_loader ${tinyobjloader-Example-Source})
  target_link_libraries(test_loader tinyobjloader)
endif()

option(TINYOBJLOADER_BUILD_OBJ_STICHER "Build OBJ Sticher Application" OFF)
if (TINYOBJLOADER_BUILD_OBJ_STICHER)
  add_executable(obj_sticher ${tinyobjloader-examples-objsticher})
  target_link_libraries(obj_sticher tinyobjloader)

  install ( TARGETS
    obj_sticher
    DESTINATION
    bin
    )
endif()

#Write CMake package config files
include(CMakePackageConfigHelpers)

configure_package_config_file(
  tinyobjloader-config.cmake.in
  tinyobjloader-config.cmake
  INSTALL_DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  PATH_VARS
  TINYOBJLOADER_INCLUDE_DIR
  TINYOBJLOADER_LIBRARY_DIR
  NO_CHECK_REQUIRED_COMPONENTS_MACRO
  )

write_basic_package_version_file(tinyobjloader-config-version.cmake
  VERSION
  ${TINYOBJLOADER_VERSION}
  COMPATIBILITY
  SameMajorVersion
  )

#Installation
install ( TARGETS
  tinyobjloader
  EXPORT ${PROJECT_NAME}-targets
  DESTINATION
  ${TINYOBJLOADER_LIBRARY_DIR}
  PUBLIC_HEADER DESTINATION
  ${TINYOBJLOADER_INCLUDE_DIR}
  RUNTIME DESTINATION
  bin
  )
install ( EXPORT
  ${PROJECT_NAME}-targets
  DESTINATION
  ${TINYOBJLOADER_LIBRARY_DIR}
  )
install ( FILES
  tiny_obj_loader.h
  DESTINATION
  ${TINYOBJLOADER_INCLUDE_DIR}
  )
install ( FILES
  "${CMAKE_CURRENT_BINARY_DIR}/tinyobjloader-config.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/tinyobjloader-config-version.cmake"
  DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  )
