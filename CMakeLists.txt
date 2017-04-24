#Tiny Object Loader Cmake configuration file.
#This configures the Cmake system with multiple properties, depending
#on the platform and configuration it is set to build in.
project(tinyobjloader)
cmake_minimum_required(VERSION 2.8.11)
set(TINYOBJLOADER_SOVERSION 1)
set(TINYOBJLOADER_VERSION 1.0.4)

#optional double precision support
option(TINYOBJLOADER_USE_DOUBLE "Build library with double precision instead of single (float)" OFF)

if(TINYOBJLOADER_USE_DOUBLE)
  add_definitions(-DTINYOBJLOADER_USE_DOUBLE)
  set(LIBRARY_NAME ${PROJECT_NAME}_double)
else()
  set(LIBRARY_NAME ${PROJECT_NAME})
endif()


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
include(GNUInstallDirs)

set(TINYOBJLOADER_CMAKE_DIR ${CMAKE_INSTALL_LIBDIR}/${PROJECT_NAME}/cmake)
set(TINYOBJLOADER_DOC_DIR ${CMAKE_INSTALL_DOCDIR})
set(TINYOBJLOADER_INCLUDE_DIR ${CMAKE_INSTALL_INCLUDEDIR})
set(TINYOBJLOADER_LIBRARY_DIR ${CMAKE_INSTALL_LIBDIR})
set(TINYOBJLOADER_PKGCONFIG_DIR ${CMAKE_INSTALL_LIBDIR}/pkgconfig)
set(TINYOBJLOADER_RUNTIME_DIR ${CMAKE_INSTALL_BINDIR})

option(TINYOBJLOADER_BUILD_TEST_LOADER "Build Example Loader Application" OFF)
option(TINYOBJLOADER_COMPILATION_SHARED "Build as shared library" OFF)

if(TINYOBJLOADER_COMPILATION_SHARED)
  add_library(${LIBRARY_NAME} SHARED ${tinyobjloader-Source})
  set_target_properties(${LIBRARY_NAME} PROPERTIES
    SOVERSION ${TINYOBJLOADER_SOVERSION}
  )
else()
  add_library(${LIBRARY_NAME} STATIC ${tinyobjloader-Source})
endif()

set_target_properties(${LIBRARY_NAME} PROPERTIES VERSION ${TINYOBJLOADER_VERSION})

target_include_directories(${LIBRARY_NAME} INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
  $<INSTALL_INTERFACE:${TINYOBJLOADER_INCLUDE_DIR}>
  )

export(TARGETS ${LIBRARY_NAME} FILE ${PROJECT_NAME}-targets.cmake)

if(TINYOBJLOADER_BUILD_TEST_LOADER)
  add_executable(test_loader ${tinyobjloader-Example-Source})
  target_link_libraries(test_loader ${LIBRARY_NAME})
endif()

option(TINYOBJLOADER_BUILD_OBJ_STICHER "Build OBJ Sticher Application" OFF)
if(TINYOBJLOADER_BUILD_OBJ_STICHER)
  add_executable(obj_sticher ${tinyobjloader-examples-objsticher})
  target_link_libraries(obj_sticher ${LIBRARY_NAME})

  install(TARGETS
    obj_sticher
    DESTINATION
    ${TINYOBJLOADER_RUNTIME_DIR}
    )
endif()

#Write CMake package config files
include(CMakePackageConfigHelpers)

configure_package_config_file(
  ${PROJECT_NAME}-config.cmake.in
  ${LIBRARY_NAME}-config.cmake
  INSTALL_DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  PATH_VARS
  TINYOBJLOADER_INCLUDE_DIR
  TINYOBJLOADER_LIBRARY_DIR
  NO_CHECK_REQUIRED_COMPONENTS_MACRO
  )

write_basic_package_version_file(${LIBRARY_NAME}-config-version.cmake
  VERSION
  ${TINYOBJLOADER_VERSION}
  COMPATIBILITY
  SameMajorVersion
  )

#pkg-config file
configure_file(${PROJECT_NAME}.pc.in ${LIBRARY_NAME}.pc @ONLY)

#Installation
install(TARGETS
  ${LIBRARY_NAME}
  EXPORT ${PROJECT_NAME}-targets
  DESTINATION
  ${TINYOBJLOADER_LIBRARY_DIR}
  PUBLIC_HEADER DESTINATION
  ${TINYOBJLOADER_INCLUDE_DIR}
  RUNTIME DESTINATION
  ${TINYOBJLOADER_RUNTIME_DIR}
  )
install(EXPORT
  ${PROJECT_NAME}-targets
  DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  )
install(FILES
  tiny_obj_loader.h
  DESTINATION
  ${TINYOBJLOADER_INCLUDE_DIR}
  )
install(FILES
  LICENSE
  DESTINATION
  ${TINYOBJLOADER_DOC_DIR}
  )
install(FILES
  "${CMAKE_CURRENT_BINARY_DIR}/${LIBRARY_NAME}-config.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/${LIBRARY_NAME}-config-version.cmake"
  DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  )
install(FILES
  "${CMAKE_CURRENT_BINARY_DIR}/${LIBRARY_NAME}.pc"
  DESTINATION
  ${TINYOBJLOADER_PKGCONFIG_DIR}
  )
