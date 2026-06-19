#Tiny Object Loader Cmake configuration file.
#This configures the Cmake system with multiple properties, depending
#on the platform and configuration it is set to build in.
cmake_minimum_required(VERSION 3.16)
project(tinyobjloader CXX)
set(TINYOBJLOADER_SOVERSION 2)
set(TINYOBJLOADER_VERSION 2.0.0-rc.13)
set(PY_TARGET "pytinyobjloader")

#optional double precision support
option(TINYOBJLOADER_USE_DOUBLE "Build library with double precision instead of single (float)" OFF)
option(TINYOBJLOADER_WITH_PYTHON "Build Python module(for developer). Use pyproject.toml/setup.py to build Python module for end-users" OFF)
option(TINYOBJLOADER_PREFER_LOCAL_PYTHON_INSTALLATION
      "Prefer locally-installed Python interpreter than system or conda/brew installed Python. Please specify your Python interpreter   with `Python3_EXECUTABLE` cmake option if you enable this option."
      OFF)

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/sanitizers)
find_package(Sanitizers) # Address sanitizer (-DSANITIZE_ADDRESS=ON)


if(TINYOBJLOADER_USE_DOUBLE)
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

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Build standalone .so for Python binding(for developer)
if (TINYOBJLOADER_WITH_PYTHON)

  if(TINYOBJLOADER_PREFER_LOCAL_PYTHON_INSTALLATION)
    #message(STATUS "Local Python")
    set(Python3_FIND_FRAMEWORK NEVER) # Do not search framework python
    set(Python3_FIND_STRATEGY LOCATION)
    set(Python3_FIND_REGISTRY NEVER) # Windows only
  else()
    set(Python3_FIND_FRAMEWORK LAST
    )# Prefer Brew/Conda to Apple framework python
  endif()

  find_package(
    Python3
    COMPONENTS Interpreter Development
    REQUIRED)

  find_package(pybind11 CONFIG REQUIRED)

endif()



add_library(${LIBRARY_NAME} ${tinyobjloader-Source})
add_sanitizers(${LIBRARY_NAME})

if(BUILD_SHARED_LIBS)
  set_target_properties(${LIBRARY_NAME} PROPERTIES
    SOVERSION ${TINYOBJLOADER_SOVERSION}
    WINDOWS_EXPORT_ALL_SYMBOLS ON
  )
endif()

if(TINYOBJLOADER_USE_DOUBLE)
  target_compile_definitions(${LIBRARY_NAME} PUBLIC TINYOBJLOADER_USE_DOUBLE)
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

if (TINYOBJLOADER_WITH_PYTHON)
  # pybind11 method:
  pybind11_add_module(${PY_TARGET} ${CMAKE_SOURCE_DIR}/python/bindings.cc ${CMAKE_SOURCE_DIR}/python/tiny_obj_loader.cc)

  add_sanitizers(${PY_TARGET})
  set_target_properties(${PY_TARGET} PROPERTIES OUTPUT_NAME "tinyobjloader")

  # copy .so to jdepp/
  add_custom_command(
    TARGET ${PY_TARGET}
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E copy "$<TARGET_FILE:${PY_TARGET}>"
            "${CMAKE_SOURCE_DIR}/python/$<TARGET_FILE_NAME:${PY_TARGET}>"
    COMMENT "copying tinyobjloader native python module file to python/"
    VERBATIM)

endif()

# ---------------------------------------------------------------------------
# Pure C11 loader (tiny_obj_c + tobj_tess)
# ---------------------------------------------------------------------------
option(TINYOBJLOADER_BUILD_C_LIBRARY "Build the pure-C11 loader (tiny_obj_c)" ON)
option(TINYOBJLOADER_C_ENABLE_FILE_IO "tiny_obj_c: file loading helpers" ON)
option(TINYOBJLOADER_C_ENABLE_MMAP "tiny_obj_c: mmap-based file loading" OFF)
option(TINYOBJLOADER_C_ENABLE_SIMD "tiny_obj_c: SIMD newline scan" OFF)
option(TINYOBJLOADER_C_ENABLE_MULTITHREADING "tiny_obj_c: multithreaded parse" OFF)
option(TINYOBJLOADER_C_BUILD_TESTS "tiny_obj_c: build C test drivers" OFF)

if(TINYOBJLOADER_BUILD_C_LIBRARY)
  enable_language(C)
  set(CMAKE_C_STANDARD 11)
  set(CMAKE_C_STANDARD_REQUIRED ON)
  set(CMAKE_C_EXTENSIONS OFF)

  add_library(tinyobjloader_c
    ${CMAKE_CURRENT_SOURCE_DIR}/tiny_obj_c.c
    ${CMAKE_CURRENT_SOURCE_DIR}/tobj_tess.c)
  add_sanitizers(tinyobjloader_c)
  target_include_directories(tinyobjloader_c PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:${TINYOBJLOADER_INCLUDE_DIR}>)

  if(TINYOBJLOADER_C_ENABLE_FILE_IO)
    target_compile_definitions(tinyobjloader_c PUBLIC TOBJ_ENABLE_FILE_IO)
  endif()
  if(TINYOBJLOADER_C_ENABLE_MMAP)
    target_compile_definitions(tinyobjloader_c PUBLIC TOBJ_ENABLE_MMAP)
  endif()
  if(TINYOBJLOADER_C_ENABLE_SIMD)
    target_compile_definitions(tinyobjloader_c PUBLIC TOBJ_ENABLE_SIMD)
  endif()
  if(TINYOBJLOADER_C_ENABLE_MULTITHREADING)
    find_package(Threads REQUIRED)
    target_compile_definitions(tinyobjloader_c PUBLIC TOBJ_ENABLE_MULTITHREADING)
    target_link_libraries(tinyobjloader_c PUBLIC Threads::Threads)
  endif()

  install(TARGETS tinyobjloader_c
    EXPORT ${PROJECT_NAME}-targets
    DESTINATION ${TINYOBJLOADER_LIBRARY_DIR})
  install(FILES
    tiny_obj_c.h tiny_obj_c_pub.inc tiny_obj_c_impl.inc
    tobj_tess.h tobj_tess_pub.inc tobj_tess_impl.inc
    DESTINATION ${TINYOBJLOADER_INCLUDE_DIR})

  if(TINYOBJLOADER_C_BUILD_TESTS)
    add_executable(tester_c tests/tester_c.c)
    target_link_libraries(tester_c tinyobjloader_c)
    target_compile_definitions(tester_c PRIVATE TOBJ_ENABLE_FILE_IO)
    add_executable(tess_tester tests/tess_tester.c
      ${CMAKE_CURRENT_SOURCE_DIR}/tobj_tess.c)
    target_include_directories(tess_tester PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
    if(UNIX)
      target_link_libraries(tester_c m)
      target_link_libraries(tess_tester m)
    endif()
    enable_testing()
    add_test(NAME tester_c COMMAND tester_c
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests)
    add_test(NAME tess_tester COMMAND tess_tester)
  endif()

  if(DEFINED ENV{LIB_FUZZING_ENGINE})
    add_executable(fuzz_tobj_c fuzzer/fuzz_tobj_c.c)
    target_link_libraries(fuzz_tobj_c tinyobjloader_c $ENV{LIB_FUZZING_ENGINE})
  endif()
endif()

#Write CMake package config files
include(CMakePackageConfigHelpers)

configure_package_config_file(
  ${PROJECT_NAME}-config.cmake.in
  ${PROJECT_NAME}-config.cmake
  INSTALL_DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  PATH_VARS
  TINYOBJLOADER_INCLUDE_DIR
  TINYOBJLOADER_LIBRARY_DIR
  NO_CHECK_REQUIRED_COMPONENTS_MACRO
  )

write_basic_package_version_file(${PROJECT_NAME}-config-version.cmake
  VERSION
  ${TINYOBJLOADER_VERSION}
  COMPATIBILITY
  SameMajorVersion
  )

#pkg-config file
configure_file(${PROJECT_NAME}.pc.in ${LIBRARY_NAME}.pc @ONLY)

if(DEFINED ENV{LIB_FUZZING_ENGINE})
  add_executable(fuzz_ParseFromString fuzzer/fuzz_ParseFromString.cc)
  target_link_libraries(fuzz_ParseFromString ${LIBRARY_NAME} $ENV{LIB_FUZZING_ENGINE})
endif()

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
  NAMESPACE
  tinyobjloader::
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
  "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}-config.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}-config-version.cmake"
  DESTINATION
  ${TINYOBJLOADER_CMAKE_DIR}
  )
install(FILES
  "${CMAKE_CURRENT_BINARY_DIR}/${LIBRARY_NAME}.pc"
  DESTINATION
  ${TINYOBJLOADER_PKGCONFIG_DIR}
  )

if(NOT TARGET uninstall)
  configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/cmake_uninstall.cmake.in
    ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake IMMEDIATE @ONLY)

  add_custom_target(
    uninstall COMMAND ${CMAKE_COMMAND} -P
                      ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake)
endif()
