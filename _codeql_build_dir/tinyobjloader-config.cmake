
####### Expanded from @PACKAGE_INIT@ by configure_package_config_file() #######
####### Any changes to this file will be overwritten by the next CMake run ####
####### The input file was tinyobjloader-config.cmake.in                            ########

get_filename_component(PACKAGE_PREFIX_DIR "${CMAKE_CURRENT_LIST_DIR}/../../../" ABSOLUTE)

macro(set_and_check _var _file)
  set(${_var} "${_file}")
  if(NOT EXISTS "${_file}")
    message(FATAL_ERROR "File or directory ${_file} referenced by variable ${_var} does not exist !")
  endif()
endmacro()

####################################################################################

set(TINYOBJLOADER_VERSION "2.0.0-rc.13")

set_and_check(TINYOBJLOADER_INCLUDE_DIRS "${PACKAGE_PREFIX_DIR}/include")
set_and_check(TINYOBJLOADER_LIBRARY_DIRS "${PACKAGE_PREFIX_DIR}/lib")
set(TINYOBJLOADER_LIBRARIES tinyobjloader)

include("${CMAKE_CURRENT_LIST_DIR}/tinyobjloader-targets.cmake")
