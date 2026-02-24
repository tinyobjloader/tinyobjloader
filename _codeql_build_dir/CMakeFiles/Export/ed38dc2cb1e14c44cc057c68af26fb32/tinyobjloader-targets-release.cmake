#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "tinyobjloader::tinyobjloader" for configuration "Release"
set_property(TARGET tinyobjloader::tinyobjloader APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(tinyobjloader::tinyobjloader PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELEASE "CXX"
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libtinyobjloader.a"
  )

list(APPEND _cmake_import_check_targets tinyobjloader::tinyobjloader )
list(APPEND _cmake_import_check_files_for_tinyobjloader::tinyobjloader "${_IMPORT_PREFIX}/lib/libtinyobjloader.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
