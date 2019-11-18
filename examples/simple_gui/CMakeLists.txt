cmake_minimum_required(VERSION 3.5)

set(BUILD_TARGET "simplegui")

project(${BUILD_TARGET})

find_package(OpenGL REQUIRED)
find_package(glfw3 REQUIRED)

set(CMAKE_CXX_STANDARD 11)

set(SIMPLEGUI_SOURCES
    glad.c
    main.cc
    trackball.cc
    imgui/imgui.cpp
    imgui/imgui_draw.cpp
    imgui/imgui_widgets.cpp)

add_executable(${BUILD_TARGET} ${SIMPLEGUI_SOURCES})

target_link_libraries(${BUILD_TARGET} glfw ${OPENGL_LIBRARIES} ${CMAKE_DL_LIBS})

# [VisualStudio]
if(WIN32)
  # Set ${BUILD_TARGET} as a startup project for VS IDE
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT ${BUILD_TARGET})

  # For easier debugging in VS IDE(cmake 3.8.0 or later required) Set working
  # directory to ${BUILD_TARGET} git repo root.
  if(CMAKE_VERSION VERSION_GREATER 3.8.0)
    set_target_properties(${BUILD_TARGET}
                          PROPERTIES VS_DEBUGGER_WORKING_DIRECTORY
                                     "${CMAKE_CURRENT_SOURCE_DIR}")
  endif()
endif()
