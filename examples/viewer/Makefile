CXX_FLAGS=-O0 -g -Wno-deprecated-declarations

ifndef PLATFORM
UNAME=$(shell uname -s)

# OSX TEST
ifeq ($(UNAME),Darwin)
PLATFORM=OSX
else
# WINDOWS MINGW TEST
ifeq ($(findstring MINGW, $(UNAME)), MINGW)
	PLATFORM=WINDOWS_MINGW
else
# ASSUME LINUX
	PLATFORM=LINUX
endif
endif

endif
$(info PLATFORM SELECTED:	$(PLATFORM))

ifeq ($(PLATFORM),OSX)
# OSX CONFIGURATION-------------------------------------------------------------
CXX_FLAGS+= -fsanitize=address
GLFW_INC=-I/usr/local/include 
GLFW_LIB_DIR=/usr/local/lib
GLFW_LIBS=-L$(GLFW_LIB_DIR) -lglfw3 -lGLEW
GL_LIBS=-framework OpenGL
# /OSX CONFIGURATION------------------------------------------------------------
else
ifeq ($(PLATFORM),LINUX)
# LINUX CONFIGURATION-----------------------------------------------------------
CXX_FLAGS+= -fsanitize=address
GLFW_INC=-I/usr/local/include 
GLFW_LIB_DIR=/usr/local/lib
GLFW_LIBS=-L$(GLFW_LIB_DIR) -lglfw3 -lGLEW
GL_LIBS=-lGL -lGLU -lX11 -lXrandr -lXi -lXxf86vm -lXcursor -lXinerama -ldl -pthread
# /LINUX CONFIGURATION----------------------------------------------------------
else
ifeq ($(PLATFORM),WINDOWS_MINGW)
# WINDOWS MINGW CONFIGURATION---------------------------------------------------
# Since Windows unfortunately doesn't have any defacto directories for third 
# party libraries, we'll have to force the user to give us them. So we check 
# that the user passed in GLFW-dirs in some way, via flag or environ.
ifndef GLFW_DIR
$(error NO GLFW_DIR SPECIFIED. PASS GLFW_DIR=<dir> TO MAKE)
endif 
ifndef GLEW_DIR
$(error NO GLEW_DIR SPECIFIED. PASS GLEW_DIR=<dir> TO MAKE)
endif
GLFW_INC=-I$(GLFW_DIR)/include
GLFW_LIB_DIR=$(GLFW_DIR)/lib-mingw-w64
GLFW_LIBS= -lglfw3 -L$(GLFW_LIB_DIR)
GL_LIBS=   -lglew32 -lopengl32 -lglu32 -lgdi32 -I$(GLEW_DIR)/include -L$(GLEW_DIR)/bin/Release/x64
# /WINDOWS CONFIGURATION--------------------------------------------------------
else
$(error UNKNOWN PLATFORM "$(PLATFORM)")
endif #ifeq ($(PLATFORM),WINDOWS_MINGW)
endif #ifeq ($(PLATFORM),LINUX)
endif #ifeq ($(PLATFORM),OSX)

all:
	g++ -o objviewer $(CXX_FLAGS) viewer.cc ../../tiny_obj_loader.cc trackball.cc $(GLFW_INC)  $(GLFW_LIBS) $(GL_LIBS)
ifeq ($(PLATFORM), WINDOWS_MINGW)
	cp $(GLEW_DIR)/bin/Release/x64/glew32.dll .
endif
