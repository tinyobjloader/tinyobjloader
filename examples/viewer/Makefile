GLFW_INC=-I/usr/local/include 

UNAME=$(shell uname -s)

ifeq ($(UNAME),Darwin)
# OSX
GLFW_LIBS=-L/usr/local/lib -lglfw3 -lGLEW
GL_LIBS=-framework OpenGL
else
# Assume Linux
GLFW_LIBS=-L/usr/local/lib -lglfw3 -lGLEW
GL_LIBS=-lGL -lGLU -lX11 -lXrandr -lXi -lXxf86vm -lXcursor -lXinerama -ldl -pthread
endif

CXX_FLAGS=-Wno-deprecated-declarations

all:
	g++ -fsanitize=address -O0 -g -o objviewer $(CXX_FLAGS) viewer.cc ../../tiny_obj_loader.cc trackball.cc $(GLFW_INC) $(GL_LIBS) $(GLFW_LIBS)
