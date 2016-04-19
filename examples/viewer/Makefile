GLFW_INC=-I/usr/local/include 

# OSX
#GLFW_LIBS=-L/usr/local/lib -lglfw3 -lGLEW
#GL_LIBS=-framework OpenGL

# Linux
GLFW_LIBS=-L/usr/local/lib -lglfw3 -lGLEW
GL_LIBS=-lGL -lGLU -lX11 -lXrandr -lXi -lXxf86vm -lXcursor -lXinerama -ldl -pthread

CXX_FLAGS=-Wno-deprecated-declarations

all:
	g++ -fsanitize=address -O0 -g -o objviewer $(CXX_FLAGS) viewer.cc ../../tiny_obj_loader.cc trackball.cc $(GLFW_INC) $(GL_LIBS) $(GLFW_LIBS)
