GLFW_INC=-I/usr/local/include 
GLFW_LIBS=-L/usr/local/lib -lglfw3 -lglew
GL_LIBS=-framework OpenGL

CXX_FLAGS=-Wno-deprecated-declarations

all:
	g++ -fsanitize=address -O0 -g -o objviewer $(CXX_FLAGS) viewer.cc ../../tiny_obj_loader.cc trackball.cc $(GLFW_INC) $(GL_LIBS) $(GLFW_LIBS)
