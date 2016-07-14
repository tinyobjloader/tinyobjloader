all:
	clang -c trackball.c
	clang -pedantic -ansi -Wno-deprecated-declarations viewer-c.c trackball.o -framework OpenGL -lglfw3 -lglew
#	clang -pedantic -ansi -Weverything -Wno-deprecated-declarations viewer-c.c trackball.o -framework OpenGL -lglfw3 -lglew
