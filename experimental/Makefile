UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
LD_FLAGS=-framework OpenGL -lglfw3 -lglew
endif

all:
	clang -c trackball.c
	clang -o viewer -g -O0 -pedantic -ansi -Wno-deprecated-declarations viewer-c.c trackball.o $(LD_FLAGS)
#	clang -pedantic -ansi -Weverything -Wno-deprecated-declarations viewer-c.c trackball.o -framework OpenGL -lglfw3 -lglew
