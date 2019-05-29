.PHONY: clean

CXX = clang++
CXXFLAGS ?= -g -O1

tester: tester.cc ../tiny_obj_loader.h
	$(CXX) $(CXXFLAGS) -std=c++11 -fsanitize=address -o tester tester.cc

all: tester

check: tester
	./tester

clean:
	rm -rf tester

