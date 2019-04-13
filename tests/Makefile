.PHONY: clean

CXX ?= g++
CXXFLAGS ?= -g -O2

tester: tester.cc ../tiny_obj_loader.h
	$(CXX) $(CXXFLAGS) -fsanitize=address -o tester tester.cc

all: tester

check: tester
	./tester

clean:
	rm -rf tester

