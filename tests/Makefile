.PHONY: clean

CXX ?= clang++
CXXFLAGS ?= -g -O1
EXTRA_CXXFLAGS ?= -std=c++11 -fsanitize=address

tester: tester.cc ../tiny_obj_loader.h
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) -o tester tester.cc

all: tester

check: tester
	./tester

clean:
	rm -rf tester

