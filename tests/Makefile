.PHONY: clean

CXX ?= g++
CXXFLAGS ?= -g -O2

tester: tester.cc
	$(CXX) $(CXXFLAGS) -o tester tester.cc

all: tester

check: tester
	./tester	

clean:
	rm -rf tester

