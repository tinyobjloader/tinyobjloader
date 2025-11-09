.PHONY: clean

CXX ?= clang++
CXXFLAGS ?= -g -O1
EXTRA_CXXFLAGS ?= -std=c++03 -fsanitize=address
EXTRA_CXXFLAGS_V3 ?= -std=c++14 -fsanitize=address -fno-rtti

tester: tester.cc ../tiny_obj_loader.h
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) -o tester tester.cc

# Note: acutest.h requires exceptions, so we don't use -fno-exceptions here
# but v3 implementation itself doesn't use exceptions
tester_v3: tester_v3.cc ../tinyobj_v3.hh ../tiny_obj_loader.h
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS_V3) -o tester_v3 tester_v3.cc

all: tester tester_v3

check: tester tester_v3
	./tester
	./tester_v3

clean:
	rm -rf tester tester_v3

