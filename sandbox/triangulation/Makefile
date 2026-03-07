# Makefile for standalone triangulation algorithm testing.
#
# Usage:
#   make          — build the test binary
#   make test     — build and run all tests
#   make benchmark — build and run the benchmark
#   make clean    — remove build artifacts

CXX      ?= g++
CXXFLAGS ?= -std=c++11 -O2 -Wall -Wextra
TARGET    = triangulation_test
BENCH     = benchmark

.PHONY: all test bench clean

all: $(TARGET) $(BENCH)

$(TARGET): main.cc triangulation.h
	$(CXX) $(CXXFLAGS) -o $@ main.cc

$(BENCH): benchmark.cc triangulation.h
	$(CXX) $(CXXFLAGS) -o $@ benchmark.cc

test: $(TARGET)
	./$(TARGET)

bench: $(BENCH)
	./$(BENCH) --quick

clean:
	rm -f $(TARGET) $(BENCH)
