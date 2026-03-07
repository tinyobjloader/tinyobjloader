# Makefile for standalone triangulation algorithm testing.
#
# Usage:
#   make          — build the test binary
#   make test     — build and run all tests
#   make clean    — remove build artifacts

CXX      ?= g++
CXXFLAGS ?= -std=c++11 -O2 -Wall -Wextra
TARGET    = triangulation_test

.PHONY: all test clean

all: $(TARGET)

$(TARGET): main.cc triangulation.h
	$(CXX) $(CXXFLAGS) -o $@ main.cc

test: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)
