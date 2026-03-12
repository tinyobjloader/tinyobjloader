.PHONY: all clean run

CXX ?= clang++
CXXFLAGS ?= -g -O1 -std=c++11
SANITIZERS ?= -fsanitize=address,undefined
CPPFLAGS ?= -DTINYOBJLOADER_USE_MULTITHREADING

TARGET := obj_fuzz

all: $(TARGET)

$(TARGET): obj_fuzz.cc ../fuzz_common.h ../../tiny_obj_loader.h ../../tiny_obj_loader.cc ../../experimental/stream/stream_obj_loader.cc ../../experimental/stream/stream_obj_loader.h
	$(CXX) $(CXXFLAGS) $(SANITIZERS) $(CPPFLAGS) -pthread -I../.. -I.. -o $(TARGET) obj_fuzz.cc ../../tiny_obj_loader.cc ../../experimental/stream/stream_obj_loader.cc

run: $(TARGET)
	./$(TARGET) --iterations 1000 --seed 1

clean:
	rm -f $(TARGET)
