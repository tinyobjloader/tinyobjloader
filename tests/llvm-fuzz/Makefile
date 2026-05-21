.PHONY: all clean run

CXX := clang++
CXXFLAGS ?= -g -O1 -std=c++11
SANITIZERS ?= -fsanitize=fuzzer,address,undefined
CPPFLAGS ?= -DTINYOBJLOADER_USE_MULTITHREADING

TARGET := fuzz_loaders

all: $(TARGET)

$(TARGET): fuzz_loaders.cc ../fuzz_common.h ../../tiny_obj_loader.h ../../tiny_obj_loader.cc ../../experimental/stream/stream_obj_loader.cc ../../experimental/stream/stream_obj_loader.h
	$(CXX) $(CXXFLAGS) $(SANITIZERS) $(CPPFLAGS) -pthread -I../.. -I.. -o $(TARGET) fuzz_loaders.cc ../../tiny_obj_loader.cc ../../experimental/stream/stream_obj_loader.cc

run: $(TARGET)
	./$(TARGET) corpus -max_total_time=600 -rss_limit_mb=2048 -max_len=4096

clean:
	rm -f $(TARGET)
