.PHONY: clean

CXX ?= clang++
CXXFLAGS ?= -g -O1
EXTRA_CXXFLAGS ?= -std=c++11 -fsanitize=address

tester: tester.cc ../tiny_obj_loader.h ../experimental/stream/stream_obj_loader.cc ../experimental/stream/stream_obj_loader.h opt/loadobjopt_multithread.inc
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) -pthread -I.. -o tester tester.cc ../experimental/stream/stream_obj_loader.cc

all: tester

obj-fuzz:
	$(MAKE) -C obj-fuzz

llvm-fuzz:
	$(MAKE) -C llvm-fuzz

check: tester
	./tester

clean:
	rm -rf tester
	$(MAKE) -C obj-fuzz clean
	$(MAKE) -C llvm-fuzz clean
