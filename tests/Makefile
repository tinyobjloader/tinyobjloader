.PHONY: clean check check_default check_features all obj-fuzz llvm-fuzz

CXX ?= clang++
CXXFLAGS ?= -g -O1
EXTRA_CXXFLAGS ?= -std=c++11 -fsanitize=address

# Optional feature macros exercised by the `tester_features` build.
FEATURE_FLAGS = -DTINYOBJLOADER_USE_MULTITHREADING \
                -DTINYOBJLOADER_USE_SIMD \
                -DTINYOBJLOADER_ENABLE_EXCEPTION

SRCS = tester.cc ../experimental/stream/stream_obj_loader.cc
DEPS = tester.cc ../tiny_obj_loader.h \
       ../experimental/stream/stream_obj_loader.cc \
       ../experimental/stream/stream_obj_loader.h \
       opt/loadobjopt_multithread.inc

# Default build: library defaults — no SIMD, no multithreading, no exceptions.
# (-pthread is required only because the experimental stream loader links
#  std::thread; the library's own threading stays disabled.)
tester: $(DEPS)
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) -pthread -I.. -o tester $(SRCS)

# Feature build: exercise the optional multithreading / SIMD / exception paths.
tester_features: $(DEPS)
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) $(FEATURE_FLAGS) -pthread -I.. \
		-o tester_features $(SRCS)

all: tester tester_features

obj-fuzz:
	$(MAKE) -C obj-fuzz

llvm-fuzz:
	$(MAKE) -C llvm-fuzz

# Run both configurations so CI covers the default and feature-enabled paths.
check: check_default check_features

check_default: tester
	./tester

check_features: tester_features
	./tester_features

clean:
	rm -rf tester tester_features
	$(MAKE) -C obj-fuzz clean
	$(MAKE) -C llvm-fuzz clean
