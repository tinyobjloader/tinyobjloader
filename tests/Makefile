.PHONY: clean check check_default check_features check_nofastfloat all \
        obj-fuzz llvm-fuzz

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

# fast_float-disabled build: exercise the hand-written fallback float parser
# (TINYOBJLOADER_DISABLE_FAST_FLOAT), otherwise library defaults.
tester_nofastfloat: $(DEPS)
	$(CXX) $(CXXFLAGS) $(EXTRA_CXXFLAGS) -DTINYOBJLOADER_DISABLE_FAST_FLOAT \
		-pthread -I.. -o tester_nofastfloat $(SRCS)

all: tester tester_features tester_nofastfloat

obj-fuzz:
	$(MAKE) -C obj-fuzz

llvm-fuzz:
	$(MAKE) -C llvm-fuzz

# Run all configurations so CI covers the default, feature-enabled, and
# fast_float-disabled code paths.
check: check_default check_features check_nofastfloat

check_default: tester
	./tester

check_features: tester_features
	./tester_features

check_nofastfloat: tester_nofastfloat
	./tester_nofastfloat

clean:
	rm -rf tester tester_features tester_nofastfloat
	$(MAKE) -C obj-fuzz clean
	$(MAKE) -C llvm-fuzz clean
