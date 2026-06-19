.PHONY: clean check check_default check_features check_nofastfloat all \
        obj-fuzz llvm-fuzz \
        check_c check_c_default check_c_features check_tess check_c_freestanding

CXX ?= clang++
CXXFLAGS ?= -g -O1
EXTRA_CXXFLAGS ?= -std=c++11 -fsanitize=address

# ---- pure C11 loader (tiny_obj_c) -------------------------------------------
CC ?= clang
CFLAGS ?= -g -O1
EXTRA_CFLAGS ?= -std=c11 -Wall -Wextra -fsanitize=address,undefined
C_SRCS = ../tiny_obj_c.c ../tobj_tess.c
C_DEPS = ../tiny_obj_c.h ../tiny_obj_c_pub.inc ../tiny_obj_c_impl.inc \
         ../tobj_tess.h ../tobj_tess_pub.inc ../tobj_tess_impl.inc acutest.h

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

all: tester tester_features tester_nofastfloat tester_c tess_tester \
     tester_c_features

# Default C build: scalar, single-threaded, file I/O + mmap, both precisions.
tester_c: tester_c.c $(C_SRCS) $(C_DEPS)
	$(CC) $(CFLAGS) $(EXTRA_CFLAGS) -DTOBJ_ENABLE_FILE_IO -DTOBJ_ENABLE_MMAP \
		-I.. -o tester_c tester_c.c $(C_SRCS) -lm

# Feature C build: exercise SIMD + multithreading paths.
tester_c_features: tester_c.c $(C_SRCS) $(C_DEPS)
	$(CC) $(CFLAGS) $(EXTRA_CFLAGS) -DTOBJ_ENABLE_FILE_IO -DTOBJ_ENABLE_MMAP \
		-DTOBJ_ENABLE_SIMD -DTOBJ_ENABLE_MULTITHREADING -pthread \
		-I.. -o tester_c_features tester_c.c $(C_SRCS) -lm

# Tessellator unit/property tests.
tess_tester: tess_tester.c ../tobj_tess.c ../tobj_tess.h ../tobj_tess_pub.inc \
             ../tobj_tess_impl.inc acutest.h
	$(CC) $(CFLAGS) $(EXTRA_CFLAGS) -I.. -o tess_tester tess_tester.c \
		../tobj_tess.c -lm

# Freestanding compile/link check: no libc, caller-supplied allocator.
tester_c_freestanding: tester_c_freestanding.c $(C_SRCS) $(C_DEPS)
	$(CC) $(CFLAGS) -std=c11 -Wall -Wextra -ffreestanding -DTOBJ_NO_LIBC \
		-I.. -o tester_c_freestanding tester_c_freestanding.c $(C_SRCS)

obj-fuzz:
	$(MAKE) -C obj-fuzz

llvm-fuzz:
	$(MAKE) -C llvm-fuzz

# Run all configurations so CI covers the default, feature-enabled, and
# fast_float-disabled code paths.
check: check_default check_features check_nofastfloat check_c

check_default: tester
	./tester

check_features: tester_features
	./tester_features

check_nofastfloat: tester_nofastfloat
	./tester_nofastfloat

# Pure C11 test suite.
check_c: check_c_default check_c_features check_tess check_c_freestanding

check_c_default: tester_c
	./tester_c

check_c_features: tester_c_features
	./tester_c_features

check_tess: tess_tester
	./tess_tester

check_c_freestanding: tester_c_freestanding
	./tester_c_freestanding

clean:
	rm -rf tester tester_features tester_nofastfloat \
	       tester_c tester_c_features tess_tester tester_c_freestanding
	$(MAKE) -C obj-fuzz clean
	$(MAKE) -C llvm-fuzz clean
