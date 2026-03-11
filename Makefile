# Use this for strict compilation check(will work on clang 3.8+)
#EXTRA_CXXFLAGS := -fsanitize=address,undefined -Wall -Werror -Weverything -DTINYOBJLOADER_ENABLE_THREADED=1 -Wno-c++98-compat
#EXTRA_CXXFLAGS := -Weverything -Wall -DTINYOBJLOADER_ENABLE_THREADED=1 -Wno-c++98-compat
# Note: fast_float is now bundled by default (no separate include path needed).
# Define TINYOBJLOADER_DISABLE_FAST_FLOAT to opt out of the bundled parser.
EXTRA_CXXFLAGS :=

all:
	g++  $(EXTRA_CXXFLAGS) -DTINYOBJLOADER_USE_DOUBLE=1 -std=c++11 -g -O0 -o loader_example loader_example.cc
	#clang++  $(EXTRA_CXXFLAGS) -DTINYOBJLOADER_USE_DOUBLE=1 -std=c++11 -g -O2 -o loader_example loader_example.cc

lint:
	./cpplint.py tiny_gltf_loader.h
