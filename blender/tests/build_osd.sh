#!/bin/sh
# Build a CPU-only OpenSubdiv (libosdCPU + headers) for the cross-check in
# blender/tests/run.py.
#
#   sh blender/tests/build_osd.sh [OSD_SRC] [PREFIX]
#
# OSD_SRC: OpenSubdiv source tree; cloned (v3_8_0) into $PREFIX/src if absent.
# PREFIX:  build/install root (default: ./build-osd). The install prefix
#          $PREFIX/install is what run_cross_check.sh passes as OSD_ROOT.
# Needs cmake and a C++ compiler; uses ninja when available.
set -eu
PREFIX=$(mkdir -p "${2:-build-osd}" && cd "${2:-build-osd}" && pwd)
SRC=${1:-$PREFIX/src}
if [ ! -f "$SRC/CMakeLists.txt" ]; then
  git clone --depth 1 --branch v3_8_0 https://github.com/PixarAnimationStudios/OpenSubdiv.git "$SRC"
fi
GEN=""
command -v ninja >/dev/null 2>&1 && GEN="-G Ninja"
cmake -S "$SRC" -B "$PREFIX/build" $GEN -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX="$PREFIX/install" \
  -DNO_OPENGL=ON -DNO_GLEW=ON -DNO_GLFW=ON -DNO_CUDA=ON -DNO_OPENCL=ON -DNO_CLEW=ON \
  -DNO_METAL=ON -DNO_DX=ON -DNO_TBB=ON -DNO_OMP=ON -DNO_PTEX=ON -DNO_DOC=ON \
  -DNO_EXAMPLES=ON -DNO_TUTORIALS=ON -DNO_REGRESSION=ON -DNO_TESTS=ON
cmake --build "$PREFIX/build" --parallel
cmake --install "$PREFIX/build"
echo "OpenSubdiv installed in $PREFIX/install"
