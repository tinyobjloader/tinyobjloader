#!/bin/bash
# Build script for TinyObjLoader v3 Python bindings

set -e

echo "=========================================="
echo "TinyObjLoader v3 Python Bindings Builder"
echo "=========================================="

# Check Python version
PYTHON=${PYTHON:-python3}
PYTHON_VERSION=$($PYTHON -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')")
echo "Python version: $PYTHON_VERSION"

if [ "$(printf '%s\n' "$PYTHON_VERSION" "3.10" | sort -V | head -n1)" != "3.10" ]; then
    echo "ERROR: Python 3.10+ required, found $PYTHON_VERSION"
    exit 1
fi

# Detect platform
UNAME_S=$(uname -s)
echo "Platform: $UNAME_S"

# Set compiler
CXX=${CXX:-g++}
echo "Compiler: $CXX"

# Build using Makefile
echo ""
echo "Building extension module..."
make -f Makefile_v3 CXX="$CXX" PYTHON="$PYTHON"

echo ""
echo "=========================================="
echo "Build complete!"
echo "=========================================="
echo ""
echo "To test: make -f Makefile_v3 test"
echo "To install: make -f Makefile_v3 install"
