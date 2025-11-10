# TinyObjLoader v3 Python Bindings - Quick Start

## What Was Created

Complete Python bindings for TinyObjLoader v3 using Python's stable ABI (abi3) for forward compatibility across Python 3.10+.

## Files Created

### Source Files
- `python/py_stable_abi.h` - Manual Python C API definitions for headerless builds
- `python/tinyobj_v3_bindings.cc` - Main binding implementation (20KB)
- `python/tinyobj_v3_loader.cc` - Implementation translation unit

### Build System
- `setup_v3.py` - setuptools configuration for `pip install`
- `python/CMakeLists_v3.txt` - CMake build configuration
- `python/Makefile_v3` - Simple Makefile for quick builds
- `python/build_v3.sh` - Shell script wrapper

### Documentation & Examples
- `python/README_v3.md` - User documentation (7.4KB)
- `python/sample_v3.py` - Example usage (4.0KB)
- `V3_PYTHON_BINDINGS.md` - Developer documentation (11KB)
- `python/QUICKSTART_v3.md` - This file

## Quick Build

### Prerequisites
```bash
# Install Python dev headers
sudo apt-get install python3-dev  # Ubuntu/Debian
sudo dnf install python3-devel     # Fedora/RHEL
brew install python3               # macOS
```

### Build & Install
```bash
# Option 1: Using setup.py
python3 setup_v3.py install

# Option 2: Using Makefile
cd python
make -f Makefile_v3
make -f Makefile_v3 install

# Option 3: Development mode
python3 setup_v3.py develop
```

## Quick Test

```python
import tinyobjloader_v3 as tobj

# Parse OBJ data
parser = tobj.ObjParser()
result = parser.parse_from_string("""
v 0 0 0
v 1 0 0
v 0 1 0
f 1 2 3
""")

# Check result
if result.success():
    attrib = result.attributes
    print(f"Vertices: {len(attrib.vertices) // 3}")
    print(f"Stats: {result.stats}")
else:
    print(f"Error: {result.errors}")
```

## Key Features

✅ **Stable ABI (abi3)** - One wheel for Python 3.10, 3.11, 3.12, 3.13+
✅ **No pybind11** - Zero dependencies beyond Python itself
✅ **Separate from v2** - Module name `tinyobjloader_v3`
✅ **Modern C++14** - Based on tinyobj_v3.hh
✅ **No exceptions/RTTI** - Efficient embedded-friendly code

## Python API

```python
# Classes
ObjParser(config=None)      # Main parser
ParserConfig()              # Configuration options
ParseResult                 # Returned by parsing
Attrib                      # Vertex attributes

# Example with config
config = tobj.ParserConfig()
config.triangulate = True
parser = tobj.ObjParser(config)

# Parse
result = parser.parse_from_string(obj_data)
result = parser.parse_from_memory(bytes_data)

# Access data
vertices = result.attributes.vertices      # [x,y,z, x,y,z, ...]
normals = result.attributes.normals        # [x,y,z, x,y,z, ...]
shapes = result.shapes                     # [{'name': ..., 'mesh': {...}}, ...]
materials = result.materials               # [{'name': ..., 'shininess': ...}, ...]
stats = result.stats                       # {'vertices_parsed': N, ...}
```

## Build Requirements

- **Compiler**: C++14 compatible (GCC 5+, Clang 3.4+, MSVC 2015+)
- **Python**: 3.10 or later
- **Python Headers**: python3-dev package (for standard build)

## Testing

```bash
# Run sample
python3 python/sample_v3.py

# Or with Makefile
cd python
make -f Makefile_v3 test
```

Expected output:
```
TinyObjLoader v3 Python Bindings Test
==================================================
Module version: 3.0.0
✓ Parsing successful!
Parsing Statistics:
  Vertices parsed: 8
  Normals parsed: 6
  Faces parsed: 12
  Triangles generated: 12
  ...
All tests passed! ✓
```

## Building Wheels

```bash
python3 setup_v3.py bdist_wheel
# Creates: dist/tinyobjloader_v3-3.0.0-cp310-abi3-linux_x86_64.whl
# Works on Python 3.10, 3.11, 3.12, 3.13+!
```

## Next Steps

1. **Complete Build**: Install python3-dev and run build
2. **Test**: Run sample_v3.py to verify
3. **Integrate**: Use `import tinyobjloader_v3` in your code
4. **Distribute**: Build wheels for your platform

## Differences from v2

| Feature | v2 | v3 |
|---------|----|----|
| Module Name | `tinyobjloader` | `tinyobjloader_v3` |
| Dependency | pybind11 | None |
| ABI | Unstable | Stable (abi3) |
| Python | 3.x specific | 3.10+ universal |
| Exceptions | C++ | Error stacks |

Both can be installed and used together!

## Troubleshooting

**"Python.h not found"**
```bash
sudo apt-get install python3-dev
```

**"undefined symbol"**
- Make sure you're using Python 3.10+
- Check that `-DPy_LIMITED_API=0x030A0000` is set

**Import error**
```bash
# Check Python version
python3 --version  # Should be 3.10+

# Try development install
python3 setup_v3.py develop
```

## More Information

- User Docs: `python/README_v3.md`
- Developer Docs: `V3_PYTHON_BINDINGS.md`
- API Examples: `python/sample_v3.py`
- v3 Design: `v3-design.md`

## Status

✅ Code complete and ready to build
⏳ Needs Python dev headers to compile
📦 Ready for wheel distribution once built
