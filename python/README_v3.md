# TinyObjLoader v3 Python Bindings

Python bindings for TinyObjLoader v3 using the **Python Stable ABI (abi3)** for forward compatibility with Python 3.10+.

## Key Features

- **Stable ABI (abi3)**: Binary wheels work across Python 3.10, 3.11, 3.12, 3.13+ without recompilation
- **Zero Python Dependency at Build Time**: Manual ABI definitions eliminate need for Python headers/distribution
- **Modern C++14 API**: Based on tinyobj_v3.hh with no exceptions, no RTTI
- **Clean Separation**: Completely separate from v2 bindings (can be installed side-by-side)
- **Efficient**: No-copy access to geometry data where possible

## Requirements

- **Python**: 3.10 or later
- **Compiler**: C++14 compatible compiler
  - GCC 5+, Clang 3.4+, MSVC 2015+

## Installation

### From Source

```bash
# Build and install the v3 module
python setup_v3.py install

# Or install in development mode
python setup_v3.py develop
```

### Building Wheels

```bash
# Build a wheel (will be abi3 tagged)
python setup_v3.py bdist_wheel

# The resulting wheel will be named like:
# tinyobjloader_v3-3.0.0-cp310-abi3-linux_x86_64.whl
# and will work on Python 3.10, 3.11, 3.12, 3.13, etc.
```

## Usage

### Basic Example

```python
import tinyobjloader_v3 as tobj

# Create parser
parser = tobj.ObjParser()

# Parse OBJ from string
obj_data = """
v 0 0 0
v 1 0 0
v 0 1 0
f 1 2 3
"""
result = parser.parse_from_string(obj_data)

# Check success
if result.success():
    # Access attributes
    attrib = result.attributes
    vertices = attrib.vertices  # [x0, y0, z0, x1, y1, z1, ...]
    normals = attrib.normals
    texcoords = attrib.texcoords
    colors = attrib.colors

    # Access shapes
    shapes = result.shapes
    for shape in shapes:
        name = shape['name']
        mesh = shape['mesh']
        indices = mesh['indices']  # [(v_idx, n_idx, t_idx), ...]
        num_face_vertices = mesh['num_face_vertices']
        material_ids = mesh['material_ids']

    # Access materials
    materials = result.materials
    for mat in materials:
        name = mat['name']
        shininess = mat['shininess']
        diffuse_texname = mat.get('diffuse_texname', '')

    # Get statistics
    stats = result.stats
    print(f"Parsed {stats['vertices_parsed']} vertices")
    print(f"Generated {stats['triangles_generated']} triangles")
else:
    print(f"Parse error: {result.errors}")
```

### Custom Configuration

```python
import tinyobjloader_v3 as tobj

# Create custom config
config = tobj.ParserConfig()
config.triangulate = True  # Automatically triangulate polygons

# Create parser with config
parser = tobj.ObjParser(config)

# Parse
result = parser.parse_from_string(obj_data)
```

### Parse from Memory

```python
# Read file into memory
with open('model.obj', 'rb') as f:
    data = f.read()

# Parse from bytes
result = parser.parse_from_memory(data)
```

## API Reference

### Classes

#### `ObjParser(config=None)`

Main parser class.

**Constructor Parameters:**
- `config` (ParserConfig, optional): Parser configuration

**Methods:**
- `parse_from_string(content: str) -> ParseResult`: Parse OBJ from string
- `parse_from_memory(data: bytes) -> ParseResult`: Parse OBJ from bytes

#### `ParserConfig()`

Parser configuration options.

**Attributes:**
- `triangulate` (bool): Enable automatic triangulation (default: True)

#### `ParseResult`

Parse result containing geometry data.

**Methods:**
- `success() -> bool`: Check if parsing succeeded (no fatal errors)

**Properties:**
- `attributes` (Attrib): Vertex attributes
- `shapes` (list[dict]): List of shapes
- `materials` (list[dict]): List of materials
- `errors` (str): Error and warning messages
- `stats` (dict): Parsing statistics

#### `Attrib`

Vertex attribute container.

**Properties:**
- `vertices` (list[float]): Vertex positions [x, y, z, x, y, z, ...]
- `normals` (list[float]): Vertex normals [x, y, z, x, y, z, ...]
- `texcoords` (list[float]): Texture coordinates [u, v, u, v, ...]
- `colors` (list[float]): Vertex colors [r, g, b, r, g, b, ...]

### Data Structures

#### Shape Dictionary

```python
shape = {
    'name': str,
    'mesh': {
        'num_face_vertices': list[int],  # Number of vertices per face
        'indices': list[tuple],          # (vertex_idx, normal_idx, texcoord_idx)
        'material_ids': list[int]        # Material ID per face
    }
}
```

#### Material Dictionary

```python
material = {
    'name': str,
    'shininess': float,
    'ior': float,
    'dissolve': float,
    'illum': int,
    'roughness': float,
    'metallic': float,
    'sheen': float,
    'ambient_texname': str,
    'diffuse_texname': str,
    # ... more texture names
}
```

#### Statistics Dictionary

```python
stats = {
    'vertices_parsed': int,
    'normals_parsed': int,
    'texcoords_parsed': int,
    'faces_parsed': int,
    'triangles_generated': int,
    'materials_loaded': int,
    'bytes_processed': int,
    'parse_time_seconds': float
}
```

## Architecture

### Stable ABI Implementation

The v3 bindings use a **manual Python C API definition** approach:

1. **No Python.h dependency**: All Python C API types and functions are manually declared in `py_stable_abi.h`
2. **Limited API subset**: Only uses functions available in the stable ABI
3. **Forward compatibility**: Binary wheels work on future Python versions without recompilation

This is achieved by:
- Defining `Py_LIMITED_API=0x030B0000` (Python 3.11+)
- Using `PyType_FromSpec()` instead of static type definitions
- Avoiding CPython implementation details
- Only using stable ABI functions

### Differences from v2 Bindings

| Feature | v2 (pybind11) | v3 (stable ABI) |
|---------|--------------|-----------------|
| Python Headers | Required | Not required |
| C++ Standard | C++11 | C++14 |
| Binary Compatibility | Python version specific | Works across 3.11+ |
| Build Dependencies | pybind11 | None (self-contained) |
| Module Name | `tinyobjloader` | `tinyobjloader_v3` |
| API Style | Object-oriented | Object-oriented |
| Exceptions | Yes (C++ exceptions) | No (error stack) |

## Building Without Python Distribution

The stable ABI approach allows building the extension **without having Python installed** on the build machine:

```bash
# Just need a C++14 compiler
g++ -std=c++14 -fPIC -shared \
    -DPy_LIMITED_API=0x030B0000 \
    python/tinyobj_v3_bindings.cc \
    python/tinyobj_v3_loader.cc \
    -o tinyobjloader_v3.so \
    -lpython3  # Link to stable ABI symbols
```

At runtime, the module will work with any Python 3.11+ interpreter.

## Performance Notes

- **Zero-copy**: Attribute data returns Python lists that copy data once
- **No GIL release**: Parsing happens with GIL held (suitable for small-medium files)
- **Memory efficient**: v3 uses no heap allocations in parser core

For large files, consider:
- Parsing in a background thread
- Using the streaming API (when implemented)

## Development

### Running Tests

```bash
# Build in development mode
python setup_v3.py develop

# Run sample
python python/sample_v3.py
```

### Testing ABI Stability

Build the wheel on Python 3.10 and test on 3.11+:

```bash
# On Python 3.10
python3.10 setup_v3.py bdist_wheel

# On Python 3.11, 3.12 (or later)
python3.11 -m pip install dist/tinyobjloader_v3-*.whl
python3.11 python/sample_v3.py
```

## License

MIT License (same as TinyObjLoader)

## Contributing

Contributions welcome! Please ensure:
- Only use stable ABI functions (check against Python C API docs)
- Maintain C++14 compatibility
- No exceptions, no RTTI
- Test on multiple Python versions (3.10, 3.11, 3.12, 3.13)
