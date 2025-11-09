# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

tinyobjloader is a header-only C++03 library for parsing Wavefront .obj files. It's designed to be embedded directly into projects with zero dependencies beyond the C++ standard library. The library supports both a legacy API and a modern object-oriented API (v2.0).

## Build System

The project uses CMake as the primary build system:

```bash
# Build the library and examples
mkdir build && cd build
cmake ..
cmake --build .

# Build with specific options
cmake -DTINYOBJLOADER_USE_DOUBLE=ON ..              # Use double precision
cmake -DTINYOBJLOADER_BUILD_TEST_LOADER=ON ..       # Build test loader
cmake -DTINYOBJLOADER_BUILD_OBJ_STICHER=ON ..       # Build obj_sticher example
```

## Testing

Run tests using the Makefile in the `tests/` directory:

```bash
cd tests
make check
```

Alternative testing methods are documented in `tests/README.md` (ninja + kuroga build system).

## Python Bindings

Python module can be built for development:

```bash
# Install in development mode
python -m pip install .

# Build standalone module (developer mode)
cmake -DTINYOBJLOADER_WITH_PYTHON=ON ..
```

Production Python packages use `cibuildwheel` (see `azure-pipelines.yml`).

## Core Architecture

### Single-Header Design

The library is implemented as a header-only library:
- **tiny_obj_loader.h**: Main header containing all declarations and implementation
- **tiny_obj_loader.cc**: Minimal translation unit that includes the header with `TINYOBJLOADER_IMPLEMENTATION` defined

To use in your project, include the header in ONE .cc file with the implementation macro:
```cpp
#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"
```

### Data Structures

The library separates geometry data from topology:

1. **attrib_t**: Contains flat arrays of all vertex attributes (positions, normals, texcoords, colors)
   - `vertices`: xyz triplets (3 floats per vertex)
   - `normals`: xyz triplets (3 floats per normal)
   - `texcoords`: uv pairs (2 floats per texcoord)
   - `colors`: rgb triplets (3 floats per vertex color, optional extension)

2. **shape_t**: Contains topology information
   - `mesh_t::indices`: Array of index_t structs with vertex/normal/texcoord indices
   - `mesh_t::num_face_vertices`: Number of vertices per face (3=triangle, 4=quad, etc.)
   - `mesh_t::material_ids`: Per-face material assignments
   - Also supports `lines_t` and `points_t` primitives

3. **index_t**: Indirection structure allowing different indices for position/normal/texcoord per vertex (OBJ format feature)

### Two API Styles

**Legacy API (v1.x)**: Direct function calls
```cpp
bool LoadObj(attrib_t* attrib, std::vector<shape_t>* shapes,
             std::vector<material_t>* materials,
             std::string* warn, std::string* err,
             const char* filename);
```

**Object-Oriented API (v2.0)**: Recommended for new code
```cpp
tinyobj::ObjReader reader;
reader.ParseFromFile("model.obj", config);
auto& attrib = reader.GetAttrib();
auto& shapes = reader.GetShapes();
auto& materials = reader.GetMaterials();
```

### Key Configuration Options

- **TINYOBJLOADER_USE_DOUBLE**: Use double precision instead of float (controlled via `real_t` typedef)
- **TINYOBJLOADER_USE_MAPBOX_EARCUT**: Enable robust triangulation using mapbox/earcut.hpp (requires C++11)
- **triangulate flag**: Automatically triangulate n-gons (enabled by default)

### Material System

Materials are parsed from .mtl files with support for:
- Standard Phong material properties (ambient, diffuse, specular, etc.)
- PBR extensions (roughness, metallic, sheen, etc. - see `pbr-mtl.md`)
- Texture maps with extensive options (-o, -s, -t, -bm, -clamp, etc.)
- Unknown material attributes are stored in `unknown_parameter` map

### Advanced Features

- **Callback API**: Stream-based parsing for memory-constrained environments (see `examples/callback_api/`)
- **Vertex skinning weights**: Custom `vw` extension for skeletal animation
- **Optimized loader**: Multi-threaded loader in `experimental/` directory (C++11 required)
- **Custom MaterialReader**: Override material loading for non-filesystem sources

## Important Implementation Details

### Index Handling
OBJ files use 1-based indexing and support negative indices (relative to end of current list). The library converts these to 0-based indices. Always check for negative values in `index_t` members - they indicate missing data (e.g., no normal or texcoord).

### Face Iteration Pattern
When iterating over faces, track the offset into the indices array:
```cpp
size_t index_offset = 0;
for (size_t f = 0; f < mesh.num_face_vertices.size(); f++) {
    size_t fv = mesh.num_face_vertices[f];
    for (size_t v = 0; v < fv; v++) {
        index_t idx = mesh.indices[index_offset + v];
        // Access vertex data via idx.vertex_index, idx.normal_index, idx.texcoord_index
    }
    index_offset += fv;
}
```

### Triangulation
When triangulation is enabled (default), complex polygons are converted to triangles. For robust triangulation of concave polygons, define `TINYOBJLOADER_USE_MAPBOX_EARCUT` and ensure `mapbox/earcut.hpp` is available.

## Directory Structure

- **examples/**: Standalone examples (viewer, callback_api, voxelize, obj_sticher)
- **experimental/**: Optimized multi-threaded loader and lock-free allocator
- **python/**: Python binding implementation (pybind11-based)
- **tests/**: Unit tests using acutest framework
- **fuzzer/**: Fuzzing harness for security testing
- **mapbox/**: earcut.hpp for robust triangulation
- **models/**: Sample .obj files for testing

## Testing and Examples

- `loader_example.cc`: Reference implementation showing basic usage
- `tests/tester.cc`: Comprehensive unit tests covering edge cases
- `examples/viewer/`: Full OpenGL viewer demonstrating practical usage
