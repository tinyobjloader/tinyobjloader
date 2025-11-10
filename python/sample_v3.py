#!/usr/bin/env python3
"""
Sample script demonstrating TinyObjLoader v3 Python bindings
"""

import tinyobjloader_v3 as tobj

def test_parse_simple_obj():
    """Test parsing a simple OBJ string"""

    # Simple cube OBJ data
    obj_data = """
# Simple cube
v -1.0 -1.0  1.0
v  1.0 -1.0  1.0
v  1.0  1.0  1.0
v -1.0  1.0  1.0
v -1.0 -1.0 -1.0
v  1.0 -1.0 -1.0
v  1.0  1.0 -1.0
v -1.0  1.0 -1.0

vn 0.0 0.0 1.0
vn 0.0 0.0 -1.0
vn 0.0 1.0 0.0
vn 0.0 -1.0 0.0
vn 1.0 0.0 0.0
vn -1.0 0.0 0.0

# Front face
f 1//1 2//1 3//1
f 1//1 3//1 4//1

# Back face
f 5//2 7//2 6//2
f 5//2 8//2 7//2

# Top face
f 4//3 3//3 7//3
f 4//3 7//3 8//3

# Bottom face
f 1//4 6//4 2//4
f 1//4 5//4 6//4

# Right face
f 2//5 6//5 7//5
f 2//5 7//5 3//5

# Left face
f 1//6 4//6 8//6
f 1//6 8//6 5//6
"""

    # Create parser with default config
    parser = tobj.ObjParser()

    # Parse from string
    result = parser.parse_from_string(obj_data)

    # Check if parsing was successful
    if result.success():
        print("✓ Parsing successful!")
    else:
        print("✗ Parsing failed!")
        print(f"Errors: {result.errors}")
        return False

    # Get statistics
    stats = result.stats
    print(f"\nParsing Statistics:")
    print(f"  Vertices parsed: {stats['vertices_parsed']}")
    print(f"  Normals parsed: {stats['normals_parsed']}")
    print(f"  Faces parsed: {stats['faces_parsed']}")
    print(f"  Triangles generated: {stats['triangles_generated']}")
    print(f"  Parse time: {stats['parse_time_seconds']:.6f} seconds")

    # Get attributes
    attrib = result.attributes
    vertices = attrib.vertices
    normals = attrib.normals

    print(f"\nAttribute Data:")
    print(f"  Total vertices: {len(vertices) // 3}")
    print(f"  Total normals: {len(normals) // 3}")

    # Print first few vertices
    print(f"\nFirst 3 vertices:")
    for i in range(min(3, len(vertices) // 3)):
        x, y, z = vertices[i*3], vertices[i*3+1], vertices[i*3+2]
        print(f"    v{i}: ({x:.2f}, {y:.2f}, {z:.2f})")

    # Get shapes
    shapes = result.shapes
    print(f"\nShapes: {len(shapes)}")
    for i, shape in enumerate(shapes):
        print(f"  Shape {i}: '{shape['name']}'")
        mesh = shape['mesh']
        num_faces = len(mesh['num_face_vertices'])
        num_indices = len(mesh['indices'])
        print(f"    Faces: {num_faces}")
        print(f"    Indices: {num_indices}")

        # Print first face
        if num_faces > 0:
            nfv = mesh['num_face_vertices'][0]
            print(f"    First face ({nfv} vertices):")
            for j in range(nfv):
                idx = mesh['indices'][j]
                print(f"      v{idx[0]}/vt{idx[2]}/vn{idx[1]}")

    return True

def test_with_custom_config():
    """Test parsing with custom configuration"""

    obj_data = """
v 0 0 0
v 1 0 0
v 1 1 0
v 0 1 0
f 1 2 3 4
"""

    # Create custom config
    config = tobj.ParserConfig()
    config.triangulate = True

    # Create parser with config
    parser = tobj.ObjParser(config)
    result = parser.parse_from_string(obj_data)

    if result.success():
        print("\n✓ Custom config parsing successful!")
        stats = result.stats
        print(f"  Faces parsed: {stats['faces_parsed']}")
        print(f"  Triangles generated: {stats['triangles_generated']}")
        return True
    else:
        print("\n✗ Custom config parsing failed!")
        return False

def main():
    print("TinyObjLoader v3 Python Bindings Test")
    print("=" * 50)

    print(f"\nModule version: {tobj.__version__}")

    # Test 1: Simple OBJ parsing
    print("\n" + "=" * 50)
    print("Test 1: Simple OBJ parsing")
    print("=" * 50)
    if not test_parse_simple_obj():
        return 1

    # Test 2: Custom configuration
    print("\n" + "=" * 50)
    print("Test 2: Custom configuration")
    print("=" * 50)
    if not test_with_custom_config():
        return 1

    print("\n" + "=" * 50)
    print("All tests passed! ✓")
    print("=" * 50)
    return 0

if __name__ == "__main__":
    exit(main())
