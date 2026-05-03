// Copyright 2025 Google LLC
// Fuzz target for TinyOBJLoader
// Targets: tinyobj::LoadObj (0% coverage, complexity 1561)
//          tinyobj::LoadObjWithData (if available)

#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <sstream>

// Fuzz target for TinyOBJLoader main loading function
// This targets the highest complexity uncovered function
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 10) return 0; // Need minimal OBJ data
    
    // Ensure null-terminated string
    std::string obj_input((const char*)data, size);
    
    // Parse the OBJ data using the main LoadObj function
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    
    std::string warn;
    std::string err;
    
    // Create a stringstream from the fuzz input
    std::istringstream obj_stream(obj_input);
    
    // Test LoadObj with various flags
    // Flag options: triangulate (default), calculate normals, etc.
    bool triangulate = (size % 2) == 0;
    bool default_vcols_fallback = (size % 3) == 0;
    
    // Use the stream-based loader
    bool result = tinyobj::LoadObj(
        &attrib,
        &shapes,
        &materials,
        &warn,
        &err,
        &obj_stream,
        NULL,  // material reader callback
        triangulate,
        default_vcols_fallback
    );
    
    // Try with different material file scenarios
    // Some OBJ files reference external .mtl files
    if (result && !materials.empty()) {
        // Access material properties to ensure coverage
        for (const auto& mat : materials) {
            // Touch various fields to prevent optimization
            volatile float ambient = mat.ambient[0];
            volatile float diffuse = mat.diffuse[0];
            volatile float specular = mat.specular[0];
            (void)ambient;
            (void)diffuse;
            (void)specular;
        }
    }
    
    // Test vertex data access
    if (result) {
        if (!attrib.vertices.empty()) {
            volatile float x = attrib.vertices[0];
            (void)x;
        }
        if (!attrib.normals.empty()) {
            volatile float nx = attrib.normals[0];
            (void)nx;
        }
        if (!attrib.texcoords.empty()) {
            volatile float u = attrib.texcoords[0];
            (void)u;
        }
    }
    
    // Test shape data access
    if (result && !shapes.empty()) {
        for (const auto& shape : shapes) {
            if (!shape.mesh.indices.empty()) {
                volatile int idx = shape.mesh.indices[0].vertex_index;
                (void)idx;
            }
            if (!shape.mesh.num_face_vertices.empty()) {
                volatile unsigned char nfv = shape.mesh.num_face_vertices[0];
                (void)nfv;
            }
        }
    }
    
    // Second pass with different flags
    obj_stream.clear();
    obj_stream.seekg(0);
    
    tinyobj::attrib_t attrib2;
    std::vector<tinyobj::shape_t> shapes2;
    std::vector<tinyobj::material_t> materials2;
    std::string warn2;
    std::string err2;
    
    // Try with opposite flags
    tinyobj::LoadObj(
        &attrib2,
        &shapes2,
        &materials2,
        &warn2,
        &err2,
        &obj_stream,
        NULL,
        !triangulate,  // opposite
        !default_vcols_fallback  // opposite
    );
    
    return 0;
}
