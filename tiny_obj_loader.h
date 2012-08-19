//
// Copyright 2012, Syoyo Fujita.
//
// Licensed under 2-clause BSD liecense.
//
#ifndef _TINY_OBJ_LOADER_H
#define _TINY_OBJ_LOADER_H

#include <string>
#include <vector>

namespace tinyobj {

typedef struct
{
    std::string name;

    float ambient[3];
    float diffuse[3];
    float specular[3];
    float transmittance[3];

    std::string ambient_texname;
    std::string diffuse_texname;
    std::string specular_texname;
} material_t;

typedef struct
{
    std::vector<float>          positions;
    std::vector<float>          normals;
    std::vector<float>          texcoords;
    std::vector<unsigned int>   indices;
} mesh_t;

typedef struct
{
    std::string  name;
    material_t   material;
    mesh_t       mesh;
} shape_t;

/// Loads .obj from a file.
/// 'shapes' will be filled with parsed shape data
/// The function returns error string.
/// Returns empty string when loading .obj success.
std::string LoadObj(
    std::vector<shape_t>& shapes,   // [output]
    const char* filename);

};

#endif  // _TINY_OBJ_LOADER_H
