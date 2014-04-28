//
// Copyright 2012-2013, Syoyo Fujita.
//
// Licensed under 2-clause BSD liecense.
//
#ifndef _TINY_OBJ_LOADER_H
#define _TINY_OBJ_LOADER_H

#include <string>
#include <vector>
#include <map>
#include <functional>
#include <memory>

namespace tinyobj {

typedef struct
{
    std::string name;

    float ambient[3];
    float diffuse[3];
    float specular[3];
    float transmittance[3];
    float emission[3];
    float shininess;
    float ior;                // index of refraction
    float dissolve;           // 1 == opaque; 0 == fully transparent
    // illumination model (see http://www.fileformat.info/format/material/)
    int illum;

    std::string ambient_texname;
    std::string diffuse_texname;
    std::string specular_texname;
    std::string normal_texname;
    std::map<std::string, std::string> unknown_parameter;
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

/// typedef for a function that returns a pointer to an istream for
/// the material identified by the const std::string&
typedef std::function< 
    std::unique_ptr<std::istream>(
        const std::string&) 
    > GetMtlIStreamFn;

/// Loads .obj from a file.
/// 'shapes' will be filled with parsed shape data
/// The function returns error string.
/// Returns empty string when loading .obj success.
/// 'mtl_basepath' is optional, and used for base path for .mtl file.
std::string LoadObj(
    std::vector<shape_t>& shapes,   // [output]
    const char* filename,
    const char* mtl_basepath = NULL);

/// Loads object from a std::istream, uses GetMtlIStreamFn to retrieve
/// std::istream for materials.
/// Returns empty string when loading .obj success.
std::string LoadObj(
    std::vector<shape_t>& shapes,   // [output]
    std::istream& inStream,
    GetMtlIStreamFn getMatFn);
};

#endif  // _TINY_OBJ_LOADER_H
