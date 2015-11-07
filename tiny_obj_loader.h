//
// Copyright 2012-2015, Syoyo Fujita.
//
// Licensed under 2-clause BSD liecense.
//
#ifndef _TINY_OBJ_LOADER_H
#define _TINY_OBJ_LOADER_H

#include <string>
#include <vector>
#include <map>

namespace tinyobj {

typedef struct {
  std::string name;

  float ambient[3];
  float diffuse[3];
  float specular[3];
  float transmittance[3];
  float emission[3];
  float shininess;
  float ior;      // index of refraction
  float dissolve; // 1 == opaque; 0 == fully transparent
  // illumination model (see http://www.fileformat.info/format/material/)
  int illum;

  std::string ambient_texname;            // map_Ka
  std::string diffuse_texname;            // map_Kd
  std::string specular_texname;           // map_Ks
  std::string specular_highlight_texname; // map_Ns
  std::string bump_texname;               // map_bump, bump
  std::string displacement_texname;       // disp
  std::string alpha_texname;              // map_d
  std::map<std::string, std::string> unknown_parameter;
} material_t;

typedef struct {
  std::vector<float> positions;
  std::vector<float> normals;
  std::vector<float> texcoords;
  std::vector<unsigned int> indices;
  std::vector<int> material_ids; // per-mesh material ID
} mesh_t;

typedef struct {
  std::string name;
  mesh_t mesh;
} shape_t;

class MaterialReader {
public:
  MaterialReader() {}
  virtual ~MaterialReader() {}

  virtual bool operator()(const std::string &matId,
                          std::vector<material_t> &materials,
                          std::map<std::string, int> &matMap,
                          std::string &err) = 0;
};

class MaterialFileReader : public MaterialReader {
public:
  MaterialFileReader(const std::string &mtl_basepath)
      : m_mtlBasePath(mtl_basepath) {}
  virtual ~MaterialFileReader() {}
  virtual bool operator()(const std::string &matId,
                                std::vector<material_t> &materials,
                                std::map<std::string, int> &matMap,
                                std::string &err);

private:
  std::string m_mtlBasePath;
};

/// Loads .obj from a file.
/// 'shapes' will be filled with parsed shape data
/// The function returns error string.
/// Returns true when loading .obj become success.
/// Returns warning and error message into `err`
/// 'mtl_basepath' is optional, and used for base path for .mtl file.
bool LoadObj(std::vector<shape_t> &shapes,       // [output]
             std::vector<material_t> &materials, // [output]
             std::string& err,                   // [output]
             const char *filename, const char *mtl_basepath = NULL);

/// Loads object from a std::istream, uses GetMtlIStreamFn to retrieve
/// std::istream for materials.
/// Returns true when loading .obj become success.
/// Returns warning and error message into `err`
bool LoadObj(std::vector<shape_t> &shapes,       // [output]
             std::vector<material_t> &materials, // [output]
             std::string& err,                   // [output]
             std::istream &inStream, MaterialReader &readMatFn);

/// Loads materials into std::map
void LoadMtl(std::map<std::string, int> &material_map, // [output]
             std::vector<material_t> &materials,       // [output]
             std::istream &inStream);
}

#endif // _TINY_OBJ_LOADER_H
