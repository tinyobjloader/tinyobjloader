//
// Copyright 2012, Syoyo Fujita.
// 
// Licensed under 2-clause BSD liecense.
//

//
// version 0.9.0: Initial
//

//
// @todo { Read .mtl }
//

#include <cassert>

#include <string>
#include <vector>
#include <map>
#include <fstream>
#include <sstream>

#include "tiny_obj_loader.h"

namespace tinyobj {

struct vertex_index {
  int v_idx, vt_idx, vn_idx;
  vertex_index() {};
  vertex_index(int idx) : v_idx(idx), vt_idx(idx), vn_idx(idx) {};
  vertex_index(int vidx, int vtidx, int vnidx) : v_idx(vidx), vt_idx(vtidx), vn_idx(vnidx) {};

};
// for std::map
static inline bool operator<(const vertex_index& a, const vertex_index& b)
{
  if (a.v_idx != b.v_idx) return (a.v_idx < b.v_idx);
  if (a.vn_idx != b.vn_idx) return (a.vn_idx < b.vn_idx);
  if (a.vt_idx != b.vt_idx) return (a.vt_idx < b.vt_idx);

  return false;
}

struct obj_shape {
  std::vector<float> v;
  std::vector<float> vn;
  std::vector<float> vt;
};

static inline bool isSpace(const char c) {
  return (c == ' ') || (c == '\t');
}

// Make index zero-base, and also support relative index. 
static inline int fixIndex(int idx, int n)
{
  int i;

  if (idx > 0) {
    i = idx - 1;
  } else if (idx == 0) {
    i = 0;
  } else { // negative value = relative
    i = n + idx;
  }
  return i;
}

static inline float parseFloat(const char*& token)
{
  token += strspn(token, " \t");
  float f = (float)atof(token);
  token += strcspn(token, " \t\r");
  return f;
}

static inline void parseFloat2(
  float& x, float& y,
  const char*& token)
{
  x = parseFloat(token);
  y = parseFloat(token);
}

static inline void parseFloat3(
  float& x, float& y, float& z,
  const char*& token)
{
  x = parseFloat(token);
  y = parseFloat(token);
  z = parseFloat(token);
}


// Parse triples: i, i/j/k, i//k, i/j
static vertex_index parseTriple(
  const char* &token,
  int vsize,
  int vnsize,
  int vtsize)
{
    vertex_index vi(-1);

    vi.v_idx = fixIndex(atoi(token), vsize);
    token += strcspn(token, "/ \t\r");
    if (token[0] != '/') {
      return vi;
    }
    token++;

    // i//k
    if (token[0] == '/') {
      token++;
      vi.vn_idx = fixIndex(atoi(token), vnsize);
      token += strcspn(token, "/ \t\r");
      return vi;
    }
    
    // i/j/k or i/j
    vi.vt_idx = fixIndex(atoi(token), vtsize);
    token += strcspn(token, "/ \t\r");
    if (token[0] != '/') {
      return vi;
    }

    // i/j/k
    vi.vn_idx = fixIndex(atoi(token), vnsize);
    token += strcspn(token, "/ \t\r");
    return vi; 
}

static unsigned int
updateVertex(
  std::map<vertex_index, unsigned int>& vertexCache,
  std::vector<float>& positions,
  std::vector<float>& normals,
  std::vector<float>& texcoords,
  const std::vector<float>& in_positions,
  const std::vector<float>& in_normals,
  const std::vector<float>& in_texcoords,
  const vertex_index& i)
{
  const std::map<vertex_index, unsigned int>::iterator it = vertexCache.find(i);

  if (it != vertexCache.end()) {
    // found cache
    return it->second;
  }

  assert(in_positions.size() > (3*i.v_idx+2));

  positions.push_back(in_positions[3*i.v_idx+0]);
  positions.push_back(in_positions[3*i.v_idx+1]);
  positions.push_back(in_positions[3*i.v_idx+2]);

  if (i.vn_idx >= 0) {
    normals.push_back(in_normals[3*i.vn_idx+0]);
    normals.push_back(in_normals[3*i.vn_idx+1]);
    normals.push_back(in_normals[3*i.vn_idx+2]);
  }

  if (i.vt_idx >= 0) {
    texcoords.push_back(in_texcoords[3*i.vt_idx+0]);
    texcoords.push_back(in_texcoords[3*i.vt_idx+1]);
    texcoords.push_back(in_texcoords[3*i.vt_idx+2]);
  }

  unsigned int idx = positions.size() / 3 - 1;
  vertexCache[i] = idx;

  return idx;
}

static bool
exportFaceGroupToShape(
  shape_t& shape,
  const std::vector<float> in_positions,
  const std::vector<float> in_normals,
  const std::vector<float> in_texcoords,
  const std::vector<std::vector<vertex_index> >& faceGroup,
  const std::string name)
{
  if (faceGroup.empty()) {
    return false;
  }

  // Flattened version of vertex data
  std::vector<float> positions;
  std::vector<float> normals;
  std::vector<float> texcoords;
  std::map<vertex_index, unsigned int> vertexCache;
  std::vector<unsigned int> indices;

  // Flatten vertices and indices
  for (size_t i = 0; i < faceGroup.size(); i++) {
    const std::vector<vertex_index>& face = faceGroup[i];

    vertex_index i0 = face[0];
    vertex_index i1(-1);
    vertex_index i2 = face[1];

    size_t npolys = face.size();

    // Polygon -> triangle fan conversion
    for (size_t k = 2; k < npolys; k++) {
      i1 = i2;
      i2 = face[k];

      unsigned int v0 = updateVertex(vertexCache, positions, normals, texcoords, in_positions, in_normals, in_texcoords, i0);
      unsigned int v1 = updateVertex(vertexCache, positions, normals, texcoords, in_positions, in_normals, in_texcoords, i1);
      unsigned int v2 = updateVertex(vertexCache, positions, normals, texcoords, in_positions, in_normals, in_texcoords, i2);

      indices.push_back(v0);
      indices.push_back(v1);
      indices.push_back(v2);
    }

  }

  //
  // Construct shape.
  //
  shape.name = name;
  shape.mesh.positions.swap(positions);
  shape.mesh.normals.swap(normals);
  shape.mesh.texcoords.swap(texcoords);
  shape.mesh.indices.swap(indices);

  // @todo { material, name }

  return true;

}

std::string
LoadObj(
  std::vector<shape_t>& shapes,
  const char* filename)
{

  shapes.clear();

  std::stringstream err;

  std::ifstream ifs(filename);
  if (!ifs) {
    err << "Cannot open file [" << filename << "]" << std::endl;
    return err.str();
  }

  std::vector<float> v;
  std::vector<float> vn;
  std::vector<float> vt;
  std::vector<std::vector<vertex_index> > faceGroup;
  std::string name;

  int maxchars = 8192;  // Alloc enough size.
  std::vector<char> buf(maxchars);  // Alloc enough size.
  while (ifs.peek() != -1) {
    ifs.getline(&buf[0], maxchars);

    std::string linebuf(&buf[0]);

    // Trim newline '\r\n' or '\r'
    if (linebuf.size() > 0) {
      if (linebuf[linebuf.size()-1] == '\n') linebuf.erase(linebuf.size()-1);
    }
    if (linebuf.size() > 0) {
      if (linebuf[linebuf.size()-1] == '\n') linebuf.erase(linebuf.size()-1);
    }

    // Skip if empty line.
    if (linebuf.empty()) {
      continue;
    }

    // Skip leading space.
    const char* token = linebuf.c_str();
    token += strspn(token, " \t");

    assert(token);
    if (token[0] == '\0') continue; // empty line
    
    if (token[0] == '#') continue;  // comment line

    // vertex
    if (token[0] == 'v' && isSpace((token[1]))) {
      token += 2;
      float x, y, z;
      parseFloat3(x, y, z, token);
      v.push_back(x);
      v.push_back(y);
      v.push_back(z);
      continue;
    }

    // normal
    if (token[0] == 'v' && token[1] == 'n' && isSpace((token[2]))) {
      token += 3;
      float x, y, z;
      parseFloat3(x, y, z, token);
      vn.push_back(x);
      vn.push_back(y);
      vn.push_back(z);
      continue;
    }

    // texcoord
    if (token[0] == 'v' && token[1] == 't' && isSpace((token[2]))) {
      token += 3;
      float x, y;
      parseFloat2(x, y, token);
      vt.push_back(x);
      vt.push_back(y);
      continue;
    }

    // face
    if (token[0] == 'f' && isSpace((token[1]))) {
      token += 2;
      token += strspn(token, " \t");

      std::vector<vertex_index> face;
      while (token[0] && (token[1] != '\0')) {
        vertex_index vi = parseTriple(token, v.size() / 3, vn.size() / 3, vt.size() / 2);
        face.push_back(vi);
        int n = strspn(token, " \t");
        token += n;
      }

      faceGroup.push_back(face);
      
      continue;
    }

    // use mtl
    if ((0 == strncmp(token, "usemtl", 6)) && isSpace((token[6]))) {

      // flush previous face group.
      shape_t shape;
      bool ret = exportFaceGroupToShape(shape, v, vn, vt, faceGroup, name);
      if (ret) {
        shapes.push_back(shape);
      }

      faceGroup.clear();

      continue;

    }

    // load mtl
    if ((0 == strncmp(token, "mtllib", 6)) && isSpace((token[6]))) {
      continue;
    }

    // object name
    if (token[0] == 'o' && isSpace((token[1]))) {
      char namebuf[4096];
      token += 2;
      sscanf(token, "%s", namebuf);
      name = std::string(namebuf);

      continue;
    }

    // Ignore unknown command.
  }

  shape_t shape;
  bool ret = exportFaceGroupToShape(shape, v, vn, vt, faceGroup, name);
  if (ret) {
    shapes.push_back(shape);
  }
  faceGroup.clear();  // for safety

  return err.str();
}


};
