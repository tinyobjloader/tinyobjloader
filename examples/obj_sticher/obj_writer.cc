//
// Simple wavefront .obj writer
//
#include "obj_writer.h"

static std::string GetFileBasename(const std::string& FileName)
{
    if(FileName.find_last_of(".") != std::string::npos)
        return FileName.substr(0, FileName.find_last_of("."));
    return "";
}

bool WriteMat(const std::string& filename, std::vector<tinyobj::shape_t> shapes) {
  FILE* fp = fopen(filename.c_str(), "w");
  if (!fp) {
    fprintf(stderr, "Failed to open file [ %s ] for write.\n", filename.c_str());
    return false;
  }

  std::map<std::string, tinyobj::material_t> mtl_table;

  for (size_t i = 0; i < shapes.size(); i++) {
    mtl_table[shapes[i].material.name] = shapes[i].material;
  }

  for (std::map<std::string, tinyobj::material_t>::iterator it = mtl_table.begin(); it != mtl_table.end(); it++) {

    tinyobj::material_t mat = it->second;

    fprintf(fp, "newmtl %s\n", mat.name.c_str());
    fprintf(fp, "Ka %f %f %f\n", mat.ambient[0], mat.ambient[1], mat.ambient[2]);
    fprintf(fp, "Kd %f %f %f\n", mat.diffuse[0], mat.diffuse[1], mat.diffuse[2]);
    fprintf(fp, "Ks %f %f %f\n", mat.specular[0], mat.specular[1], mat.specular[2]);
    fprintf(fp, "Kt %f %f %f\n", mat.transmittance[0], mat.specular[1], mat.specular[2]);
    fprintf(fp, "Ke %f %f %f\n", mat.emission[0], mat.emission[1], mat.emission[2]);
    fprintf(fp, "Ns %f\n", mat.shininess);
    fprintf(fp, "Ni %f\n", mat.ior);
    // @todo { texture }
  }
  
  fclose(fp);

  return true;
}

bool WriteObj(const std::string& filename, std::vector<tinyobj::shape_t> shapes) {
  FILE* fp = fopen(filename.c_str(), "w");
  if (!fp) {
    fprintf(stderr, "Failed to open file [ %s ] for write.\n", filename.c_str());
    return false;
  }

  std::string basename = GetFileBasename(filename);
  std::string material_filename = basename + ".mtl";

  int v_offset = 0;
  int vn_offset = 0;
  int vt_offset = 0;

  fprintf(fp, "mtllib %s\n", material_filename.c_str());

  for (size_t i = 0; i < shapes.size(); i++) {

    bool has_vn = false;
    bool has_vt = false;

    if (shapes[i].name.empty()) {
      fprintf(fp, "g Unknown\n");
    } else {
      fprintf(fp, "g %s\n", shapes[i].name.c_str());
    }

    if (!shapes[i].material.name.empty()) {
      fprintf(fp, "usemtl %s\n", shapes[i].material.name.c_str());
    }

    // vtx
    for (size_t k = 0; k < shapes[i].mesh.positions.size() / 3; k++) {
      fprintf(fp, "v %f %f %f\n",
        shapes[i].mesh.positions[3*k+0],
        shapes[i].mesh.positions[3*k+1],
        shapes[i].mesh.positions[3*k+2]);
    }

    // normal
    for (size_t k = 0; k < shapes[i].mesh.normals.size() / 3; k++) {
      fprintf(fp, "vn %f %f %f\n",
        shapes[i].mesh.normals[3*k+0],
        shapes[i].mesh.normals[3*k+1],
        shapes[i].mesh.normals[3*k+2]);
    }
    if (shapes[i].mesh.normals.size() > 0) has_vn = true;

    // texcoord
    for (size_t k = 0; k < shapes[i].mesh.texcoords.size() / 2; k++) {
      fprintf(fp, "vt %f %f\n",
        shapes[i].mesh.texcoords[2*k+0],
        shapes[i].mesh.texcoords[2*k+1]);
    }
    if (shapes[i].mesh.texcoords.size() > 0) has_vt = true;

    // face
    for (size_t k = 0; k < shapes[i].mesh.indices.size() / 3; k++) {
  
      // Face index is 1-base.
      int v0 = shapes[i].mesh.indices[3*k+0] + 1 + v_offset;
      int v1 = shapes[i].mesh.indices[3*k+1] + 1 + v_offset;
      int v2 = shapes[i].mesh.indices[3*k+2] + 1 + v_offset;

      if (has_vn && has_vt) {
        fprintf(fp, "f %d/%d/%d %d/%d/%d %d/%d/%d\n",
          v0, v0, v0, v1, v1, v1, v2, v2, v2);
      } else if (has_vn && !has_vt) {
        fprintf(fp, "f %d//%d %d//%d %d//%d\n", v0, v0, v1, v1, v2, v2);
      } else if (!has_vn && has_vt) {
        fprintf(fp, "f %d/%d %d/%d %d/%d\n", v0, v0, v1, v1, v2, v2);
      } else {
        fprintf(fp, "f %d %d %d\n", v0, v1, v2);
      }
      
    }

    v_offset  += shapes[i].mesh.positions.size() / 3;
    vn_offset += shapes[i].mesh.normals.size() / 3;
    vt_offset += shapes[i].mesh.texcoords.size() / 2;

  }

  fclose(fp);

  //
  // Write material file
  //
  bool ret = WriteMat(material_filename, shapes);

  return ret;
}


