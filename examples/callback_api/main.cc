#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

typedef struct
{
  std::vector<float> vertices;
  std::vector<float> normals;
  std::vector<float> texcoords;
  std::vector<int>   v_indices;
  std::vector<int>   vn_indices;
  std::vector<int>   vt_indices;

  std::vector<tinyobj::material_t> materials;

} MyMesh;

void vertex_cb(void *user_data, float x, float y, float z)
{
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("v[%ld] = %f, %f, %f\n", mesh->vertices.size() / 3, x, y, z);

  mesh->vertices.push_back(x);
  mesh->vertices.push_back(y);
  mesh->vertices.push_back(z);
}

void normal_cb(void *user_data, float x, float y, float z)
{
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("vn[%ld] = %f, %f, %f\n", mesh->normals.size() / 3, x, y, z);

  mesh->normals.push_back(x);
  mesh->normals.push_back(y);
  mesh->normals.push_back(z);
}

void texcoord_cb(void *user_data, float x, float y)
{
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("vt[%ld] = %f, %f\n", mesh->texcoords.size() / 2, x, y);

  mesh->texcoords.push_back(x);
  mesh->texcoords.push_back(y);
}

void index_cb(void *user_data, int v_idx, int vn_idx, int vt_idx)
{
  // NOTE: the value of each index is raw value. 
  // For example, the application must manually adjust the index with offset
  // (e.g. v_indices.size()) when the value is negative(relative index).
  // See fixIndex() function in tiny_obj_loader.h for details.
  // Also, -2147483648(0x80000000) is set for the index value which does not exist in .obj 
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("idx[%ld] = %d, %d, %d\n", mesh->v_indices.size(), v_idx, vn_idx, vt_idx);

  if (v_idx != 0x80000000) {
    mesh->v_indices.push_back(v_idx);
  }
  if (vn_idx != 0x80000000) {
    mesh->vn_indices.push_back(vn_idx);
  }
  if (vt_idx != 0x80000000) {
    mesh->vt_indices.push_back(vt_idx);
  }
}

void usemtl_cb(void *user_data, const char* name, int material_idx)
{
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  if ((material_idx > -1) && (material_idx < mesh->materials.size())) {
    printf("usemtl. material id = %d(name = %s)\n", material_idx, mesh->materials[material_idx].name.c_str());
  } else {
    printf("usemtl. name = %s\n", name);
  }
}

void mtllib_cb(void *user_data, const tinyobj::material_t *materials, int num_materials)
{
  MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("mtllib. # of materials = %d\n", num_materials);

  for (int i = 0; i < num_materials; i++) {
    mesh->materials.push_back(materials[i]);
  }
}

void group_cb(void *user_data, const char **names, int num_names)
{
  //MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("group : name = \n");

  for (int i = 0; i < num_names; i++) {
    printf("  %s\n", names[i]);
  }
}

void object_cb(void *user_data, const char *name)
{
  //MyMesh *mesh = reinterpret_cast<MyMesh*>(user_data);
  printf("object : name = %s\n", name);

}

int
main(int argc, char** argv)
{
  tinyobj::callback_t cb;
  cb.vertex_cb = vertex_cb;
  cb.normal_cb = normal_cb;
  cb.texcoord_cb = texcoord_cb;
  cb.index_cb = index_cb;
  cb.usemtl_cb = usemtl_cb;
  cb.mtllib_cb = mtllib_cb;
  cb.group_cb = group_cb;
  cb.object_cb = object_cb;

  MyMesh mesh;
  std::string err;
  std::ifstream ifs("../../models/cornell_box.obj");

  if (ifs.fail()) {
    std::cerr << "file not found." << std::endl;
    return EXIT_FAILURE;
  }

  tinyobj::MaterialFileReader mtlReader("../../models/");
  
  bool ret = tinyobj::LoadObjWithCallback(&mesh, cb, &err, &ifs, &mtlReader);

  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    std::cerr << "Failed to parse .obj" << std::endl;
    return EXIT_FAILURE;
  }

  printf("# of vertices         = %ld\n", mesh.vertices.size() / 3);
  printf("# of normals          = %ld\n", mesh.normals.size() / 3);
  printf("# of texcoords        = %ld\n", mesh.texcoords.size() / 2);
  printf("# of vertex indices   = %ld\n", mesh.v_indices.size());
  printf("# of normal indices   = %ld\n", mesh.vn_indices.size());
  printf("# of texcoord indices   = %ld\n", mesh.vt_indices.size());
  printf("# of materials = %ld\n", mesh.materials.size());

  return EXIT_SUCCESS;
}
