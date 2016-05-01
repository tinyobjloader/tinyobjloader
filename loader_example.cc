//
// g++ loader_example.cc
//
#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

static void PrintInfo(const tinyobj::attrib_t &attrib, const std::vector<tinyobj::shape_t>& shapes, const std::vector<tinyobj::material_t>& materials)
{
  std::cout << "# of vertices  : " << (attrib.vertices.size() / 3) << std::endl;
  std::cout << "# of normals   : " << (attrib.normals.size() / 3) << std::endl;
  std::cout << "# of texcoords : " << (attrib.texcoords.size() / 2) << std::endl;

  std::cout << "# of shapes    : " << shapes.size() << std::endl;
  std::cout << "# of materials : " << materials.size() << std::endl;

  for (size_t v = 0; v < attrib.vertices.size() / 3; v++) {
    printf("  v[%ld] = (%f, %f, %f)\n", static_cast<long>(v),
      static_cast<const double>(attrib.vertices[3*v+0]),
      static_cast<const double>(attrib.vertices[3*v+1]),
      static_cast<const double>(attrib.vertices[3*v+2]));
  }

  for (size_t v = 0; v < attrib.normals.size() / 3; v++) {
    printf("  n[%ld] = (%f, %f, %f)\n", static_cast<long>(v),
      static_cast<const double>(attrib.normals[3*v+0]),
      static_cast<const double>(attrib.normals[3*v+1]),
      static_cast<const double>(attrib.normals[3*v+2]));
  }

  for (size_t v = 0; v < attrib.texcoords.size() / 2; v++) {
    printf("  uv[%ld] = (%f, %f)\n", static_cast<long>(v),
      static_cast<const double>(attrib.texcoords[2*v+0]),
      static_cast<const double>(attrib.texcoords[2*v+1]));
  }

  // For each shape
  for (size_t i = 0; i < shapes.size(); i++) {
    printf("shape[%ld].name = %s\n", static_cast<long>(i), shapes[i].name.c_str());
    printf("Size of shape[%ld].indices: %lu\n", static_cast<long>(i), static_cast<unsigned long>(shapes[i].mesh.indices.size()));

	size_t index_offset = 0;

	assert(shapes[i].mesh.num_face_vertices.size() == shapes[i].mesh.material_ids.size());

	printf("shape[%ld].num_faces: %lu\n", static_cast<long>(i), static_cast<unsigned long>(shapes[i].mesh.num_face_vertices.size()));

	// For each face
    for (size_t f = 0; f < shapes[i].mesh.num_face_vertices.size(); f++) {
		size_t fnum = shapes[i].mesh.num_face_vertices[f];

		// For each vertex in the face
		for (size_t v = 0; v < fnum; v++) {
			tinyobj::index_t idx = shapes[i].mesh.indices[index_offset + v];
			printf("  face[%ld].v[%ld].idx = %d/%d/%d\n", static_cast<long>(f), static_cast<long>(v), idx.vertex_index, idx.normal_index, idx.texcoord_index);
		}

		printf("  face[%ld].material_id = %d\n", static_cast<long>(f), shapes[i].mesh.material_ids[f]);

		index_offset += fnum;
    }

    printf("shape[%ld].num_tags: %lu\n", static_cast<long>(i), static_cast<unsigned long>(shapes[i].mesh.tags.size()));
    for (size_t t = 0; t < shapes[i].mesh.tags.size(); t++) {
      printf("  tag[%ld] = %s ", static_cast<long>(t), shapes[i].mesh.tags[t].name.c_str());
      printf(" ints: [");
      for (size_t j = 0; j < shapes[i].mesh.tags[t].intValues.size(); ++j)
      {
          printf("%ld", static_cast<long>(shapes[i].mesh.tags[t].intValues[j]));
          if (j < (shapes[i].mesh.tags[t].intValues.size()-1))
          {
              printf(", ");
          }
      }
      printf("]");

      printf(" floats: [");
      for (size_t j = 0; j < shapes[i].mesh.tags[t].floatValues.size(); ++j)
      {
          printf("%f", static_cast<const double>(shapes[i].mesh.tags[t].floatValues[j]));
          if (j < (shapes[i].mesh.tags[t].floatValues.size()-1))
          {
              printf(", ");
          }
      }
      printf("]");

      printf(" strings: [");
      for (size_t j = 0; j < shapes[i].mesh.tags[t].stringValues.size(); ++j)
      {
          printf("%s", shapes[i].mesh.tags[t].stringValues[j].c_str());
          if (j < (shapes[i].mesh.tags[t].stringValues.size()-1))
          {
              printf(", ");
          }
      }
      printf("]");
      printf("\n");
    }
  }

  for (size_t i = 0; i < materials.size(); i++) {
    printf("material[%ld].name = %s\n", static_cast<long>(i), materials[i].name.c_str());
    printf("  material.Ka = (%f, %f ,%f)\n", static_cast<const double>(materials[i].ambient[0]),       static_cast<const double>(materials[i].ambient[1]),       static_cast<const double>(materials[i].ambient[2]));
    printf("  material.Kd = (%f, %f ,%f)\n", static_cast<const double>(materials[i].diffuse[0]),       static_cast<const double>(materials[i].diffuse[1]),       static_cast<const double>(materials[i].diffuse[2]));
    printf("  material.Ks = (%f, %f ,%f)\n", static_cast<const double>(materials[i].specular[0]),      static_cast<const double>(materials[i].specular[1]),      static_cast<const double>(materials[i].specular[2]));
    printf("  material.Tr = (%f, %f ,%f)\n", static_cast<const double>(materials[i].transmittance[0]), static_cast<const double>(materials[i].transmittance[1]), static_cast<const double>(materials[i].transmittance[2]));
    printf("  material.Ke = (%f, %f ,%f)\n", static_cast<const double>(materials[i].emission[0]),      static_cast<const double>(materials[i].emission[1]),      static_cast<const double>(materials[i].emission[2]));
    printf("  material.Ns = %f\n", static_cast<const double>(materials[i].shininess));
    printf("  material.Ni = %f\n", static_cast<const double>(materials[i].ior));
    printf("  material.dissolve = %f\n", static_cast<const double>(materials[i].dissolve));
    printf("  material.illum = %d\n",  materials[i].illum);
    printf("  material.map_Ka = %s\n", materials[i].ambient_texname.c_str());
    printf("  material.map_Kd = %s\n", materials[i].diffuse_texname.c_str());
    printf("  material.map_Ks = %s\n", materials[i].specular_texname.c_str());
    printf("  material.map_Ns = %s\n", materials[i].specular_highlight_texname.c_str());
    printf("  material.map_bump = %s\n", materials[i].bump_texname.c_str());
    printf("  material.map_d = %s\n", materials[i].alpha_texname.c_str());
    printf("  material.disp = %s\n", materials[i].displacement_texname.c_str());
    std::map<std::string, std::string>::const_iterator it(materials[i].unknown_parameter.begin());
    std::map<std::string, std::string>::const_iterator itEnd(materials[i].unknown_parameter.end());

    for (; it != itEnd; it++) {
      printf("  material.%s = %s\n", it->first.c_str(), it->second.c_str());
    }
    printf("\n");
  }
}

static bool
TestLoadObj(
  const char* filename,
  const char* basepath = NULL,
  bool triangulate = true)
{
  std::cout << "Loading " << filename << std::endl;

  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;

  std::string err;
  bool ret = tinyobj::LoadObj(&attrib, &shapes, &materials, &err, filename, basepath, triangulate);

  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    printf("Failed to load/parse .obj.\n");
    return false;
  }

  PrintInfo(attrib, shapes, materials);

  return true;
}


static bool
TestStreamLoadObj()
{
  std::cout << "Stream Loading " << std::endl;

  std::stringstream objStream;
  objStream
    << "mtllib cube.mtl\n"
    "\n"
    "v 0.000000 2.000000 2.000000\n"
    "v 0.000000 0.000000 2.000000\n"
    "v 2.000000 0.000000 2.000000\n"
    "v 2.000000 2.000000 2.000000\n"
    "v 0.000000 2.000000 0.000000\n"
    "v 0.000000 0.000000 0.000000\n"
    "v 2.000000 0.000000 0.000000\n"
    "v 2.000000 2.000000 0.000000\n"
    "# 8 vertices\n"
    "\n"
    "g front cube\n"
    "usemtl white\n"
    "f 1 2 3 4\n"
    "g back cube\n"
    "# expects white material\n"
    "f 8 7 6 5\n"
    "g right cube\n"
    "usemtl red\n"
    "f 4 3 7 8\n"
    "g top cube\n"
    "usemtl white\n"
    "f 5 1 4 8\n"
    "g left cube\n"
    "usemtl green\n"
    "f 5 6 2 1\n"
    "g bottom cube\n"
    "usemtl white\n"
    "f 2 6 7 3\n"
    "# 6 elements";

std::string matStream(
    "newmtl white\n"
    "Ka 0 0 0\n"
    "Kd 1 1 1\n"
    "Ks 0 0 0\n"
    "\n"
    "newmtl red\n"
    "Ka 0 0 0\n"
    "Kd 1 0 0\n"
    "Ks 0 0 0\n"
    "\n"
    "newmtl green\n"
    "Ka 0 0 0\n"
    "Kd 0 1 0\n"
    "Ks 0 0 0\n"
    "\n"
    "newmtl blue\n"
    "Ka 0 0 0\n"
    "Kd 0 0 1\n"
    "Ks 0 0 0\n"
    "\n"
    "newmtl light\n"
    "Ka 20 20 20\n"
    "Kd 1 1 1\n"
    "Ks 0 0 0");

    using namespace tinyobj;
    class MaterialStringStreamReader:
        public MaterialReader
    {
        public:
            MaterialStringStreamReader(const std::string& matSStream): m_matSStream(matSStream) {}
            virtual ~MaterialStringStreamReader() {}
            virtual bool operator() (
              const std::string& matId,
              std::vector<material_t>* materials,
              std::map<std::string, int>* matMap,
              std::string* err)
            {
                (void)matId;
                (void)err;
                LoadMtl(matMap, materials, &m_matSStream);
                return true;
            }

        private:
            std::stringstream m_matSStream;
    };

  MaterialStringStreamReader matSSReader(matStream);
  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string err;
  bool ret = tinyobj::LoadObj(&attrib, &shapes, &materials, &err, &objStream, &matSSReader);    
  
  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    return false;
  }

  PrintInfo(attrib, shapes, materials);
    
  return true;
}

int
main(
  int argc,
  char **argv)
{
  if (argc > 1) {
    const char* basepath = "models/";
    if (argc > 2) {
      basepath = argv[2];
    }
    assert(true == TestLoadObj(argv[1], basepath));
  } else {
    //assert(true == TestLoadObj("cornell_box.obj"));
    //assert(true == TestLoadObj("cube.obj"));
    assert(true == TestStreamLoadObj());
    assert(true == TestLoadObj("models/catmark_torus_creases0.obj", "models/", false));
  }

  return 0;
}
