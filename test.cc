#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

static void PrintInfo(const std::vector<tinyobj::shape_t>& shapes, const std::vector<tinyobj::material_t>& materials)
{
  std::cout << "# of shapes    : " << shapes.size() << std::endl;
  std::cout << "# of materials : " << materials.size() << std::endl;

  for (size_t i = 0; i < shapes.size(); i++) {
    printf("shape[%ld].name = %s\n", i, shapes[i].name.c_str());
    printf("Size of shape[%ld].indices: %ld\n", i, shapes[i].mesh.indices.size());
    printf("Size of shape[%ld].material_ids: %ld\n", i, shapes[i].mesh.material_ids.size());
    assert((shapes[i].mesh.indices.size() % 3) == 0);
    for (size_t f = 0; f < shapes[i].mesh.indices.size() / 3; f++) {
      printf("  idx[%ld] = %d, %d, %d. mat_id = %d\n", f, shapes[i].mesh.indices[3*f+0], shapes[i].mesh.indices[3*f+1], shapes[i].mesh.indices[3*f+2], shapes[i].mesh.material_ids[f]);
    }

    printf("shape[%ld].vertices: %ld\n", i, shapes[i].mesh.positions.size());
    assert((shapes[i].mesh.positions.size() % 3) == 0);
    for (size_t v = 0; v < shapes[i].mesh.positions.size() / 3; v++) {
      printf("  v[%ld] = (%f, %f, %f)\n", v,
        shapes[i].mesh.positions[3*v+0],
        shapes[i].mesh.positions[3*v+1],
        shapes[i].mesh.positions[3*v+2]);
    }
  }

  for (size_t i = 0; i < materials.size(); i++) {
    printf("material[%ld].name = %s\n", i, materials[i].name.c_str());
    printf("  material.Ka = (%f, %f ,%f)\n", materials[i].ambient[0], materials[i].ambient[1], materials[i].ambient[2]);
    printf("  material.Kd = (%f, %f ,%f)\n", materials[i].diffuse[0], materials[i].diffuse[1], materials[i].diffuse[2]);
    printf("  material.Ks = (%f, %f ,%f)\n", materials[i].specular[0], materials[i].specular[1], materials[i].specular[2]);
    printf("  material.Tr = (%f, %f ,%f)\n", materials[i].transmittance[0], materials[i].transmittance[1], materials[i].transmittance[2]);
    printf("  material.Ke = (%f, %f ,%f)\n", materials[i].emission[0], materials[i].emission[1], materials[i].emission[2]);
    printf("  material.Ns = %f\n", materials[i].shininess);
    printf("  material.Ni = %f\n", materials[i].ior);
    printf("  material.dissolve = %f\n", materials[i].dissolve);
    printf("  material.illum = %d\n", materials[i].illum);
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
  const char* basepath = NULL)
{
  std::cout << "Loading " << filename << std::endl;

  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;

  std::string err;
  bool ret = tinyobj::LoadObj(shapes, materials, err, filename, basepath);

  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    return false;
  }

  PrintInfo(shapes, materials);

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
              std::vector<material_t>& materials,
              std::map<std::string, int>& matMap,
              std::string& err)
            {
                (void)matId;
                (void)err;
                LoadMtl(matMap, materials, m_matSStream);
                return true;
            }

        private:
            std::stringstream m_matSStream;
    };  

  MaterialStringStreamReader matSSReader(matStream);
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string err;
  bool ret = tinyobj::LoadObj(shapes, materials, err, objStream, matSSReader);    
  
  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    return false;
  }

  PrintInfo(shapes, materials);
    
  return true;
}

int
main(
  int argc,
  char **argv)
{

  if (argc > 1) {
    const char* basepath = NULL;
    if (argc > 2) {
      basepath = argv[2];
    }
    assert(true == TestLoadObj(argv[1], basepath));
  } else {
    //assert(true == TestLoadObj("cornell_box.obj"));
    //assert(true == TestLoadObj("cube.obj"));
    assert(true == TestStreamLoadObj());
  }
  
  return 0;
}
