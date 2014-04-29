#include "tiny_obj_loader.h"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

static void PrintInfo(const std::vector<tinyobj::shape_t>& shapes)
{
  std::cout << "# of shapes : " << shapes.size() << std::endl;

  for (size_t i = 0; i < shapes.size(); i++) {
    printf("shape[%ld].name = %s\n", i, shapes[i].name.c_str());
    printf("shape[%ld].indices: %ld\n", i, shapes[i].mesh.indices.size());
    assert((shapes[i].mesh.indices.size() % 3) == 0);
    for (size_t f = 0; f < shapes[i].mesh.indices.size(); f++) {
      printf("  idx[%ld] = %d\n", f, shapes[i].mesh.indices[f]);
    }

    printf("shape[%ld].vertices: %ld\n", i, shapes[i].mesh.positions.size());
    assert((shapes[i].mesh.positions.size() % 3) == 0);
    for (size_t v = 0; v < shapes[i].mesh.positions.size() / 3; v++) {
      printf("  v[%ld] = (%f, %f, %f)\n", v,
        shapes[i].mesh.positions[3*v+0],
        shapes[i].mesh.positions[3*v+1],
        shapes[i].mesh.positions[3*v+2]);
    }
  
    printf("shape[%ld].material.name = %s\n", i, shapes[i].material.name.c_str());
    printf("  material.Ka = (%f, %f ,%f)\n", shapes[i].material.ambient[0], shapes[i].material.ambient[1], shapes[i].material.ambient[2]);
    printf("  material.Kd = (%f, %f ,%f)\n", shapes[i].material.diffuse[0], shapes[i].material.diffuse[1], shapes[i].material.diffuse[2]);
    printf("  material.Ks = (%f, %f ,%f)\n", shapes[i].material.specular[0], shapes[i].material.specular[1], shapes[i].material.specular[2]);
    printf("  material.Tr = (%f, %f ,%f)\n", shapes[i].material.transmittance[0], shapes[i].material.transmittance[1], shapes[i].material.transmittance[2]);
    printf("  material.Ke = (%f, %f ,%f)\n", shapes[i].material.emission[0], shapes[i].material.emission[1], shapes[i].material.emission[2]);
    printf("  material.Ns = %f\n", shapes[i].material.shininess);
    printf("  material.Ni = %f\n", shapes[i].material.ior);
    printf("  material.dissolve = %f\n", shapes[i].material.dissolve);
    printf("  material.illum = %d\n", shapes[i].material.illum);
    printf("  material.map_Ka = %s\n", shapes[i].material.ambient_texname.c_str());
    printf("  material.map_Kd = %s\n", shapes[i].material.diffuse_texname.c_str());
    printf("  material.map_Ks = %s\n", shapes[i].material.specular_texname.c_str());
    printf("  material.map_Ns = %s\n", shapes[i].material.normal_texname.c_str());
    std::map<std::string, std::string>::const_iterator it(shapes[i].material.unknown_parameter.begin());
    std::map<std::string, std::string>::const_iterator itEnd(shapes[i].material.unknown_parameter.end());
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
  std::string err = tinyobj::LoadObj(shapes, filename, basepath);

  if (!err.empty()) {
    std::cerr << err << std::endl;
    return false;
  }

  PrintInfo(shapes);

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
            virtual std::string operator() (
              const std::string& matId,
              std::map<std::string, material_t>& matMap)
            {
                return LoadMtl(matMap, m_matSStream);
            }

        private:
            std::stringstream m_matSStream;
    };  

  MaterialStringStreamReader matSSReader(matStream);
  std::vector<tinyobj::shape_t> shapes;
  std::string err = tinyobj::LoadObj(shapes, objStream, matSSReader);    
  
  if (!err.empty()) {
    std::cerr << err << std::endl;
    return false;
  }

  PrintInfo(shapes);
    
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
    assert(true == TestLoadObj("cornell_box.obj"));
    assert(true == TestLoadObj("cube.obj"));
    assert(true == TestStreamLoadObj());
  }
  
  return 0;
}
