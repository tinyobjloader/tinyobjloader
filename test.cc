#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

#ifdef _WIN32
#ifdef __cplusplus
extern "C" {
#endif
#include <windows.h>
#include <mmsystem.h>
#ifdef __cplusplus
}
#endif
#pragma comment(lib, "winmm.lib")
#else
#if defined(__unix__) || defined(__APPLE__)
#include <sys/time.h>
#else
#include <ctime>
#endif
#endif

// not thread-safe 
class timerutil {
public:
#ifdef _WIN32
  typedef DWORD time_t;

  timerutil() { ::timeBeginPeriod(1); }
  ~timerutil() { ::timeEndPeriod(1); }

  void start() { t_[0] = ::timeGetTime(); }
  void end() { t_[1] = ::timeGetTime(); }

  time_t sec() { return (time_t)((t_[1] - t_[0]) / 1000); }
  time_t msec() { return (time_t)((t_[1] - t_[0])); }
  time_t usec() { return (time_t)((t_[1] - t_[0]) * 1000); }
  time_t current() { return ::timeGetTime(); }

#else
#if defined(__unix__) || defined(__APPLE__)
  typedef unsigned long int time_t;

  void start() { gettimeofday(tv + 0, &tz); }
  void end() { gettimeofday(tv + 1, &tz); }

  time_t sec() { return (time_t)(tv[1].tv_sec - tv[0].tv_sec); }
  time_t msec() {
    return this->sec() * 1000 +
           (time_t)((tv[1].tv_usec - tv[0].tv_usec) / 1000);
  }
  time_t usec() {
    return this->sec() * 1000000 + (time_t)(tv[1].tv_usec - tv[0].tv_usec);
  }
  time_t current() {
    struct timeval t;
    gettimeofday(&t, NULL);
    return (time_t)(t.tv_sec * 1000 + t.tv_usec);
  }

#else // C timer
  // using namespace std;
  typedef clock_t time_t;

  void start() { t_[0] = clock(); }
  void end() { t_[1] = clock(); }

  time_t sec() { return (time_t)((t_[1] - t_[0]) / CLOCKS_PER_SEC); }
  time_t msec() { return (time_t)((t_[1] - t_[0]) * 1000 / CLOCKS_PER_SEC); }
  time_t usec() { return (time_t)((t_[1] - t_[0]) * 1000000 / CLOCKS_PER_SEC); }
  time_t current() { return (time_t)clock(); }

#endif
#endif

private:
#ifdef _WIN32
  DWORD t_[2];
#else
#if defined(__unix__) || defined(__APPLE__)
  struct timeval tv[2];
  struct timezone tz;
#else
  time_t t_[2];
#endif
#endif
};

static void PrintInfo(const std::vector<tinyobj::shape_t>& shapes, const std::vector<tinyobj::material_t>& materials, bool triangulate = true)
{
  std::cout << "# of shapes    : " << shapes.size() << std::endl;
  std::cout << "# of materials : " << materials.size() << std::endl;

  for (size_t i = 0; i < shapes.size(); i++) {
    printf("shape[%ld].name = %s\n", i, shapes[i].name.c_str());
    printf("Size of shape[%ld].indices: %ld\n", i, shapes[i].mesh.indices.size());

    if (triangulate)
    {
        printf("Size of shape[%ld].material_ids: %ld\n", i, shapes[i].mesh.material_ids.size());
        assert((shapes[i].mesh.indices.size() % 3) == 0);
        for (size_t f = 0; f < shapes[i].mesh.indices.size() / 3; f++) {
          printf("  idx[%ld] = %d, %d, %d. mat_id = %d\n", f, shapes[i].mesh.indices[3*f+0], shapes[i].mesh.indices[3*f+1], shapes[i].mesh.indices[3*f+2], shapes[i].mesh.material_ids[f]);
        }
    } else {
      for (size_t f = 0; f < shapes[i].mesh.indices.size(); f++) {
        printf("  idx[%ld] = %d\n", f, shapes[i].mesh.indices[f]);
      }

      printf("Size of shape[%ld].material_ids: %ld\n", i, shapes[i].mesh.material_ids.size());
      assert(shapes[i].mesh.material_ids.size() == shapes[i].mesh.num_vertices.size());
      for (size_t m = 0; m < shapes[i].mesh.material_ids.size(); m++) {
        printf("  material_id[%ld] = %d\n", m,
          shapes[i].mesh.material_ids[m]);
      }

    }

    printf("shape[%ld].num_faces: %ld\n", i, shapes[i].mesh.num_vertices.size());
    for (size_t v = 0; v < shapes[i].mesh.num_vertices.size(); v++) {
      printf("  num_vertices[%ld] = %ld\n", v,
        static_cast<long>(shapes[i].mesh.num_vertices[v]));
    }

    printf("shape[%ld].vertices: %ld\n", i, shapes[i].mesh.positions.size());
    assert((shapes[i].mesh.positions.size() % 3) == 0);
    for (size_t v = 0; v < shapes[i].mesh.positions.size() / 3; v++) {
      printf("  v[%ld] = (%f, %f, %f)\n", v,
        shapes[i].mesh.positions[3*v+0],
        shapes[i].mesh.positions[3*v+1],
        shapes[i].mesh.positions[3*v+2]);
    }

    printf("shape[%ld].num_tags: %ld\n", i, shapes[i].mesh.tags.size());
    for (size_t t = 0; t < shapes[i].mesh.tags.size(); t++) {
      printf("  tag[%ld] = %s ", t, shapes[i].mesh.tags[t].name.c_str());
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
          printf("%f", shapes[i].mesh.tags[t].floatValues[j]);
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
  const char* basepath = NULL,
  unsigned int flags = 1 )
{
  std::cout << "Loading " << filename << std::endl;

  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;

  timerutil t;
  t.start();
  std::string err;
  bool ret = tinyobj::LoadObj(shapes, materials, err, filename, basepath, flags);
  t.end();

  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  if (!ret) {
    printf("Failed to load/parse .obj.\n");
    return false;
  }

  printf("Parse time: %lu [msecs]\n", t.msec());

  bool triangulate( ( flags & tinyobj::triangulation ) == tinyobj::triangulation );
  PrintInfo(shapes, materials, triangulate );

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
    assert(true == TestLoadObj("catmark_torus_creases0.obj", NULL,  0));
  }

  return 0;
}
