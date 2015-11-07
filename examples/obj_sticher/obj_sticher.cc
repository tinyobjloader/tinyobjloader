//
// Stiches multiple .obj files into one .obj. 
//
#include "../../tiny_obj_loader.h"
#include "obj_writer.h"

#include <cassert>
#include <iostream>
#include <cstdlib>
#include <cstdio>

typedef std::vector<tinyobj::shape_t> Shape;
typedef std::vector<tinyobj::material_t> Material;

void
StichObjs(
  std::vector<tinyobj::shape_t>& out_shape,
  std::vector<tinyobj::material_t>& out_material,
  const std::vector<Shape>& shapes,
  const std::vector<Material>& materials)
{
  int numShapes = 0;
  for (size_t i = 0; i < shapes.size(); i++) {
    numShapes += (int)shapes[i].size();
  }

  printf("Total # of shapes = %d\n", numShapes);
  int materialIdOffset = 0;

  size_t face_offset = 0;
  for (size_t i = 0; i < shapes.size(); i++) {

    for (size_t k = 0; k < shapes[i].size(); k++) {

      std::string new_name = shapes[i][k].name;
      // Add suffix
      char buf[1024];
      sprintf(buf, "_%04d", (int)i);
      new_name += std::string(buf);

      printf("shape[%ld][%ld].name = %s\n", i, k, shapes[i][k].name.c_str());
      assert((shapes[i][k].mesh.indices.size() % 3) == 0);
      assert((shapes[i][k].mesh.positions.size() % 3) == 0);

      tinyobj::shape_t new_shape = shapes[i][k];
      // Add offset.
      for (size_t f = 0; f < new_shape.mesh.material_ids.size(); f++) {
        new_shape.mesh.material_ids[f] += materialIdOffset;
      }

      new_shape.name = new_name;
      printf("shape[%ld][%ld].new_name = %s\n", i, k, new_shape.name.c_str());

      out_shape.push_back(new_shape);
    }

    materialIdOffset += materials[i].size();
  }

  for (size_t i = 0; i < materials.size(); i++) {
    for (size_t k = 0; k < materials[i].size(); k++) {
      out_material.push_back(materials[i][k]);
    }
  }

}

int
main(
  int argc,
  char **argv)
{
  if (argc < 3) {
    printf("Usage: obj_sticher input0.obj input1.obj ... output.obj\n");
    exit(1);
  }

  int num_objfiles = argc - 2;
  std::string out_filename = std::string(argv[argc-1]); // last element

  std::vector<Shape> shapes;
  std::vector<Material> materials;
  shapes.resize(num_objfiles);
  materials.resize(num_objfiles);

  for (int i = 0; i < num_objfiles; i++) {
    std::cout << "Loading " << argv[i+1] << " ... " << std::flush;
    
    std::string err;
    bool ret = tinyobj::LoadObj(shapes[i], materials[i], err, argv[i+1]);
    if (!err.empty()) {
      std::cerr << err << std::endl;
    }
    if (!ret) {
      exit(1);
    }

    std::cout << "DONE." << std::endl;
  }

  std::vector<tinyobj::shape_t> out_shape;
  std::vector<tinyobj::material_t> out_material;
  StichObjs(out_shape, out_material, shapes, materials);

  bool coordTransform = true;
  bool ret = WriteObj(out_filename, out_shape, out_material, coordTransform);
  assert(ret);

  return 0;
}
