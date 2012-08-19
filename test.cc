#include "tiny_obj_loader.h"

#include <cassert>
#include <iostream>

int
main(
  int argc,
  char **argv)
{
  std::string inputfile = "cornell_box.obj";
  std::vector<tinyobj::shape_t> shapes;

  if (argc > 1) {
    inputfile = std::string(argv[1]);
  }
  
  std::string err = tinyobj::LoadObj(shapes, inputfile.c_str());

  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

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
  }

  return 0;
}
