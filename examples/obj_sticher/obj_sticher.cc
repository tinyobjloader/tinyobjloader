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

void
StichObjs(
  std::vector<tinyobj::shape_t>& out,
  const std::vector<Shape>& shapes)
{
  int numShapes = 0;
  for (size_t i = 0; i < shapes.size(); i++) {
    numShapes += (int)shapes[i].size();
  }

  printf("Total # of shapes = %d\n", numShapes);

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
      new_shape.name = new_name;
      printf("shape[%ld][%ld].new_name = %s\n", i, k, new_shape.name.c_str());

      out.push_back(new_shape);
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
  shapes.resize(num_objfiles);

  for (int i = 0; i < num_objfiles; i++) {
    std::cout << "Loading " << argv[i+1] << " ... " << std::flush;
    
    std::string err = tinyobj::LoadObj(shapes[i], argv[i+1]);
    if (!err.empty()) {
      std::cerr << err << std::endl;
      exit(1);
    }

    std::cout << "DONE." << std::endl;
  }

  std::vector<tinyobj::shape_t> out;
  StichObjs(out, shapes);

  bool ret = WriteObj(out_filename, out);
  assert(ret);

  return 0;
}
