// subd_test_cxx FILE.obj: C++ loader (triangulate = false) + tobj_subd per
// shape. Same output as tests/subd_test.c, compared to the same golden files.
#define TINYOBJLOADER_IMPLEMENTATION
#include <cstdio>
#include <vector>

#include "../tiny_obj_loader.h"
#include "../tobj_subd.h"

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  tinyobj::ObjReaderConfig cfg;
  cfg.triangulate = false;
  tinyobj::ObjReader r;
  if (!r.ParseFromFile(argv[1], cfg)) {
    std::printf("load failed: %s\n", r.Error().c_str());
    return 1;
  }
  for (const tinyobj::shape_t &sh : r.GetShapes()) {
    const tinyobj::mesh_t &m = sh.mesh;
    std::vector<const char *> lines;
    for (const std::string &l : m.tag_lines) lines.push_back(l.c_str());
    std::vector<int> vi;
    for (const tinyobj::index_t &i : m.indices) vi.push_back(i.vertex_index);
    tobj_subd sd;
    if (tobj_subd_parse_lines(lines.data(), lines.size(), m.num_face_vertices.data(),
                              m.num_face_vertices.size(), vi.data(), &sd))
      return 1;
    std::printf("shape %s faces=%zu tags=%zu/%zu ok=%d\n", sh.name.c_str(),
                m.num_face_vertices.size(), m.tags.size(), m.tag_lines.size(), sd.ok);
    for (size_t e = 0; e < sd.num_errors; e++) std::printf("  error: %s\n", sd.errors[e]);
    char *t = tobj_subd_to_lines(&sd, nullptr);
    if (!t) return 1;
    std::fputs(t, stdout);
    std::free(t);
    tobj_subd_free(&sd);
  }
  return 0;
}
