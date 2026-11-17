// skel_test_cxx FILE.obj: C++ loader + tobj_skel on attrib_t::skel_lines, with
// the vw joint-id bound from attrib_t::skin_weights. Same output as
// tests/skel_test.c (same golden files).
#define TINYOBJLOADER_IMPLEMENTATION
#include <cstdio>
#include <vector>

#include "../tiny_obj_loader.h"
#include "../tobj_skel.h"

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  tinyobj::ObjReaderConfig cfg;
  tinyobj::ObjReader r;
  if (!r.ParseFromFile(argv[1], cfg)) {
    std::printf("load failed\n");
    return 1;
  }
  const tinyobj::attrib_t &a = r.GetAttrib();
  long max_id = -1;
  for (const auto &sw : a.skin_weights)
    for (const auto &jw : sw.weightValues)
      if (jw.joint_id > max_id) max_id = jw.joint_id;
  std::vector<const char *> lines;
  for (const std::string &l : a.skel_lines) lines.push_back(l.c_str());
  tobj_skel s;
  if (tobj_skel_parse_lines(lines.data(), lines.size(), max_id, &s)) return 1;
  std::printf("skel ext=%d ok=%d joints=%zu lines=%zu\n", s.ext, s.ok, s.num_joints,
              a.skel_lines.size());
  for (size_t e = 0; e < s.num_errors; e++) std::printf("  error: %s\n", s.errors[e]);
  char *t = tobj_skel_to_lines(&s, nullptr);
  if (!t) return 1;
  std::fputs(t, stdout);
  std::free(t);
  tobj_skel_free(&s);
  return 0;
}
