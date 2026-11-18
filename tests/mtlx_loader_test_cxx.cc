// C++ loader: material_t::mtlx_lines must give the same verdicts as the whole-file parse.
#define TINYOBJLOADER_IMPLEMENTATION
#include "../tiny_obj_loader.h"
#include <cstdio>
#include <fstream>
#include <sstream>
#include <vector>
#include "../tobj_mtlx.h"

int main(int argc, char **argv) {
  int fails = 0, skipped = 0;
  for (int a = 1; a < argc; a++) {
    std::ifstream f(argv[a], std::ios::binary);
    std::stringstream ss; ss << f.rdbuf();
    std::string text = ss.str();
    tobj_mtlx_doc whole;
    if (tobj_mtlx_parse(text.data(), text.size(), &whole)) return 3;
    std::istringstream in(text);
    std::map<std::string, int> mm;
    std::vector<tinyobj::material_t> mats;
    std::string warn, err;
    tinyobj::LoadMtl(&mm, &mats, &in, &warn, &err);
    // The C++ loader names materials by its own rules ("newmtl a b" -> "a",
    // empty names dropped); compare only files where the naming agrees.
    bool same = mats.size() == whole.num_materials;
    for (size_t i = 0; same && i < mats.size(); i++) same = mats[i].name == whole.materials[i].name;
    if (!same) { skipped++; tobj_mtlx_free(&whole); continue; }
    size_t wi = 0;
    for (const auto &m : mats) {
      while (wi < whole.num_materials && m.name != whole.materials[wi].name) wi++;
      if (wi == whole.num_materials) { std::printf("FAIL %s: %s missing\n", argv[a], m.name.c_str()); fails++; break; }
      const tobj_mtlx_material &w = whole.materials[wi++];
      std::vector<const char *> lines;
      for (const auto &l : m.mtlx_lines) lines.push_back(l.c_str());
      tobj_mtlx_doc one;
      if (tobj_mtlx_parse_lines(m.name.c_str(), lines.data(), lines.size(), &one)) return 3;
      if (one.materials[0].ext != w.ext || one.materials[0].ok != w.ok) {
        std::printf("FAIL %s: %s %d/%d vs %d/%d\n", argv[a], m.name.c_str(), one.materials[0].ext,
                    one.materials[0].ok, w.ext, w.ok);
        fails++;
      }
      for (const auto &kv : m.unknown_parameter)
        if (kv.first.rfind("mtlx_", 0) == 0) { std::printf("FAIL leak %s\n", kv.first.c_str()); fails++; }
      tobj_mtlx_free(&one);
    }
    tobj_mtlx_free(&whole);
  }
  std::printf("mtlx C++ loader test: %s (%d of %d files skipped: C++ material naming differs)\n", fails ? "FAIL" : "ok", skipped, argc - 1);
  return fails != 0;
}
