#include <stdint.h>

#include <cstdlib>
#include "../../experimental/stream/stream_obj_loader.h"

#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>

#include "../fuzz_common.h"

namespace {

struct Options {
  uint64_t seed;
  size_t iterations;
  size_t max_vertices;
  size_t max_faces;
  bool allow_mtllib;
  bool strict_opt;

  Options()
      : seed(1),
        iterations(1000),
        max_vertices(128),
        max_faces(128),
        allow_mtllib(false),
        strict_opt(false) {}
};

struct GeneratedCase {
  std::string obj_text;
  std::string mtl_text;
};

class Rng {
 public:
  explicit Rng(uint64_t seed) : state_(seed ? seed : 0x9e3779b97f4a7c15ULL) {}

  uint64_t NextU64() {
    uint64_t x = state_;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    state_ = x;
    return x * 0x2545F4914F6CDD1DULL;
  }

  uint32_t NextU32() {
    return static_cast<uint32_t>(NextU64() >> 32);
  }

  size_t Uniform(size_t upper_bound) {
    if (upper_bound == 0) {
      return 0;
    }
    return static_cast<size_t>(NextU64() % upper_bound);
  }

  bool OneIn(size_t n) {
    return Uniform(n) == 0;
  }

  bool Bool() {
    return (NextU32() & 1u) != 0u;
  }

  double Real(double min_value, double max_value) {
    const double unit =
        static_cast<double>(NextU64() & 0x1fffffffffffffULL) /
        static_cast<double>(0x1fffffffffffffULL);
    return min_value + (max_value - min_value) * unit;
  }

 private:
  uint64_t state_;
};

std::string FormatReal(double value) {
  std::ostringstream os;
  os.setf(std::ios::fixed);
  os.precision(6);
  os << value;
  return os.str();
}

std::string MakeIndexToken(Rng *rng, size_t v_count, size_t vt_count,
                           size_t vn_count) {
  const bool use_negative = (v_count > 0) && rng->OneIn(3);
  const int v_idx = use_negative
                        ? -static_cast<int>(rng->Uniform(v_count) + 1)
                        : static_cast<int>(rng->Uniform(v_count) + 1);
  const int vt_idx = rng->OneIn(3)
                         ? -static_cast<int>(rng->Uniform(vt_count) + 1)
                         : static_cast<int>(rng->Uniform(vt_count) + 1);
  const int vn_idx = rng->OneIn(3)
                         ? -static_cast<int>(rng->Uniform(vn_count) + 1)
                         : static_cast<int>(rng->Uniform(vn_count) + 1);

  std::ostringstream os;
  os << v_idx << "/" << vt_idx << "/" << vn_idx;
  return os.str();
}

GeneratedCase BuildCase(Rng *rng, const Options &options) {
  GeneratedCase out;
  const bool has_mtllib = options.allow_mtllib && rng->OneIn(4);
  const size_t material_count = 1 + rng->Uniform(4);
  const size_t vertex_count = 3 + rng->Uniform(options.max_vertices);
  const size_t texcoord_count = 1 + rng->Uniform(options.max_vertices);
  const size_t normal_count = 1 + rng->Uniform(options.max_vertices);
  const size_t face_count = 1 + rng->Uniform(options.max_faces);

  std::vector<std::string> materials;
  for (size_t i = 0; i < material_count; i++) {
    std::ostringstream name;
    name << "mat_" << i;
    materials.push_back(name.str());
    out.mtl_text += "newmtl " + name.str() + "\n";
    out.mtl_text += "Kd " + FormatReal(rng->Real(0.0, 1.0)) + " " +
                    FormatReal(rng->Real(0.0, 1.0)) + " " +
                    FormatReal(rng->Real(0.0, 1.0)) + "\n";
  }

  if (has_mtllib) {
    out.obj_text += "mtllib fuzz.mtl\n";
  }
  out.obj_text += "o fuzz_object\n";
  out.obj_text += "g fuzz_group_0\n";

  for (size_t i = 0; i < vertex_count; i++) {
    out.obj_text += "v " + FormatReal(rng->Real(-10.0, 10.0)) + " " +
                    FormatReal(rng->Real(-10.0, 10.0)) + " " +
                    FormatReal(rng->Real(-10.0, 10.0));
    if (rng->OneIn(10)) {
      out.obj_text += " # vertex";
    }
    out.obj_text += "\n";
  }

  for (size_t i = 0; i < texcoord_count; i++) {
    out.obj_text += "vt " + FormatReal(rng->Real(-2.0, 2.0)) + " " +
                    FormatReal(rng->Real(-2.0, 2.0)) + "\n";
  }

  for (size_t i = 0; i < normal_count; i++) {
    out.obj_text += "vn " + FormatReal(rng->Real(-1.0, 1.0)) + " " +
                    FormatReal(rng->Real(-1.0, 1.0)) + " " +
                    FormatReal(rng->Real(-1.0, 1.0)) + "\n";
  }

  out.obj_text += "usemtl " + materials[rng->Uniform(materials.size())] + "\n";
  out.obj_text += rng->Bool() ? "s 1\n" : "s off\n";

  for (size_t i = 0; i < face_count; i++) {
    if (rng->OneIn(7)) {
      std::ostringstream group_name;
      group_name << "g fuzz_group_" << i;
      out.obj_text += group_name.str() + "\n";
    }
    if (rng->OneIn(9)) {
      std::ostringstream object_name;
      object_name << "o fuzz_object_" << i;
      out.obj_text += object_name.str() + "\n";
    }
    if (rng->OneIn(5)) {
      out.obj_text += "usemtl " + materials[rng->Uniform(materials.size())] +
                      "\n";
    }
    if (rng->OneIn(6)) {
      out.obj_text += rng->Bool() ? "s 2\n" : "s off\n";
    }

    const size_t verts_in_face = 3;
    out.obj_text += "f";
    for (size_t v = 0; v < verts_in_face; v++) {
      out.obj_text += " " +
                      MakeIndexToken(rng, vertex_count, texcoord_count,
                                     normal_count);
    }
    if (rng->OneIn(6)) {
      out.obj_text += " # face";
    }
    out.obj_text += "\n";
  }

  return out;
}

void PrintUsage(const char *argv0) {
  std::cerr << "Usage: " << argv0
            << " [--iterations N] [--seed N] [--max-vertices N]"
               " [--max-faces N] [--allow-mtllib] [--strict-opt]\n";
}

bool ParseSizeArg(const char *value, size_t *out) {
  if (!value || !out) {
    return false;
  }
  char *end = NULL;
  unsigned long long parsed = strtoull(value, &end, 10);
  if (!end || *end != '\0') {
    return false;
  }
  if (parsed > static_cast<unsigned long long>(
                   (std::numeric_limits<size_t>::max)())) {
    return false;
  }
  *out = static_cast<size_t>(parsed);
  return true;
}

bool ParseU64Arg(const char *value, uint64_t *out) {
  if (!value || !out) {
    return false;
  }
  char *end = NULL;
  unsigned long long parsed = strtoull(value, &end, 10);
  if (!end || *end != '\0') {
    return false;
  }
  *out = static_cast<uint64_t>(parsed);
  return true;
}

}  // namespace

int main(int argc, char **argv) {
  Options options;
  for (int i = 1; i < argc; i++) {
    const std::string arg(argv[i]);
    if (arg == "--iterations" && (i + 1) < argc) {
      if (!ParseSizeArg(argv[++i], &options.iterations)) {
        PrintUsage(argv[0]);
        return 2;
      }
    } else if (arg == "--seed" && (i + 1) < argc) {
      if (!ParseU64Arg(argv[++i], &options.seed)) {
        PrintUsage(argv[0]);
        return 2;
      }
    } else if (arg == "--max-vertices" && (i + 1) < argc) {
      if (!ParseSizeArg(argv[++i], &options.max_vertices)) {
        PrintUsage(argv[0]);
        return 2;
      }
    } else if (arg == "--max-faces" && (i + 1) < argc) {
      if (!ParseSizeArg(argv[++i], &options.max_faces)) {
        PrintUsage(argv[0]);
        return 2;
      }
    } else if (arg == "--allow-mtllib") {
      options.allow_mtllib = true;
    } else if (arg == "--strict-opt") {
      options.strict_opt = true;
    } else if (arg == "--help") {
      PrintUsage(argv[0]);
      return 0;
    } else {
      PrintUsage(argv[0]);
      return 2;
    }
  }

  Rng rng(options.seed);
  for (size_t iter = 0; iter < options.iterations; iter++) {
    const GeneratedCase generated = BuildCase(&rng, options);
    tinyobj_fuzz::InMemoryMaterialReader material_reader(generated.mtl_text);

    tinyobj::attrib_t legacy_attrib;
    std::vector<tinyobj::shape_t> legacy_shapes;
    std::vector<tinyobj::material_t> legacy_materials;
    std::string legacy_warn;
    std::string legacy_err;
    std::istringstream legacy_stream(generated.obj_text);
    const bool legacy_ok = tinyobj::LoadObj(
        &legacy_attrib, &legacy_shapes, &legacy_materials, &legacy_warn,
        &legacy_err, &legacy_stream, &material_reader, true, false);

    tinyobj::ObjReaderConfig reader_config;
    reader_config.triangulate = true;
    reader_config.vertex_color = false;
    tinyobj::ObjReader reader;
    reader.ParseFromString(generated.obj_text, generated.mtl_text, reader_config);

    tinyobj::basic_attrib_t<> opt_attrib;
    std::vector<tinyobj::basic_shape_t<> > opt_shapes;
    std::vector<tinyobj::material_t> opt_materials;
    std::string opt_warn;
    std::string opt_err;
    tinyobj::OptLoadConfig opt_config;
    opt_config.triangulate = true;
    opt_config.num_threads = 4;
    const bool opt_ok =
        tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                            &opt_warn, &opt_err, generated.obj_text.data(),
                            generated.obj_text.size(), opt_config);

    tinyobj::attrib_t stream_attrib;
    std::vector<tinyobj::shape_t> stream_shapes;
    std::vector<tinyobj::material_t> stream_materials;
    std::string stream_warn;
    std::string stream_err;
    std::istringstream stream_input(generated.obj_text);
    tinyobj::experimental_stream::StreamLoadConfig stream_config;
    stream_config.triangulate = true;
    stream_config.num_threads = 4;
    stream_config.chunk_line_count = 64;
    const bool stream_ok =
        tinyobj::experimental_stream::LoadObjStreamExperimental(
            &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
            &stream_err, &stream_input, &material_reader, stream_config);

    if (legacy_ok != stream_ok) {
      std::cerr << "legacy/stream success mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (options.strict_opt && !options.allow_mtllib && legacy_ok != opt_ok) {
      std::cerr << "legacy/opt success mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (legacy_ok && !tinyobj_fuzz::LegacyAttribEquals(
                         legacy_attrib, reader.GetAttrib())) {
      std::cerr << "legacy/ObjReader attrib mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (legacy_ok && !tinyobj_fuzz::LegacyShapesEqual(legacy_shapes,
                                                      reader.GetShapes())) {
      std::cerr << "legacy/ObjReader shape mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (legacy_ok && !tinyobj_fuzz::LegacyAttribEquals(legacy_attrib,
                                                       stream_attrib)) {
      std::cerr << "legacy/stream attrib mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (legacy_ok &&
        !tinyobj_fuzz::LegacyShapesEqual(legacy_shapes, stream_shapes)) {
      std::cerr << "legacy/stream shape mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (options.strict_opt && !options.allow_mtllib && legacy_ok &&
        !tinyobj_fuzz::LegacyAttribEqualsOpt(legacy_attrib, opt_attrib)) {
      std::cerr << "legacy/opt attrib mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    if (options.strict_opt && !options.allow_mtllib && legacy_ok &&
        !tinyobj_fuzz::LegacyShapesEqualOpt(legacy_shapes, opt_shapes)) {
      std::cerr << "legacy/opt shape mismatch at iteration " << iter
                << " seed " << options.seed << "\n";
      std::cerr << generated.obj_text << "\n";
      return 1;
    }

    // Exercise LoadObjOptTyped (TypedArray/arena path) — crash/ASAN check
    {
      std::string typed_warn, typed_err;
      tinyobj::OptLoadConfig typed_config;
      typed_config.triangulate = true;
      typed_config.num_threads = 1;
      typed_config.float_cache = (iter & 1u) != 0u;  // alternate cache on/off
      tinyobj::OptResult typed_result = tinyobj::LoadObjOptTyped(
          generated.obj_text.data(), generated.obj_text.size(),
          &typed_warn, &typed_err, typed_config);
      (void)typed_result;
    }
  }

  std::cout << "obj_fuzz: completed " << options.iterations
            << " iterations with seed " << options.seed << "\n";
  return 0;
}
