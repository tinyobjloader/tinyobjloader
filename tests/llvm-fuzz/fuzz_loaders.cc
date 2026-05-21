#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "../../experimental/stream/stream_obj_loader.h"

#include <sstream>
#include <string>
#include <vector>

#include "../fuzz_common.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  // Cap input size to prevent per-iteration memory explosion from running
  // 5 parsers (ObjReader, LoadObj, LoadObjOpt, StreamLoader, LoadObjOptTyped)
  // simultaneously.  Inputs above this threshold are unlikely to find new
  // coverage but can push RSS past the limit.
  if (size > 4096) return 0;

  std::string obj_text;
  std::string mtl_text;
  tinyobj_fuzz::SplitInput(data, size, &obj_text, &mtl_text);

  tinyobj::ObjReaderConfig reader_config;
  reader_config.triangulate = (size == 0) ? true : ((data[0] & 1u) != 0u);
  reader_config.vertex_color = (size > 1) ? ((data[1] & 1u) != 0u) : false;

  tinyobj::ObjReader reader;
  reader.ParseFromString(obj_text, mtl_text, reader_config);

  tinyobj_fuzz::InMemoryMaterialReader material_reader(mtl_text);

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn;
  std::string legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream,
                                    &material_reader, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<> > opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn;
  std::string opt_err;
  tinyobj::OptLoadConfig opt_config;
  opt_config.triangulate = true;
  opt_config.num_threads = (size > 2) ? static_cast<int>((data[2] % 4u) + 1u) : 2;
  tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials, &opt_warn,
                      &opt_err, obj_text.data(), obj_text.size(), opt_config);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn;
  std::string stream_err;
  std::istringstream stream_input(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig stream_config;
  stream_config.triangulate = true;
  stream_config.num_threads =
      (size > 3) ? static_cast<int>((data[3] % 4u) + 1u) : 2;
  stream_config.chunk_line_count = 32u + (size > 4 ? data[4] : 64u);
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream_input, &material_reader, stream_config);

  const bool can_cross_check =
      tinyobj_fuzz::IsTextLikeObj(obj_text) &&
      tinyobj_fuzz::IsSharedSubsetForCrossCheck(obj_text);
  const bool both_have_faces =
      tinyobj_fuzz::ShapeIndexCount(legacy_shapes) > 0 &&
      tinyobj_fuzz::ShapeIndexCount(stream_shapes) > 0;
  const bool clean_parse = legacy_err.empty() && stream_err.empty() &&
                           legacy_warn.empty() && stream_warn.empty();

  if (can_cross_check && both_have_faces && clean_parse && legacy_ok && stream_ok) {
    assert(tinyobj_fuzz::LegacyAttribEquals(legacy_attrib, stream_attrib));
    assert(tinyobj_fuzz::LegacyShapesEqual(legacy_shapes, stream_shapes));
    assert(
        tinyobj_fuzz::LegacyMaterialsEqual(legacy_materials, stream_materials));
  }

  (void)opt_attrib;
  (void)opt_shapes;
  (void)opt_materials;

  // Exercise LoadObjOptTyped (TypedArray/arena path)
  {
    std::string typed_warn;
    std::string typed_err;
    tinyobj::OptLoadConfig typed_config;
    typed_config.triangulate = true;
    typed_config.num_threads = 1;
    // Toggle cache based on input byte to exercise both paths
    typed_config.float_cache = (size > 5) ? ((data[5] & 1u) != 0u) : false;
    tinyobj::OptResult typed_result = tinyobj::LoadObjOptTyped(
        obj_text.data(), obj_text.size(), &typed_warn, &typed_err, typed_config);
    (void)typed_result;
  }

  return 0;
}
