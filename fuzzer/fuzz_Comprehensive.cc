#include <cstddef>
#include <cstdint>
#include <cstring>
#include <sstream>
#include <string>
#include <vector>
#include <map>

#include "tiny_obj_loader.h"

static void SplitPayload(const uint8_t *data, size_t size,
                         std::string &obj_text, std::string &mtl_text) {
  const uint8_t *sep = static_cast<const uint8_t *>(
      std::memchr(data, 0, size));
  if (sep) {
    size_t obj_len = static_cast<size_t>(sep - data);
    obj_text.assign(reinterpret_cast<const char *>(data), obj_len);
    size_t mtl_off = obj_len + 1;
    if (mtl_off < size) {
      mtl_text.assign(reinterpret_cast<const char *>(data + mtl_off),
                      size - mtl_off);
    } else {
      mtl_text.clear();
    }
  } else {
    obj_text.assign(reinterpret_cast<const char *>(data), size);
    mtl_text.clear();
  }
}

static void FuzzParseFromString(const uint8_t *data, size_t size,
                                bool triangulate, bool vertex_color) {
  std::string obj_text, mtl_text;
  SplitPayload(data, size, obj_text, mtl_text);

  tinyobj::ObjReaderConfig config;
  config.triangulate = triangulate;
  config.vertex_color = vertex_color;

  tinyobj::ObjReader reader;
  reader.ParseFromString(obj_text, mtl_text, config);
}

static void FuzzLoadObjOpt(const uint8_t *data, size_t size,
                           bool triangulate, bool float_cache,
                           bool fp32_cache) {
  tinyobj::basic_attrib_t<> attrib;
  std::vector<tinyobj::basic_shape_t<>> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.triangulate = triangulate;
  config.num_threads = 1;
  config.float_cache = float_cache;
  config.fp32_cache = fp32_cache;

  tinyobj::LoadObjOpt(&attrib, &shapes, &materials, &warn, &err,
                      reinterpret_cast<const char *>(data), size, config);
}

static void FuzzLoadObjOptTyped(const uint8_t *data, size_t size,
                                bool triangulate, bool float_cache,
                                bool fp32_cache) {
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.triangulate = triangulate;
  config.num_threads = 1;
  config.float_cache = float_cache;
  config.fp32_cache = fp32_cache;

  tinyobj::OptResult result = tinyobj::LoadObjOptTyped(
      reinterpret_cast<const char *>(data), size, &warn, &err, config);

  if (result.valid) {
    volatile size_t nv = result.attrib.vertices.size();
    volatile size_t ns = result.shapes.size();
    volatile size_t nm = result.materials.size();
    (void)nv;
    (void)ns;
    (void)nm;
  }
}

struct CallbackUserData {
  size_t vertex_count;
  size_t normal_count;
  size_t texcoord_count;
  size_t face_count;
  size_t group_count;
  size_t object_count;
  size_t usemtl_count;
  size_t mtllib_count;
};

static void cb_vertex(void *ud, tinyobj::real_t x, tinyobj::real_t y,
                      tinyobj::real_t z, tinyobj::real_t w) {
  (void)x; (void)y; (void)z; (void)w;
  static_cast<CallbackUserData *>(ud)->vertex_count++;
}

static void cb_vertex_color(void *ud, tinyobj::real_t x, tinyobj::real_t y,
                            tinyobj::real_t z, tinyobj::real_t r,
                            tinyobj::real_t g, tinyobj::real_t b,
                            bool has_color) {
  (void)x; (void)y; (void)z; (void)r; (void)g; (void)b; (void)has_color;
  static_cast<CallbackUserData *>(ud)->vertex_count++;
}

static void cb_normal(void *ud, tinyobj::real_t x, tinyobj::real_t y,
                      tinyobj::real_t z) {
  (void)x; (void)y; (void)z;
  static_cast<CallbackUserData *>(ud)->normal_count++;
}

static void cb_texcoord(void *ud, tinyobj::real_t x, tinyobj::real_t y,
                        tinyobj::real_t z) {
  (void)x; (void)y; (void)z;
  static_cast<CallbackUserData *>(ud)->texcoord_count++;
}

static void cb_index(void *ud, tinyobj::index_t *indices, int num_indices) {
  (void)indices; (void)num_indices;
  static_cast<CallbackUserData *>(ud)->face_count++;
}

static void cb_usemtl(void *ud, const char *name, int material_id) {
  (void)name; (void)material_id;
  static_cast<CallbackUserData *>(ud)->usemtl_count++;
}

static void cb_mtllib(void *ud, const tinyobj::material_t *materials,
                      int num_materials) {
  (void)materials; (void)num_materials;
  static_cast<CallbackUserData *>(ud)->mtllib_count++;
}

static void cb_group(void *ud, const char **names, int num_names) {
  (void)names; (void)num_names;
  static_cast<CallbackUserData *>(ud)->group_count++;
}

static void cb_object(void *ud, const char *name) {
  (void)name;
  static_cast<CallbackUserData *>(ud)->object_count++;
}

static void FuzzLoadObjWithCallback(const uint8_t *data, size_t size) {
  std::string obj_text, mtl_text;
  SplitPayload(data, size, obj_text, mtl_text);

  std::istringstream obj_stream(obj_text);
  std::istringstream mtl_stream(mtl_text);

  tinyobj::MaterialStreamReader mtl_reader(mtl_stream);
  CallbackUserData ud = {};

  tinyobj::callback_t cb;
  cb.vertex_cb = cb_vertex;
  cb.vertex_color_cb = cb_vertex_color;
  cb.normal_cb = cb_normal;
  cb.texcoord_cb = cb_texcoord;
  cb.index_cb = cb_index;
  cb.usemtl_cb = cb_usemtl;
  cb.mtllib_cb = cb_mtllib;
  cb.group_cb = cb_group;
  cb.object_cb = cb_object;

  std::string warn, err;
  tinyobj::LoadObjWithCallback(obj_stream, cb, &ud, &mtl_reader, &warn, &err);
}

static void FuzzLoadMtlDirect(const uint8_t *data, size_t size) {
  std::string mtl_text(reinterpret_cast<const char *>(data), size);
  std::istringstream mtl_stream(mtl_text);

  std::map<std::string, int> material_map;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::LoadMtl(&material_map, &materials, &mtl_stream, &warn, &err);

  size_t line_end = 0;
  while (line_end < size && data[line_end] != '\n' &&
         data[line_end] != '\r' && data[line_end] != '\0') {
    line_end++;
  }
  
  if (line_end > 4096) {
    line_end = 4096;
  }

  std::string line(reinterpret_cast<const char *>(data), line_end);

  std::string texname;
  tinyobj::texture_option_t texopt;
  
  texopt.type = tinyobj::TEXTURE_TYPE_NONE;
  texopt.sharpness = 1.0f;
  texopt.brightness = 0.0f;
  texopt.contrast = 1.0f;
  texopt.origin_offset[0] = 0.0f;
  texopt.origin_offset[1] = 0.0f;
  texopt.origin_offset[2] = 0.0f;
  texopt.scale[0] = 1.0f;
  texopt.scale[1] = 1.0f;
  texopt.scale[2] = 1.0f;
  texopt.turbulence[0] = 0.0f;
  texopt.turbulence[1] = 0.0f;
  texopt.turbulence[2] = 0.0f;
  texopt.texture_resolution = -1;
  texopt.clamp = false;
  texopt.imfchan = 'm';
  texopt.blendu = true;
  texopt.blendv = true;
  texopt.bump_multiplier = 1.0f;
  texopt.colorspace.clear();

  tinyobj::ParseTextureNameAndOption(&texname, &texopt, line.c_str());
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  if (Size < 3) {
    return 0;
  }

  uint8_t selector = Data[0] % 5;
  uint8_t config_bits = Data[1];
  
  bool triangulate   = (config_bits & 0x01) != 0;
  bool float_cache   = (config_bits & 0x02) != 0;
  bool fp32_cache    = (config_bits & 0x04) != 0;
  bool vertex_color  = (config_bits & 0x08) != 0;

  const uint8_t *payload = Data + 2;
  size_t payload_size = Size - 2;

  switch (selector) {
    case 0:
      FuzzParseFromString(payload, payload_size, triangulate, vertex_color);
      break;
    case 1:
      FuzzLoadObjOpt(payload, payload_size, triangulate, float_cache,
                     fp32_cache);
      break;
    case 2:
      FuzzLoadObjOptTyped(payload, payload_size, triangulate, float_cache,
                          fp32_cache);
      break;
    case 3:
      FuzzLoadObjWithCallback(payload, payload_size);
      break;
    case 4:
      FuzzLoadMtlDirect(payload, payload_size);
      break;
  }

  return 0;
}
