#ifndef TINYOBJ_EXPERIMENTAL_STREAM_OBJ_LOADER_H_
#define TINYOBJ_EXPERIMENTAL_STREAM_OBJ_LOADER_H_

#include <iosfwd>
#include <string>
#include <vector>

#include "tiny_obj_loader.h"

namespace tinyobj {
namespace experimental_stream {

struct StreamLoadConfig {
  bool triangulate;
  bool default_vcols_fallback;
  int num_threads;
  size_t chunk_line_count;

  StreamLoadConfig()
      : triangulate(true),
        default_vcols_fallback(false),
        num_threads(1),
        chunk_line_count(4096) {}
};

class StreamHandler {
 public:
  virtual ~StreamHandler() {}

  virtual void OnVertex(real_t x, real_t y, real_t z, bool has_weight,
                        real_t w, bool has_color, real_t r, real_t g,
                        real_t b) = 0;
  virtual void OnNormal(real_t x, real_t y, real_t z) = 0;
  virtual void OnTexcoord(real_t u, real_t v, bool has_w, real_t w) = 0;
  virtual void OnFace(const index_t *indices, size_t num_indices) = 0;
  virtual void OnDegenerateFace() {}
  virtual void OnGroup(const std::string &name) = 0;
  virtual void OnObject(const std::string &name) = 0;
  virtual void OnUsemtl(const std::string &name) = 0;
  virtual void OnMtllib(const std::vector<std::string> &filenames) = 0;
  virtual void OnMtllibWithLine(const std::vector<std::string> &filenames,
                                size_t line_num) {
    (void)line_num;
    OnMtllib(filenames);
  }
  virtual void OnSmoothingGroup(unsigned int smoothing_group_id) = 0;
};

bool ParseObjStream(std::istream *input, StreamHandler *handler,
                    std::string *warn, std::string *err,
                    const std::string &source_name,
                    const StreamLoadConfig &config = StreamLoadConfig());

bool LoadObjStreamExperimental(
    attrib_t *attrib, std::vector<shape_t> *shapes,
    std::vector<material_t> *materials, std::string *warn, std::string *err,
    std::istream *input, MaterialReader *readMatFn = NULL,
    const StreamLoadConfig &config = StreamLoadConfig());

bool LoadObjStreamExperimental(
    attrib_t *attrib, std::vector<shape_t> *shapes,
    std::vector<material_t> *materials, std::string *warn, std::string *err,
    const char *filename, const char *mtl_basedir = NULL,
    const StreamLoadConfig &config = StreamLoadConfig());

}  // namespace experimental_stream
}  // namespace tinyobj

#endif  // TINYOBJ_EXPERIMENTAL_STREAM_OBJ_LOADER_H_
