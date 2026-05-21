#include "stream_obj_loader.h"

#include <cassert>
#include <cctype>
#include <cerrno>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <thread>

namespace tinyobj {
namespace experimental_stream {
namespace {

struct RawIndex {
  int vertex_index;
  int texcoord_index;
  int normal_index;
  bool has_texcoord_index;
  bool has_normal_index;

  RawIndex()
      : vertex_index(0),
        texcoord_index(0),
        normal_index(0),
        has_texcoord_index(false),
        has_normal_index(false) {}
};

enum ParsedEventType {
  EVENT_VERTEX,
  EVENT_NORMAL,
  EVENT_TEXCOORD,
  EVENT_FACE,
  EVENT_GROUP,
  EVENT_OBJECT,
  EVENT_USEMTL,
  EVENT_MTLLIB,
  EVENT_SMOOTHING,
  EVENT_WARNING
};

struct ParsedEvent {
  ParsedEventType type;
  size_t line_num;
  real_t x, y, z;
  real_t vertex_weight;
  real_t r, g, b;
  real_t w;
  bool has_vertex_weight;
  bool has_color;
  bool has_texcoord_w;
  std::vector<RawIndex> face;
  std::vector<std::string> filenames;
  std::string text;
  unsigned int smoothing_group_id;

  ParsedEvent()
      : type(EVENT_WARNING),
        line_num(0),
        x(real_t(0)),
        y(real_t(0)),
        z(real_t(0)),
        vertex_weight(real_t(1)),
        r(real_t(1)),
        g(real_t(1)),
        b(real_t(1)),
        w(real_t(0)),
        has_vertex_weight(false),
        has_color(false),
        has_texcoord_w(false),
        smoothing_group_id(0) {}
};

struct ParsedChunk {
  std::vector<ParsedEvent> events;
  std::string err;
};

static std::string Trim(const std::string &s) {
  size_t begin = 0;
  while (begin < s.size() &&
         (s[begin] == ' ' || s[begin] == '\t' || s[begin] == '\r')) {
    begin++;
  }

  size_t end = s.size();
  while (end > begin &&
         (s[end - 1] == ' ' || s[end - 1] == '\t' || s[end - 1] == '\r')) {
    end--;
  }

  return s.substr(begin, end - begin);
}

static std::string TrimLeading(const std::string &s) {
  size_t begin = 0;
  while (begin < s.size() &&
         (s[begin] == ' ' || s[begin] == '\t' || s[begin] == '\r')) {
    begin++;
  }
  return s.substr(begin);
}

static bool ParseRealToken(const std::string &token, real_t *value) {
  if (!value) return false;

  char *end = NULL;
  errno = 0;
  double v = std::strtod(token.c_str(), &end);
  if (end == token.c_str() || (end && *end != '\0') || errno == ERANGE) {
    return false;
  }

  *value = static_cast<real_t>(v);
  return true;
}

static bool ParseIntToken(const std::string &token, int *value) {
  if (!value) return false;

  char *end = NULL;
  errno = 0;
  long v = std::strtol(token.c_str(), &end, 10);
  if (end == token.c_str() || (end && *end != '\0') || errno == ERANGE) {
    return false;
  }
  if (v < static_cast<long>(std::numeric_limits<int>::min()) ||
      v > static_cast<long>(std::numeric_limits<int>::max())) {
    return false;
  }

  *value = static_cast<int>(v);
  return true;
}

template <typename T>
static int PointInPolygon(int nvert, T *vertx, T *verty, T testx, T testy) {
  int c = 0;
  for (int i = 0, j = nvert - 1; i < nvert; j = i++) {
    if (((verty[i] > testy) != (verty[j] > testy)) &&
        (testx < (vertx[j] - vertx[i]) * (testy - verty[i]) /
                         (verty[j] - verty[i]) +
                     vertx[i])) {
      c = !c;
    }
  }
  return c;
}

static void AppendZeroIndexWarning(std::string *warn,
                                   const std::string &source_name,
                                   size_t line_num) {
  if (!warn) return;

  std::stringstream ss;
  ss << source_name << ":" << line_num
     << ": warning: zero value index found (will have a value of -1 for "
        "normal and tex indices)\n";
  (*warn) += ss.str();
}

static bool ResolveIndexLikeLegacy(int idx, int n, int *ret, bool allow_zero,
                                   const std::string &source_name,
                                   size_t line_num, std::string *warn) {
  if (!ret) return false;
  if (idx > 0) {
    (*ret) = idx - 1;
    return true;
  }
  if (idx == 0) {
    AppendZeroIndexWarning(warn, source_name, line_num);
    (*ret) = -1;
    return allow_zero;
  }

  (*ret) = n + idx;
  return ((*ret) >= 0);
}

static void UpdateGreatestIndex(int idx, int *greatest) {
  if (!greatest) return;
  if (idx > *greatest) {
    *greatest = idx;
  }
}

static void AppendOutOfBoundsWarnings(std::string *warn,
                                      int greatest_v_idx,
                                      int greatest_vn_idx,
                                      int greatest_vt_idx,
                                      int num_vertices,
                                      int num_normals,
                                      int num_texcoords,
                                      size_t line_num) {
  if (!warn) return;

  if (greatest_v_idx >= num_vertices) {
    std::stringstream ss;
    ss << "Vertex indices out of bounds (line " << line_num << ".)\n\n";
    (*warn) += ss.str();
  }
  if (greatest_vn_idx >= num_normals) {
    std::stringstream ss;
    ss << "Vertex normal indices out of bounds (line " << line_num << ".)\n\n";
    (*warn) += ss.str();
  }
  if (greatest_vt_idx >= num_texcoords) {
    std::stringstream ss;
    ss << "Vertex texcoord indices out of bounds (line " << line_num
       << ".)\n\n";
    (*warn) += ss.str();
  }
}

static bool IsValidFaceVertex(const std::vector<real_t> &vertices,
                              const index_t &idx) {
  if (idx.vertex_index < 0) return false;
  const size_t vi = static_cast<size_t>(idx.vertex_index);
  return ((3 * vi + 2) < vertices.size());
}

static size_t TriangulateFaceLikeLegacy(const std::vector<real_t> &vertices,
                                        const index_t *face, size_t face_count,
                                        index_t *dst) {
  if (face_count < 3) return 0;
  if (face_count == 3) {
    dst[0] = face[0];
    dst[1] = face[1];
    dst[2] = face[2];
    return 3;
  }

  for (size_t i = 0; i < face_count; i++) {
    if (!IsValidFaceVertex(vertices, face[i])) {
      return 0;
    }
  }

  if (face_count == 4) {
    const size_t vi0 = static_cast<size_t>(face[0].vertex_index);
    const size_t vi1 = static_cast<size_t>(face[1].vertex_index);
    const size_t vi2 = static_cast<size_t>(face[2].vertex_index);
    const size_t vi3 = static_cast<size_t>(face[3].vertex_index);
    const real_t v0x = vertices[vi0 * 3 + 0];
    const real_t v0y = vertices[vi0 * 3 + 1];
    const real_t v0z = vertices[vi0 * 3 + 2];
    const real_t v1x = vertices[vi1 * 3 + 0];
    const real_t v1y = vertices[vi1 * 3 + 1];
    const real_t v1z = vertices[vi1 * 3 + 2];
    const real_t v2x = vertices[vi2 * 3 + 0];
    const real_t v2y = vertices[vi2 * 3 + 1];
    const real_t v2z = vertices[vi2 * 3 + 2];
    const real_t v3x = vertices[vi3 * 3 + 0];
    const real_t v3y = vertices[vi3 * 3 + 1];
    const real_t v3z = vertices[vi3 * 3 + 2];
    const real_t e02x = v2x - v0x;
    const real_t e02y = v2y - v0y;
    const real_t e02z = v2z - v0z;
    const real_t e13x = v3x - v1x;
    const real_t e13y = v3y - v1y;
    const real_t e13z = v3z - v1z;
    const real_t sqr02 = e02x * e02x + e02y * e02y + e02z * e02z;
    const real_t sqr13 = e13x * e13x + e13y * e13y + e13z * e13z;
    if (sqr02 < sqr13) {
      dst[0] = face[0];
      dst[1] = face[1];
      dst[2] = face[2];
      dst[3] = face[0];
      dst[4] = face[2];
      dst[5] = face[3];
    } else {
      dst[0] = face[0];
      dst[1] = face[1];
      dst[2] = face[3];
      dst[3] = face[1];
      dst[4] = face[2];
      dst[5] = face[3];
    }
    return 6;
  }

  std::vector<index_t> remaining(face, face + face_count);
  size_t axes[2] = {1, 2};
  for (size_t k = 0; k < face_count; ++k) {
    const size_t vi0 = static_cast<size_t>(face[(k + 0) % face_count].vertex_index);
    const size_t vi1 = static_cast<size_t>(face[(k + 1) % face_count].vertex_index);
    const size_t vi2 = static_cast<size_t>(face[(k + 2) % face_count].vertex_index);
    const real_t v0x = vertices[vi0 * 3 + 0];
    const real_t v0y = vertices[vi0 * 3 + 1];
    const real_t v0z = vertices[vi0 * 3 + 2];
    const real_t v1x = vertices[vi1 * 3 + 0];
    const real_t v1y = vertices[vi1 * 3 + 1];
    const real_t v1z = vertices[vi1 * 3 + 2];
    const real_t v2x = vertices[vi2 * 3 + 0];
    const real_t v2y = vertices[vi2 * 3 + 1];
    const real_t v2z = vertices[vi2 * 3 + 2];
    const real_t e0x = v1x - v0x;
    const real_t e0y = v1y - v0y;
    const real_t e0z = v1z - v0z;
    const real_t e1x = v2x - v1x;
    const real_t e1y = v2y - v1y;
    const real_t e1z = v2z - v1z;
    const real_t cx = std::fabs(e0y * e1z - e0z * e1y);
    const real_t cy = std::fabs(e0z * e1x - e0x * e1z);
    const real_t cz = std::fabs(e0x * e1y - e0y * e1x);
    const real_t epsilon = std::numeric_limits<real_t>::epsilon();
    if (cx > epsilon || cy > epsilon || cz > epsilon) {
      if (!(cx > cy && cx > cz)) {
        axes[0] = 0;
        if (cz > cx && cz > cy) {
          axes[1] = 1;
        }
      }
      break;
    }
  }

  size_t out = 0;
  size_t guess_vert = 0;
  size_t remaining_iterations = remaining.size();
  size_t previous_remaining_vertices = remaining.size();
  while (remaining.size() > 3 && remaining_iterations > 0) {
    const size_t npolys = remaining.size();
    if (guess_vert >= npolys) {
      guess_vert -= npolys;
    }
    if (previous_remaining_vertices != npolys) {
      previous_remaining_vertices = npolys;
      remaining_iterations = npolys;
    } else {
      remaining_iterations--;
    }

    index_t ind[3];
    real_t vx[3];
    real_t vy[3];
    for (size_t k = 0; k < 3; k++) {
      ind[k] = remaining[(guess_vert + k) % npolys];
      const size_t vi = static_cast<size_t>(ind[k].vertex_index);
      vx[k] = vertices[vi * 3 + axes[0]];
      vy[k] = vertices[vi * 3 + axes[1]];
    }

    const real_t e0x = vx[1] - vx[0];
    const real_t e0y = vy[1] - vy[0];
    const real_t e1x = vx[2] - vx[1];
    const real_t e1y = vy[2] - vy[1];
    const real_t cross_val = e0x * e1y - e0y * e1x;
    const real_t area =
        (vx[0] * vy[1] - vy[0] * vx[1]) * static_cast<real_t>(0.5);
    if (cross_val * area < static_cast<real_t>(0.0)) {
      guess_vert += 1;
      continue;
    }

    bool overlap = false;
    for (size_t other_vert = 3; other_vert < npolys; ++other_vert) {
      const size_t idx = (guess_vert + other_vert) % npolys;
      const size_t ovi = static_cast<size_t>(remaining[idx].vertex_index);
      const real_t tx = vertices[ovi * 3 + axes[0]];
      const real_t ty = vertices[ovi * 3 + axes[1]];
      if (PointInPolygon(3, vx, vy, tx, ty)) {
        overlap = true;
        break;
      }
    }

    if (overlap) {
      guess_vert += 1;
      continue;
    }

    dst[out++] = ind[0];
    dst[out++] = ind[1];
    dst[out++] = ind[2];
    remaining.erase(remaining.begin() +
                    static_cast<std::ptrdiff_t>((guess_vert + 1) % npolys));
  }

  if (remaining.size() == 3) {
    dst[out++] = remaining[0];
    dst[out++] = remaining[1];
    dst[out++] = remaining[2];
  }

  return out;
}

static bool ParseRawTripleToken(const std::string &token, RawIndex *out) {
  if (!out) return false;

  out->vertex_index = 0;
  out->texcoord_index = 0;
  out->normal_index = 0;

  size_t first = token.find('/');
  if (first == std::string::npos) {
    return ParseIntToken(token, &out->vertex_index);
  }

  std::string v_str = token.substr(0, first);
  size_t second = token.find('/', first + 1);

  if (v_str.empty() || !ParseIntToken(v_str, &out->vertex_index)) return false;

  if (second == std::string::npos) {
    std::string vt_str = token.substr(first + 1);
    if (!vt_str.empty()) {
      out->has_texcoord_index = true;
      if (!ParseIntToken(vt_str, &out->texcoord_index)) return false;
    }
    return true;
  }

  std::string vt_str = token.substr(first + 1, second - first - 1);
  std::string vn_str = token.substr(second + 1);

  if (!vt_str.empty()) {
    out->has_texcoord_index = true;
    if (!ParseIntToken(vt_str, &out->texcoord_index)) return false;
  }

  if (!vn_str.empty()) {
    out->has_normal_index = true;
    if (!ParseIntToken(vn_str, &out->normal_index)) return false;
  }

  return true;
}

static void SplitFilenames(const std::string &s,
                           std::vector<std::string> *filenames) {
  if (!filenames) return;
  filenames->clear();
  std::string token;
  token.reserve(s.size());
  bool escaped = false;
  for (size_t i = 0; i < s.size(); i++) {
    const char c = s[i];
    if (escaped) {
      token.push_back(c);
      escaped = false;
      continue;
    }
    if (c == '\\') {
      escaped = true;
      continue;
    }
    if (c == ' ' || c == '\t') {
      if (!token.empty()) {
        filenames->push_back(token);
        token.clear();
      }
      continue;
    }
    token.push_back(c);
  }
  if (escaped) {
    token.push_back('\\');
  }
  if (!token.empty()) {
    filenames->push_back(token);
  }
}

static std::string ParseLegacyGroupName(std::istringstream *iss) {
  std::string name;
  std::string token;
  while ((*iss) >> token) {
    if (!token.empty() && token[0] == '#') {
      break;
    }
    if (!name.empty()) {
      name.push_back(' ');
    }
    name += token;
  }
  return name;
}

class MeshBuilderHandler : public StreamHandler {
 public:
  MeshBuilderHandler(attrib_t *attrib, std::vector<shape_t> *shapes,
                     std::vector<material_t> *materials, MaterialReader *reader,
                     std::string *warn, std::string *err,
                     const StreamLoadConfig &config)
      : attrib_(attrib),
        shapes_(shapes),
        materials_(materials),
        material_reader_(reader),
        warn_(warn),
        err_(err),
        config_(config),
        current_material_id_(-1),
        current_smoothing_group_id_(0),
        saw_explicit_color_(false),
        saw_missing_color_(false),
        current_shape_from_group_(false),
        current_shape_has_face_record_(false),
        current_shape_degenerate_face_count_(0) {
    assert(attrib_);
    assert(shapes_);
    attrib_->vertices.clear();
    attrib_->vertex_weights.clear();
    attrib_->normals.clear();
    attrib_->texcoords.clear();
    attrib_->texcoord_ws.clear();
    attrib_->colors.clear();
    attrib_->skin_weights.clear();
    shapes_->clear();
    if (materials_) materials_->clear();
  }

  void Finish() {
    FlushShape(true);
    if (!config_.default_vcols_fallback && saw_explicit_color_ &&
        saw_missing_color_) {
      attrib_->colors.clear();
    }
    if (config_.default_vcols_fallback && !saw_explicit_color_ &&
        attrib_->colors.empty() && !attrib_->vertices.empty()) {
      attrib_->colors.assign(attrib_->vertices.size(), real_t(1.0));
    }
  }

  virtual void OnVertex(real_t x, real_t y, real_t z, bool has_weight, real_t w,
                        bool has_color, real_t r, real_t g, real_t b) {
    attrib_->vertices.push_back(x);
    attrib_->vertices.push_back(y);
    attrib_->vertices.push_back(z);
    attrib_->vertex_weights.push_back(has_weight ? w : real_t(1.0));

    if (has_color) {
      if (!saw_explicit_color_ && attrib_->colors.empty() &&
          attrib_->vertices.size() > 3) {
        const size_t prior_vertex_count = attrib_->vertices.size() / 3 - 1;
        attrib_->colors.assign(prior_vertex_count * 3, real_t(1.0));
      }
      saw_explicit_color_ = true;
      attrib_->colors.push_back(r);
      attrib_->colors.push_back(g);
      attrib_->colors.push_back(b);
    } else if (saw_explicit_color_) {
      saw_missing_color_ = true;
      attrib_->colors.push_back(real_t(1.0));
      attrib_->colors.push_back(real_t(1.0));
      attrib_->colors.push_back(real_t(1.0));
    } else {
      saw_missing_color_ = true;
    }
  }

  virtual void OnNormal(real_t x, real_t y, real_t z) {
    attrib_->normals.push_back(x);
    attrib_->normals.push_back(y);
    attrib_->normals.push_back(z);
  }

  virtual void OnTexcoord(real_t u, real_t v, bool has_w, real_t w) {
    attrib_->texcoords.push_back(u);
    attrib_->texcoords.push_back(v);
    attrib_->texcoord_ws.push_back(has_w ? w : real_t(0.0));
  }

  virtual void OnFace(const index_t *indices, size_t num_indices) {
    current_shape_has_face_record_ = true;
    for (size_t i = 0; i < num_indices; i++) {
      current_shape_.mesh.indices.push_back(indices[i]);
    }
    current_shape_.mesh.num_face_vertices.push_back(
        static_cast<unsigned int>(num_indices));
    current_shape_.mesh.material_ids.push_back(current_material_id_);
    current_shape_.mesh.smoothing_group_ids.push_back(
        current_smoothing_group_id_);
  }

  virtual void OnDegenerateFace() {
    current_shape_has_face_record_ = true;
    current_shape_degenerate_face_count_++;
  }

  virtual void OnGroup(const std::string &name) {
    SwitchShape(name, true);
  }

  virtual void OnObject(const std::string &name) {
    SwitchShape(name, false);
  }

  virtual void OnUsemtl(const std::string &name) {
    current_material_name_ = name;
    std::map<std::string, int>::const_iterator it = material_map_.find(name);
    if (it != material_map_.end()) {
      current_material_id_ = it->second;
    } else {
      current_material_id_ = -1;
      if (warn_) {
        (*warn_) += "material [ '" + name + "' ] not found in .mtl\n";
      }
    }
  }

  virtual void OnMtllib(const std::vector<std::string> &filenames) {
    HandleMtllib(filenames, 0);
  }

  virtual void OnMtllibWithLine(const std::vector<std::string> &filenames,
                                size_t line_num) {
    HandleMtllib(filenames, line_num);
  }

  private:
  void HandleMtllib(const std::vector<std::string> &filenames,
                    size_t line_num) {
    if (!material_reader_) return;

    std::vector<material_t> *material_dst =
        materials_ ? materials_ : &scratch_materials_;

    if (filenames.empty()) {
      if (warn_) {
        if (line_num != 0) {
          std::stringstream ss;
          ss << "Looks like empty filename for mtllib. Use default material "
                "(line "
             << line_num << ".)\n";
          (*warn_) += ss.str();
        } else {
          (*warn_) +=
              "Looks like empty filename for mtllib. Use default material.\n";
        }
      }
      return;
    }

    bool found = false;
    for (size_t i = 0; i < filenames.size(); i++) {
      if (loaded_material_filenames_.count(filenames[i]) > 0) {
        found = true;
        continue;
      }

      std::string warn_mtl;
      std::string err_mtl;
      bool ok = (*material_reader_)(filenames[i], material_dst, &material_map_,
                                    &warn_mtl, &err_mtl);
      if (warn_ && !warn_mtl.empty()) {
        (*warn_) += warn_mtl;
      }
      if (err_ && !err_mtl.empty()) {
        (*err_) += err_mtl;
      }

      if (ok) {
        found = true;
        loaded_material_filenames_.insert(filenames[i]);
        break;
      }
    }

    if (!found && warn_) {
      (*warn_) += "Failed to load material file(s). Use default material.\n";
    }
  }

 public:
  virtual void OnSmoothingGroup(unsigned int smoothing_group_id) {
    current_smoothing_group_id_ = smoothing_group_id;
  }

 private:
  void SwitchShape(const std::string &name, bool from_group) {
    if (!current_shape_.mesh.indices.empty() || current_shape_has_face_record_) {
      FlushShape(false);
    } else {
      current_shape_ = shape_t();
      current_shape_has_face_record_ = false;
      current_shape_degenerate_face_count_ = 0;
    }
    current_shape_.name = name;
    current_shape_from_group_ = from_group;
  }

  void FlushShape(bool at_eof) {
    EmitDegenerateFaceWarnings();

    if (current_shape_.mesh.indices.empty() &&
        !(at_eof && current_shape_has_face_record_)) {
      current_shape_has_face_record_ = false;
      current_shape_degenerate_face_count_ = 0;
      if (at_eof) {
        current_shape_from_group_ = false;
      }
      return;
    }

    shapes_->push_back(current_shape_);
    current_shape_ = shape_t();
    current_shape_.name.clear();
    current_shape_from_group_ = false;
    current_shape_has_face_record_ = false;
    current_shape_degenerate_face_count_ = 0;
  }

  void EmitDegenerateFaceWarnings() {
    if (!warn_) {
      current_shape_degenerate_face_count_ = 0;
      return;
    }

    for (size_t i = 0; i < current_shape_degenerate_face_count_; i++) {
      (*warn_) += "Degenerated face found\n.";
    }
    current_shape_degenerate_face_count_ = 0;
  }

  attrib_t *attrib_;
  std::vector<shape_t> *shapes_;
  std::vector<material_t> *materials_;
  std::vector<material_t> scratch_materials_;
  MaterialReader *material_reader_;
  std::string *warn_;
  std::string *err_;
  StreamLoadConfig config_;
  shape_t current_shape_;
  std::map<std::string, int> material_map_;
  std::set<std::string> loaded_material_filenames_;
  std::string current_material_name_;
  int current_material_id_;
  unsigned int current_smoothing_group_id_;
  bool saw_explicit_color_;
  bool saw_missing_color_;
  bool current_shape_from_group_;
  bool current_shape_has_face_record_;
  size_t current_shape_degenerate_face_count_;
};

static bool ParseLineToEvent(size_t line_num, const std::string &line,
                             ParsedChunk *chunk) {
  std::string work = line;
  const size_t nul_pos = work.find('\0');
  if (nul_pos != std::string::npos) {
    work.resize(nul_pos);
  }
  for (size_t i = 0; i < work.size(); i++) {
    if (work[i] == '\r') {
      work[i] = ' ';
    }
  }
  if (Trim(work).empty()) {
    return true;
  }

  work = TrimLeading(work);
  std::istringstream iss(work);
  std::string tag;
  iss >> tag;
  if (!tag.empty() && tag[0] == '#') {
    return true;
  }

  ParsedEvent event;
  event.line_num = line_num;

  if (tag == "v") {
    std::vector<std::string> tokens;
    std::string token;
    while (iss >> token) {
      if (!token.empty() && token[0] == '#') {
        break;
      }
      tokens.push_back(token);
    }
    if (tokens.size() < 3) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed vertex record\n";
      return false;
    }

    event.type = EVENT_VERTEX;
    if (!ParseRealToken(tokens[0], &event.x) ||
        !ParseRealToken(tokens[1], &event.y) ||
        !ParseRealToken(tokens[2], &event.z)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed vertex coordinates\n";
      return false;
    }

    // Mirror LoadObjOpt's weight + color handling, keyed on the number of
    // components beyond `x y z`:
    //   +0  (v x y z)        -> position only
    //   +1  (v x y z w)      -> weight only
    //   +3  (v x y z r g b)  -> color, weight = r (legacy compat)
    //   +4+ (v x y z w r g b)-> weight + color
    // The OBJ spec / common vertex-color extension only define xyz / xyzw /
    // xyzrgb (weight and color are mutually exclusive); the +4 case is a
    // tinyobjloader extension shared with LoadObjOpt.  The classic LoadObj
    // path caps at 6 and differs here.
    const size_t extra = tokens.size() - 3;
    if (extra == 1) {
      real_t w = real_t(1.0);
      if (ParseRealToken(tokens[3], &w)) {
        event.has_vertex_weight = true;
        event.vertex_weight = w;
      }
    } else if (extra == 3) {
      real_t cr = real_t(1.0), cg = real_t(1.0), cb = real_t(1.0);
      if (ParseRealToken(tokens[3], &cr) && ParseRealToken(tokens[4], &cg) &&
          ParseRealToken(tokens[5], &cb)) {
        event.has_vertex_weight = true;
        event.vertex_weight = cr;
        event.has_color = true;
        event.r = cr;
        event.g = cg;
        event.b = cb;
      }
    } else if (extra >= 4) {
      real_t w = real_t(1.0), cr = real_t(1.0), cg = real_t(1.0),
             cb = real_t(1.0);
      if (ParseRealToken(tokens[3], &w) && ParseRealToken(tokens[4], &cr) &&
          ParseRealToken(tokens[5], &cg) && ParseRealToken(tokens[6], &cb)) {
        event.has_vertex_weight = true;
        event.vertex_weight = w;
        event.has_color = true;
        event.r = cr;
        event.g = cg;
        event.b = cb;
      }
    }

    chunk->events.push_back(event);
    return true;
  }

  if (tag == "vn") {
    std::string sx, sy, sz;
    if (!(iss >> sx >> sy >> sz)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed normal record\n";
      return false;
    }
    event.type = EVENT_NORMAL;
    if (!ParseRealToken(sx, &event.x) || !ParseRealToken(sy, &event.y) ||
        !ParseRealToken(sz, &event.z)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed normal record\n";
      return false;
    }
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "vt") {
    std::string su, sv, sw;
    if (!(iss >> su)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed texcoord record\n";
      return false;
    }
    event.type = EVENT_TEXCOORD;
    event.y = real_t(0.0);
    if (!ParseRealToken(su, &event.x)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed texcoord record\n";
      return false;
    }
    if (iss >> sv) {
      if (sv[0] == '#') {
        chunk->events.push_back(event);
        return true;
      }
      if (!ParseRealToken(sv, &event.y)) {
        chunk->err = "line " + std::to_string(line_num) +
                     ": malformed texcoord record\n";
        return false;
      }
    }
    if (iss >> sw) {
      if (sw[0] != '#') {
        event.has_texcoord_w = true;
        if (!ParseRealToken(sw, &event.w)) {
          chunk->err = "line " + std::to_string(line_num) +
                       ": malformed texcoord record\n";
          return false;
        }
      }
    }
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "f") {
    event.type = EVENT_FACE;
    std::string tok;
    while (iss >> tok) {
      if (!tok.empty() && tok[0] == '#') {
        break;
      }
      RawIndex idx;
      if (!ParseRawTripleToken(tok, &idx)) {
        chunk->err = "line " + std::to_string(line_num) +
                     ": malformed face record\n";
        return false;
      }
      event.face.push_back(idx);
    }
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "g") {
    event.type = EVENT_GROUP;
    event.text = ParseLegacyGroupName(&iss);
    chunk->events.push_back(event);
    if (event.text.empty()) {
      ParsedEvent warn_event;
      warn_event.type = EVENT_WARNING;
      warn_event.text = "Empty group name. line: " + std::to_string(line_num) +
                        "\n";
      chunk->events.push_back(warn_event);
    }
    return true;
  }

  if (tag == "o") {
    event.type = EVENT_OBJECT;
    if (iss.peek() == ' ' || iss.peek() == '\t') {
      iss.get();
    }
    std::getline(iss, event.text);
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "usemtl") {
    event.type = EVENT_USEMTL;
    iss >> event.text;
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "mtllib") {
    event.type = EVENT_MTLLIB;
    std::string rest;
    std::getline(iss, rest);
    SplitFilenames(Trim(rest), &event.filenames);
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "s") {
    event.type = EVENT_SMOOTHING;
    std::string value;
    iss >> value;
    if (value == "off" || value == "0") {
      event.smoothing_group_id = 0;
    } else {
      int smoothing = 0;
      if (ParseIntToken(value, &smoothing) && smoothing > 0) {
        event.smoothing_group_id = static_cast<unsigned int>(smoothing);
      } else {
        event.smoothing_group_id = 0;
      }
    }
    chunk->events.push_back(event);
    return true;
  }

  event.type = EVENT_WARNING;
  event.text = "line " + std::to_string(line_num) + ": ignoring `" + tag +
               "` in experimental stream parser\n";
  chunk->events.push_back(event);
  return true;
}

static bool ReplayChunk(const ParsedChunk &chunk, StreamHandler *handler,
                        std::string *warn, std::string *err,
                        int *num_vertices, int *num_normals,
                        int *num_texcoords, int *greatest_v_idx,
                        int *greatest_vn_idx, int *greatest_vt_idx,
                        std::vector<real_t> *vertex_positions,
                        const std::string &source_name,
                        const StreamLoadConfig &config) {
  for (size_t i = 0; i < chunk.events.size(); i++) {
    const ParsedEvent &event = chunk.events[i];
    switch (event.type) {
      case EVENT_VERTEX:
        handler->OnVertex(event.x, event.y, event.z, event.has_vertex_weight,
                          event.vertex_weight, event.has_color, event.r,
                          event.g, event.b);
        if (vertex_positions) {
          vertex_positions->push_back(event.x);
          vertex_positions->push_back(event.y);
          vertex_positions->push_back(event.z);
        }
        (*num_vertices)++;
        break;
      case EVENT_NORMAL:
        handler->OnNormal(event.x, event.y, event.z);
        (*num_normals)++;
        break;
      case EVENT_TEXCOORD:
        handler->OnTexcoord(event.x, event.y, event.has_texcoord_w, event.w);
        (*num_texcoords)++;
        break;
      case EVENT_FACE:
        if (event.face.size() < 3) {
          handler->OnDegenerateFace();
          break;
        }
        {
          std::vector<index_t> face(event.face.size());
          for (size_t k = 0; k < event.face.size(); k++) {
            if (!ResolveIndexLikeLegacy(event.face[k].vertex_index,
                                        *num_vertices, &face[k].vertex_index,
                                        false, source_name, event.line_num,
                                        warn)) {
              if (err) {
                (*err) += "line " + std::to_string(event.line_num) +
                          ": malformed face record\n";
              }
              return false;
            }
            UpdateGreatestIndex(face[k].vertex_index, greatest_v_idx);

            if (event.face[k].has_texcoord_index) {
              if (!ResolveIndexLikeLegacy(event.face[k].texcoord_index,
                                          *num_texcoords,
                                          &face[k].texcoord_index, true,
                                          source_name, event.line_num, warn)) {
                if (err) {
                  (*err) += "line " + std::to_string(event.line_num) +
                            ": malformed face record\n";
                }
                return false;
              }
              if (face[k].texcoord_index >= 0) {
                UpdateGreatestIndex(face[k].texcoord_index, greatest_vt_idx);
              }
            } else {
              face[k].texcoord_index = -1;
            }

            if (event.face[k].has_normal_index) {
              if (!ResolveIndexLikeLegacy(event.face[k].normal_index,
                                          *num_normals, &face[k].normal_index,
                                          true, source_name, event.line_num,
                                          warn)) {
                if (err) {
                  (*err) += "line " + std::to_string(event.line_num) +
                            ": malformed face record\n";
                }
                return false;
              }
              if (face[k].normal_index >= 0) {
                UpdateGreatestIndex(face[k].normal_index, greatest_vn_idx);
              }
            } else {
              face[k].normal_index = -1;
            }
          }

          if (config.triangulate && face.size() > 3) {
            std::vector<index_t> tris((face.size() - 2) * 3);
            const size_t tri_count = TriangulateFaceLikeLegacy(
                *vertex_positions, face.data(), face.size(), tris.data());
            for (size_t k = 0; k + 2 < tri_count; k += 3) {
              handler->OnFace(&tris[k], 3);
            }
          } else {
            handler->OnFace(face.data(), face.size());
          }
        }
        break;
      case EVENT_GROUP:
        handler->OnGroup(event.text);
        break;
      case EVENT_OBJECT:
        handler->OnObject(event.text);
        break;
      case EVENT_USEMTL:
        handler->OnUsemtl(event.text);
        break;
      case EVENT_MTLLIB:
        handler->OnMtllibWithLine(event.filenames, event.line_num);
        break;
      case EVENT_SMOOTHING:
        handler->OnSmoothingGroup(event.smoothing_group_id);
        break;
      case EVENT_WARNING:
        if (warn) {
          (*warn) += event.text;
        }
        break;
    }
  }

  return true;
}

}  // namespace

bool ParseObjStream(std::istream *input, StreamHandler *handler,
                    std::string *warn, std::string *err,
                    const std::string &source_name,
                    const StreamLoadConfig &config) {
  if (!input || !handler) {
    if (err) {
      (*err) += "input stream and handler must not be null.\n";
    }
    return false;
  }

  std::string line;
  size_t line_num = 0;
  int num_vertices = 0;
  int num_normals = 0;
  int num_texcoords = 0;
  int greatest_v_idx = -1;
  int greatest_vn_idx = -1;
  int greatest_vt_idx = -1;
  std::vector<real_t> vertex_positions;

  int num_threads = config.num_threads;
  if (num_threads < 1) {
    num_threads = 1;
  }

  size_t chunk_line_count = config.chunk_line_count;
  if (chunk_line_count < 1) {
    chunk_line_count = 1;
  }

  while (true) {
    std::vector<std::vector<std::pair<size_t, std::string> > > chunk_inputs;
    chunk_inputs.reserve(static_cast<size_t>(num_threads));

    for (int t = 0; t < num_threads; t++) {
      std::vector<std::pair<size_t, std::string> > lines;
      lines.reserve(chunk_line_count);
      while (lines.size() < chunk_line_count && std::getline(*input, line)) {
        line_num++;
        if (!line.empty() && line[line.size() - 1] == '\r') {
          line.resize(line.size() - 1);
        }
        lines.push_back(std::make_pair(line_num, line));
      }
      if (!lines.empty()) {
        chunk_inputs.push_back(lines);
      }
      if (!(*input)) {
        break;
      }
    }

    if (chunk_inputs.empty()) {
      break;
    }

    std::vector<ParsedChunk> chunks(chunk_inputs.size());
    size_t error_chunk_index = chunks.size();
    if (chunk_inputs.size() == 1) {
      for (size_t i = 0; i < chunk_inputs[0].size(); i++) {
        if (!ParseLineToEvent(chunk_inputs[0][i].first, chunk_inputs[0][i].second,
                              &chunks[0])) {
          error_chunk_index = 0;
          break;
        }
      }
    } else {
      std::vector<std::thread> workers;
      workers.reserve(chunk_inputs.size());
      for (size_t c = 0; c < chunk_inputs.size(); c++) {
        workers.push_back(std::thread([&, c]() {
          for (size_t i = 0; i < chunk_inputs[c].size(); i++) {
            if (!ParseLineToEvent(chunk_inputs[c][i].first,
                                  chunk_inputs[c][i].second, &chunks[c])) {
              return;
            }
          }
        }));
      }
      for (size_t c = 0; c < workers.size(); c++) {
        workers[c].join();
      }
      for (size_t c = 0; c < chunks.size(); c++) {
        if (!chunks[c].err.empty()) {
          error_chunk_index = c;
          break;
        }
      }
    }

    const size_t replay_chunk_count =
        (error_chunk_index < chunks.size()) ? (error_chunk_index + 1)
                                            : chunks.size();
    for (size_t c = 0; c < replay_chunk_count; c++) {
      if (!ReplayChunk(chunks[c], handler, warn, err, &num_vertices,
                       &num_normals, &num_texcoords, &greatest_v_idx,
                       &greatest_vn_idx, &greatest_vt_idx, &vertex_positions,
                       source_name, config)) {
        return false;
      }
    }

    if (error_chunk_index < chunks.size()) {
      if (err) {
        (*err) += chunks[error_chunk_index].err;
      }
      return false;
    }
  }

  AppendOutOfBoundsWarnings(warn, greatest_v_idx, greatest_vn_idx,
                            greatest_vt_idx, num_vertices, num_normals,
                            num_texcoords, line_num + 1);
  return true;
}

bool LoadObjStreamExperimental(
    attrib_t *attrib, std::vector<shape_t> *shapes,
    std::vector<material_t> *materials, std::string *warn, std::string *err,
    std::istream *input, MaterialReader *readMatFn,
    const StreamLoadConfig &config) {
  if (!attrib || !shapes || !input) {
    if (err) {
      (*err) += "attrib, shapes and input stream must not be null.\n";
    }
    return false;
  }

  MeshBuilderHandler builder(attrib, shapes, materials, readMatFn, warn, err,
                             config);
  bool ok = ParseObjStream(input, &builder, warn, err, "<stream>", config);
  if (!ok) {
    attrib->vertices.clear();
    attrib->vertex_weights.clear();
    attrib->normals.clear();
    attrib->texcoords.clear();
    attrib->texcoord_ws.clear();
    attrib->colors.clear();
    attrib->skin_weights.clear();
    shapes->clear();
    if (materials) materials->clear();
    return false;
  }
  builder.Finish();
  return ok;
}

bool LoadObjStreamExperimental(
    attrib_t *attrib, std::vector<shape_t> *shapes,
    std::vector<material_t> *materials, std::string *warn, std::string *err,
    const char *filename, const char *mtl_basedir,
    const StreamLoadConfig &config) {
  if (!filename) {
    if (err) {
      (*err) += "filename must not be null.\n";
    }
    return false;
  }

  std::ifstream ifs(filename);
  if (!ifs) {
    if (err) {
      (*err) += "Cannot open file: " + std::string(filename) + "\n";
    }
    return false;
  }

  std::string base_dir;
  if (mtl_basedir) {
    base_dir = mtl_basedir;
  } else {
    std::string path(filename);
    size_t pos = path.find_last_of("/\\");
    if (pos != std::string::npos) {
      base_dir = path.substr(0, pos + 1);
    }
  }

  MaterialFileReader mat_reader(base_dir);
  if (!attrib || !shapes) {
    if (err) {
      (*err) += "attrib and shapes must not be null.\n";
    }
    return false;
  }

  MeshBuilderHandler builder(attrib, shapes, materials, &mat_reader, warn, err,
                             config);
  bool ok = ParseObjStream(&ifs, &builder, warn, err, filename, config);
  if (!ok) {
    attrib->vertices.clear();
    attrib->vertex_weights.clear();
    attrib->normals.clear();
    attrib->texcoords.clear();
    attrib->texcoord_ws.clear();
    attrib->colors.clear();
    attrib->skin_weights.clear();
    shapes->clear();
    if (materials) materials->clear();
    return false;
  }

  builder.Finish();
  return true;
}

}  // namespace experimental_stream
}  // namespace tinyobj
