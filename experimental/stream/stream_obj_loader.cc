#include "stream_obj_loader.h"

#include <cassert>
#include <cctype>
#include <cerrno>
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

  RawIndex() : vertex_index(0), texcoord_index(0), normal_index(0) {}
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
  real_t x, y, z;
  real_t r, g, b;
  bool has_color;
  std::vector<RawIndex> face;
  std::vector<std::string> filenames;
  std::string text;
  unsigned int smoothing_group_id;

  ParsedEvent()
      : type(EVENT_WARNING),
        x(real_t(0)),
        y(real_t(0)),
        z(real_t(0)),
        r(real_t(1)),
        g(real_t(1)),
        b(real_t(1)),
        has_color(false),
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

static std::string StripComment(const std::string &s) {
  size_t pos = s.find('#');
  if (pos == std::string::npos) {
    return s;
  }
  return s.substr(0, pos);
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

static int FixIndex(int idx, int n) {
  if (idx > 0) return idx - 1;
  if (idx == 0) return -1;
  return n + idx;
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
      if (!ParseIntToken(vt_str, &out->texcoord_index)) return false;
    }
    return true;
  }

  std::string vt_str = token.substr(first + 1, second - first - 1);
  std::string vn_str = token.substr(second + 1);

  if (!vt_str.empty()) {
    if (!ParseIntToken(vt_str, &out->texcoord_index)) return false;
  }

  if (!vn_str.empty()) {
    if (!ParseIntToken(vn_str, &out->normal_index)) return false;
  }

  return true;
}

static void SplitFilenames(const std::string &s,
                           std::vector<std::string> *filenames) {
  if (!filenames) return;
  filenames->clear();

  std::istringstream iss(s);
  std::string token;
  while (iss >> token) {
    filenames->push_back(token);
  }
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
        saw_explicit_color_(false) {
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
    FlushShape();
    if (config_.default_vcols_fallback && !saw_explicit_color_ &&
        attrib_->colors.empty() && !attrib_->vertices.empty()) {
      attrib_->colors.assign(attrib_->vertices.size(), real_t(1.0));
    }
  }

  virtual void OnVertex(real_t x, real_t y, real_t z, bool has_color, real_t r,
                        real_t g, real_t b) {
    attrib_->vertices.push_back(x);
    attrib_->vertices.push_back(y);
    attrib_->vertices.push_back(z);

    if (has_color) {
      saw_explicit_color_ = true;
      attrib_->colors.push_back(r);
      attrib_->colors.push_back(g);
      attrib_->colors.push_back(b);
    } else if (saw_explicit_color_) {
      attrib_->colors.push_back(real_t(1.0));
      attrib_->colors.push_back(real_t(1.0));
      attrib_->colors.push_back(real_t(1.0));
    }
  }

  virtual void OnNormal(real_t x, real_t y, real_t z) {
    attrib_->normals.push_back(x);
    attrib_->normals.push_back(y);
    attrib_->normals.push_back(z);
  }

  virtual void OnTexcoord(real_t u, real_t v) {
    attrib_->texcoords.push_back(u);
    attrib_->texcoords.push_back(v);
  }

  virtual void OnFace(const index_t *indices, size_t num_indices) {
    for (size_t i = 0; i < num_indices; i++) {
      current_shape_.mesh.indices.push_back(indices[i]);
    }
    current_shape_.mesh.num_face_vertices.push_back(
        static_cast<unsigned int>(num_indices));
    current_shape_.mesh.material_ids.push_back(current_material_id_);
    current_shape_.mesh.smoothing_group_ids.push_back(
        current_smoothing_group_id_);
  }

  virtual void OnGroup(const std::string &name) {
    SwitchShape(name);
  }

  virtual void OnObject(const std::string &name) {
    SwitchShape(name);
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
    if (!material_reader_ || !materials_) return;

    if (filenames.empty()) {
      if (warn_) {
        (*warn_) +=
            "Looks like empty filename for mtllib. Use default material.\n";
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
      bool ok = (*material_reader_)(filenames[i], materials_, &material_map_,
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

  virtual void OnSmoothingGroup(unsigned int smoothing_group_id) {
    current_smoothing_group_id_ = smoothing_group_id;
  }

 private:
  void SwitchShape(const std::string &name) {
    if (!current_shape_.mesh.indices.empty()) {
      FlushShape();
    }
    current_shape_.name = name;
  }

  void FlushShape() {
    if (current_shape_.mesh.indices.empty()) {
      return;
    }

    shapes_->push_back(current_shape_);
    current_shape_ = shape_t();
    current_shape_.name.clear();
  }

  attrib_t *attrib_;
  std::vector<shape_t> *shapes_;
  std::vector<material_t> *materials_;
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
};

static bool ParseLineToEvent(size_t line_num, const std::string &line,
                             ParsedChunk *chunk) {
  std::string work = Trim(StripComment(line));
  if (work.empty()) {
    return true;
  }

  std::istringstream iss(work);
  std::string tag;
  iss >> tag;

  ParsedEvent event;

  if (tag == "v") {
    std::vector<std::string> tokens;
    std::string token;
    while (iss >> token) tokens.push_back(token);
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

    if (tokens.size() >= 6) {
      event.has_color = ParseRealToken(tokens[3], &event.r) &&
                        ParseRealToken(tokens[4], &event.g) &&
                        ParseRealToken(tokens[5], &event.b);
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
    std::string su, sv;
    if (!(iss >> su >> sv)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed texcoord record\n";
      return false;
    }
    event.type = EVENT_TEXCOORD;
    if (!ParseRealToken(su, &event.x) || !ParseRealToken(sv, &event.y)) {
      chunk->err = "line " + std::to_string(line_num) +
                   ": malformed texcoord record\n";
      return false;
    }
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "f") {
    event.type = EVENT_FACE;
    std::string tok;
    while (iss >> tok) {
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
    std::getline(iss, event.text);
    event.text = Trim(event.text);
    chunk->events.push_back(event);
    return true;
  }

  if (tag == "o") {
    event.type = EVENT_OBJECT;
    std::getline(iss, event.text);
    event.text = Trim(event.text);
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
                        std::string *warn, int *num_vertices,
                        int *num_normals, int *num_texcoords,
                        const StreamLoadConfig &config) {
  for (size_t i = 0; i < chunk.events.size(); i++) {
    const ParsedEvent &event = chunk.events[i];
    switch (event.type) {
      case EVENT_VERTEX:
        handler->OnVertex(event.x, event.y, event.z, event.has_color, event.r,
                          event.g, event.b);
        (*num_vertices)++;
        break;
      case EVENT_NORMAL:
        handler->OnNormal(event.x, event.y, event.z);
        (*num_normals)++;
        break;
      case EVENT_TEXCOORD:
        handler->OnTexcoord(event.x, event.y);
        (*num_texcoords)++;
        break;
      case EVENT_FACE:
        if (event.face.size() < 3) {
          break;
        }
        {
          std::vector<index_t> face(event.face.size());
          for (size_t k = 0; k < event.face.size(); k++) {
            face[k].vertex_index =
                FixIndex(event.face[k].vertex_index, *num_vertices);
            face[k].texcoord_index = (event.face[k].texcoord_index == 0)
                                         ? -1
                                         : FixIndex(event.face[k].texcoord_index,
                                                    *num_texcoords);
            face[k].normal_index = (event.face[k].normal_index == 0)
                                       ? -1
                                       : FixIndex(event.face[k].normal_index,
                                                  *num_normals);
          }

          if (config.triangulate && face.size() > 3) {
            index_t tri[3];
            tri[0] = face[0];
            for (size_t k = 2; k < face.size(); k++) {
              tri[1] = face[k - 1];
              tri[2] = face[k];
              handler->OnFace(tri, 3);
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
        handler->OnMtllib(event.filenames);
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
    if (chunk_inputs.size() == 1) {
      for (size_t i = 0; i < chunk_inputs[0].size(); i++) {
        if (!ParseLineToEvent(chunk_inputs[0][i].first, chunk_inputs[0][i].second,
                              &chunks[0])) {
          if (err) {
            (*err) += chunks[0].err;
          }
          return false;
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
          if (err) {
            (*err) += chunks[c].err;
          }
          return false;
        }
      }
    }

    for (size_t c = 0; c < chunks.size(); c++) {
      ReplayChunk(chunks[c], handler, warn, &num_vertices, &num_normals,
                  &num_texcoords, config);
    }
  }

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
  bool ok = ParseObjStream(input, &builder, warn, err, config);
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
  return LoadObjStreamExperimental(attrib, shapes, materials, warn, err, &ifs,
                                   &mat_reader, config);
}

}  // namespace experimental_stream
}  // namespace tinyobj
