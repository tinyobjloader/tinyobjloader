#ifndef TINYOBJ_TESTS_FUZZ_COMMON_H_
#define TINYOBJ_TESTS_FUZZ_COMMON_H_

#include <cctype>
#include <cstddef>
#include <cstdint>
#include <map>
#include <sstream>
#include <string>
#include <vector>

// Include tiny_obj_loader.h (or stream_obj_loader.h, which includes it)
// before including this helper. We intentionally avoid including it here
// because TINYOBJLOADER_IMPLEMENTATION lives outside the header guard.

namespace tinyobj_fuzz {

class InMemoryMaterialReader : public tinyobj::MaterialReader {
 public:
  explicit InMemoryMaterialReader(const std::string &mtl_text)
      : mtl_text_(mtl_text) {}

  virtual bool operator()(const std::string &mat_id,
                          std::vector<tinyobj::material_t> *materials,
                          std::map<std::string, int> *mat_map,
                          std::string *warn, std::string *err) {
    (void)mat_id;
    std::istringstream stream(mtl_text_);
    tinyobj::MaterialStreamReader reader(stream);
    return reader("", materials, mat_map, warn, err);
  }

 private:
  std::string mtl_text_;
};

inline void SplitInput(const uint8_t *data, size_t size, std::string *obj_text,
                       std::string *mtl_text) {
  obj_text->clear();
  mtl_text->clear();
  if (!data || size == 0) {
    return;
  }

  size_t split = size;
  for (size_t i = 0; i < size; i++) {
    if (data[i] == 0) {
      split = i;
      break;
    }
  }

  obj_text->assign(reinterpret_cast<const char *>(data), split);
  if (split < size) {
    mtl_text->assign(reinterpret_cast<const char *>(data + split + 1),
                     size - split - 1);
  }
}

inline std::string FirstToken(const std::string &line) {
  size_t pos = 0;
  while (pos < line.size() &&
         std::isspace(static_cast<unsigned char>(line[pos]))) {
    pos++;
  }
  if (pos >= line.size() || line[pos] == '#') {
    return std::string();
  }
  size_t end = pos;
  while (end < line.size() &&
         !std::isspace(static_cast<unsigned char>(line[end]))) {
    end++;
  }
  return line.substr(pos, end - pos);
}

inline bool IsSharedSubsetForCrossCheck(const std::string &obj_text) {
  std::istringstream stream(obj_text);
  std::string line;
  while (std::getline(stream, line)) {
    const std::string token = FirstToken(line);
    if (token.empty()) {
      continue;
    }
    if (token == "mtllib" || token == "vw" || token == "l" || token == "p" ||
        token == "t") {
      return false;
    }
  }
  return true;
}

inline bool IsTextLikeObj(const std::string &obj_text) {
  for (size_t i = 0; i < obj_text.size(); i++) {
    const unsigned char c = static_cast<unsigned char>(obj_text[i]);
    if (c == '\n' || c == '\r' || c == '\t') {
      continue;
    }
    if (c < 0x20 || c > 0x7e) {
      return false;
    }
  }
  return true;
}

inline bool IndexEquals(const tinyobj::index_t &lhs,
                        const tinyobj::index_t &rhs) {
  return lhs.vertex_index == rhs.vertex_index &&
         lhs.texcoord_index == rhs.texcoord_index &&
         lhs.normal_index == rhs.normal_index;
}

inline bool TagEquals(const tinyobj::tag_t &lhs, const tinyobj::tag_t &rhs) {
  return lhs.name == rhs.name && lhs.intValues == rhs.intValues &&
         lhs.floatValues == rhs.floatValues &&
         lhs.stringValues == rhs.stringValues;
}

template <typename SkinWeightT>
inline bool SkinWeightEquals(const SkinWeightT &lhs, const SkinWeightT &rhs) {
  if (lhs.vertex_id != rhs.vertex_id ||
      lhs.weightValues.size() != rhs.weightValues.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.weightValues.size(); i++) {
    if (lhs.weightValues[i].joint_id != rhs.weightValues[i].joint_id ||
        lhs.weightValues[i].weight != rhs.weightValues[i].weight) {
      return false;
    }
  }
  return true;
}

inline bool LegacyMeshEquals(const tinyobj::mesh_t &lhs,
                             const tinyobj::mesh_t &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  if (lhs.num_face_vertices != rhs.num_face_vertices ||
      lhs.material_ids != rhs.material_ids ||
      lhs.smoothing_group_ids != rhs.smoothing_group_ids ||
      lhs.tags.size() != rhs.tags.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.tags.size(); i++) {
    if (!TagEquals(lhs.tags[i], rhs.tags[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyLinesEquals(const tinyobj::lines_t &lhs,
                              const tinyobj::lines_t &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  return lhs.num_line_vertices == rhs.num_line_vertices;
}

inline bool LegacyPointsEquals(const tinyobj::points_t &lhs,
                               const tinyobj::points_t &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyShapeEquals(const tinyobj::shape_t &lhs,
                              const tinyobj::shape_t &rhs) {
  return lhs.name == rhs.name && LegacyMeshEquals(lhs.mesh, rhs.mesh) &&
         LegacyLinesEquals(lhs.lines, rhs.lines) &&
         LegacyPointsEquals(lhs.points, rhs.points);
}

inline bool LegacyShapesEqual(const std::vector<tinyobj::shape_t> &lhs,
                              const std::vector<tinyobj::shape_t> &rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.size(); i++) {
    if (!LegacyShapeEquals(lhs[i], rhs[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyMaterialsEqual(
    const std::vector<tinyobj::material_t> &lhs,
    const std::vector<tinyobj::material_t> &rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.size(); i++) {
    if (lhs[i].name != rhs[i].name) {
      return false;
    }
  }
  return true;
}

inline size_t ShapeIndexCount(const std::vector<tinyobj::shape_t> &shapes) {
  size_t count = 0;
  for (size_t i = 0; i < shapes.size(); i++) {
    count += shapes[i].mesh.indices.size();
  }
  return count;
}

inline bool LegacyAttribEquals(const tinyobj::attrib_t &lhs,
                               const tinyobj::attrib_t &rhs) {
  if (lhs.vertices != rhs.vertices || lhs.vertex_weights != rhs.vertex_weights ||
      lhs.normals != rhs.normals || lhs.texcoords != rhs.texcoords ||
      lhs.texcoord_ws != rhs.texcoord_ws || lhs.colors != rhs.colors ||
      lhs.skin_weights.size() != rhs.skin_weights.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.skin_weights.size(); i++) {
    if (!SkinWeightEquals(lhs.skin_weights[i], rhs.skin_weights[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyMeshEqualsOpt(const tinyobj::mesh_t &lhs,
                                const tinyobj::basic_mesh_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  if (lhs.num_face_vertices != rhs.num_face_vertices ||
      lhs.material_ids != rhs.material_ids ||
      lhs.smoothing_group_ids != rhs.smoothing_group_ids ||
      lhs.tags.size() != rhs.tags.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.tags.size(); i++) {
    if (!TagEquals(lhs.tags[i], rhs.tags[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyLinesEqualsOpt(const tinyobj::lines_t &lhs,
                                 const tinyobj::basic_lines_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  return lhs.num_line_vertices == rhs.num_line_vertices;
}

inline bool LegacyPointsEqualsOpt(const tinyobj::points_t &lhs,
                                  const tinyobj::basic_points_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyShapeEqualsOpt(const tinyobj::shape_t &lhs,
                                 const tinyobj::basic_shape_t<> &rhs) {
  return lhs.name == rhs.name && LegacyMeshEqualsOpt(lhs.mesh, rhs.mesh) &&
         LegacyLinesEqualsOpt(lhs.lines, rhs.lines) &&
         LegacyPointsEqualsOpt(lhs.points, rhs.points);
}

inline bool LegacyShapesEqualOpt(
    const std::vector<tinyobj::shape_t> &lhs,
    const std::vector<tinyobj::basic_shape_t<> > &rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.size(); i++) {
    if (!LegacyShapeEqualsOpt(lhs[i], rhs[i])) {
      return false;
    }
  }
  return true;
}

inline bool LegacyAttribEqualsOpt(const tinyobj::attrib_t &lhs,
                                  const tinyobj::basic_attrib_t<> &rhs) {
  if (lhs.vertices != rhs.vertices || lhs.vertex_weights != rhs.vertex_weights ||
      lhs.normals != rhs.normals || lhs.texcoords != rhs.texcoords ||
      lhs.texcoord_ws != rhs.texcoord_ws || lhs.colors != rhs.colors ||
      lhs.skin_weights.size() != rhs.skin_weights.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.skin_weights.size(); i++) {
    if (!SkinWeightEquals(lhs.skin_weights[i], rhs.skin_weights[i])) {
      return false;
    }
  }
  return true;
}

}  // namespace tinyobj_fuzz

#endif  // TINYOBJ_TESTS_FUZZ_COMMON_H_
