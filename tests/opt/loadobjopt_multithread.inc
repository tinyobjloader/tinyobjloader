namespace opt_test {

static bool IndexEquals(const tinyobj::index_t &lhs, const tinyobj::index_t &rhs) {
  return lhs.vertex_index == rhs.vertex_index &&
         lhs.normal_index == rhs.normal_index &&
         lhs.texcoord_index == rhs.texcoord_index;
}

template <typename LhsTag, typename RhsTag>
static bool TagEquals(const LhsTag &lhs, const RhsTag &rhs) {
  if (!(lhs.name == rhs.name) || lhs.intValues != rhs.intValues ||
      lhs.floatValues != rhs.floatValues ||
      lhs.stringValues.size() != rhs.stringValues.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.stringValues.size(); i++) {
    if (!(lhs.stringValues[i] == rhs.stringValues[i])) return false;
  }
  return true;
}

template <typename LhsTag, typename LhsAlloc, typename RhsTag, typename RhsAlloc>
static bool TagsEqual(const std::vector<LhsTag, LhsAlloc> &lhs,
                      const std::vector<RhsTag, RhsAlloc> &rhs) {
  if (lhs.size() != rhs.size()) return false;
  for (size_t i = 0; i < lhs.size(); i++) {
    if (!TagEquals(lhs[i], rhs[i])) return false;
  }
  return true;
}

template <typename LhsSkin, typename RhsSkin>
static bool SkinWeightEquals(const LhsSkin &lhs, const RhsSkin &rhs) {
  if (lhs.vertex_id != rhs.vertex_id) return false;
  if (lhs.weightValues.size() != rhs.weightValues.size()) return false;
  for (size_t i = 0; i < lhs.weightValues.size(); i++) {
    if (lhs.weightValues[i].joint_id != rhs.weightValues[i].joint_id) {
      return false;
    }
    if (!FloatEquals(static_cast<float>(lhs.weightValues[i].weight),
                     static_cast<float>(rhs.weightValues[i].weight))) {
      return false;
    }
  }
  return true;
}

static bool MeshEquals(const tinyobj::basic_mesh_t<> &lhs,
                       const tinyobj::basic_mesh_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }

  return lhs.num_face_vertices == rhs.num_face_vertices &&
         lhs.material_ids == rhs.material_ids &&
         lhs.smoothing_group_ids == rhs.smoothing_group_ids &&
         TagsEqual(lhs.tags, rhs.tags);
}

static bool LinesEquals(const tinyobj::basic_lines_t<> &lhs,
                        const tinyobj::basic_lines_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }
  return lhs.num_line_vertices == rhs.num_line_vertices;
}

static bool PointsEquals(const tinyobj::basic_points_t<> &lhs,
                         const tinyobj::basic_points_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }
  return true;
}

static bool ShapeEquals(const tinyobj::basic_shape_t<> &lhs,
                        const tinyobj::basic_shape_t<> &rhs) {
  return lhs.name == rhs.name && MeshEquals(lhs.mesh, rhs.mesh) &&
         LinesEquals(lhs.lines, rhs.lines) && PointsEquals(lhs.points, rhs.points);
}

static bool AttribEquals(const tinyobj::basic_attrib_t<> &lhs,
                         const tinyobj::basic_attrib_t<> &rhs) {
  if (lhs.vertices != rhs.vertices) return false;
  if (lhs.vertex_weights != rhs.vertex_weights) return false;
  if (lhs.normals != rhs.normals) return false;
  if (lhs.texcoords != rhs.texcoords) return false;
  if (lhs.texcoord_ws != rhs.texcoord_ws) return false;
  if (lhs.colors != rhs.colors) return false;
  if (lhs.skin_weights.size() != rhs.skin_weights.size()) return false;
  for (size_t i = 0; i < lhs.skin_weights.size(); i++) {
    if (!SkinWeightEquals(lhs.skin_weights[i], rhs.skin_weights[i])) return false;
  }
  if (lhs.face_num_verts != rhs.face_num_verts) return false;
  if (lhs.material_ids != rhs.material_ids) return false;
  if (lhs.indices.size() != rhs.indices.size()) return false;

  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }

  return true;
}

static bool ShapesEquals(const std::vector<tinyobj::basic_shape_t<>> &lhs,
                         const std::vector<tinyobj::basic_shape_t<>> &rhs) {
  if (lhs.size() != rhs.size()) return false;
  for (size_t i = 0; i < lhs.size(); i++) {
    if (!ShapeEquals(lhs[i], rhs[i])) return false;
  }
  return true;
}

static bool LegacyMeshEquals(const tinyobj::mesh_t &lhs,
                             const tinyobj::basic_mesh_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }

  return lhs.num_face_vertices == rhs.num_face_vertices &&
         lhs.material_ids == rhs.material_ids &&
         lhs.smoothing_group_ids == rhs.smoothing_group_ids &&
         TagsEqual(lhs.tags, rhs.tags);
}

static bool LegacyLinesEquals(const tinyobj::lines_t &lhs,
                              const tinyobj::basic_lines_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }
  return lhs.num_line_vertices == rhs.num_line_vertices;
}

static bool LegacyPointsEquals(const tinyobj::points_t &lhs,
                               const tinyobj::basic_points_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }
  return true;
}

static bool LegacyShapeEquals(const tinyobj::shape_t &lhs,
                              const tinyobj::basic_shape_t<> &rhs) {
  return lhs.name == rhs.name && LegacyMeshEquals(lhs.mesh, rhs.mesh) &&
         LegacyLinesEquals(lhs.lines, rhs.lines) &&
         LegacyPointsEquals(lhs.points, rhs.points);
}

static bool LegacyShapesEqualOpt(
    const std::vector<tinyobj::shape_t> &lhs,
    const std::vector<tinyobj::basic_shape_t<>> &rhs) {
  if (lhs.size() != rhs.size()) return false;
  for (size_t i = 0; i < lhs.size(); i++) {
    if (!LegacyShapeEquals(lhs[i], rhs[i])) return false;
  }
  return true;
}

static bool LegacyAttribEqualsOpt(const tinyobj::attrib_t &lhs,
                                  const std::vector<tinyobj::shape_t> &lhs_shapes,
                                  const tinyobj::basic_attrib_t<> &rhs) {
  if (lhs.vertices != rhs.vertices) return false;
  if (lhs.vertex_weights != rhs.vertex_weights) return false;
  if (lhs.normals != rhs.normals) return false;
  if (lhs.texcoords != rhs.texcoords) return false;
  if (lhs.texcoord_ws != rhs.texcoord_ws) return false;
  if (lhs.colors != rhs.colors) return false;
  if (lhs.skin_weights.size() != rhs.skin_weights.size()) return false;
  for (size_t i = 0; i < lhs.skin_weights.size(); i++) {
    if (!SkinWeightEquals(lhs.skin_weights[i], rhs.skin_weights[i])) return false;
  }

  std::vector<tinyobj::index_t> legacy_indices;
  std::vector<int> legacy_face_num_verts;
  std::vector<int> legacy_material_ids;
  for (size_t i = 0; i < lhs_shapes.size(); i++) {
    legacy_indices.insert(legacy_indices.end(), lhs_shapes[i].mesh.indices.begin(),
                          lhs_shapes[i].mesh.indices.end());
    legacy_face_num_verts.insert(legacy_face_num_verts.end(),
                                 lhs_shapes[i].mesh.num_face_vertices.begin(),
                                 lhs_shapes[i].mesh.num_face_vertices.end());
    legacy_material_ids.insert(legacy_material_ids.end(),
                               lhs_shapes[i].mesh.material_ids.begin(),
                               lhs_shapes[i].mesh.material_ids.end());
  }

  if (legacy_face_num_verts != rhs.face_num_verts) return false;
  if (legacy_material_ids != rhs.material_ids) return false;
  if (legacy_indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < legacy_indices.size(); i++) {
    if (!IndexEquals(legacy_indices[i], rhs.indices[i])) return false;
  }

  return true;
}

static bool LegacyMaterialsEqualOpt(
    const std::vector<tinyobj::material_t> &lhs,
    const std::vector<tinyobj::material_t> &rhs) {
  if (lhs.size() != rhs.size()) return false;
  for (size_t i = 0; i < lhs.size(); i++) {
    if (lhs[i].name != rhs[i].name) return false;
  }
  return true;
}

static std::string BuildChunkedSyntheticObj(size_t group_count,
                                            size_t faces_per_group) {
  std::ostringstream os;
  size_t vertex_index = 1;
  size_t texcoord_index = 1;
  size_t normal_index = 1;

  for (size_t group = 0; group < group_count; group++) {
    os << "o object_" << group << "\n";
    os << "g group_" << group << "\n";

    for (size_t face = 0; face < faces_per_group; face++) {
      const float base = static_cast<float>(group * faces_per_group + face);
      os << "v " << base << " 0.0 0.0\n";
      os << "v " << base << " 1.0 0.0\n";
      os << "v " << base << " 0.0 1.0\n";

      os << "vt 0.0 0.0\n";
      os << "vt 1.0 0.0\n";
      os << "vt 0.0 1.0\n";

      os << "vn 0.0 0.0 1.0\n";
      os << "vn 0.0 0.0 1.0\n";
      os << "vn 0.0 0.0 1.0\n";

      os << "f "
         << vertex_index << "/" << texcoord_index << "/" << normal_index << " "
         << (vertex_index + 1) << "/" << (texcoord_index + 1) << "/"
         << (normal_index + 1) << " "
         << (vertex_index + 2) << "/" << (texcoord_index + 2) << "/"
         << (normal_index + 2) << "\n";

      vertex_index += 3;
      texcoord_index += 3;
      normal_index += 3;
    }
  }

  return os.str();
}

static std::string BuildRelativeIndexObj(size_t face_count) {
  std::ostringstream os;
  for (size_t face = 0; face < face_count; face++) {
    const float base = static_cast<float>(face);
    os << "v " << base << " 0.0 0.0\n";
    os << "v " << base << " 1.0 0.0\n";
    os << "v " << base << " 0.0 1.0\n";
    os << "f -3 -2 -1\n";
  }
  return os.str();
}

static void RunOptLoad(const std::string &obj_text, int num_threads,
                       tinyobj::basic_attrib_t<> *attrib,
                       std::vector<tinyobj::basic_shape_t<>> *shapes,
                       std::vector<tinyobj::material_t> *materials,
                       std::string *warn, std::string *err) {
  tinyobj::OptLoadConfig config;
  config.num_threads = num_threads;
  config.triangulate = true;

  bool ok = tinyobj::LoadObjOpt(attrib, shapes, materials, warn, err,
                                obj_text.c_str(), obj_text.size(), config);
  if (!ok && !err->empty()) {
    std::cerr << "LoadObjOpt failed: " << *err << "\n";
  }
  TEST_CHECK(ok == true);
}

static bool WriteTextFile(const std::string &path, const std::string &content) {
#ifdef _WIN32
  std::ofstream out(LongPathW(UTF8ToWchar(path)).c_str(), std::ios::binary);
#else
  std::ofstream out(path.c_str(), std::ios::binary);
#endif
  if (!out) return false;
  out << content;
  return !out.fail();
}

static std::string BuildTriangleSoupObj(size_t triangle_count) {
  std::ostringstream os;
  size_t vertex_index = 1;

  for (size_t i = 0; i < triangle_count; i++) {
    const float base = static_cast<float>(i);
    os << "v " << base << " 0.0 0.0\n";
    os << "v " << base << " 1.0 0.0\n";
    os << "v " << base << " 0.0 1.0\n";
    os << "f " << vertex_index << " " << (vertex_index + 1) << " "
       << (vertex_index + 2) << "\n";
    vertex_index += 3;
  }

  return os.str();
}

static std::string BuildPointsOnlyObj(size_t vertex_count) {
  std::ostringstream os;
  for (size_t i = 0; i < vertex_count; i++) {
    const float base = static_cast<float>(i);
    os << "v " << base << " " << (base + 0.5f) << " 0.0\n";
    os << "p " << (i + 1) << "\n";
  }
  return os.str();
}

static std::string BuildFacesOnlyObj(size_t face_count) {
  std::ostringstream os;
  for (size_t i = 0; i < face_count; i++) {
    const size_t base = i * 3 + 1;
    os << "f " << base << " " << (base + 1) << " " << (base + 2) << "\n";
  }
  return os.str();
}

static std::string BuildInvalidFaceTokenObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 bad 3\n";
}

static std::string BuildTexcoordWObj() {
  return
      "vt 0.0 0.0 0.5\n"
      "vt 1.0 0.0\n"
      "vt 0.0 1.0 0.25\n";
}

static std::string BuildExtendedFeatureObj() {
  return
      "o extended\n"
      "v 0.0 0.0 0.0 0.5\n"
      "v 1.0 0.0 0.0 0.75\n"
      "v 0.0 1.0 0.0 1.0\n"
      "vt 0.0 0.0 0.25\n"
      "vt 1.0 0.0 0.0\n"
      "vt 0.0 1.0 0.5\n"
      "vw 0 1 0.75 2 0.25\n"
      "l 1/1 2/2 3/3\n"
      "p 3\n"
      "t crease 1/1/1 7 0.5 hard\n"
      "f 1/1 2/2 3/3\n";
}

static std::string BuildWeightedVertexTexcoordObj() {
  return
      "v 0.0 0.0 0.0 0.5\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0 0.75\n"
      "vt 0.0 0.0 0.25\n"
      "vt 1.0 0.0\n"
      "vt 0.0 1.0 0.5\n"
      "f 1/1 2/2 3/3\n";
}

static std::string BuildSingleComponentTexcoordObj() {
  return "vt 0.5\n";
}

static std::string BuildEmbeddedCarriageReturnObj() {
  return
      "o seed\n"
      "g s\reed_group\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "vt 0.0 0.0\n"
      "vt 1.0 0.0\n"
      "vt 0.0 1.0\n"
      "usemtl default\n"
      "s 1\n"
      "f 1/1/1 2/2/1 3/8/1\n";
}

static std::string BuildEmbeddedNulEmptyShapeObj() {
  std::string obj =
      "o seed\n"
      "g seed_grou\n"
      "vn 0.0 0.0 1.0\n"
      "usemtl default\n"
      "s 1\n"
      "f 1/1\n"
      "usemtl defau_";
  obj.append(7, '\0');
  obj += " 1/1/1 2/2/1 3/3/1\n";
  return obj;
}

static std::string BuildObjectOnlyObj() {
  return "o seedo\n";
}

static std::string BuildGroupOnlyObj() {
  return "g group_only\n";
}

static std::string BuildDegenerateFaceOnlyObj() {
  return
      "o obj\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "f 1 2\n";
}

static std::string BuildDegenerateFaceThenMissingUsemtlObj() {
  return
      "g grp\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "f 1 2\n"
      "usemtl missing\n";
}

static std::string BuildDegenerateFaceThenInvalidFaceObj() {
  return
      "g grp\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "f 1 2\n"
      "f 1 bad 3\n";
}

static std::string BuildInitialNamedShapeThenBoundaryObj() {
  return
      "o root_object\n"
      "g first_group\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "v 0.0 0.0 1.0\n"
      "f 1 2 3\n"
      "g second_group\n"
      "f 1 3 4\n";
}

static std::string BuildInvalidRelativeVertexIndexObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f -4 -3 -2\n";
}

static std::string BuildInvalidRelativeTexcoordNormalIndexObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "vt 0.0 0.0\n"
      "vt 1.0 0.0\n"
      "vt 0.0 1.0\n"
      "vn 0.0 0.0 1.0\n"
      "f 1/-4/-2 2/2/1 3/3/1\n";
}

static std::string BuildAcceptedOutOfBoundsFaceObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "vt 0.0 0.0\n"
      "vn 0.0 0.0 1.0\n"
      "f 4/2/2 1/1/1 2/1/1\n";
}

static std::string BuildZeroVertexIndexThenMissingMaterialObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 0 1 2\n"
      "usemtl later_missing\n";
}

static std::string BuildZeroTexcoordNormalIndexObj() {
  return
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "vt 0.0 0.0\n"
      "vn 0.0 0.0 1.0\n"
      "f 1/0/0 2/1/1 3/1/1\n";
}

static size_t ParseBenchmarkTriCount() {
  const char *env = std::getenv("TINYOBJ_OPT_BENCH_TRIS");
  if (!env || env[0] == '\0') {
    return 100000;  // sane default for normal test runs
  }

  char *end = NULL;
  unsigned long long parsed = strtoull(env, &end, 10);
  if (end == env || (end && *end != '\0')) {
    return 100000;
  }

  // Empirical slope from local runs is ~0.93 KB / triangle for the
  // optimized synthetic benchmark binary built without ASAN.
  // Clamp to a conservative ~48 GiB budget with some headroom.
  const unsigned long long max_triangles = 45000000ULL;
  if (parsed > max_triangles) {
    parsed = max_triangles;
  }

  if (parsed == 0) {
    parsed = 1;
  }

  return static_cast<size_t>(parsed);
}

static size_t ParseCorrectnessTriCount() {
  const char *env = std::getenv("TINYOBJ_OPT_COMPARE_TRIS");
  if (!env || env[0] == '\0') {
    return 100000;
  }

  char *end = NULL;
  unsigned long long parsed = strtoull(env, &end, 10);
  if (end == env || (end && *end != '\0')) {
    return 100000;
  }

  if (parsed == 0) {
    parsed = 1;
  }

  if (parsed > 100000ULL) {
    parsed = 100000ULL;
  }

  return static_cast<size_t>(parsed);
}

static std::string BuildThreadedMaterialObj(size_t face_count_per_material) {
  std::ostringstream os;
  size_t vertex_index = 1;
  os << "mtllib materials.mtl\n";
  os << "usemtl mat_a\n";

  for (size_t i = 0; i < face_count_per_material; i++) {
    const float base = static_cast<float>(i);
    os << "v " << base << " 0.0 0.0\n";
    os << "v " << base << " 1.0 0.0\n";
    os << "v " << base << " 0.0 1.0\n";
    os << "f " << vertex_index << " " << (vertex_index + 1) << " "
       << (vertex_index + 2) << "\n";
    vertex_index += 3;
  }

  os << "usemtl mat_b\n";
  for (size_t i = 0; i < face_count_per_material; i++) {
    const float base = static_cast<float>(face_count_per_material + i);
    os << "v " << base << " 0.0 0.0\n";
    os << "v " << base << " 1.0 0.0\n";
    os << "v " << base << " 0.0 1.0\n";
    os << "f " << vertex_index << " " << (vertex_index + 1) << " "
       << (vertex_index + 2) << "\n";
    vertex_index += 3;
  }

  return os.str();
}

static std::string BuildColorAndSmoothingObj() {
  std::ostringstream os;
  os << "mtllib mat.mtl\n";
  os << "usemtl mat_a # trailing comment must be ignored\n";
  os << "v 0.0 0.0 0.0 1.0 0.0 0.0\n";
  os << "v 1.0 0.0 0.0 0.0 1.0 0.0\n";
  os << "v 0.0 1.0 0.0 0.0 0.0 1.0\n";
  os << "s 7\n";
  os << "f 1 2 3\n";
  os << "s off\n";
  os << "g second\n";
  os << "v 0.0 0.0 1.0 0.5 0.5 0.5\n";
  os << "v 1.0 0.0 1.0 0.2 0.2 0.2\n";
  os << "v 0.0 1.0 1.0 0.8 0.8 0.8\n";
  os << "f 4 5 6\n";
  return os.str();
}

static std::string BuildMixedColorObj() {
  std::ostringstream os;
  os << "v 0.0 0.0 0.0\n";
  os << "v 1.0 0.0 0.0 0.1 0.2 0.3\n";
  os << "v 0.0 1.0 0.0\n";
  os << "f 1 2 3\n";
  return os.str();
}

static std::string BuildFaceCommentObj() {
  std::ostringstream os;
  os << "v 0.0 0.0 0.0\n";
  os << "v 1.0 0.0 0.0\n";
  os << "v 0.0 1.0 0.0\n";
  os << "f 1 2 3 # trailing comment should be ignored\n";
  return os.str();
}

static std::string BuildConcavePolygonObj() {
  std::ostringstream os;
  os << "v 0.0 0.0 0.0\n";
  os << "v 2.0 0.0 0.0\n";
  os << "v 2.0 2.0 0.0\n";
  os << "v 1.0 1.0 0.0\n";
  os << "v 0.0 2.0 0.0\n";
  os << "f 1 2 3 4 5\n";
  return os.str();
}

static std::string BuildInvalidPolygonObj() {
  std::ostringstream os;
  os << "v 0.0 0.0 0.0\n";
  os << "v 1.0 0.0 0.0\n";
  os << "v 1.0 1.0 0.0\n";
  os << "v 0.0 1.0 0.0\n";
  os << "f 1 2 3 4 5\n";
  return os.str();
}

static std::string BuildUsemtlBeforeMtllibObj() {
  return
      "usemtl mat_early\n"
      "mtllib mats.mtl\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildGroupCommentObj() {
  return
      "g foo # trailing comment should be ignored\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildWeightedVertexCommentObj() {
  return
      "v 0.0 0.0 0.0 0.5 # trailing comment must be ignored\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildEmptyGroupObj() {
  return
      "g   # empty group should warn and reset the current group\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildOptionalVertexFallbackObj() {
  return
      "v 0.0 0.0 0.0 foo\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildObjectSpacingObj() {
  return
      "o   foo  \n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildEmptyMtllibObj() {
  return
      "mtllib    \n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
}

static std::string BuildInvalidVertexRecordObj() {
  return "v a 0.0 0.0\n";
}

}  // namespace opt_test

void test_loadobjopt_multithread_matches_single_thread() {
  const std::string obj_text = opt_test::BuildChunkedSyntheticObj(6, 24);

  tinyobj::basic_attrib_t<> single_attrib;
  tinyobj::basic_attrib_t<> multi_attrib;
  std::vector<tinyobj::basic_shape_t<>> single_shapes;
  std::vector<tinyobj::basic_shape_t<>> multi_shapes;
  std::vector<tinyobj::material_t> single_materials;
  std::vector<tinyobj::material_t> multi_materials;
  std::string single_warn;
  std::string single_err;
  std::string multi_warn;
  std::string multi_err;

  opt_test::RunOptLoad(obj_text, 1, &single_attrib, &single_shapes,
                       &single_materials, &single_warn, &single_err);
  opt_test::RunOptLoad(obj_text, 4, &multi_attrib, &multi_shapes,
                       &multi_materials, &multi_warn, &multi_err);

  TEST_CHECK(single_warn == multi_warn);
  TEST_CHECK(single_materials.size() == multi_materials.size());
  TEST_CHECK(opt_test::AttribEquals(single_attrib, multi_attrib));
  TEST_CHECK(opt_test::ShapesEquals(single_shapes, multi_shapes));
  TEST_CHECK(multi_shapes.size() == 6);
}

void test_loadobjopt_multithread_relative_indices_match_single_thread() {
  const std::string obj_text = opt_test::BuildRelativeIndexObj(256);

  tinyobj::basic_attrib_t<> single_attrib;
  tinyobj::basic_attrib_t<> multi_attrib;
  std::vector<tinyobj::basic_shape_t<>> single_shapes;
  std::vector<tinyobj::basic_shape_t<>> multi_shapes;
  std::vector<tinyobj::material_t> single_materials;
  std::vector<tinyobj::material_t> multi_materials;
  std::string single_warn;
  std::string single_err;
  std::string multi_warn;
  std::string multi_err;

  opt_test::RunOptLoad(obj_text, 1, &single_attrib, &single_shapes,
                       &single_materials, &single_warn, &single_err);
  opt_test::RunOptLoad(obj_text, 8, &multi_attrib, &multi_shapes,
                       &multi_materials, &multi_warn, &multi_err);

  TEST_CHECK(single_warn == multi_warn);
  TEST_CHECK(single_materials.size() == multi_materials.size());
  TEST_CHECK(opt_test::AttribEquals(single_attrib, multi_attrib));
  TEST_CHECK(opt_test::ShapesEquals(single_shapes, multi_shapes));
  TEST_CHECK(multi_attrib.face_num_verts.size() == 256);
}

void test_loadobjopt_mtllib_multiple_filenames() {
#ifdef _WIN32
  const char path_sep = '\\';
  std::string test_dir = WcharToUTF8(L"") + std::string();
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_mtllib_multi\\";
#else
  const char path_sep = '/';
  std::string test_dir = "/tmp/tinyobj_opt_mtllib_multi/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "good.mtl";
  const std::string obj_text =
      "mtllib missing.mtl good.mtl\n"
      "usemtl mat_ok\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_text =
      "newmtl mat_ok\n"
      "Kd 1.0 0.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::basic_attrib_t<> attrib;
  std::vector<tinyobj::basic_shape_t<>> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 1;
  config.triangulate = true;

  bool ok = tinyobj::LoadObjOpt(&attrib, &shapes, &materials, &warn, &err,
                                obj_path.c_str(),
                                static_cast<const char *>(NULL), config);
  RemoveTestDir(test_dir);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(materials.size() == 1);
  TEST_CHECK(materials[0].name == "mat_ok");
  TEST_CHECK(attrib.material_ids.size() == 1);
  TEST_CHECK(attrib.material_ids[0] == 0);
  TEST_CHECK(warn.find("Failed to load material file(s)") == std::string::npos);
}

void test_loadobjopt_mtllib_repeated_lines() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_mtllib_repeat\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_mtllib_repeat/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_a_path = test_dir + "a.mtl";
  const std::string mtl_b_path = test_dir + "b.mtl";
  const std::string obj_text =
      "mtllib a.mtl\n"
      "mtllib b.mtl\n"
      "usemtl mat_b\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_a_text =
      "newmtl mat_a\n"
      "Kd 1.0 0.0 0.0\n";
  const std::string mtl_b_text =
      "newmtl mat_b\n"
      "Kd 0.0 1.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_a_path, mtl_a_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_b_path, mtl_b_text));

  tinyobj::basic_attrib_t<> attrib;
  std::vector<tinyobj::basic_shape_t<>> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 1;
  config.triangulate = true;

  bool ok = tinyobj::LoadObjOpt(&attrib, &shapes, &materials, &warn, &err,
                                obj_path.c_str(),
                                static_cast<const char *>(NULL), config);
  RemoveTestDir(test_dir);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(materials.size() == 2);
  TEST_CHECK(attrib.material_ids.size() == 1);
  TEST_CHECK(attrib.material_ids[0] == 1);
}

void test_loadobjopt_points_only_input() {
  const std::string obj_text = opt_test::BuildPointsOnlyObj(256);

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);

  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);
  if (!legacy_ok && !legacy_err.empty()) {
    std::cerr << "Legacy LoadObj failed: " << legacy_err << "\n";
  }
  TEST_CHECK(legacy_ok == true);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;

  bool ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                &opt_warn, &opt_err, obj_text.c_str(),
                                obj_text.size(), config);

  TEST_CHECK(ok == true);
  TEST_CHECK(opt_err.empty());
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
  TEST_CHECK(opt_materials.size() == legacy_materials.size());
}

void test_loadobjopt_faces_only_input() {
  const std::string obj_text = opt_test::BuildFacesOnlyObj(128);

  tinyobj::basic_attrib_t<> attrib;
  std::vector<tinyobj::basic_shape_t<>> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;

  bool ok = tinyobj::LoadObjOpt(&attrib, &shapes, &materials, &warn, &err,
                                obj_text.c_str(), obj_text.size(), config);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(attrib.vertices.empty());
  TEST_CHECK(attrib.indices.size() == 128 * 3);
  TEST_CHECK(attrib.face_num_verts.size() == 128);
  TEST_CHECK(!shapes.empty());
}

void test_loadobjopt_synthetic_benchmark() {
  const size_t triangle_count = opt_test::ParseBenchmarkTriCount();
  const std::string obj_text = opt_test::BuildTriangleSoupObj(triangle_count);

  tinyobj::basic_attrib_t<> attrib;
  std::vector<tinyobj::basic_shape_t<>> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;

  const clock_t begin = clock();
  bool ok = tinyobj::LoadObjOpt(&attrib, &shapes, &materials, &warn, &err,
                                obj_text.c_str(), obj_text.size(), config);
  const double elapsed_sec =
      static_cast<double>(clock() - begin) / static_cast<double>(CLOCKS_PER_SEC);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(attrib.vertices.size() == triangle_count * 9);
  TEST_CHECK(attrib.indices.size() == triangle_count * 3);
  TEST_CHECK(attrib.face_num_verts.size() == triangle_count);
  TEST_MSG("LoadObjOpt benchmark: %lu triangles in %.3f sec",
           static_cast<unsigned long>(triangle_count), elapsed_sec);
}

void test_loadobjopt_matches_legacy_parser_triangle_soup() {
  const size_t triangle_count = opt_test::ParseCorrectnessTriCount();
  const std::string obj_text = opt_test::BuildTriangleSoupObj(triangle_count);

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);

  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);
  if (!legacy_ok && !legacy_err.empty()) {
    std::cerr << "Legacy LoadObj failed: " << legacy_err << "\n";
  }
  TEST_CHECK(legacy_ok == true);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;

  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;

  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);
  if (!opt_ok && !opt_err.empty()) {
    std::cerr << "LoadObjOpt failed: " << opt_err << "\n";
  }
  TEST_CHECK(opt_ok == true);

  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_materials.size() == opt_materials.size());
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
  TEST_CHECK(opt_attrib.face_num_verts.size() == triangle_count);
}

void test_loadobjopt_matches_legacy_parser_mtllib_threaded() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_compare_mtllib\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_compare_mtllib/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "materials.mtl";
  const std::string obj_text = opt_test::BuildThreadedMaterialObj(256);
  const std::string mtl_text =
      "newmtl mat_a\n"
      "Kd 1.0 0.0 0.0\n"
      "newmtl mat_b\n"
      "Kd 0.0 1.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, obj_path.c_str(),
                                    test_dir.c_str(), true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyMaterialsEqualOpt(legacy_materials, opt_materials));
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_matches_legacy_parser_colors_smoothing_and_comments() {
  const std::string obj_text = opt_test::BuildColorAndSmoothingObj();
  const std::string mtl_text =
      "newmtl mat_a\n"
      "Kd 1.0 0.0 0.0\n";
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_compare_colors\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_compare_colors/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "mat.mtl";
  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;

  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    obj_path.c_str(), test_dir.c_str(), true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;

  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyMaterialsEqualOpt(legacy_materials, opt_materials));
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_mixed_vertex_colors_drop_like_legacy() {
  const std::string obj_text = opt_test::BuildMixedColorObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_attrib.colors.empty());
  TEST_CHECK(opt_attrib.colors.empty());
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_mixed_vertex_colors_drop_like_legacy() {
  const std::string obj_text = opt_test::BuildMixedColorObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &attrib, &shapes, &materials, &warn, &err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(legacy_attrib.colors.empty());
  TEST_CHECK(attrib.colors.empty());
  TEST_CHECK(legacy_attrib.vertices == attrib.vertices);
  TEST_CHECK(legacy_attrib.vertex_weights == attrib.vertex_weights);
  TEST_CHECK(legacy_attrib.normals == attrib.normals);
  TEST_CHECK(legacy_attrib.texcoords == attrib.texcoords);
  TEST_CHECK(legacy_attrib.texcoord_ws == attrib.texcoord_ws);
  TEST_CHECK(legacy_shapes.size() == shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() == shapes[0].mesh.indices.size());
  TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
             shapes[0].mesh.num_face_vertices);
  TEST_CHECK(legacy_shapes[0].mesh.material_ids == shapes[0].mesh.material_ids);
}

void test_stream_loader_mixed_vertex_colors_backfill() {
  const std::string obj_text = opt_test::BuildMixedColorObj();

  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.default_vcols_fallback = true;
  bool ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &attrib, &shapes, &materials, &warn, &err, &stream, NULL, config);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(attrib.vertices.size() == 9);
  TEST_CHECK(attrib.colors.size() == 9);
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[0]));
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[1]));
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[2]));
  TEST_CHECK(FloatEquals(0.1f, attrib.colors[3]));
  TEST_CHECK(FloatEquals(0.2f, attrib.colors[4]));
  TEST_CHECK(FloatEquals(0.3f, attrib.colors[5]));
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[6]));
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[7]));
  TEST_CHECK(FloatEquals(1.0f, attrib.colors[8]));
}

void test_stream_loader_mtllib_escaped_spaces() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_stream_mtllib_space\\";
#else
  std::string test_dir = "/tmp/tinyobj_stream_mtllib_space/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "my file.mtl";
  const std::string obj_text =
      "mtllib my\\ file.mtl\n"
      "usemtl mat_ok\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_text =
      "newmtl mat_ok\n"
      "Kd 0.2 0.3 0.4\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;
  std::string warn, err;
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &attrib, &shapes, &materials, &warn, &err, obj_path.c_str(),
      static_cast<const char *>(NULL), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(ok == true);
  TEST_CHECK(err.empty());
  TEST_CHECK(materials.size() == 1);
  TEST_CHECK(materials[0].name == "mat_ok");
}

void test_stream_loader_clears_outputs_on_failure() {
  const std::string obj_text =
      "v 0.0 0.0 0.0\n"
      "f bad bad bad\n";

  tinyobj::attrib_t attrib;
  attrib.vertices.push_back(42.0f);
  std::vector<tinyobj::shape_t> shapes(1);
  std::vector<tinyobj::material_t> materials(1);
  std::string warn, err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &attrib, &shapes, &materials, &warn, &err, &stream, NULL, config);

  TEST_CHECK(ok == false);
  TEST_CHECK(!err.empty());
  TEST_CHECK(attrib.vertices.empty());
  TEST_CHECK(attrib.colors.empty());
  TEST_CHECK(shapes.empty());
  TEST_CHECK(materials.empty());
}

void test_loadobjopt_face_comment_matches_legacy() {
  const std::string obj_text = opt_test::BuildFaceCommentObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_concave_polygon_matches_legacy() {
  const std::string obj_text = opt_test::BuildConcavePolygonObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_concave_polygon_matches_legacy() {
  const std::string obj_text = opt_test::BuildConcavePolygonObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.triangulate = true;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn, &stream_err,
      &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() == stream_shapes[0].mesh.indices.size());
  for (size_t i = 0; i < legacy_shapes[0].mesh.indices.size(); i++) {
    TEST_CHECK(opt_test::IndexEquals(legacy_shapes[0].mesh.indices[i],
                                     stream_shapes[0].mesh.indices[i]));
  }
}

void test_loadobjopt_invalid_polygon_matches_legacy() {
  const std::string obj_text = opt_test::BuildInvalidPolygonObj();

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(opt_ok == true);
  TEST_CHECK(opt_err.empty());
  TEST_CHECK(opt_attrib.face_num_verts.size() == opt_attrib.material_ids.size());
  size_t total_face_indices = 0;
  for (size_t i = 0; i < opt_attrib.face_num_verts.size(); i++) {
    total_face_indices += static_cast<size_t>(opt_attrib.face_num_verts[i]);
  }
  TEST_CHECK(total_face_indices == opt_attrib.indices.size());
  for (size_t i = 0; i < opt_shapes.size(); i++) {
    TEST_CHECK(opt_shapes[i].mesh.num_face_vertices.size() ==
               opt_shapes[i].mesh.material_ids.size());
    size_t shape_index_count = 0;
    for (size_t k = 0; k < opt_shapes[i].mesh.num_face_vertices.size(); k++) {
      shape_index_count +=
          static_cast<size_t>(opt_shapes[i].mesh.num_face_vertices[k]);
    }
    TEST_CHECK(shape_index_count == opt_shapes[i].mesh.indices.size());
  }
}

void test_stream_loader_hash_in_names() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_stream_hash_names\\";
#else
  std::string test_dir = "/tmp/tinyobj_stream_hash_names/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "lib#1.mtl";
  const std::string obj_text =
      "mtllib lib#1.mtl\n"
      "o object#1\n"
      "usemtl mat#1\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_text =
      "newmtl mat#1\n"
      "Kd 1.0 0.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, obj_path.c_str(), static_cast<const char *>(NULL), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(stream_ok == true);
  TEST_CHECK(stream_err.empty());
  TEST_CHECK(stream_materials.size() == 1);
  TEST_CHECK(stream_materials[0].name == "mat#1");
  TEST_CHECK(stream_shapes.size() == 1);
  TEST_CHECK(stream_shapes[0].name == "object#1");
  TEST_CHECK(stream_shapes[0].mesh.material_ids.size() == 1);
  TEST_CHECK(stream_shapes[0].mesh.material_ids[0] == 0);
}

void test_loadobjopt_hash_in_usemtl_matches_legacy() {
  const std::string obj_text =
      "mtllib mats.mtl\n"
      "usemtl mat#1\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_text =
      "newmtl mat#1\n"
      "Kd 1.0 0.0 0.0\n";
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_hash_usemtl\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_hash_usemtl/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "mats.mtl";
  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    obj_path.c_str(), test_dir.c_str(), true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(opt_test::LegacyMaterialsEqualOpt(legacy_materials, opt_materials));
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_usemtl_before_mtllib_matches_legacy() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_usemtl_before_mtllib\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_usemtl_before_mtllib/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "mats.mtl";
  const std::string obj_text = opt_test::BuildUsemtlBeforeMtllibObj();
  const std::string mtl_text =
      "newmtl mat_early\n"
      "Kd 1.0 0.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    obj_path.c_str(), test_dir.c_str(), true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyMaterialsEqualOpt(legacy_materials, opt_materials));
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_group_comment_matches_legacy() {
  const std::string obj_text = opt_test::BuildGroupCommentObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_invalid_face_token_matches_legacy_error() {
  const std::string obj_text = opt_test::BuildInvalidFaceTokenObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(opt_warn.empty());
  TEST_CHECK(opt_err.find("failed to parse `f' line (invalid vertex index)") !=
             std::string::npos);
  TEST_CHECK(opt_attrib.vertices.empty());
  TEST_CHECK(opt_shapes.empty());
}

void test_stream_loader_texcoord_w() {
  const std::string obj_text = opt_test::BuildTexcoordWObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.texcoords == stream_attrib.texcoords);
  TEST_CHECK(legacy_attrib.texcoord_ws == stream_attrib.texcoord_ws);
}

void test_stream_loader_vertex_weight() {
  const std::string obj_text =
      "v 0.0 0.0 0.0 0.5\n"
      "v 1.0 0.0 0.0\n";

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertex_weights == stream_attrib.vertex_weights);
}

void test_stream_loader_colored_vertex_weight() {
  const std::string obj_text =
      "v 0.0 0.0 0.0 0.1 0.2 0.3\n"
      "v 1.0 0.0 0.0 0.4 0.5 0.6\n";

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertex_weights == stream_attrib.vertex_weights);
  TEST_CHECK(legacy_attrib.colors == stream_attrib.colors);
}

// `v x y z w r g b` (7 components) -> weight = w, color = (r, g, b).
// 7-component vertices are not part of the OBJ spec or the common vertex-color
// extension (which define only xyz / xyzw / xyzrgb); tinyobjloader accepts them
// as an extension in LoadObjOpt and the stream loader (4th value = weight, next
// three = RGB).  The classic LoadObj path caps at 6, so we assert explicit
// values here rather than comparing against it.
void test_stream_loader_weighted_color_vertex_7_components() {
  const std::string obj_text =
      "v 0.0 0.0 0.0 0.5 0.1 0.2 0.3\n"
      "v 1.0 0.0 0.0 0.6 0.4 0.5 0.6\n";

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(stream_ok == true);
  TEST_CHECK(stream_attrib.vertex_weights.size() == 2);
  TEST_CHECK(FloatEquals(0.5f, stream_attrib.vertex_weights[0]));
  TEST_CHECK(FloatEquals(0.6f, stream_attrib.vertex_weights[1]));
  TEST_CHECK(stream_attrib.colors.size() == 6);
  TEST_CHECK(FloatEquals(0.1f, stream_attrib.colors[0]));
  TEST_CHECK(FloatEquals(0.2f, stream_attrib.colors[1]));
  TEST_CHECK(FloatEquals(0.3f, stream_attrib.colors[2]));
  TEST_CHECK(FloatEquals(0.4f, stream_attrib.colors[3]));
  TEST_CHECK(FloatEquals(0.5f, stream_attrib.colors[4]));
  TEST_CHECK(FloatEquals(0.6f, stream_attrib.colors[5]));
}

void test_stream_loader_group_comment_matches_legacy() {
  const std::string obj_text = opt_test::BuildGroupCommentObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
  TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
             stream_shapes[0].mesh.num_face_vertices);
}

void test_stream_loader_weighted_vertex_comment_matches_legacy() {
  const std::string obj_text = opt_test::BuildWeightedVertexCommentObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_attrib.vertex_weights == stream_attrib.vertex_weights);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
             stream_shapes[0].mesh.num_face_vertices);
}

void test_loadobjopt_mtllib_warning_preserved_on_parse_error() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_mtllib_warn_error\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_mtllib_warn_error/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string obj_text =
      "mtllib missing.mtl\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 bad 3\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    obj_path.c_str(), test_dir.c_str(), true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(legacy_warn.find("Material file [ missing.mtl ]") !=
             std::string::npos);
  TEST_CHECK(legacy_warn.find(
                 "Failed to load material file(s). Use default material.") !=
             std::string::npos);
  TEST_CHECK(opt_warn.find("Material file [ missing.mtl ]") !=
             std::string::npos);
  TEST_CHECK(opt_warn.find(
                 "Failed to load material file(s). Use default material.") !=
             std::string::npos);
  TEST_CHECK(opt_err.find("failed to parse `f' line (invalid vertex index)") !=
             std::string::npos);
}

void test_loadobjopt_empty_group_warning_matches_legacy() {
  const std::string obj_text = opt_test::BuildEmptyGroupObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_empty_group_warning_matches_legacy() {
  const std::string obj_text = opt_test::BuildEmptyGroupObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
  TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
             stream_shapes[0].mesh.num_face_vertices);
}

void test_stream_loader_optional_vertex_token_matches_legacy() {
  const std::string obj_text = opt_test::BuildOptionalVertexFallbackObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_attrib.vertex_weights == stream_attrib.vertex_weights);
  TEST_CHECK(legacy_attrib.colors == stream_attrib.colors);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
  TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
             stream_shapes[0].mesh.num_face_vertices);
}

void test_loadobjopt_buffer_ignores_mtllib_like_legacy_stream() {
  const std::string obj_text =
      "mtllib missing.mtl\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_parse_error_reports_record_type() {
  const std::string obj_text = opt_test::BuildInvalidVertexRecordObj();

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(opt_ok == false);
  TEST_CHECK(opt_warn.empty());
  TEST_CHECK(opt_err.find("failed to parse `v' line") != std::string::npos);
  TEST_CHECK(opt_err.find("Failed parse `f' line") == std::string::npos);
}

void test_stream_loader_object_spacing_matches_legacy() {
  const std::string obj_text = opt_test::BuildObjectSpacingObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
}

void test_loadobjopt_object_spacing_matches_legacy() {
  const std::string obj_text = opt_test::BuildObjectSpacingObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_empty_mtllib_warning_matches_legacy_file() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_opt_empty_mtllib_warn\\";
#else
  std::string test_dir = "/tmp/tinyobj_opt_empty_mtllib_warn/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string obj_text = opt_test::BuildEmptyMtllibObj();
  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, obj_path.c_str(),
                                    test_dir.c_str(), true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_path.c_str(),
                                    test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_empty_mtllib_warning_matches_legacy() {
  const std::string obj_text = opt_test::BuildEmptyMtllibObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  tinyobj::MaterialFileReader legacy_reader((std::string()));
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream,
                                    &legacy_reader, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::MaterialFileReader stream_reader((std::string()));
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, &stream_reader, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
}

void test_stream_loader_warnings_preserved_on_parse_error() {
  const std::string obj_text =
      "mtllib missing.mtl\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 bad 3\n";

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  tinyobj::MaterialFileReader legacy_reader((std::string()));
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream,
                                    &legacy_reader, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::MaterialFileReader stream_reader((std::string()));
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.num_threads = 1;
  config.chunk_line_count = 64;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, &stream_reader, config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(stream_ok == false);
  TEST_CHECK(legacy_warn.find("Material file [ missing.mtl ]") !=
             std::string::npos);
  TEST_CHECK(legacy_warn.find(
                 "Failed to load material file(s). Use default material.") !=
             std::string::npos);
  TEST_CHECK(stream_warn.find("Material file [ missing.mtl ]") !=
             std::string::npos);
  TEST_CHECK(stream_warn.find(
                 "Failed to load material file(s). Use default material.") !=
             std::string::npos);
  TEST_CHECK(stream_err.find("malformed face record") != std::string::npos);
}

void test_stream_loader_material_resolution_without_material_output() {
#ifdef _WIN32
  std::string test_dir;
  wchar_t wtmpbuf[MAX_PATH];
  GetTempPathW(MAX_PATH, wtmpbuf);
  test_dir = WcharToUTF8(wtmpbuf) + "tinyobj_stream_null_materials\\";
#else
  std::string test_dir = "/tmp/tinyobj_stream_null_materials/";
#endif

  RemoveTestDir(test_dir);
  TEST_CHECK(MakeDir(test_dir));

  const std::string obj_path = test_dir + "scene.obj";
  const std::string mtl_path = test_dir + "mats.mtl";
  const std::string obj_text =
      "mtllib mats.mtl\n"
      "usemtl mat1\n"
      "v 0.0 0.0 0.0\n"
      "v 1.0 0.0 0.0\n"
      "v 0.0 1.0 0.0\n"
      "f 1 2 3\n";
  const std::string mtl_text =
      "newmtl mat1\n"
      "Kd 1.0 0.0 0.0\n";

  TEST_CHECK(opt_test::WriteTextFile(obj_path, obj_text));
  TEST_CHECK(opt_test::WriteTextFile(mtl_path, mtl_text));

  tinyobj::attrib_t with_material_attrib;
  std::vector<tinyobj::shape_t> with_material_shapes;
  std::vector<tinyobj::material_t> with_materials;
  std::string with_warn, with_err;
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool with_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &with_material_attrib, &with_material_shapes, &with_materials,
      &with_warn, &with_err, obj_path.c_str(), test_dir.c_str(), config);

  tinyobj::attrib_t without_material_attrib;
  std::vector<tinyobj::shape_t> without_material_shapes;
  std::string without_warn, without_err;
  bool without_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &without_material_attrib, &without_material_shapes, NULL,
      &without_warn, &without_err, obj_path.c_str(), test_dir.c_str(), config);

  RemoveTestDir(test_dir);

  TEST_CHECK(with_ok == true);
  TEST_CHECK(without_ok == true);
  TEST_CHECK(with_warn == without_warn);
  TEST_CHECK(with_err == without_err);
  TEST_CHECK(with_materials.size() == 1);
  TEST_CHECK(with_material_shapes.size() == without_material_shapes.size());
  TEST_CHECK(with_material_shapes[0].name == without_material_shapes[0].name);
  TEST_CHECK(with_material_shapes[0].mesh.indices.size() ==
             without_material_shapes[0].mesh.indices.size());
  for (size_t i = 0; i < with_material_shapes[0].mesh.indices.size(); i++) {
    TEST_CHECK(opt_test::IndexEquals(with_material_shapes[0].mesh.indices[i],
                                     without_material_shapes[0].mesh.indices[i]));
  }
  TEST_CHECK(with_material_shapes[0].mesh.material_ids ==
             without_material_shapes[0].mesh.material_ids);
  TEST_CHECK(without_material_shapes[0].mesh.material_ids.size() == 1);
  TEST_CHECK(without_material_shapes[0].mesh.material_ids[0] == 0);
}

void test_loadobjopt_matches_legacy_extended_features() {
  const std::string obj_text = opt_test::BuildExtendedFeatureObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 4;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_vertex_weight_and_texcoord_w_match_legacy() {
  const std::string obj_text = opt_test::BuildWeightedVertexTexcoordObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_single_component_texcoord_matches_legacy() {
  const std::string obj_text = opt_test::BuildSingleComponentTexcoordObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_single_component_texcoord_matches_legacy() {
  const std::string obj_text = opt_test::BuildSingleComponentTexcoordObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(stream_warn == legacy_warn);
  TEST_CHECK(stream_err == legacy_err);
  TEST_CHECK(stream_attrib.texcoords == legacy_attrib.texcoords);
  TEST_CHECK(stream_attrib.texcoord_ws == legacy_attrib.texcoord_ws);
}

void test_stream_loader_embedded_carriage_return_matches_legacy() {
  const std::string obj_text = opt_test::BuildEmbeddedCarriageReturnObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_attrib.texcoords == stream_attrib.texcoords);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
}

void test_stream_loader_embedded_nul_empty_shape_matches_legacy() {
  const std::string obj_text = opt_test::BuildEmbeddedNulEmptyShapeObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
}

void test_stream_loader_object_only_matches_legacy() {
  const std::string obj_text = opt_test::BuildObjectOnlyObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
}

void test_stream_loader_group_only_matches_legacy() {
  const std::string obj_text = opt_test::BuildGroupOnlyObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
}

void test_stream_loader_degenerate_face_matches_legacy() {
  const std::string obj_text = opt_test::BuildDegenerateFaceOnlyObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.triangulate = false;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  if (legacy_shapes.size() == stream_shapes.size() && !legacy_shapes.empty()) {
    TEST_CHECK(legacy_shapes[0].name == stream_shapes[0].name);
    TEST_CHECK(legacy_shapes[0].mesh.num_face_vertices ==
               stream_shapes[0].mesh.num_face_vertices);
    TEST_CHECK(legacy_shapes[0].mesh.material_ids ==
               stream_shapes[0].mesh.material_ids);
    TEST_CHECK(legacy_shapes[0].mesh.smoothing_group_ids ==
               stream_shapes[0].mesh.smoothing_group_ids);
    TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
               stream_shapes[0].mesh.indices.size());
    for (size_t i = 0; i < legacy_shapes[0].mesh.indices.size(); i++) {
      TEST_CHECK(opt_test::IndexEquals(legacy_shapes[0].mesh.indices[i],
                                       stream_shapes[0].mesh.indices[i]));
    }
  }
}

void test_loadobjopt_degenerate_face_matches_legacy() {
  const std::string obj_text = opt_test::BuildDegenerateFaceOnlyObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = false;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_degenerate_face_warning_order_matches_legacy() {
  const std::string obj_text = opt_test::BuildDegenerateFaceThenMissingUsemtlObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.triangulate = false;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
}

void test_stream_loader_degenerate_face_warning_suppressed_on_parse_error() {
  const std::string obj_text = opt_test::BuildDegenerateFaceThenInvalidFaceObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  config.triangulate = false;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(stream_ok == false);
  TEST_CHECK(legacy_warn.find("Degenerated face found") == std::string::npos);
  TEST_CHECK(stream_warn.find("Degenerated face found") == std::string::npos);
}

void test_loadobjopt_degenerate_face_warning_order_matches_legacy() {
  const std::string obj_text = opt_test::BuildDegenerateFaceThenMissingUsemtlObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = false;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
}

void test_loadobjopt_degenerate_face_warning_suppressed_on_parse_error() {
  const std::string obj_text = opt_test::BuildDegenerateFaceThenInvalidFaceObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, false, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = false;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(legacy_warn.find("Degenerated face found") == std::string::npos);
  TEST_CHECK(opt_warn.find("Degenerated face found") == std::string::npos);
}

void test_loadobjopt_initial_named_shape_matches_legacy() {
  const std::string obj_text = opt_test::BuildInitialNamedShapeThenBoundaryObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_loadobjopt_invalid_relative_vertex_index_matches_legacy_error() {
  const std::string obj_text = opt_test::BuildInvalidRelativeVertexIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(opt_err.find("failed to parse `f' line (invalid vertex index)") !=
             std::string::npos);
}

void test_loadobjopt_invalid_relative_texcoord_normal_index_matches_legacy_error() {
  const std::string obj_text =
      opt_test::BuildInvalidRelativeTexcoordNormalIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(opt_err.find("failed to parse `f' line (invalid vertex index)") !=
             std::string::npos);
}

void test_stream_loader_invalid_relative_vertex_index_matches_legacy_error() {
  const std::string obj_text = opt_test::BuildInvalidRelativeVertexIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(stream_ok == false);
  TEST_CHECK(stream_err.find("malformed face record") != std::string::npos);
}

void test_stream_loader_invalid_relative_texcoord_normal_index_matches_legacy_error() {
  const std::string obj_text =
      opt_test::BuildInvalidRelativeTexcoordNormalIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(stream_ok == false);
  TEST_CHECK(stream_err.find("malformed face record") != std::string::npos);
}

void test_loadobjopt_out_of_bounds_warning_matches_legacy() {
  const std::string obj_text = opt_test::BuildAcceptedOutOfBoundsFaceObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
}

void test_stream_loader_out_of_bounds_warning_matches_legacy() {
  const std::string obj_text = opt_test::BuildAcceptedOutOfBoundsFaceObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn, &legacy_err,
                                    &legacy_stream, NULL, true, false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
}

void test_loadobjopt_zero_vertex_index_warning_matches_legacy() {
  const std::string obj_text =
      opt_test::BuildZeroVertexIndexThenMissingMaterialObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(opt_ok == false);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(opt_warn.find("material [ 'later_missing' ] not found in .mtl") ==
             std::string::npos);
  TEST_CHECK(opt_err.find("failed to parse `f' line (invalid vertex index)") !=
             std::string::npos);
}

void test_stream_loader_zero_vertex_index_warning_matches_legacy() {
  const std::string obj_text =
      opt_test::BuildZeroVertexIndexThenMissingMaterialObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == false);
  TEST_CHECK(stream_ok == false);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(stream_warn.find("material [ 'later_missing' ] not found in .mtl") ==
             std::string::npos);
  TEST_CHECK(stream_err.find("malformed face record") != std::string::npos);
}

void test_loadobjopt_zero_texcoord_normal_indices_match_legacy() {
  const std::string obj_text = opt_test::BuildZeroTexcoordNormalIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::basic_attrib_t<> opt_attrib;
  std::vector<tinyobj::basic_shape_t<>> opt_shapes;
  std::vector<tinyobj::material_t> opt_materials;
  std::string opt_warn, opt_err;
  tinyobj::OptLoadConfig config;
  config.num_threads = 2;
  config.triangulate = true;
  bool opt_ok = tinyobj::LoadObjOpt(&opt_attrib, &opt_shapes, &opt_materials,
                                    &opt_warn, &opt_err, obj_text.c_str(),
                                    obj_text.size(), config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(opt_ok == true);
  TEST_CHECK(legacy_warn == opt_warn);
  TEST_CHECK(legacy_err == opt_err);
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, legacy_shapes,
                                             opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}

void test_stream_loader_zero_texcoord_normal_indices_match_legacy() {
  const std::string obj_text = opt_test::BuildZeroTexcoordNormalIndexObj();

  tinyobj::attrib_t legacy_attrib;
  std::vector<tinyobj::shape_t> legacy_shapes;
  std::vector<tinyobj::material_t> legacy_materials;
  std::string legacy_warn, legacy_err;
  std::istringstream legacy_stream(obj_text);
  bool legacy_ok = tinyobj::LoadObj(&legacy_attrib, &legacy_shapes,
                                    &legacy_materials, &legacy_warn,
                                    &legacy_err, &legacy_stream, NULL, true,
                                    false);

  tinyobj::attrib_t stream_attrib;
  std::vector<tinyobj::shape_t> stream_shapes;
  std::vector<tinyobj::material_t> stream_materials;
  std::string stream_warn, stream_err;
  std::istringstream stream(obj_text);
  tinyobj::experimental_stream::StreamLoadConfig config;
  bool stream_ok = tinyobj::experimental_stream::LoadObjStreamExperimental(
      &stream_attrib, &stream_shapes, &stream_materials, &stream_warn,
      &stream_err, &stream, NULL, config);

  TEST_CHECK(legacy_ok == true);
  TEST_CHECK(stream_ok == true);
  TEST_CHECK(legacy_warn == stream_warn);
  TEST_CHECK(legacy_err == stream_err);
  TEST_CHECK(legacy_attrib.vertices == stream_attrib.vertices);
  TEST_CHECK(legacy_attrib.normals == stream_attrib.normals);
  TEST_CHECK(legacy_attrib.texcoords == stream_attrib.texcoords);
  TEST_CHECK(legacy_shapes.size() == stream_shapes.size());
  TEST_CHECK(legacy_shapes[0].mesh.indices.size() ==
             stream_shapes[0].mesh.indices.size());
  for (size_t i = 0; i < legacy_shapes[0].mesh.indices.size(); i++) {
    TEST_CHECK(opt_test::IndexEquals(legacy_shapes[0].mesh.indices[i],
                                     stream_shapes[0].mesh.indices[i]));
  }
}
