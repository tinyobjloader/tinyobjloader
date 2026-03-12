namespace opt_test {

static bool IndexEquals(const tinyobj::index_t &lhs, const tinyobj::index_t &rhs) {
  return lhs.vertex_index == rhs.vertex_index &&
         lhs.normal_index == rhs.normal_index &&
         lhs.texcoord_index == rhs.texcoord_index;
}

static bool MeshEquals(const tinyobj::basic_mesh_t<> &lhs,
                       const tinyobj::basic_mesh_t<> &rhs) {
  if (lhs.indices.size() != rhs.indices.size()) return false;
  for (size_t i = 0; i < lhs.indices.size(); i++) {
    if (!IndexEquals(lhs.indices[i], rhs.indices[i])) return false;
  }

  return lhs.num_face_vertices == rhs.num_face_vertices &&
         lhs.material_ids == rhs.material_ids &&
         lhs.smoothing_group_ids == rhs.smoothing_group_ids;
}

static bool ShapeEquals(const tinyobj::basic_shape_t<> &lhs,
                        const tinyobj::basic_shape_t<> &rhs) {
  return lhs.name == rhs.name && MeshEquals(lhs.mesh, rhs.mesh);
}

static bool AttribEquals(const tinyobj::basic_attrib_t<> &lhs,
                         const tinyobj::basic_attrib_t<> &rhs) {
  if (lhs.vertices != rhs.vertices) return false;
  if (lhs.normals != rhs.normals) return false;
  if (lhs.texcoords != rhs.texcoords) return false;
  if (lhs.colors != rhs.colors) return false;
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
         lhs.material_ids == rhs.material_ids;
}

static bool LegacyShapeEquals(const tinyobj::shape_t &lhs,
                              const tinyobj::basic_shape_t<> &rhs) {
  return lhs.name == rhs.name && lhs.lines.indices.empty() &&
         lhs.points.indices.empty() && LegacyMeshEquals(lhs.mesh, rhs.mesh);
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
                                  const tinyobj::basic_attrib_t<> &rhs) {
  if (lhs.vertices != rhs.vertices) return false;
  if (lhs.normals != rhs.normals) return false;
  if (lhs.texcoords != rhs.texcoords) return false;
  if (lhs.colors != rhs.colors) return false;
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
  TEST_CHECK(attrib.vertices.size() == 256 * 3);
  TEST_CHECK(attrib.indices.empty());
  TEST_CHECK(attrib.face_num_verts.empty());
  TEST_CHECK(shapes.empty());
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
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, opt_attrib));
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
  TEST_CHECK(opt_test::LegacyAttribEqualsOpt(legacy_attrib, opt_attrib));
  TEST_CHECK(opt_test::LegacyShapesEqualOpt(legacy_shapes, opt_shapes));
}
