#include "../tinyobj_v3.hh"

#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#elif defined(__GNUC__)
#pragma GCC diagnostic ignored "-Wmissing-declarations"
#pragma GCC diagnostic ignored "-Wignored-qualifiers"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"
#pragma GCC diagnostic ignored "-Wsign-conversion"
#pragma GCC diagnostic ignored "-Wformat"
#pragma GCC diagnostic ignored "-Wswitch-default"
#endif

#include "acutest.h"

#if defined(__clang__)
#pragma clang diagnostic pop
#elif defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <sstream>

// ============================================================================
// File I/O callbacks for v3
// ============================================================================

const char* PosixFileRead(const char* filepath, size_t* out_size, void* user_data) {
    (void)user_data;
    FILE* fp = fopen(filepath, "rb");
    if (!fp) {
        *out_size = 0;
        return nullptr;
    }

    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    char* buffer = (char*)malloc(size);
    if (!buffer) {
        fclose(fp);
        *out_size = 0;
        return nullptr;
    }

    size_t bytes_read = fread(buffer, 1, size, fp);
    fclose(fp);

    *out_size = bytes_read;
    return buffer;
}

void PosixFileFree(const char* data, void* user_data) {
    (void)user_data;
    free((void*)data);
}

// ============================================================================
// Helper functions
// ============================================================================

template <typename T>
static bool FloatEquals(const T& a, const T& b) {
    const T eps = std::numeric_limits<T>::epsilon() * static_cast<T>(100);
    const T abs_diff = std::abs(a - b);
    return abs_diff < eps;
}

// Load OBJ file helper
static bool LoadObjFile(const char* filename, const char* basepath,
                       tinyobj::v3::ParseResult& result,
                       bool triangulate = true) {
    size_t obj_size;
    const char* obj_data = PosixFileRead(filename, &obj_size, nullptr);
    if (!obj_data) {
        std::cerr << "Failed to load: " << filename << std::endl;
        return false;
    }

    tinyobj::v3::ParserConfig config;
    config.triangulate = triangulate;
    config.file_callbacks.read_fn = PosixFileRead;
    config.file_callbacks.free_fn = PosixFileFree;
    config.file_callbacks.user_data = nullptr;

    if (basepath) {
        config.mtl_search_path = basepath;
    }

    tinyobj::v3::ObjParser parser(config);
    result = parser.parseFromMemory(obj_data, obj_size);

    PosixFileFree(obj_data, nullptr);

    return result.success();
}

static void PrintInfo(const tinyobj::v3::ParseResult& result, bool triangulate = true) {
    if (!result.success()) {
        std::cout << "Parse failed!\n";
        return;
    }

    const auto& attrib = result.attributes();
    const auto& shapes = result.shapes();
    const auto& materials = result.materials();

    std::cout << "# of vertices  : " << (attrib.vertices.size() / 3) << std::endl;
    std::cout << "# of normals   : " << (attrib.normals.size() / 3) << std::endl;
    std::cout << "# of texcoords : " << (attrib.texcoords.size() / 2) << std::endl;
    std::cout << "# of shapes    : " << shapes.size() << std::endl;
    std::cout << "# of materials : " << materials.size() << std::endl;

    for (size_t v = 0; v < attrib.vertices.size() / 3; v++) {
        printf("  v[%ld] = (%f, %f, %f)\n", v,
               static_cast<const double>(attrib.vertices[3 * v + 0]),
               static_cast<const double>(attrib.vertices[3 * v + 1]),
               static_cast<const double>(attrib.vertices[3 * v + 2]));
    }

    for (size_t i = 0; i < shapes.size(); i++) {
        printf("shape[%ld].name = %s\n", i, shapes[i].name.c_str());
        printf("Size of shape[%ld].indices: %ld\n", i, shapes[i].mesh.indices.size());
        printf("shape[%ld].num_faces: %ld\n", i, shapes[i].mesh.num_face_vertices.size());
    }

    for (size_t i = 0; i < materials.size(); i++) {
        printf("material[%ld].name = %s\n", i, materials[i].name.c_str());
        printf("  material.Ka = (%f, %f ,%f)\n",
               static_cast<const double>(materials[i].ambient[0]),
               static_cast<const double>(materials[i].ambient[1]),
               static_cast<const double>(materials[i].ambient[2]));
        printf("  material.Kd = (%f, %f ,%f)\n",
               static_cast<const double>(materials[i].diffuse[0]),
               static_cast<const double>(materials[i].diffuse[1]),
               static_cast<const double>(materials[i].diffuse[2]));
    }
}

// ============================================================================
// Test cases
// ============================================================================

const char* gMtlBasePath = "../models/";

void test_v3_cornell_box() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/cornell_box.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    TEST_CHECK(result.success());
}

void test_v3_pbr() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/pbr-mat-ext.obj", gMtlBasePath, result, false);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    TEST_CHECK(result.success());

    const auto& materials = result.materials();
    TEST_CHECK(1 == materials.size());
    TEST_CHECK(FloatEquals(0.2f, materials[0].roughness));
    TEST_CHECK(FloatEquals(0.3f, materials[0].metallic));
    TEST_CHECK(FloatEquals(0.4f, materials[0].sheen));
    TEST_CHECK(FloatEquals(0.5f, materials[0].clearcoat_thickness));
    TEST_CHECK(FloatEquals(0.6f, materials[0].clearcoat_roughness));
    TEST_CHECK(FloatEquals(0.7f, materials[0].anisotropy));
    TEST_CHECK(FloatEquals(0.8f, materials[0].anisotropy_rotation));
    TEST_CHECK(0 == materials[0].roughness_texname.compare("roughness.tex"));
    TEST_CHECK(0 == materials[0].metallic_texname.compare("metallic.tex"));
    TEST_CHECK(0 == materials[0].sheen_texname.compare("sheen.tex"));
    TEST_CHECK(0 == materials[0].emissive_texname.compare("emissive.tex"));
    TEST_CHECK(0 == materials[0].normal_texname.compare("normalmap.tex"));
}

void test_v3_stream_load() {
    std::string obj_data =
        "mtllib cube.mtl\n"
        "\n"
        "v 0.000000 2.000000 2.000000\n"
        "v 0.000000 0.000000 2.000000\n"
        "v 2.000000 0.000000 2.000000\n"
        "v 2.000000 2.000000 2.000000\n"
        "v 0.000000 2.000000 0.000000\n"
        "v 0.000000 0.000000 0.000000\n"
        "v 2.000000 0.000000 0.000000\n"
        "v 2.000000 2.000000 0.000000\n"
        "# 8 vertices\n"
        "\n"
        "g front cube\n"
        "usemtl white\n"
        "f 1 2 3 4\n"
        "g back cube\n"
        "f 8 7 6 5\n"
        "g right cube\n"
        "usemtl red\n"
        "f 4 3 7 8\n"
        "g top cube\n"
        "usemtl white\n"
        "f 5 1 4 8\n"
        "g left cube\n"
        "usemtl green\n"
        "f 5 6 2 1\n"
        "g bottom cube\n"
        "usemtl white\n"
        "f 2 6 7 3\n"
        "# 6 elements";

    tinyobj::v3::ParserConfig config;
    config.triangulate = true;

    tinyobj::v3::ObjParser parser(config);
    auto result = parser.parseFromString(obj_data);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(result.success());
    TEST_CHECK(8 == result.attributes().vertices.size() / 3);
    TEST_CHECK(6 == result.shapes().size());
}

void test_v3_trailing_whitespace_in_mtl_issue92() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-92.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    TEST_CHECK(1 == result.materials().size());
    TEST_CHECK(0 == result.materials()[0].diffuse_texname.compare("tmp.png"));
}

void test_v3_transmittance_filter_issue95() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-95.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& materials = result.materials();
    TEST_CHECK(1 == materials.size());
    TEST_CHECK(FloatEquals(0.1f, materials[0].transmittance[0]));
    TEST_CHECK(FloatEquals(0.2f, materials[0].transmittance[1]));
    TEST_CHECK(FloatEquals(0.3f, materials[0].transmittance[2]));
}

void test_v3_texture_opts_issue85() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/texture-options-issue-85.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    const auto& materials = result.materials();

    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(3 == materials.size());
    TEST_CHECK(0 == materials[0].name.compare("default"));
    TEST_CHECK(0 == materials[1].name.compare("bm2"));
    TEST_CHECK(0 == materials[2].name.compare("bm3"));
    TEST_CHECK(true == materials[0].ambient_texopt.clamp);
    TEST_CHECK(FloatEquals(0.1f, materials[0].diffuse_texopt.origin_offset[0]));
    TEST_CHECK(FloatEquals(0.1f, materials[0].specular_texopt.scale[0]));
    TEST_CHECK(FloatEquals(0.2f, materials[0].specular_texopt.scale[1]));
    TEST_CHECK(FloatEquals(3.0f, materials[0].bump_texopt.bump_multiplier));
}

void test_v3_vertex_col_ext_issue144() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/cube-vertexcol.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& attrib = result.attributes();
    TEST_CHECK((8 * 3) == attrib.colors.size());

    TEST_CHECK(FloatEquals(0.0f, attrib.colors[3 * 0 + 0]));
    TEST_CHECK(FloatEquals(0.0f, attrib.colors[3 * 0 + 1]));
    TEST_CHECK(FloatEquals(0.0f, attrib.colors[3 * 0 + 2]));

    TEST_CHECK(FloatEquals(0.0f, attrib.colors[3 * 1 + 0]));
    TEST_CHECK(FloatEquals(0.0f, attrib.colors[3 * 1 + 1]));
    TEST_CHECK(FloatEquals(1.0f, attrib.colors[3 * 1 + 2]));

    TEST_CHECK(FloatEquals(1.0f, attrib.colors[3 * 7 + 0]));
    TEST_CHECK(FloatEquals(1.0f, attrib.colors[3 * 7 + 1]));
    TEST_CHECK(FloatEquals(1.0f, attrib.colors[3 * 7 + 2]));
}

void test_v3_zero_face_idx_value_issue140() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-140-zero-face-idx.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(false == ret);
    TEST_CHECK(!result.success());
}

void test_v3_leading_decimal_dots_issue201() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/leading-decimal-dot-issue-201.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    const auto& materials = result.materials();
    const auto& attrib = result.attributes();

    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(1 == materials.size());
    TEST_CHECK(FloatEquals(0.8e-1f, attrib.vertices[0]));
    TEST_CHECK(FloatEquals(-.7e+2f, attrib.vertices[1]));
    TEST_CHECK(FloatEquals(.575869f, attrib.vertices[3]));
    TEST_CHECK(FloatEquals(-.666304f, attrib.vertices[4]));
    TEST_CHECK(FloatEquals(.940448f, attrib.vertices[6]));
}

void test_v3_line_primitive() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/line-prim.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(8 == shapes[0].lines.indices.size());
    TEST_CHECK(2 == shapes[0].lines.num_line_vertices.size());
}

void test_v3_points_primitive() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/points-prim.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(8 == shapes[0].points.indices.size());
}

void test_v3_multiple_group_names() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/cube.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(6 == shapes.size());
    TEST_CHECK(0 == shapes[0].name.compare("front cube"));
    TEST_CHECK(0 == shapes[1].name.compare("back cube"));
}

void test_v3_smoothing_group_issue162() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-162-smoothing-group.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(2 == shapes.size());

    TEST_CHECK(2 == shapes[0].mesh.smoothing_group_ids.size());
    TEST_CHECK(1 == shapes[0].mesh.smoothing_group_ids[0]);
    TEST_CHECK(1 == shapes[0].mesh.smoothing_group_ids[1]);

    TEST_CHECK(10 == shapes[1].mesh.smoothing_group_ids.size());
    TEST_CHECK(0 == shapes[1].mesh.smoothing_group_ids[0]);
    TEST_CHECK(3 == shapes[1].mesh.smoothing_group_ids[2]);
}

void test_v3_catmark_torus_creases0() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/catmark_torus_creases0.obj", gMtlBasePath, result, false);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(8 == shapes[0].mesh.tags.size());
}

void test_v3_tr_and_d_issue43() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/tr-and-d-issue-43.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& materials = result.materials();
    TEST_CHECK(2 == materials.size());
    TEST_CHECK(FloatEquals(0.75f, materials[0].dissolve));
    TEST_CHECK(FloatEquals(0.75f, materials[1].dissolve));
}

void test_v3_norm_texopts() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/norm-texopt.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    const auto& materials = result.materials();
    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(1 == materials.size());
    TEST_CHECK(FloatEquals(3.0f, materials[0].normal_texopt.bump_multiplier));
}

void test_v3_colorspace_issue184() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/colorspace-issue-184.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    const auto& materials = result.materials();
    TEST_CHECK(1 == shapes.size());
    TEST_CHECK(1 == materials.size());
    TEST_CHECK(0 == materials[0].diffuse_texopt.colorspace.compare("sRGB"));
    TEST_CHECK(0 == materials[0].specular_texopt.colorspace.size());
    TEST_CHECK(0 == materials[0].bump_texopt.colorspace.compare("linear"));
}

void test_v3_face_missing_issue295() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-295-trianguation-failure.obj", gMtlBasePath, result, true);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    TEST_CHECK(true == ret);
    const auto& shapes = result.shapes();
    TEST_CHECK(1 == shapes.size());

    // 14 quad faces are triangulated into 28 triangles.
    TEST_CHECK(28 == shapes[0].mesh.num_face_vertices.size());
    TEST_CHECK(28 == shapes[0].mesh.smoothing_group_ids.size());
    TEST_CHECK(28 == shapes[0].mesh.material_ids.size());
    TEST_CHECK((3 * 28) == shapes[0].mesh.indices.size());
}

void test_v3_default_kd_for_multiple_materials_issue391() {
    tinyobj::v3::ParseResult result;
    bool ret = LoadObjFile("../models/issue-391.obj", gMtlBasePath, result);

    if (!result.success()) {
        std::cout << "Errors: " << result.errors().formatErrors() << std::endl;
    }

    const tinyobj::real_t kGrey[] = {0.6, 0.6, 0.6};
    const tinyobj::real_t kRed[] = {1.0, 0.0, 0.0};

    TEST_CHECK(true == ret);
    const auto& materials = result.materials();
    TEST_CHECK(2 == materials.size());

    for (size_t i = 0; i < materials.size(); ++i) {
        const tinyobj::material_t& material = materials[i];
        if (material.name == "has_map") {
            for (int j = 0; j < 3; ++j) TEST_CHECK(material.diffuse[j] == kGrey[j]);
        } else if (material.name == "has_kd") {
            for (int j = 0; j < 3; ++j) TEST_CHECK(material.diffuse[j] == kRed[j]);
        }
    }
}

// ============================================================================
// Test list
// ============================================================================

TEST_LIST = {
    {"v3_cornell_box", test_v3_cornell_box},
    {"v3_pbr", test_v3_pbr},
    {"v3_stream_load", test_v3_stream_load},
    {"v3_trailing_whitespace_in_mtl_issue92", test_v3_trailing_whitespace_in_mtl_issue92},
    {"v3_transmittance_filter_issue95", test_v3_transmittance_filter_issue95},
    {"v3_texture_opts_issue85", test_v3_texture_opts_issue85},
    {"v3_vertex_col_ext_issue144", test_v3_vertex_col_ext_issue144},
    {"v3_zero_face_idx_value_issue140", test_v3_zero_face_idx_value_issue140},
    {"v3_leading_decimal_dots_issue201", test_v3_leading_decimal_dots_issue201},
    {"v3_line_primitive", test_v3_line_primitive},
    {"v3_points_primitive", test_v3_points_primitive},
    {"v3_multiple_group_names", test_v3_multiple_group_names},
    {"v3_smoothing_group_issue162", test_v3_smoothing_group_issue162},
    {"v3_catmark_torus_creases0", test_v3_catmark_torus_creases0},
    {"v3_tr_and_d_issue43", test_v3_tr_and_d_issue43},
    {"v3_norm_texopts", test_v3_norm_texopts},
    {"v3_colorspace_issue184", test_v3_colorspace_issue184},
    {"v3_face_missing_issue295", test_v3_face_missing_issue295},
    {"v3_default_kd_for_multiple_materials_issue391", test_v3_default_kd_for_multiple_materials_issue391},
    {NULL, NULL}
};
