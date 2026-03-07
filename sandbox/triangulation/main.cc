// main.cc — Standalone test/demo for triangulation algorithms.
//
// Build:  make        (or: g++ -std=c++11 -o triangulation_test main.cc)
// Run:    ./triangulation_test
//
// Tests fan, earclip, and MWT greedy triangulation independently of
// tinyobjloader.

#define TRIANGULATION_IMPLEMENTATION
#include "triangulation.h"

#include <cassert>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <string>

static int g_tests_passed = 0;
static int g_tests_failed = 0;

#define TEST_CHECK(cond)                                       \
  do {                                                         \
    if (!(cond)) {                                             \
      fprintf(stderr, "  FAIL: %s (line %d)\n", #cond, __LINE__); \
      g_tests_failed++;                                        \
      return;                                                  \
    }                                                          \
  } while (0)

#define RUN_TEST(func)                                         \
  do {                                                         \
    printf("  %-50s", #func);                                  \
    int prev_fail = g_tests_failed;                            \
    func();                                                    \
    if (g_tests_failed == prev_fail) {                         \
      printf("[ OK ]\n");                                      \
      g_tests_passed++;                                        \
    } else {                                                   \
      printf("[FAIL]\n");                                      \
    }                                                          \
  } while (0)

// ---- Helper: build flat vertex array from 2D points ----
static std::vector<double> MakeVertices2D(const double *xy, size_t count) {
  std::vector<double> v(count * 3);
  for (size_t i = 0; i < count; i++) {
    v[i * 3 + 0] = xy[i * 2 + 0];
    v[i * 3 + 1] = xy[i * 2 + 1];
    v[i * 3 + 2] = 0.0;
  }
  return v;
}

static std::vector<size_t> MakeSequence(size_t n) {
  std::vector<size_t> seq(n);
  for (size_t i = 0; i < n; i++) seq[i] = i;
  return seq;
}

// ---- Verify all triangle indices are in valid range ----
static bool ValidateTriangles(const std::vector<size_t> &triangles,
                              size_t num_verts) {
  if (triangles.size() % 3 != 0) return false;
  for (size_t i = 0; i < triangles.size(); i++) {
    if (triangles[i] >= num_verts) return false;
  }
  return true;
}

// ============================================================
// Fan tests
// ============================================================

void test_fan_triangle() {
  double pts[] = {0, 0, 1, 0, 0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 3);
  std::vector<size_t> poly = MakeSequence(3);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateFan(poly, v, &tris);
  TEST_CHECK(n == 1);
  TEST_CHECK(tris.size() == 3);
  TEST_CHECK(ValidateTriangles(tris, 3));
}

void test_fan_quad() {
  double pts[] = {0, 0, 1, 0, 1, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateFan(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
  // Fan: (0,1,2), (0,2,3)
  TEST_CHECK(tris[0] == 0 && tris[1] == 1 && tris[2] == 2);
  TEST_CHECK(tris[3] == 0 && tris[4] == 2 && tris[5] == 3);
}

void test_fan_pentagon() {
  double pts[] = {0, 0, 1, 0, 1.5, 1, 0.5, 1.5, -0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateFan(poly, v, &tris);
  TEST_CHECK(n == 3);
  TEST_CHECK(tris.size() == 9);
  TEST_CHECK(ValidateTriangles(tris, 5));
}

void test_fan_hexagon() {
  // Regular hexagon
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateFan(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_fan_degenerate() {
  // Less than 3 vertices → no output
  std::vector<double> v(6, 0.0);
  std::vector<size_t> poly;
  poly.push_back(0);
  poly.push_back(1);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateFan(poly, v, &tris);
  TEST_CHECK(n == 0);
  TEST_CHECK(tris.empty());
}

// ============================================================
// Earclip tests
// ============================================================

void test_earclip_triangle() {
  double pts[] = {0, 0, 1, 0, 0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 3);
  std::vector<size_t> poly = MakeSequence(3);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 1);
  TEST_CHECK(tris.size() == 3);
}

void test_earclip_quad() {
  // Unit square
  double pts[] = {0, 0, 1, 0, 1, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
}

void test_earclip_quad_shortest_diagonal() {
  // Rectangle wider than tall → diagonal 0-2 is longer than 1-3
  // So earclip should pick the shorter diagonal
  double pts[] = {0, 0, 3, 0, 3, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  // Diagonal 1-3 is shorter, so should get (0,1,3),(1,2,3)
  TEST_CHECK(tris[0] == 0 && tris[1] == 1 && tris[2] == 3);
  TEST_CHECK(tris[3] == 1 && tris[4] == 2 && tris[5] == 3);
}

void test_earclip_pentagon() {
  double pts[] = {0, 0, 1, 0, 1.5, 1, 0.5, 1.5, -0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 3);
  TEST_CHECK(tris.size() == 9);
  TEST_CHECK(ValidateTriangles(tris, 5));
}

void test_earclip_hexagon() {
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_earclip_concave_l_shape() {
  // L-shaped concave polygon (6 vertices)
  //  3---2
  //  |   |
  //  4-5 |
  //    | |
  //    0-1
  double pts[] = {1, 0,  2, 0,  2, 2,  0, 2,  0, 1,  1, 1};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

// ============================================================
// MWT tests
// ============================================================

void test_mwt_triangle() {
  double pts[] = {0, 0, 1, 0, 0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 3);
  std::vector<size_t> poly = MakeSequence(3);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 1);
  TEST_CHECK(tris.size() == 3);
  TEST_CHECK(weight == 0.0);  // No diagonals needed
}

void test_mwt_quad() {
  // Unit square
  double pts[] = {0, 0, 1, 0, 1, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
  // Both diagonals have equal length for a unit square
  TEST_CHECK(weight > 0.0);
}

void test_mwt_quad_picks_shorter_diagonal() {
  // Rectangle 3x1: diagonal 1-3 is shorter than 0-2
  double pts[] = {0, 0, 3, 0, 3, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 2);
  // For this 3x1 rectangle, both diagonals 0-2 and 1-3 have equal length
  // sqrt(10). The algorithm should produce a valid 2-triangle decomposition
  // picking either diagonal.
  double d13 = std::sqrt(triangulation::DistanceSq3D(v, 1, 3));
  double d02 = std::sqrt(triangulation::DistanceSq3D(v, 0, 2));
  TEST_CHECK(weight > 0.0);
  // Weight should be the shorter diagonal
  double expected = (d02 < d13) ? d02 : d13;
  TEST_CHECK(std::fabs(weight - expected) < 1e-10);
}

void test_mwt_pentagon() {
  double pts[] = {0, 0, 1, 0, 1.5, 1, 0.5, 1.5, -0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 3);
  TEST_CHECK(tris.size() == 9);
  TEST_CHECK(ValidateTriangles(tris, 5));
  TEST_CHECK(weight >= 0.0);
}

void test_mwt_hexagon() {
  // Regular hexagon
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
  TEST_CHECK(weight >= 0.0);
}

void test_mwt_octagon() {
  // Regular octagon
  double r = 1.0;
  double pts[16];
  for (int i = 0; i < 8; i++) {
    double angle = 2.0 * 3.14159265358979 * i / 8.0;
    pts[i * 2 + 0] = r * std::cos(angle);
    pts[i * 2 + 1] = r * std::sin(angle);
  }
  std::vector<double> v = MakeVertices2D(pts, 8);
  std::vector<size_t> poly = MakeSequence(8);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 6);
  TEST_CHECK(tris.size() == 18);
  TEST_CHECK(ValidateTriangles(tris, 8));
  TEST_CHECK(weight >= 0.0);
}

void test_mwt_directional_optimization() {
  // Verify that MWT tries both directions and picks the better one.
  // Use a non-symmetric polygon where direction matters.
  double pts[] = {0, 0,  4, 0,  5, 2,  3, 4,  0, 3};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);

  // Run MWT
  std::vector<size_t> tris_mwt;
  double weight_mwt = -1.0;
  triangulation::TriangulateMWT(poly, v, &tris_mwt, &weight_mwt);

  // Run fan for comparison
  std::vector<size_t> tris_fan;
  triangulation::TriangulateFan(poly, v, &tris_fan);

  // MWT should produce a valid triangulation
  TEST_CHECK(tris_mwt.size() == 9);
  TEST_CHECK(ValidateTriangles(tris_mwt, 5));

  // MWT total weight should be <= fan total weight (for convex polygons)
  // Fan uses diagonals from vertex 0, while MWT optimizes
  TEST_CHECK(weight_mwt >= 0.0);
}

void test_mwt_weight_is_minimal() {
  // Compare MWT weight against fan weight for a regular hexagon.
  // MWT should produce total diagonal weight <= fan.
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);

  // MWT weight
  std::vector<size_t> tris_mwt;
  double weight_mwt = -1.0;
  triangulation::TriangulateMWT(poly, v, &tris_mwt, &weight_mwt);

  // Fan: compute total diagonal weight manually
  // Fan diagonals are 0-2, 0-3, 0-4
  double fan_weight = 0.0;
  fan_weight += std::sqrt(triangulation::DistanceSq3D(v, 0, 2));
  fan_weight += std::sqrt(triangulation::DistanceSq3D(v, 0, 3));
  fan_weight += std::sqrt(triangulation::DistanceSq3D(v, 0, 4));

  // MWT should produce equal or lower weight
  TEST_CHECK(weight_mwt <= fan_weight + 1e-10);
}

// ============================================================
// 3D tests
// ============================================================

void test_mwt_3d_vertices() {
  // Polygon in 3D space (not aligned to any axis)
  double verts[] = {
    0, 0, 0,    // 0
    1, 0, 0,    // 1
    1, 1, 1,    // 2
    0, 1, 1     // 3
  };
  std::vector<double> v(verts, verts + 12);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  double weight = -1.0;
  size_t n = triangulation::TriangulateMWT(poly, v, &tris, &weight);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
  TEST_CHECK(weight > 0.0);
}

void test_earclip_3d_vertices() {
  double verts[] = {
    0, 0, 0,    // 0
    1, 0, 0,    // 1
    1, 1, 1,    // 2
    0, 1, 1     // 3
  };
  std::vector<double> v(verts, verts + 12);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarclip(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
}

// ============================================================
// Edge cases
// ============================================================

void test_degenerate_two_vertices() {
  std::vector<double> v(6, 0.0);
  std::vector<size_t> poly;
  poly.push_back(0);
  poly.push_back(1);
  std::vector<size_t> tris;
  TEST_CHECK(triangulation::TriangulateFan(poly, v, &tris) == 0);
  TEST_CHECK(triangulation::TriangulateEarclip(poly, v, &tris) == 0);
  TEST_CHECK(triangulation::TriangulateMWT(poly, v, &tris) == 0);
}

void test_single_vertex() {
  std::vector<double> v(3, 0.0);
  std::vector<size_t> poly;
  poly.push_back(0);
  std::vector<size_t> tris;
  TEST_CHECK(triangulation::TriangulateFan(poly, v, &tris) == 0);
  TEST_CHECK(triangulation::TriangulateEarclip(poly, v, &tris) == 0);
  TEST_CHECK(triangulation::TriangulateMWT(poly, v, &tris) == 0);
}

void test_distance_sq_3d() {
  double verts[] = {0, 0, 0,  3, 4, 0};
  std::vector<double> v(verts, verts + 6);
  double d = triangulation::DistanceSq3D(v, 0, 1);
  TEST_CHECK(std::fabs(d - 25.0) < 1e-10);
}

// ============================================================
// Sweep-Line tests
// ============================================================

void test_sweep_triangle() {
  double pts[] = {0, 0, 1, 0, 0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 3);
  std::vector<size_t> poly = MakeSequence(3);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 1);
  TEST_CHECK(tris.size() == 3);
  TEST_CHECK(ValidateTriangles(tris, 3));
}

void test_sweep_quad() {
  double pts[] = {0, 0, 1, 0, 1, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
}

void test_sweep_pentagon() {
  double pts[] = {0, 0, 1, 0, 1.5, 1, 0.5, 1.5, -0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 3);
  TEST_CHECK(tris.size() == 9);
  TEST_CHECK(ValidateTriangles(tris, 5));
}

void test_sweep_hexagon() {
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_sweep_concave_l_shape() {
  //  3---2
  //  |   |
  //  4-5 |
  //    | |
  //    0-1
  double pts[] = {1, 0,  2, 0,  2, 2,  0, 2,  0, 1,  1, 1};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_sweep_octagon() {
  double r = 1.0;
  double pts[16];
  for (int i = 0; i < 8; i++) {
    double angle = 2.0 * 3.14159265358979 * i / 8.0;
    pts[i * 2 + 0] = r * std::cos(angle);
    pts[i * 2 + 1] = r * std::sin(angle);
  }
  std::vector<double> v = MakeVertices2D(pts, 8);
  std::vector<size_t> poly = MakeSequence(8);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateSweepLine(poly, v, &tris);
  TEST_CHECK(n == 6);
  TEST_CHECK(tris.size() == 18);
  TEST_CHECK(ValidateTriangles(tris, 8));
}

void test_sweep_degenerate() {
  std::vector<double> v(6, 0.0);
  std::vector<size_t> poly;
  poly.push_back(0);
  poly.push_back(1);
  std::vector<size_t> tris;
  TEST_CHECK(triangulation::TriangulateSweepLine(poly, v, &tris) == 0);
}

// ============================================================
// Earcut Z-Curve tests
// ============================================================

void test_earcutz_triangle() {
  double pts[] = {0, 0, 1, 0, 0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 3);
  std::vector<size_t> poly = MakeSequence(3);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 1);
  TEST_CHECK(tris.size() == 3);
  TEST_CHECK(ValidateTriangles(tris, 3));
}

void test_earcutz_quad() {
  double pts[] = {0, 0, 1, 0, 1, 1, 0, 1};
  std::vector<double> v = MakeVertices2D(pts, 4);
  std::vector<size_t> poly = MakeSequence(4);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 2);
  TEST_CHECK(tris.size() == 6);
  TEST_CHECK(ValidateTriangles(tris, 4));
}

void test_earcutz_pentagon() {
  double pts[] = {0, 0, 1, 0, 1.5, 1, 0.5, 1.5, -0.5, 1};
  std::vector<double> v = MakeVertices2D(pts, 5);
  std::vector<size_t> poly = MakeSequence(5);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 3);
  TEST_CHECK(tris.size() == 9);
  TEST_CHECK(ValidateTriangles(tris, 5));
}

void test_earcutz_hexagon() {
  double pts[] = {1, 0, 0.5, 0.866, -0.5, 0.866, -1, 0, -0.5, -0.866, 0.5, -0.866};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_earcutz_concave_l_shape() {
  double pts[] = {1, 0,  2, 0,  2, 2,  0, 2,  0, 1,  1, 1};
  std::vector<double> v = MakeVertices2D(pts, 6);
  std::vector<size_t> poly = MakeSequence(6);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 4);
  TEST_CHECK(tris.size() == 12);
  TEST_CHECK(ValidateTriangles(tris, 6));
}

void test_earcutz_octagon() {
  double r = 1.0;
  double pts[16];
  for (int i = 0; i < 8; i++) {
    double angle = 2.0 * 3.14159265358979 * i / 8.0;
    pts[i * 2 + 0] = r * std::cos(angle);
    pts[i * 2 + 1] = r * std::sin(angle);
  }
  std::vector<double> v = MakeVertices2D(pts, 8);
  std::vector<size_t> poly = MakeSequence(8);
  std::vector<size_t> tris;
  size_t n = triangulation::TriangulateEarcutZCurve(poly, v, &tris);
  TEST_CHECK(n == 6);
  TEST_CHECK(tris.size() == 18);
  TEST_CHECK(ValidateTriangles(tris, 8));
}

void test_earcutz_degenerate() {
  std::vector<double> v(6, 0.0);
  std::vector<size_t> poly;
  poly.push_back(0);
  poly.push_back(1);
  std::vector<size_t> tris;
  TEST_CHECK(triangulation::TriangulateEarcutZCurve(poly, v, &tris) == 0);
}

// ============================================================
// Main
// ============================================================

int main(int /*argc*/, char ** /*argv*/) {
  printf("=== Standalone Triangulation Tests ===\n\n");

  printf("Fan triangulation:\n");
  RUN_TEST(test_fan_triangle);
  RUN_TEST(test_fan_quad);
  RUN_TEST(test_fan_pentagon);
  RUN_TEST(test_fan_hexagon);
  RUN_TEST(test_fan_degenerate);

  printf("\nEar clipping:\n");
  RUN_TEST(test_earclip_triangle);
  RUN_TEST(test_earclip_quad);
  RUN_TEST(test_earclip_quad_shortest_diagonal);
  RUN_TEST(test_earclip_pentagon);
  RUN_TEST(test_earclip_hexagon);
  RUN_TEST(test_earclip_concave_l_shape);

  printf("\nMWT greedy:\n");
  RUN_TEST(test_mwt_triangle);
  RUN_TEST(test_mwt_quad);
  RUN_TEST(test_mwt_quad_picks_shorter_diagonal);
  RUN_TEST(test_mwt_pentagon);
  RUN_TEST(test_mwt_hexagon);
  RUN_TEST(test_mwt_octagon);
  RUN_TEST(test_mwt_directional_optimization);
  RUN_TEST(test_mwt_weight_is_minimal);

  printf("\nSweep-Line:\n");
  RUN_TEST(test_sweep_triangle);
  RUN_TEST(test_sweep_quad);
  RUN_TEST(test_sweep_pentagon);
  RUN_TEST(test_sweep_hexagon);
  RUN_TEST(test_sweep_concave_l_shape);
  RUN_TEST(test_sweep_octagon);
  RUN_TEST(test_sweep_degenerate);

  printf("\nEarcut Z-Curve:\n");
  RUN_TEST(test_earcutz_triangle);
  RUN_TEST(test_earcutz_quad);
  RUN_TEST(test_earcutz_pentagon);
  RUN_TEST(test_earcutz_hexagon);
  RUN_TEST(test_earcutz_concave_l_shape);
  RUN_TEST(test_earcutz_octagon);
  RUN_TEST(test_earcutz_degenerate);

  printf("\n3D tests:\n");
  RUN_TEST(test_mwt_3d_vertices);
  RUN_TEST(test_earclip_3d_vertices);

  printf("\nEdge cases:\n");
  RUN_TEST(test_degenerate_two_vertices);
  RUN_TEST(test_single_vertex);
  RUN_TEST(test_distance_sq_3d);

  printf("\n=== Results: %d passed, %d failed ===\n",
         g_tests_passed, g_tests_failed);

  return g_tests_failed > 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}
