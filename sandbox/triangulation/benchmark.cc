// benchmark.cc — Benchmark program for triangulation algorithms.
//
// Build:  make benchmark
// Run:    ./benchmark
//
// Generates regular n-gons, random convex, and random concave (star)
// polygons of various sizes, then measures each algorithm's throughput.

#define TRIANGULATION_IMPLEMENTATION
#include "triangulation.h"

#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

// ---------------------------------------------------------------------------
// Polygon generators
// ---------------------------------------------------------------------------

static const double kPi = 3.14159265358979323846;

// Regular n-gon with given number of vertices, radius 1.
static void MakeRegularNgon(size_t n, std::vector<double> *vertices,
                            std::vector<size_t> *indices) {
  vertices->resize(n * 3);
  indices->resize(n);
  for (size_t i = 0; i < n; i++) {
    double angle = 2.0 * kPi * static_cast<double>(i) / static_cast<double>(n);
    (*vertices)[i * 3 + 0] = std::cos(angle);
    (*vertices)[i * 3 + 1] = std::sin(angle);
    (*vertices)[i * 3 + 2] = 0.0;
    (*indices)[i] = i;
  }
}

// Star-shaped concave polygon with n points (2*n vertices total).
// Outer radius 1.0, inner radius 0.4.
static void MakeStarPolygon(size_t n_points, std::vector<double> *vertices,
                            std::vector<size_t> *indices) {
  size_t n = n_points * 2;
  vertices->resize(n * 3);
  indices->resize(n);
  double outer_r = 1.0;
  double inner_r = 0.4;
  for (size_t i = 0; i < n; i++) {
    double angle =
        2.0 * kPi * static_cast<double>(i) / static_cast<double>(n);
    double r = (i % 2 == 0) ? outer_r : inner_r;
    (*vertices)[i * 3 + 0] = r * std::cos(angle);
    (*vertices)[i * 3 + 1] = r * std::sin(angle);
    (*vertices)[i * 3 + 2] = 0.0;
    (*indices)[i] = i;
  }
}

// Simple pseudo-random number generator (deterministic, no stdlib dependency).
struct SimpleRNG {
  uint64_t state;
  explicit SimpleRNG(uint64_t seed = 12345) : state(seed) {}
  uint64_t next() {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return state;
  }
  double uniform() {
    return static_cast<double>(next() % 1000000) / 1000000.0;
  }
};

// Random convex polygon with n vertices (random angles, sorted, on unit circle).
static void MakeRandomConvex(size_t n, std::vector<double> *vertices,
                             std::vector<size_t> *indices, uint64_t seed) {
  SimpleRNG rng(seed);
  std::vector<double> angles(n);
  for (size_t i = 0; i < n; i++) {
    angles[i] = rng.uniform() * 2.0 * kPi;
  }
  std::sort(angles.begin(), angles.end());

  vertices->resize(n * 3);
  indices->resize(n);
  for (size_t i = 0; i < n; i++) {
    double r = 0.8 + 0.2 * rng.uniform();
    (*vertices)[i * 3 + 0] = r * std::cos(angles[i]);
    (*vertices)[i * 3 + 1] = r * std::sin(angles[i]);
    (*vertices)[i * 3 + 2] = 0.0;
    (*indices)[i] = i;
  }
}

// ---------------------------------------------------------------------------
// Benchmark harness
// ---------------------------------------------------------------------------

typedef size_t (*TriFunc)(const std::vector<size_t> &,
                          const std::vector<double> &,
                          std::vector<size_t> *);

static size_t TriangulateMWTWrapper(const std::vector<size_t> &poly,
                                    const std::vector<double> &verts,
                                    std::vector<size_t> *out) {
  return triangulation::TriangulateMWT(poly, verts, out, nullptr);
}

struct Algorithm {
  const char *name;
  TriFunc func;
};

static Algorithm g_algorithms[] = {
    {"Fan", triangulation::TriangulateFan},
    {"Earclip", triangulation::TriangulateEarclip},
    {"MWT", TriangulateMWTWrapper},
    {"SweepLine", triangulation::TriangulateSweepLine},
    {"EarcutZ", triangulation::TriangulateEarcutZCurve},
};
static const size_t g_num_algorithms =
    sizeof(g_algorithms) / sizeof(g_algorithms[0]);

struct BenchResult {
  double us_per_call;  // microseconds per triangulation call
  size_t num_triangles;
  bool valid;
};

static BenchResult RunBenchmark(TriFunc func,
                                const std::vector<size_t> &polygon,
                                const std::vector<double> &vertices,
                                size_t iterations) {
  BenchResult result;
  result.us_per_call = 0;
  result.num_triangles = 0;
  result.valid = true;

  // Warm-up
  {
    std::vector<size_t> tris;
    result.num_triangles = func(polygon, vertices, &tris);
    if (tris.size() % 3 != 0 ||
        result.num_triangles != polygon.size() - 2) {
      result.valid = false;
    }
    // Validate all indices are in range
    for (size_t i = 0; i < tris.size(); i++) {
      if (tris[i] >= vertices.size() / 3) {
        result.valid = false;
        break;
      }
    }
  }

  // Timed run
  auto start = std::chrono::high_resolution_clock::now();
  for (size_t iter = 0; iter < iterations; iter++) {
    std::vector<size_t> tris;
    func(polygon, vertices, &tris);
  }
  auto end = std::chrono::high_resolution_clock::now();

  double elapsed_us =
      std::chrono::duration_cast<std::chrono::microseconds>(end - start)
          .count();
  result.us_per_call = elapsed_us / static_cast<double>(iterations);
  return result;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

static void PrintSeparator(size_t width) {
  for (size_t i = 0; i < width; i++) putchar('-');
  putchar('\n');
}

int main(int argc, char **argv) {
  // Parse optional --quick flag for shorter runs
  bool quick = false;
  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--quick") == 0) quick = true;
  }

  printf("=== Triangulation Benchmark ===\n\n");

  // Polygon sizes to test
  size_t convex_sizes[] = {4, 8, 16, 32, 64, 128, 256, 512, 1024};
  size_t num_convex_sizes = sizeof(convex_sizes) / sizeof(convex_sizes[0]);

  size_t star_points[] = {4, 8, 16, 32, 64, 128, 256};
  size_t num_star_sizes = sizeof(star_points) / sizeof(star_points[0]);

  // ---- Regular convex n-gons ----
  printf("Regular convex n-gons (time in microseconds per call):\n\n");
  printf("%-10s", "N");
  for (size_t a = 0; a < g_num_algorithms; a++) {
    printf("  %12s", g_algorithms[a].name);
  }
  printf("\n");
  PrintSeparator(10 + g_num_algorithms * 14);

  for (size_t si = 0; si < num_convex_sizes; si++) {
    size_t nv = convex_sizes[si];
    std::vector<double> verts;
    std::vector<size_t> poly;
    MakeRegularNgon(nv, &verts, &poly);

    size_t iters = quick ? 100 : std::max(static_cast<size_t>(10),
                                          static_cast<size_t>(100000 / nv));

    printf("%-10zu", nv);
    for (size_t a = 0; a < g_num_algorithms; a++) {
      BenchResult r = RunBenchmark(g_algorithms[a].func, poly, verts, iters);
      if (r.valid) {
        printf("  %10.2f  ", r.us_per_call);
      } else {
        printf("  %10s  ", "INVALID");
      }
    }
    printf("\n");
  }

  // ---- Random convex polygons ----
  printf("\nRandom convex polygons (time in microseconds per call):\n\n");
  printf("%-10s", "N");
  for (size_t a = 0; a < g_num_algorithms; a++) {
    printf("  %12s", g_algorithms[a].name);
  }
  printf("\n");
  PrintSeparator(10 + g_num_algorithms * 14);

  for (size_t si = 0; si < num_convex_sizes; si++) {
    size_t nv = convex_sizes[si];
    std::vector<double> verts;
    std::vector<size_t> poly;
    MakeRandomConvex(nv, &verts, &poly, 42 + nv);

    size_t iters = quick ? 100 : std::max(static_cast<size_t>(10),
                                          static_cast<size_t>(100000 / nv));

    printf("%-10zu", nv);
    for (size_t a = 0; a < g_num_algorithms; a++) {
      BenchResult r = RunBenchmark(g_algorithms[a].func, poly, verts, iters);
      if (r.valid) {
        printf("  %10.2f  ", r.us_per_call);
      } else {
        printf("  %10s  ", "INVALID");
      }
    }
    printf("\n");
  }

  // ---- Star-shaped concave polygons ----
  printf("\nStar-shaped concave polygons (time in microseconds per call):\n");
  printf("(N = total vertices = 2 * star_points)\n\n");
  printf("%-10s", "N");
  for (size_t a = 0; a < g_num_algorithms; a++) {
    printf("  %12s", g_algorithms[a].name);
  }
  printf("\n");
  PrintSeparator(10 + g_num_algorithms * 14);

  for (size_t si = 0; si < num_star_sizes; si++) {
    size_t np = star_points[si];
    size_t nv = np * 2;
    std::vector<double> verts;
    std::vector<size_t> poly;
    MakeStarPolygon(np, &verts, &poly);

    size_t iters = quick ? 100 : std::max(static_cast<size_t>(10),
                                          static_cast<size_t>(100000 / nv));

    printf("%-10zu", nv);
    for (size_t a = 0; a < g_num_algorithms; a++) {
      BenchResult r = RunBenchmark(g_algorithms[a].func, poly, verts, iters);
      if (r.valid) {
        printf("  %10.2f  ", r.us_per_call);
      } else {
        printf("  %10s  ", "INVALID");
      }
    }
    printf("\n");
  }

  printf("\nDone.\n");
  return 0;
}
