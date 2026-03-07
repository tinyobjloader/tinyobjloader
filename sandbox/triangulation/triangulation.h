// triangulation.h — Standalone polygon triangulation algorithms.
//
// Self-contained header (no tinyobjloader dependency) for testing and
// evaluating triangulation strategies independently.
//
// Algorithms provided:
//   - Fan:     Simple triangle fan from vertex 0
//   - Earclip: Built-in ear clipping (handles concave polygons)
//   - MWT:     Minimum Weight Triangulation greedy with directional
//              optimization (based on drmasifhabib/MWT_Greedy_Algorithm)
//
// Usage:
//   #define TRIANGULATION_IMPLEMENTATION   // in exactly one .cc file
//   #include "triangulation.h"
//
// All functions operate on flat vertex arrays (x,y,z interleaved) and
// produce triangle index triples into an output vector.
//
// License: MIT (same as tinyobjloader)

#ifndef TRIANGULATION_H_
#define TRIANGULATION_H_

#include <cmath>
#include <cstddef>
#include <limits>
#include <vector>

namespace triangulation {

// Triangulate a polygon using a simple triangle fan from vertex 0.
// Fastest method but may produce degenerate triangles for concave polygons.
//
// @param polygon_indices  Polygon vertex indices (into `vertices`)
// @param vertices         Flat vertex array (x,y,z interleaved, stride 3)
// @param out_triangles    Output: triangle index triples (appended)
// @return                 Number of triangles produced
size_t TriangulateFan(const std::vector<size_t> &polygon_indices,
                      const std::vector<double> &vertices,
                      std::vector<size_t> *out_triangles);

// Triangulate a polygon using the ear clipping algorithm.
// Robust for concave polygons; O(n^2) worst case.
//
// @param polygon_indices  Polygon vertex indices (into `vertices`)
// @param vertices         Flat vertex array (x,y,z interleaved, stride 3)
// @param out_triangles    Output: triangle index triples (appended)
// @return                 Number of triangles produced
size_t TriangulateEarclip(const std::vector<size_t> &polygon_indices,
                          const std::vector<double> &vertices,
                          std::vector<size_t> *out_triangles);

// Triangulate a polygon using the MWT (Minimum Weight Triangulation)
// greedy algorithm with directional optimization.
//
// Based on "A Linear-Time Greedy Algorithm with Directional Optimization
// for Near-Optimal Minimum Weight Triangulation of Convex Polygons"
// (drmasifhabib/MWT_Greedy_Algorithm).
//
// The algorithm:
//  1. Finds the shortest external edge and rotates the polygon to start there
//  2. For each window of 4 consecutive vertices, compares two possible
//     diagonals and picks the shorter one to split off a triangle
//  3. Tries both winding directions and picks the result with lower total
//     diagonal weight
//
// Best suited for convex polygons; produces near-optimal triangulations.
//
// @param polygon_indices  Polygon vertex indices (into `vertices`)
// @param vertices         Flat vertex array (x,y,z interleaved, stride 3)
// @param out_triangles    Output: triangle index triples (appended)
// @param out_weight       Optional: total diagonal weight of the result
// @return                 Number of triangles produced
size_t TriangulateMWT(const std::vector<size_t> &polygon_indices,
                      const std::vector<double> &vertices,
                      std::vector<size_t> *out_triangles,
                      double *out_weight = nullptr);

// Compute squared Euclidean distance between two 3D vertices.
// Helper exposed for testing.
inline double DistanceSq3D(const std::vector<double> &vertices, size_t a,
                           size_t b) {
  double dx = vertices[a * 3 + 0] - vertices[b * 3 + 0];
  double dy = vertices[a * 3 + 1] - vertices[b * 3 + 1];
  double dz = vertices[a * 3 + 2] - vertices[b * 3 + 2];
  return dx * dx + dy * dy + dz * dz;
}

}  // namespace triangulation

// ---------------------------------------------------------------------------
// Implementation
// ---------------------------------------------------------------------------
#ifdef TRIANGULATION_IMPLEMENTATION

namespace triangulation {

size_t TriangulateFan(const std::vector<size_t> &polygon_indices,
                      const std::vector<double> & /*vertices*/,
                      std::vector<size_t> *out_triangles) {
  size_t n = polygon_indices.size();
  if (n < 3) return 0;

  size_t count = 0;
  for (size_t k = 2; k < n; k++) {
    out_triangles->push_back(polygon_indices[0]);
    out_triangles->push_back(polygon_indices[k - 1]);
    out_triangles->push_back(polygon_indices[k]);
    count++;
  }
  return count;
}

// Point-in-triangle test for 2D ear clipping.
static bool PnPoly(size_t nvert, const double *vx, const double *vy, double tx,
                    double ty) {
  bool c = false;
  for (size_t i = 0, j = nvert - 1; i < nvert; j = i++) {
    if (((vy[i] > ty) != (vy[j] > ty)) &&
        (tx < (vx[j] - vx[i]) * (ty - vy[i]) / (vy[j] - vy[i]) + vx[i])) {
      c = !c;
    }
  }
  return c;
}

size_t TriangulateEarclip(const std::vector<size_t> &polygon_indices,
                          const std::vector<double> &vertices,
                          std::vector<size_t> *out_triangles) {
  size_t n = polygon_indices.size();
  if (n < 3) return 0;

  if (n == 3) {
    out_triangles->push_back(polygon_indices[0]);
    out_triangles->push_back(polygon_indices[1]);
    out_triangles->push_back(polygon_indices[2]);
    return 1;
  }

  // For quads, use shortest-diagonal split (same as tinyobjloader)
  if (n == 4) {
    double sqr02 = DistanceSq3D(vertices, polygon_indices[0], polygon_indices[2]);
    double sqr13 = DistanceSq3D(vertices, polygon_indices[1], polygon_indices[3]);
    if (sqr02 < sqr13) {
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[3]);
    } else {
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[3]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[3]);
    }
    return 2;
  }

  // 5+ ngon: full ear clipping
  // Find the two best projection axes using Newell's method
  size_t axes[2] = {1, 2};
  for (size_t k = 0; k < n; ++k) {
    size_t vi0 = polygon_indices[(k + 0) % n];
    size_t vi1 = polygon_indices[(k + 1) % n];
    size_t vi2 = polygon_indices[(k + 2) % n];

    double e0x = vertices[vi1 * 3 + 0] - vertices[vi0 * 3 + 0];
    double e0y = vertices[vi1 * 3 + 1] - vertices[vi0 * 3 + 1];
    double e0z = vertices[vi1 * 3 + 2] - vertices[vi0 * 3 + 2];
    double e1x = vertices[vi2 * 3 + 0] - vertices[vi1 * 3 + 0];
    double e1y = vertices[vi2 * 3 + 1] - vertices[vi1 * 3 + 1];
    double e1z = vertices[vi2 * 3 + 2] - vertices[vi1 * 3 + 2];

    double cx = std::fabs(e0y * e1z - e0z * e1y);
    double cy = std::fabs(e0z * e1x - e0x * e1z);
    double cz = std::fabs(e0x * e1y - e0y * e1x);
    double epsilon = std::numeric_limits<double>::epsilon();

    if (cx > epsilon || cy > epsilon || cz > epsilon) {
      if (cx > cy && cx > cz) {
        // axes stay {1, 2}
      } else {
        axes[0] = 0;
        if (cz > cx && cz > cy) {
          axes[1] = 1;
        }
      }
      break;
    }
  }

  // Working copy of polygon indices
  std::vector<size_t> remaining(polygon_indices);
  size_t guess_vert = 0;
  size_t count = 0;

  size_t remaining_iterations = remaining.size();
  size_t previous_remaining = remaining.size();

  while (remaining.size() > 3 && remaining_iterations > 0) {
    size_t npolys = remaining.size();
    if (guess_vert >= npolys) {
      guess_vert -= npolys;
    }

    if (previous_remaining != npolys) {
      previous_remaining = npolys;
      remaining_iterations = npolys;
    } else {
      remaining_iterations--;
    }

    // Get candidate ear vertices
    size_t ind[3];
    double vx[3], vy[3];
    for (size_t k = 0; k < 3; k++) {
      ind[k] = remaining[(guess_vert + k) % npolys];
      vx[k] = vertices[ind[k] * 3 + axes[0]];
      vy[k] = vertices[ind[k] * 3 + axes[1]];
    }

    // Check convexity
    double e0x = vx[1] - vx[0];
    double e0y = vy[1] - vy[0];
    double e1x = vx[2] - vx[1];
    double e1y = vy[2] - vy[1];
    double cross = e0x * e1y - e0y * e1x;

    double signed_area_ref = (vx[0] * vy[1] - vy[0] * vx[1]) * 0.5;
    if (cross * signed_area_ref < 0.0) {
      guess_vert += 1;
      continue;
    }

    // Check no other vertex inside the candidate ear
    bool overlap = false;
    for (size_t other = 3; other < npolys; ++other) {
      size_t idx = (guess_vert + other) % npolys;
      if (idx >= remaining.size()) continue;

      double tx = vertices[remaining[idx] * 3 + axes[0]];
      double ty = vertices[remaining[idx] * 3 + axes[1]];
      if (PnPoly(3, vx, vy, tx, ty)) {
        overlap = true;
        break;
      }
    }

    if (overlap) {
      guess_vert += 1;
      continue;
    }

    // This triangle is an ear
    out_triangles->push_back(ind[0]);
    out_triangles->push_back(ind[1]);
    out_triangles->push_back(ind[2]);
    count++;

    // Remove middle vertex
    size_t removed = (guess_vert + 1) % npolys;
    remaining.erase(remaining.begin() + static_cast<std::ptrdiff_t>(removed));
  }

  // Emit final triangle
  if (remaining.size() == 3) {
    out_triangles->push_back(remaining[0]);
    out_triangles->push_back(remaining[1]);
    out_triangles->push_back(remaining[2]);
    count++;
  }

  return count;
}

// Internal: run one pass of the MWT greedy algorithm on a given vertex ordering.
static double MWTGreedyPass(const std::vector<size_t> &order,
                            const std::vector<double> &vertices,
                            std::vector<size_t> *out_triangles) {
  size_t n = order.size();
  if (n < 3) return 0.0;

  // Find shortest external edge
  double min_edge_sq = std::numeric_limits<double>::max();
  size_t start_idx = 0;
  for (size_t k = 0; k < n; k++) {
    double sq = DistanceSq3D(vertices, order[k], order[(k + 1) % n]);
    if (sq < min_edge_sq) {
      min_edge_sq = sq;
      start_idx = k;
    }
  }

  // Rotate order to start from shortest edge
  std::vector<size_t> work(n);
  for (size_t k = 0; k < n; k++) {
    work[k] = order[(k + start_idx) % n];
  }

  // Greedy triangulation
  double total_weight = 0.0;
  out_triangles->reserve(out_triangles->size() + (n - 2) * 3);

  while (n > 3) {
    bool cut_made = false;
    for (size_t k = 0; k < n; k++) {
      size_t k0 = k;
      size_t k1 = (k + 1) % n;
      size_t k2 = (k + 2) % n;
      size_t k3 = (k + 3) % n;

      // Diagonal v0-v2
      double d1_sq = DistanceSq3D(vertices, work[k0], work[k2]);
      // Diagonal v1-v3
      double d2_sq = DistanceSq3D(vertices, work[k1], work[k3]);

      if (d1_sq < d2_sq) {
        // Use diagonal v0-v2, emit triangle (v0, v1, v2), remove v1
        out_triangles->push_back(work[k0]);
        out_triangles->push_back(work[k1]);
        out_triangles->push_back(work[k2]);
        total_weight += std::sqrt(d1_sq);
        work.erase(work.begin() + static_cast<std::ptrdiff_t>(k1));
      } else {
        // Use diagonal v1-v3, emit triangle (v1, v2, v3), remove v2
        out_triangles->push_back(work[k1]);
        out_triangles->push_back(work[k2]);
        out_triangles->push_back(work[k3]);
        total_weight += std::sqrt(d2_sq);
        work.erase(work.begin() + static_cast<std::ptrdiff_t>(k2));
      }
      n--;
      cut_made = true;
      break;  // Restart scan after each removal
    }
    if (!cut_made) break;
  }

  // Emit final triangle
  if (n == 3) {
    out_triangles->push_back(work[0]);
    out_triangles->push_back(work[1]);
    out_triangles->push_back(work[2]);
  }

  return total_weight;
}

size_t TriangulateMWT(const std::vector<size_t> &polygon_indices,
                      const std::vector<double> &vertices,
                      std::vector<size_t> *out_triangles,
                      double *out_weight) {
  size_t n = polygon_indices.size();
  if (n < 3) return 0;

  if (n == 3) {
    out_triangles->push_back(polygon_indices[0]);
    out_triangles->push_back(polygon_indices[1]);
    out_triangles->push_back(polygon_indices[2]);
    if (out_weight) *out_weight = 0.0;
    return 1;
  }

  // For quads, use shortest-diagonal split
  if (n == 4) {
    double sqr02 = DistanceSq3D(vertices, polygon_indices[0], polygon_indices[2]);
    double sqr13 = DistanceSq3D(vertices, polygon_indices[1], polygon_indices[3]);
    if (sqr02 < sqr13) {
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[3]);
      if (out_weight) *out_weight = std::sqrt(sqr02);
    } else {
      out_triangles->push_back(polygon_indices[0]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[3]);
      out_triangles->push_back(polygon_indices[1]);
      out_triangles->push_back(polygon_indices[2]);
      out_triangles->push_back(polygon_indices[3]);
      if (out_weight) *out_weight = std::sqrt(sqr13);
    }
    return 2;
  }

  // 5+ ngon: run greedy in both directions, pick best
  // Forward order
  std::vector<size_t> order_fwd(polygon_indices);

  // Reversed order
  std::vector<size_t> order_rev(n);
  for (size_t k = 0; k < n; k++) {
    order_rev[k] = polygon_indices[n - 1 - k];
  }

  std::vector<size_t> tris_fwd, tris_rev;
  double w_fwd = MWTGreedyPass(order_fwd, vertices, &tris_fwd);
  double w_rev = MWTGreedyPass(order_rev, vertices, &tris_rev);

  if (w_fwd <= w_rev) {
    for (size_t k = 0; k < tris_fwd.size(); k++) {
      out_triangles->push_back(tris_fwd[k]);
    }
    if (out_weight) *out_weight = w_fwd;
    return tris_fwd.size() / 3;
  } else {
    for (size_t k = 0; k < tris_rev.size(); k++) {
      out_triangles->push_back(tris_rev[k]);
    }
    if (out_weight) *out_weight = w_rev;
    return tris_rev.size() / 3;
  }
}

}  // namespace triangulation

#endif  // TRIANGULATION_IMPLEMENTATION
#endif  // TRIANGULATION_H_
