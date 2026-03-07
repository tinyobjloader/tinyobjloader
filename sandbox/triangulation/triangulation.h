// triangulation.h — Standalone polygon triangulation algorithms.
//
// Self-contained header (no tinyobjloader dependency) for testing and
// evaluating triangulation strategies independently.
//
// Algorithms provided:
//   - Fan:       Simple triangle fan from vertex 0
//   - Earclip:   Built-in ear clipping (handles concave polygons)
//   - MWT:       Minimum Weight Triangulation greedy with directional
//                optimization (based on drmasifhabib/MWT_Greedy_Algorithm)
//   - SweepLine: Monotone decomposition via sweep-line, then stack-based
//                triangulation of each monotone sub-polygon
//   - EarcutZ:   Ear clipping with Z-order curve (Morton code) spatial
//                indexing for fast point-in-triangle rejection
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

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <utility>
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

// Triangulate a polygon using monotone decomposition via sweep-line.
// Decomposes the polygon into y-monotone sub-polygons by adding diagonals
// at split/merge vertices, then triangulates each monotone piece using a
// stack-based O(n) algorithm.
//
// Handles both convex and concave simple polygons.  O(n^2) implementation
// (linear-search status structure; production code would use a balanced BST).
//
// @param polygon_indices  Polygon vertex indices (into `vertices`)
// @param vertices         Flat vertex array (x,y,z interleaved, stride 3)
// @param out_triangles    Output: triangle index triples (appended)
// @return                 Number of triangles produced
size_t TriangulateSweepLine(const std::vector<size_t> &polygon_indices,
                            const std::vector<double> &vertices,
                            std::vector<size_t> *out_triangles);

// Triangulate a polygon using ear clipping with Z-order curve (Morton code)
// spatial indexing.
//
// Based on the mapbox/earcut concept:
//  1. Build a doubly-linked circular list of polygon vertices
//  2. Compute Z-order curve values for spatial hashing
//  3. Remove ears iteratively; use Z-curve to efficiently reject vertices
//     that cannot be inside a candidate ear triangle
//  4. Falls back to full scan if Z-filtered pass gets stuck
//
// Handles both convex and concave simple polygons.
//
// @param polygon_indices  Polygon vertex indices (into `vertices`)
// @param vertices         Flat vertex array (x,y,z interleaved, stride 3)
// @param out_triangles    Output: triangle index triples (appended)
// @return                 Number of triangles produced
size_t TriangulateEarcutZCurve(const std::vector<size_t> &polygon_indices,
                               const std::vector<double> &vertices,
                               std::vector<size_t> *out_triangles);

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

// ---------------------------------------------------------------------------
// Sweep-Line Triangulation
// ---------------------------------------------------------------------------

// Shared helper: find best 2D projection axes for a 3D polygon.
static void FindProjectionAxes(const std::vector<size_t> &polygon_indices,
                               const std::vector<double> &vertices,
                               size_t axes[2]) {
  size_t n = polygon_indices.size();
  axes[0] = 1;
  axes[1] = 2;
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
    double eps = std::numeric_limits<double>::epsilon();
    if (cx > eps || cy > eps || cz > eps) {
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
}

// Sweep vertex is "above" another in sweep order (higher y, then smaller x).
static bool SweepAbove(double ax, double ay, double bx, double by) {
  if (ay != by) return ay > by;
  return ax < bx;
}

// Triangulate a y-monotone polygon using the standard stack-based algorithm.
// poly contains indices into the original vertex array.
// px/py are 2D coordinates indexed by POSITION in poly (0..n-1).
static size_t TriangulateMonotone(const std::vector<size_t> &poly,
                                  const std::vector<double> &px,
                                  const std::vector<double> &py,
                                  std::vector<size_t> *out) {
  size_t n = poly.size();
  if (n < 3) return 0;
  if (n == 3) {
    out->push_back(poly[0]);
    out->push_back(poly[1]);
    out->push_back(poly[2]);
    return 1;
  }

  // Find topmost and bottommost vertices (by position index)
  size_t top_pos = 0, bot_pos = 0;
  for (size_t i = 1; i < n; i++) {
    if (SweepAbove(px[i], py[i], px[top_pos], py[top_pos])) top_pos = i;
    if (SweepAbove(px[bot_pos], py[bot_pos], px[i], py[i])) bot_pos = i;
  }

  // Build left and right chains (from top to bottom).
  // Walk forward from top to bottom → one chain.
  // Walk backward from top to bottom → the other chain.
  std::vector<size_t> chain_fwd, chain_bwd;
  {
    size_t cur = top_pos;
    do {
      chain_fwd.push_back(cur);
      cur = (cur + 1) % n;
    } while (cur != bot_pos);
    chain_fwd.push_back(bot_pos);
  }
  {
    size_t cur = top_pos;
    do {
      chain_bwd.push_back(cur);
      cur = (cur + n - 1) % n;
    } while (cur != bot_pos);
    chain_bwd.push_back(bot_pos);
  }

  // Determine which chain is left (smaller x) vs right.
  std::vector<size_t> *left_chain = &chain_fwd;
  std::vector<size_t> *right_chain = &chain_bwd;
  if (chain_fwd.size() > 1 && chain_bwd.size() > 1) {
    if (px[chain_fwd[1]] > px[chain_bwd[1]]) {
      std::swap(left_chain, right_chain);
    }
  }

  // Tag each position as LEFT(0) or RIGHT(1).
  std::vector<int> side(n, 0);
  for (size_t i = 0; i < right_chain->size(); i++) {
    side[(*right_chain)[i]] = 1;
  }
  side[top_pos] = 0;
  side[bot_pos] = 0;

  // Merge both chains into sorted order (decreasing y).
  std::vector<size_t> sorted_pos(n);
  for (size_t i = 0; i < n; i++) sorted_pos[i] = i;
  std::sort(sorted_pos.begin(), sorted_pos.end(),
            [&](size_t a, size_t b) {
              return SweepAbove(px[a], py[a], px[b], py[b]);
            });

  // Stack-based triangulation
  std::vector<size_t> stk;
  stk.push_back(sorted_pos[0]);
  stk.push_back(sorted_pos[1]);
  size_t count = 0;

  for (size_t i = 2; i < n; i++) {
    size_t u = sorted_pos[i];
    size_t stk_top = stk.back();

    // The last vertex (bottommost) belongs to both chains, so always use
    // the "opposite chain" code path to pop everything remaining.
    if (i == n - 1 || side[u] != side[stk_top]) {
      // Opposite chain (or last vertex): pop all, create triangles
      while (stk.size() > 1) {
        size_t v1 = stk.back();
        stk.pop_back();
        size_t v2 = stk.back();
        out->push_back(poly[u]);
        out->push_back(poly[v1]);
        out->push_back(poly[v2]);
        count++;
      }
      stk.pop_back();
      if (i < n - 1) {
        stk.push_back(stk_top);
        stk.push_back(u);
      }
    } else {
      // Same chain: pop while diagonal is inside
      size_t last = stk.back();
      stk.pop_back();
      while (!stk.empty()) {
        size_t v = stk.back();
        double cross = (px[last] - px[u]) * (py[v] - py[u]) -
                       (py[last] - py[u]) * (px[v] - px[u]);
        bool valid = (side[u] == 0) ? (cross > 0) : (cross < 0);
        if (valid) {
          out->push_back(poly[u]);
          out->push_back(poly[last]);
          out->push_back(poly[v]);
          count++;
          last = v;
          stk.pop_back();
        } else {
          break;
        }
      }
      stk.push_back(last);
      stk.push_back(u);
    }
  }
  return count;
}

// Recursively split a polygon by diagonals (pairs of polygon positions),
// then triangulate each resulting monotone piece.
static size_t SplitAndTriangulate(
    const std::vector<size_t> &poly,   // original vertex indices
    const std::vector<double> &px,
    const std::vector<double> &py,
    const std::vector<std::pair<size_t, size_t> > &diagonals,
    std::vector<size_t> *out) {
  if (diagonals.empty()) {
    return TriangulateMonotone(poly, px, py, out);
  }

  size_t n = poly.size();
  size_t a = diagonals[0].first;
  size_t b = diagonals[0].second;

  // Build sub-polygon 1: walk from a → b (forward)
  std::vector<size_t> poly1, poly2;
  std::vector<double> px1, py1, px2, py2;

  {
    size_t cur = a;
    while (true) {
      poly1.push_back(poly[cur]);
      px1.push_back(px[cur]);
      py1.push_back(py[cur]);
      if (cur == b) break;
      cur = (cur + 1) % n;
    }
  }
  // Build sub-polygon 2: walk from b → a (forward)
  {
    size_t cur = b;
    while (true) {
      poly2.push_back(poly[cur]);
      px2.push_back(px[cur]);
      py2.push_back(py[cur]);
      if (cur == a) break;
      cur = (cur + 1) % n;
    }
  }

  // Build position maps: old position → new position in each sub-polygon
  std::vector<int> map1(n, -1), map2(n, -1);
  {
    size_t cur = a;
    for (size_t i = 0; i < poly1.size(); i++) {
      map1[cur] = static_cast<int>(i);
      if (cur == b) break;
      cur = (cur + 1) % n;
    }
  }
  {
    size_t cur = b;
    for (size_t i = 0; i < poly2.size(); i++) {
      map2[cur] = static_cast<int>(i);
      if (cur == a) break;
      cur = (cur + 1) % n;
    }
  }

  // Distribute remaining diagonals to sub-polygons
  std::vector<std::pair<size_t, size_t> > d1, d2;
  for (size_t i = 1; i < diagonals.size(); i++) {
    size_t c = diagonals[i].first;
    size_t d = diagonals[i].second;
    if (map1[c] >= 0 && map1[d] >= 0) {
      d1.push_back(std::make_pair(static_cast<size_t>(map1[c]),
                                  static_cast<size_t>(map1[d])));
    } else if (map2[c] >= 0 && map2[d] >= 0) {
      d2.push_back(std::make_pair(static_cast<size_t>(map2[c]),
                                  static_cast<size_t>(map2[d])));
    }
  }

  size_t count = 0;
  count += SplitAndTriangulate(poly1, px1, py1, d1, out);
  count += SplitAndTriangulate(poly2, px2, py2, d2, out);
  return count;
}

size_t TriangulateSweepLine(const std::vector<size_t> &polygon_indices,
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

  // For quads, use shortest-diagonal split
  if (n == 4) {
    double sqr02 =
        DistanceSq3D(vertices, polygon_indices[0], polygon_indices[2]);
    double sqr13 =
        DistanceSq3D(vertices, polygon_indices[1], polygon_indices[3]);
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

  // Project to 2D
  size_t axes[2];
  FindProjectionAxes(polygon_indices, vertices, axes);

  std::vector<double> px(n), py(n);
  for (size_t i = 0; i < n; i++) {
    size_t vi = polygon_indices[i];
    px[i] = vertices[vi * 3 + axes[0]];
    py[i] = vertices[vi * 3 + axes[1]];
  }

  // Compute signed area to determine orientation
  double area2 = 0;
  for (size_t i = 0; i < n; i++) {
    size_t j = (i + 1) % n;
    area2 += px[i] * py[j] - px[j] * py[i];
  }
  bool ccw = (area2 > 0);

  // Classify vertices
  enum VType { V_START, V_END, V_SPLIT, V_MERGE, V_REG_LEFT, V_REG_RIGHT };
  std::vector<int> vtype(n);

  for (size_t i = 0; i < n; i++) {
    size_t p = (i + n - 1) % n;
    size_t nx = (i + 1) % n;
    bool prev_below = SweepAbove(px[i], py[i], px[p], py[p]);
    bool next_below = SweepAbove(px[i], py[i], px[nx], py[nx]);

    if (prev_below && next_below) {
      double cross = (px[nx] - px[i]) * (py[p] - py[i]) -
                     (py[nx] - py[i]) * (px[p] - px[i]);
      bool convex = ccw ? (cross > 0) : (cross < 0);
      vtype[i] = convex ? V_START : V_SPLIT;
    } else if (!prev_below && !next_below) {
      double cross = (px[nx] - px[i]) * (py[p] - py[i]) -
                     (py[nx] - py[i]) * (px[p] - px[i]);
      bool convex = ccw ? (cross > 0) : (cross < 0);
      vtype[i] = convex ? V_END : V_MERGE;
    } else if (!prev_below && next_below) {
      vtype[i] = V_REG_LEFT;
    } else {
      vtype[i] = V_REG_RIGHT;
    }
  }

  // Sort vertices by sweep order (decreasing y, increasing x)
  std::vector<size_t> events(n);
  for (size_t i = 0; i < n; i++) events[i] = i;
  std::sort(events.begin(), events.end(), [&](size_t a, size_t b) {
    return SweepAbove(px[a], py[a], px[b], py[b]);
  });

  // Status: active (downward) edges sorted by x at sweep y.
  // For a CCW polygon, only edges whose start vertex is the upper endpoint
  // are tracked (left-boundary edges of interior regions).
  struct EdgeInfo {
    size_t edge_idx;  // edge e_k: from vertex k to vertex (k+1)%n
    size_t helper;    // helper vertex (polygon position)
  };
  std::vector<EdgeInfo> status;

  // Tolerance for near-horizontal edge detection and edge-x comparison.
  static const double kEdgeTolerance = 1e-12;

  // Compute x-coordinate where edge e_k intersects sweep line at y.
  auto edgeXAtY = [&](size_t eidx, double y) -> double {
    size_t from = eidx;
    size_t to = (eidx + 1) % n;
    double dy = py[to] - py[from];
    if (std::fabs(dy) < kEdgeTolerance) return std::min(px[from], px[to]);
    return px[from] + (px[to] - px[from]) * (y - py[from]) / dy;
  };

  // Find index in status of edge directly to the left of vertex v.
  auto findLeftEdge = [&](size_t v) -> int {
    double vx = px[v];
    double vy = py[v];
    int best = -1;
    double best_x = -std::numeric_limits<double>::max();
    for (size_t j = 0; j < status.size(); j++) {
      double ex = edgeXAtY(status[j].edge_idx, vy);
      if (ex <= vx + kEdgeTolerance && ex > best_x) {
        best_x = ex;
        best = static_cast<int>(j);
      }
    }
    return best;
  };

  auto insertEdge = [&](size_t eidx, size_t helper, double y) {
    double ex = edgeXAtY(eidx, y);
    size_t pos = 0;
    while (pos < status.size() && edgeXAtY(status[pos].edge_idx, y) < ex) {
      pos++;
    }
    EdgeInfo ei;
    ei.edge_idx = eidx;
    ei.helper = helper;
    status.insert(status.begin() + static_cast<std::ptrdiff_t>(pos), ei);
  };

  auto removeEdge = [&](size_t eidx) {
    for (size_t j = 0; j < status.size(); j++) {
      if (status[j].edge_idx == eidx) {
        status.erase(status.begin() + static_cast<std::ptrdiff_t>(j));
        return;
      }
    }
  };

  auto findEdge = [&](size_t eidx) -> int {
    for (size_t j = 0; j < status.size(); j++) {
      if (status[j].edge_idx == eidx) return static_cast<int>(j);
    }
    return -1;
  };

  // Collect diagonals (pairs of polygon positions)
  std::vector<std::pair<size_t, size_t> > diagonals;

  for (size_t ev = 0; ev < n; ev++) {
    size_t i = events[ev];
    size_t prev_edge = (i + n - 1) % n;  // e_{i-1}

    switch (vtype[i]) {
      case V_START:
        insertEdge(i, i, py[i]);
        break;

      case V_END: {
        int ei = findEdge(prev_edge);
        if (ei >= 0 && vtype[status[ei].helper] == V_MERGE) {
          diagonals.push_back(std::make_pair(i, status[ei].helper));
        }
        removeEdge(prev_edge);
        break;
      }

      case V_SPLIT: {
        int left = findLeftEdge(i);
        if (left >= 0) {
          diagonals.push_back(std::make_pair(i, status[left].helper));
          status[left].helper = i;
        }
        insertEdge(i, i, py[i]);
        break;
      }

      case V_MERGE: {
        int ei = findEdge(prev_edge);
        if (ei >= 0 && vtype[status[ei].helper] == V_MERGE) {
          diagonals.push_back(std::make_pair(i, status[ei].helper));
        }
        removeEdge(prev_edge);
        int left = findLeftEdge(i);
        if (left >= 0) {
          if (vtype[status[left].helper] == V_MERGE) {
            diagonals.push_back(std::make_pair(i, status[left].helper));
          }
          status[left].helper = i;
        }
        break;
      }

      case V_REG_LEFT: {
        // Interior to right: handle like END for e_{i-1}, START for e_i
        int ei = findEdge(prev_edge);
        if (ei >= 0 && vtype[status[ei].helper] == V_MERGE) {
          diagonals.push_back(std::make_pair(i, status[ei].helper));
        }
        removeEdge(prev_edge);
        insertEdge(i, i, py[i]);
        break;
      }

      case V_REG_RIGHT: {
        // Interior to left: find edge to left, update helper
        int left = findLeftEdge(i);
        if (left >= 0) {
          if (vtype[status[left].helper] == V_MERGE) {
            diagonals.push_back(std::make_pair(i, status[left].helper));
          }
          status[left].helper = i;
        }
        break;
      }
    }
  }

  // If no diagonals needed, polygon is already monotone
  if (diagonals.empty()) {
    return TriangulateMonotone(polygon_indices, px, py, out_triangles);
  }

  return SplitAndTriangulate(polygon_indices, px, py, diagonals, out_triangles);
}

// ---------------------------------------------------------------------------
// Earcut Z-Curve Triangulation
// ---------------------------------------------------------------------------

// Compute Z-order curve (Morton code) value for a 2D point.
static int32_t ZOrderValue(double x, double y, double minX, double minY,
                           double invSize) {
  int32_t ix =
      static_cast<int32_t>(std::min(static_cast<double>(32767),
                                    std::max(0.0, (x - minX) * invSize)));
  int32_t iy =
      static_cast<int32_t>(std::min(static_cast<double>(32767),
                                    std::max(0.0, (y - minY) * invSize)));

  ix = (ix | (ix << 8)) & 0x00FF00FF;
  ix = (ix | (ix << 4)) & 0x0F0F0F0F;
  ix = (ix | (ix << 2)) & 0x33333333;
  ix = (ix | (ix << 1)) & 0x55555555;

  iy = (iy | (iy << 8)) & 0x00FF00FF;
  iy = (iy | (iy << 4)) & 0x0F0F0F0F;
  iy = (iy | (iy << 2)) & 0x33333333;
  iy = (iy | (iy << 1)) & 0x55555555;

  return ix | (iy << 1);
}

// 2D signed area of triangle (a, b, c).  Positive if CCW.
static double TriArea2D(double ax, double ay, double bx, double by, double cx,
                        double cy) {
  return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
}

// True if point (px,py) is strictly inside triangle (ax,ay,bx,by,cx,cy).
static bool PointInTriangle2D(double ax, double ay, double bx, double by,
                              double cx, double cy, double ptx, double pty) {
  double d1 = TriArea2D(ptx, pty, ax, ay, bx, by);
  double d2 = TriArea2D(ptx, pty, bx, by, cx, cy);
  double d3 = TriArea2D(ptx, pty, cx, cy, ax, ay);
  bool has_neg = (d1 < 0) || (d2 < 0) || (d3 < 0);
  bool has_pos = (d1 > 0) || (d2 > 0) || (d3 > 0);
  return !(has_neg && has_pos);
}

size_t TriangulateEarcutZCurve(const std::vector<size_t> &polygon_indices,
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

  // For quads, use shortest-diagonal split
  if (n == 4) {
    double sqr02 =
        DistanceSq3D(vertices, polygon_indices[0], polygon_indices[2]);
    double sqr13 =
        DistanceSq3D(vertices, polygon_indices[1], polygon_indices[3]);
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

  // Project to 2D
  size_t axes[2];
  FindProjectionAxes(polygon_indices, vertices, axes);

  // Node for doubly-linked list
  struct Node {
    size_t orig_idx;  // original vertex index (into vertices array)
    double x, y;
    int32_t z;
    int prev, next;    // circular polygon list (indices into nodes[])
    int prevZ, nextZ;  // z-sorted list
  };

  std::vector<Node> nodes(n);
  double minX = std::numeric_limits<double>::max();
  double minY = std::numeric_limits<double>::max();
  double maxX = -std::numeric_limits<double>::max();
  double maxY = -std::numeric_limits<double>::max();

  for (size_t i = 0; i < n; i++) {
    size_t vi = polygon_indices[i];
    nodes[i].orig_idx = vi;
    nodes[i].x = vertices[vi * 3 + axes[0]];
    nodes[i].y = vertices[vi * 3 + axes[1]];
    nodes[i].z = 0;
    nodes[i].prev = static_cast<int>((i + n - 1) % n);
    nodes[i].next = static_cast<int>((i + 1) % n);
    nodes[i].prevZ = -1;
    nodes[i].nextZ = -1;
    if (nodes[i].x < minX) minX = nodes[i].x;
    if (nodes[i].x > maxX) maxX = nodes[i].x;
    if (nodes[i].y < minY) minY = nodes[i].y;
    if (nodes[i].y > maxY) maxY = nodes[i].y;
  }

  // Compute signed area for winding direction
  double area2 = 0;
  for (size_t i = 0; i < n; i++) {
    size_t j = (i + 1) % n;
    area2 += nodes[i].x * nodes[j].y - nodes[j].x * nodes[i].y;
  }
  bool ccw = (area2 > 0);

  // Compute Z-order values
  double sz = std::max(maxX - minX, maxY - minY);
  double invSize = (sz > 0) ? 32767.0 / sz : 0.0;

  for (size_t i = 0; i < n; i++) {
    nodes[i].z = ZOrderValue(nodes[i].x, nodes[i].y, minX, minY, invSize);
  }

  // Build Z-sorted linked list
  std::vector<size_t> zSorted(n);
  for (size_t i = 0; i < n; i++) zSorted[i] = i;
  std::sort(zSorted.begin(), zSorted.end(),
            [&](size_t a, size_t b) { return nodes[a].z < nodes[b].z; });

  for (size_t i = 0; i < n; i++) {
    nodes[zSorted[i]].prevZ =
        (i > 0) ? static_cast<int>(zSorted[i - 1]) : -1;
    nodes[zSorted[i]].nextZ =
        (i + 1 < n) ? static_cast<int>(zSorted[i + 1]) : -1;
  }

  // Main ear removal loop
  size_t remaining = n;
  int ear = 0;
  size_t count = 0;
  size_t max_iter = n * n;  // safety limit

  while (remaining > 3 && max_iter > 0) {
    bool found = false;
    int start = ear;

    do {
      max_iter--;
      int ai = nodes[ear].prev;
      int bi = ear;
      int ci = nodes[ear].next;

      double ax = nodes[ai].x, ay = nodes[ai].y;
      double bx = nodes[bi].x, by = nodes[bi].y;
      double cx = nodes[ci].x, cy = nodes[ci].y;

      double cross = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
      bool convex = ccw ? (cross > 0) : (cross < 0);

      if (convex) {
        // Check that no other vertex is inside the ear triangle
        // using Z-curve filtering.
        bool inside = false;

        double triMinX = std::min({ax, bx, cx});
        double triMinY = std::min({ay, by, cy});
        double triMaxX = std::max({ax, bx, cx});
        double triMaxY = std::max({ay, by, cy});
        int32_t zMin =
            ZOrderValue(triMinX, triMinY, minX, minY, invSize);
        int32_t zMax =
            ZOrderValue(triMaxX, triMaxY, minX, minY, invSize);

        // Search outward from bi in Z-sorted list
        int p = nodes[bi].prevZ;
        int q = nodes[bi].nextZ;

        while (p >= 0 && nodes[p].z >= zMin) {
          if (p != ai && p != ci &&
              PointInTriangle2D(ax, ay, bx, by, cx, cy, nodes[p].x,
                                nodes[p].y)) {
            inside = true;
            break;
          }
          p = nodes[p].prevZ;
        }
        if (!inside) {
          while (q >= 0 && nodes[q].z <= zMax) {
            if (q != ai && q != ci &&
                PointInTriangle2D(ax, ay, bx, by, cx, cy, nodes[q].x,
                                  nodes[q].y)) {
              inside = true;
              break;
            }
            q = nodes[q].nextZ;
          }
        }

        if (!inside) {
          // Valid ear! Output triangle and unlink bi.
          out_triangles->push_back(nodes[ai].orig_idx);
          out_triangles->push_back(nodes[bi].orig_idx);
          out_triangles->push_back(nodes[ci].orig_idx);
          count++;

          // Unlink bi from polygon list
          nodes[ai].next = ci;
          nodes[ci].prev = ai;

          // Unlink bi from Z-sorted list
          if (nodes[bi].prevZ >= 0)
            nodes[nodes[bi].prevZ].nextZ = nodes[bi].nextZ;
          if (nodes[bi].nextZ >= 0)
            nodes[nodes[bi].nextZ].prevZ = nodes[bi].prevZ;

          remaining--;
          ear = ci;
          found = true;
          break;
        }
      }

      ear = nodes[ear].next;
    } while (ear != start);

    if (!found) {
      // Fallback: try full scan without Z-filtering
      start = ear;
      do {
        max_iter--;
        int ai = nodes[ear].prev;
        int bi = ear;
        int ci = nodes[ear].next;

        double ax = nodes[ai].x, ay = nodes[ai].y;
        double bx = nodes[bi].x, by = nodes[bi].y;
        double cx = nodes[ci].x, cy = nodes[ci].y;

        double cross = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
        bool convex = ccw ? (cross > 0) : (cross < 0);

        if (convex) {
          bool inside = false;
          // Full scan of all remaining vertices
          int p = nodes[ci].next;
          while (p != ai) {
            if (PointInTriangle2D(ax, ay, bx, by, cx, cy, nodes[p].x,
                                  nodes[p].y)) {
              inside = true;
              break;
            }
            p = nodes[p].next;
          }

          if (!inside) {
            out_triangles->push_back(nodes[ai].orig_idx);
            out_triangles->push_back(nodes[bi].orig_idx);
            out_triangles->push_back(nodes[ci].orig_idx);
            count++;

            nodes[ai].next = ci;
            nodes[ci].prev = ai;

            if (nodes[bi].prevZ >= 0)
              nodes[nodes[bi].prevZ].nextZ = nodes[bi].nextZ;
            if (nodes[bi].nextZ >= 0)
              nodes[nodes[bi].nextZ].prevZ = nodes[bi].prevZ;

            remaining--;
            ear = ci;
            found = true;
            break;
          }
        }
        ear = nodes[ear].next;
      } while (ear != start);

      if (!found) break;  // No more ears found (degenerate polygon)
    }
  }

  // Emit final triangle
  if (remaining == 3) {
    int a = ear;
    int b = nodes[a].next;
    int c = nodes[b].next;
    out_triangles->push_back(nodes[a].orig_idx);
    out_triangles->push_back(nodes[b].orig_idx);
    out_triangles->push_back(nodes[c].orig_idx);
    count++;
  }

  return count;
}

}  // namespace triangulation

#endif  // TRIANGULATION_IMPLEMENTATION
#endif  // TRIANGULATION_H_
