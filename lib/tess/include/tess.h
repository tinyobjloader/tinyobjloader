/* SPDX-License-Identifier: MIT */
#ifndef TESS_H
#define TESS_H
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Bounded exact arithmetic API. Resource failure never supplies a sign.
 */
typedef enum {
  TESS_OK = 0,
  TESS_INVALID_INPUT,
  TESS_UNSUPPORTED_CHART,
  TESS_RESOURCE_LIMIT,
  TESS_ALLOCATION_FAILURE,
  TESS_INTERNAL_ERROR,
  TESS_VALID_TARGETS_UNMET,
  TESS_VALID_TARGETS_MET,
  TESS_CERTIFICATE_REJECTED,
  TESS_EXPORT_FAILURE,
  TESS_IO_ERROR
} tess_status;
typedef struct {
  int64_t x, y;
} tess_point2i;
/* Exact for every accepted input, including collinearity. On failure *sign
   is untouched. No allocation or global state; safe for concurrent calls. */
tess_status tess_orient2i(tess_point2i a, tess_point2i b, tess_point2i c,
                          int* sign);
const char* tess_status_string(tess_status status);
/* Ring offsets have ring_count+1 entries; vertices are consecutive xyz triples.
   The first ring is outer. Holes have opposite winding. No repeated closure. */
typedef struct {
  const double* xyz;
  size_t vertex_count;
  const size_t* ring_offsets;
  size_t ring_count;
} tess_input;
typedef struct {
  void* user;
  void* (*allocate)(size_t bytes, void* user);
  void (*release)(void* pointer, void* user);
} tess_allocator;
typedef enum {
  TESS_DIAG_NONE = 0,
  TESS_DIAG_INPUT,
  TESS_DIAG_COORDINATE,
  TESS_DIAG_RING_AREA,
  TESS_DIAG_RING_WINDING,
  TESS_DIAG_PROJECTION_COLLISION,
  TESS_DIAG_SEGMENT_CONTACT,
  TESS_DIAG_HOLE_OUTSIDE,
  TESS_DIAG_HOLE_NESTING,
  TESS_DIAG_NONPLANAR,
  TESS_DIAG_TRIANGLE_CONTACT,
  TESS_DIAG_DEGENERATE_TRIANGLE
} tess_diagnostic_reason;
typedef struct {
  tess_status status;
  tess_diagnostic_reason reason;
  int axis;
  unsigned charts_tried;
  size_t ring, other_ring, vertex_a, vertex_b, edge_a, edge_b, face_a, face_b;
  size_t operations, peak_bytes;
} tess_diagnostic;
typedef struct {
  int chart_axis;    /* -1 automatic, otherwise 0,1,2 */
  int strict_planar; /* default graph surface */
  size_t max_vertices, max_faces, max_limbs, max_bytes,
      max_operations;       /* 0 selects defaults */
  tess_allocator allocator; /* both callbacks NULL selects malloc/free */
  /* Optional output for triangulation only. IDs are original input indices;
     unavailable IDs are SIZE_MAX. Borrowed only for the construction call. */
  tess_diagnostic* diagnostic;
} tess_options;
/* Borrowed little-endian base-2^32 limbs. Denominator is strictly positive.
   A zero numerator has sign=0 and numerator_count=0. */
typedef struct {
  int sign;
  const uint32_t* numerator;
  size_t numerator_count;
  const uint32_t* denominator;
  size_t denominator_count;
} tess_rational;
typedef struct {
  const tess_rational* xyz;
  size_t vertex_count;
  const size_t* ring_offsets;
  size_t ring_count;
} tess_exact_input;
typedef struct tess_result tess_result;
typedef struct {
  size_t a, b;
  uint64_t tag;
} tess_seed_feature;
/* Before prepare/remesh, tag existing frozen seed edges and pin seed vertices.
   Input seed vertices are already pinned. This transaction does not insert
   general constraints. Save a version-2 certificate after prepare. */
tess_status tess_set_seed_features(tess_result* result,
                                   const tess_seed_feature* features,
                                   size_t feature_count,
                                   const size_t* pinned_vertices,
                                   size_t pinned_count);
tess_options tess_default_options(void);
/* On failure *out is NULL. Input is borrowed for this call only. */
tess_status tess_triangulate(const tess_input* input,
                             const tess_options* options, tess_result** out);
tess_status tess_triangulate_exact(const tess_exact_input* input,
                                   const tess_options* options,
                                   tess_result** out);
/* Returned limbs are valid until the result is destroyed or modified. */
tess_status tess_coordinate(const tess_result* result, size_t vertex, int axis,
                            tess_rational* out);
size_t tess_vertex_source(const tess_result* result, size_t vertex);
size_t tess_constraint_count(const tess_result* result);
typedef struct {
  size_t a, b, source_edge, owner;
  int kind; /* 1 boundary, 2 implicit crease, 3 user feature */
  uint64_t tag;
} tess_constraint_info;
tess_status tess_constraint_details(const tess_result* result, size_t index,
                                    tess_constraint_info* info);
size_t tess_triangle_id(const tess_result* result, size_t index);
tess_status tess_constraint(const tess_result* result, size_t index,
                            size_t endpoints[2], size_t* source_edge);
void tess_result_free(tess_result* result);
size_t tess_vertex_count(const tess_result* result);
size_t tess_triangle_count(const tess_result* result);
tess_status tess_triangle(const tess_result* result, size_t index,
                          size_t ids[3]);
/* Rounds to binary64 and revalidates the complete rounded mesh against the
   frozen exact reference. Pinned coordinates must remain exact. */
tess_status tess_export_binary64(tess_result* result, double* xyz,
                                 size_t count);
int tess_chart_axis(const tess_result* result);
const char* tess_seed_policy(void);
/* Seed-only chart-metric local legality; no claim about remeshed output. */
int tess_seed_delaunay_complete(const tess_result* result);
typedef struct {
  size_t target_count; /* mutually exclusive with area */
  double target_area;
  const tess_rational* exact_target_area;
  double height_tolerance;
  const tess_rational* exact_height_tolerance;
  size_t max_passes, max_edits, max_candidates;
  int subdivide_boundary, subdivide_features;
  /* NULL permits all boundary owners when subdivide_boundary is set. */
  const size_t* boundary_owners;
  size_t boundary_owner_count;
  double max_area_cv, min_fraction_target_band, min_angle_p05;
} tess_remesh_options;
tess_remesh_options tess_default_remesh_options(void);
typedef enum {
  TESS_STOP_TARGETS_MET = 0,
  TESS_STOP_BUDGET,
  TESS_STOP_CONSTRAINTS,
  TESS_STOP_STAGNATION,
  TESS_STOP_RESOURCE,
  TESS_STOP_ALLOCATION,
  TESS_STOP_ERROR
} tess_termination;
typedef struct {
  tess_status outcome, stop_reason;
  tess_termination termination;
  size_t passes, edits, candidates, validity_rejections, objective_rejections;
  size_t constraint_rejections, batches, edge_splits, face_splits, collapses,
      flips, relocations;
} tess_run_report;
/* Every committed candidate is validated. Failure preserves a validated mesh.
   All option pointers are borrowed for this call only. */
/* Optional prepare step freezes run options and the count-derived target, so a
   caller-held canonical request can be saved before optimization. After prepare
   call tess_remesh(result,NULL,...). Each result supports one optimization run.
 */
tess_status tess_prepare_remesh(tess_result* result,
                                const tess_remesh_options* options);
tess_status tess_remesh(tess_result* result, const tess_remesh_options* options,
                        tess_run_report* report);
tess_status tess_constraint_parameter(const tess_result* result, size_t index,
                                      int endpoint, tess_rational* parameter);
size_t tess_vertex_id(const tess_result* result, size_t vertex);

/* Engineering statistics use long-double intermediates and Type-7 linear
   percentile interpolation; stored report values are binary64. */
typedef struct {
  size_t vertices, triangles, operations, peak_bytes;
  double target_area, total_area, area_cv, area_ratio_p05, area_ratio_p50,
      area_ratio_p95;
  double min_angle_p05, min_angle_min, mean_ratio, mean_squared_log_area_error;
  double fraction_target_band, objective, max_reference_deviation;
} tess_quality;
tess_status tess_target_area(const tess_result* result, tess_rational* area);
/* Exact maximum from the final overlay validation, when available. */
tess_status tess_reference_deviation(const tess_result* result,
                                     tess_rational* deviation);
tess_status tess_result_quality(const tess_result* result,
                                tess_quality* report);
/* NULL target measures ratios against the current mean area. */
tess_status tess_measure(tess_result* result, const tess_rational* target,
                         tess_quality* report);

/* Versioned exact artifact. A successful C check is not a Lean certification.
   request supplies caller-held input/options; certificate bytes are borrowed.
 */
tess_status tess_write_certificate(const tess_result* result, FILE* stream);
/* Validate supplied binary64 coordinates and certify those actual coordinates,
   retaining the original exact request and frozen seed. */
tess_status tess_write_export_certificate(tess_result* result,
                                          const double* xyz, size_t count,
                                          FILE* stream);
tess_status tess_check_certificate(const tess_result* request,
                                   const char* bytes, size_t length);

#ifdef __cplusplus
}
#endif
#endif
