/* SPDX-License-Identifier: MIT */
#ifndef TESS_GEOMETRY_H
#define TESS_GEOMETRY_H
#define TESS_SEED_POLICY "SEED-VISIBILITY-ROTATION-LEFT1-LAWSON1"
#include "exact.h"
typedef struct {
  qr p[3];
  size_t source, id;
  int pinned;
} tv;
typedef struct {
  size_t v[3];
  size_t id;
} tf;
typedef struct {
  size_t a, b;
  int constraint;
  size_t source, owner;
  uint64_t tag;
  qr ta, tb;
} te;
typedef struct {
  tx c;
  tess_diagnostic diagnostic;
  tv* v;
  size_t nv, vcap;
  tf* f;
  size_t nf, fcap;
  te* e;
  size_t ne, ecap;
  size_t* rings;
  size_t nr;
  int axis, u, w, orientation;
  size_t max_vertices, max_faces, max_edits, next_id, next_face_id;
  size_t edits, rejected;
  int planar, approximate, legalization_complete;
} tm;
void tm_init(tm* m);
void tm_clear(tm* m);
int tg_orient(tm* m, size_t a, size_t b, size_t c);
int tg_orient_q(tm* m, const qr* ax, const qr* ay, const qr* bx, const qr* by,
                const qr* cx, const qr* cy);
int tg_equal(tm* m, size_t a, size_t b, int projected);
int tg_segments(tm* m, size_t a, size_t b, size_t c, size_t d);
int tg_domain(tm* m, const qr* x,
              const qr* y); /* -1 boundary, 0 outside, 1 inside */
int tg_validate(tm* m);
int tg_prepare(tm* m, int requested_axis, int strict_planar);
int tg_seed(tm* m);
int tg_add_vertex(tm* m, const double p[3], size_t source);
int tg_add_face(tm* m, size_t a, size_t b, size_t c);
/* Signs use exact rational determinants; caller must inspect m->c.status. */
int tg_orient3(tm* m, size_t a, size_t b, size_t c, size_t d);
int tg_incircle(tm* m, size_t a, size_t b, size_t c, size_t d);

int tg_audit3(tm* m);
int tg_legalize(tm* m, size_t fuel, int* complete);

int tg_topology(tm* m, int patch);

int tg_reference(tm* output, const tm* seed, const qr* tolerance);
int tg_reference_measure(tm* output, const tm* seed, const qr* tolerance,
                         qr* maximum);
int tg_protect_creases(tm* m);
int tg_tag_seed_edge(tm* m, size_t a, size_t b, uint64_t tag);
void tg_freeze_constraints(tm* m);
int tg_constraint_append(tm* m, const te* base, size_t a, size_t b,
                         const qr* ta, const qr* tb);
int tg_reference_height(tm* work, const tm* reference, const qr* x, const qr* y,
                        qr* height);
int tg_validate_mode(tm* m, int accelerated);
int tg_audit3_mode(tm* m, int accelerated);
#endif
