/* SPDX-License-Identifier: MIT */
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "edits.h"
#include "metrics.h"
#include "result.h"
static int freeze(tess_result* r, tess_options o) {
  r->options = o;
  r->options.diagnostic = NULL;
  tx_init(&r->control);
  r->control.allocator = o.allocator;
  if (!tg_protect_creases(&r->mesh)) return 0;
  tg_freeze_constraints(&r->mesh);
  if (!tm_clone(&r->seed, &r->mesh)) {
    r->mesh.c.status = r->seed.c.status;
    return 0;
  }
  r->mesh.c.max_bytes -= r->seed.c.bytes;
  r->mesh.c.max_ops -= r->seed.c.ops;
  r->peak_bytes = r->mesh.c.peak;
  if (r->mesh.c.bytes + r->seed.c.peak > r->peak_bytes)
    r->peak_bytes = r->mesh.c.bytes + r->seed.c.peak;
  r->peak_bytes += sizeof(*r);
  r->mesh.c.peak = r->mesh.c.bytes;
  return 1;
}
tess_options tess_default_options(void) {
  tess_options o = {0};
  o.chart_axis = -1;
  o.max_vertices = 10000;
  o.max_faces = 20000;
  o.max_limbs = 4096;
  o.max_bytes = 256 * 1024 * 1024;
  o.max_operations = 100000000;
  return o;
}
static void diagnostic_start(tess_diagnostic* diagnostic) {
  if (diagnostic)
    *diagnostic = (tess_diagnostic){.status = TESS_INVALID_INPUT,
                                    .reason = TESS_DIAG_INPUT,
                                    .axis = -1,
                                    .ring = SIZE_MAX,
                                    .other_ring = SIZE_MAX,
                                    .vertex_a = SIZE_MAX,
                                    .vertex_b = SIZE_MAX,
                                    .edge_a = SIZE_MAX,
                                    .edge_b = SIZE_MAX,
                                    .face_a = SIZE_MAX,
                                    .face_b = SIZE_MAX};
}
static void diagnostic_finish(tess_diagnostic* diagnostic,
                              tess_result* result) {
  tm* m = &result->mesh;
  if (diagnostic) {
    *diagnostic = m->diagnostic;
    diagnostic->status = m->c.status;
    diagnostic->operations = m->c.ops + result->seed.c.ops;
    diagnostic->peak_bytes = m->c.peak;
    if (m->c.bytes + result->seed.c.peak > diagnostic->peak_bytes)
      diagnostic->peak_bytes = m->c.bytes + result->seed.c.peak;
    diagnostic->peak_bytes += sizeof(*result);
    if (diagnostic->ring == SIZE_MAX && diagnostic->vertex_a != SIZE_MAX &&
        m->rings)
      for (size_t r = 0; r < m->nr; r++)
        if (m->diagnostic.vertex_a >= m->rings[r] &&
            m->diagnostic.vertex_a < m->rings[r + 1])
          diagnostic->ring = r;
  }
}

tess_status tess_triangulate(const tess_input* in, const tess_options* opts,
                             tess_result** out) {
  tess_result* r;
  tm* m;
  size_t i;
  tess_options o = opts ? *opts : tess_default_options();
  diagnostic_start(o.diagnostic);
  if (!out) return TESS_INVALID_INPUT;
  *out = NULL;
  if (!in || !in->xyz || !in->ring_offsets || !in->ring_count ||
      in->vertex_count < 3 || in->vertex_count > SIZE_MAX / 3 ||
      in->ring_count > in->vertex_count / 3 ||
      (!!o.allocator.allocate != !!o.allocator.release) ||
      o.max_limbs > (size_t)INT_MAX / 64 || o.chart_axis < -1 ||
      o.chart_axis > 2)
    return TESS_INVALID_INPUT;
  if (in->ring_offsets[0] ||
      in->ring_offsets[in->ring_count] != in->vertex_count)
    return TESS_INVALID_INPUT;
  for (i = 0; i < in->ring_count; i++)
    if (in->ring_offsets[i] > in->ring_offsets[i + 1] ||
        in->ring_offsets[i + 1] - in->ring_offsets[i] < 3)
      return TESS_INVALID_INPUT;
  if ((o.max_bytes ? o.max_bytes : tess_default_options().max_bytes) <
      sizeof(*r)) {
    if (o.diagnostic) o.diagnostic->status = TESS_RESOURCE_LIMIT;
    return TESS_RESOURCE_LIMIT;
  }
  r = o.allocator.allocate ? o.allocator.allocate(sizeof(*r), o.allocator.user)
                           : malloc(sizeof(*r));
  if (!r) {
    if (o.diagnostic) o.diagnostic->status = TESS_ALLOCATION_FAILURE;
    return TESS_ALLOCATION_FAILURE;
  }
  memset(r, 0, sizeof(*r));
  m = &r->mesh;
  tm_init(m);
  m->c.allocator = o.allocator;
  if (o.max_vertices) m->max_vertices = o.max_vertices;
  if (o.max_faces) m->max_faces = o.max_faces;
  if (o.max_limbs) m->c.max_limbs = o.max_limbs;
  m->c.max_bytes =
      (o.max_bytes ? o.max_bytes : tess_default_options().max_bytes) -
      sizeof(*r);
  if (o.max_operations) m->c.max_ops = o.max_operations;
  m->nr = in->ring_count;
  m->rings = tx_alloc(&m->c, m->nr + 1, sizeof(size_t));
  if (m->rings)
    for (i = 0; i <= m->nr; i++) m->rings[i] = in->ring_offsets[i];
  for (i = 0; i < in->vertex_count && !m->c.status; i++) {
    if (!tg_add_vertex(m, &in->xyz[i * 3], i) &&
        m->c.status == TESS_INVALID_INPUT) {
      m->diagnostic.reason = TESS_DIAG_COORDINATE;
      m->diagnostic.vertex_a = i;
    }
  }
  if (!m->c.status && tg_prepare(m, o.chart_axis, o.strict_planar)) tg_seed(m);
  if (!m->c.status) freeze(r, o);
  diagnostic_finish(o.diagnostic, r);
  if (m->c.status) {
    tess_status s = m->c.status;
    tess_result_free(r);
    return s;
  }
  *out = r;
  return TESS_OK;
}
void tess_result_free(tess_result* r) {
  if (r) {
    tess_allocator a = r->mesh.c.allocator;
    qr_clear(&r->mesh.c, &r->deviation);
    tm_clear(&r->mesh);
    tm_clear(&r->seed);
    qr_clear(&r->control, &r->target);
    qr_clear(&r->control, &r->tolerance);
    qr_clear(&r->control, &r->split_threshold);
    qr_clear(&r->control, &r->batch_threshold);
    tx_free(&r->control, r->allowed_owners, r->allowed_count * sizeof(size_t));
    if (a.release)
      a.release(r, a.user);
    else
      free(r);
  }
}
size_t tess_vertex_count(const tess_result* r) { return r ? r->mesh.nv : 0; }
size_t tess_triangle_count(const tess_result* r) { return r ? r->mesh.nf : 0; }
tess_status tess_triangle(const tess_result* r, size_t i, size_t ids[3]) {
  size_t k;
  if (!r || !ids || i >= r->mesh.nf) return TESS_INVALID_INPUT;
  for (k = 0; k < 3; k++) ids[k] = r->mesh.f[i].v[k];
  return TESS_OK;
}
int tess_seed_delaunay_complete(const tess_result* r) {
  return r ? r->seed.legalization_complete : 0;
}
const char* tess_seed_policy(void) { return TESS_SEED_POLICY; }
int tess_chart_axis(const tess_result* r) { return r ? r->mesh.axis : -1; }
static tess_status export_mesh(tess_result* r, const double* xyz, size_t count,
                               tm* test) {
  tm* m = &r->mesh;
  qr tolerance = {0};
  size_t i, k;
  int ok = 0;
  tess_status failure;
  tm_init(test);
  test->c.allocator = m->c.allocator;
  test->c.max_bytes = m->c.max_bytes - m->c.bytes;
  test->c.max_ops = m->c.max_ops - m->c.ops;
  test->c.max_limbs = m->c.max_limbs;
  test->max_vertices = m->max_vertices;
  test->max_faces = m->max_faces;
  if (m->nv > SIZE_MAX / 3 || count < m->nv * 3) return TESS_INVALID_INPUT;
  test->nr = m->nr;
  test->rings = tx_alloc(&test->c, test->nr + 1, sizeof(size_t));
  if (!test->rings) goto end;
  for (i = 0; i <= test->nr; i++) test->rings[i] = m->rings[i];
  for (i = 0; i < m->nv && !test->c.status; i++) {
    for (k = 0; k < 3; k++)
      if (!isfinite(xyz[i * 3 + k])) goto end;
    if (!tg_add_vertex(test, &xyz[i * 3], m->v[i].source)) goto end;
    test->v[i].pinned = m->v[i].pinned;
    test->v[i].id = m->v[i].id;
    if (m->v[i].pinned)
      for (k = 0; k < 3; k++)
        if (qr_cmp(&test->c, &test->v[i].p[k], &m->v[i].p[k])) goto end;
  }
  test->axis = m->axis;
  test->u = m->u;
  test->w = m->w;
  test->orientation = m->orientation;
  test->planar = m->planar;
  test->approximate = m->approximate;
  test->ecap = test->ne = m->ne;
  test->e = tx_alloc(&test->c, test->ne, sizeof(te));
  if (!test->e) {
    test->ne = 0;
    goto end;
  }
  for (i = 0; i < test->ne; i++) {
    test->e[i] = m->e[i];
    test->e[i].ta = (qr){0};
    test->e[i].tb = (qr){0};
    qr_copy(&test->c, &test->e[i].ta, &m->e[i].ta);
    qr_copy(&test->c, &test->e[i].tb, &m->e[i].tb);
  }
  for (i = 0; i < m->nf && !test->c.status; i++) {
    if (!tg_add_face(test, m->f[i].v[0], m->f[i].v[1], m->f[i].v[2])) goto end;
    test->f[i].id = m->f[i].id;
  }
  if (r->remeshed)
    qr_copy(&test->c, &tolerance, &r->tolerance);
  else
    qr_i64(&test->c, &tolerance, 0);
  ok = tg_validate(test) && tg_audit3(test) &&
       tg_reference(test, &r->seed, &tolerance);
  if (ok && r->remeshed)
    ok = tg_check_chains(test, &r->seed, &r->remesh_options);
end:
  failure = test->c.status;
  qr_clear(&test->c, &tolerance);
  m->c.ops += test->c.ops;
  {
    size_t total = m->c.bytes + r->seed.c.bytes + r->control.bytes +
                   sizeof(*r) + test->c.peak;
    if (total > r->peak_bytes) r->peak_bytes = total;
  }
  return ok ? TESS_OK
            : (failure == TESS_RESOURCE_LIMIT ||
                       failure == TESS_ALLOCATION_FAILURE
                   ? failure
                   : TESS_EXPORT_FAILURE);
}
tess_status tess_export_binary64(tess_result* r, double* xyz, size_t count) {
  tm rounded;
  size_t i, j;
  tess_status status;
  if (!r || !xyz || r->mesh.nv > SIZE_MAX / 3 || count < r->mesh.nv * 3)
    return TESS_INVALID_INPUT;
  for (i = 0; i < r->mesh.nv; i++)
    for (j = 0; j < 3; j++)
      if (!tx_report_double(qr_approx(&r->mesh.v[i].p[j]), &xyz[3 * i + j]))
        return TESS_EXPORT_FAILURE;
  status = export_mesh(r, xyz, count, &rounded);
  tm_clear(&rounded);
  return status;
}
tess_status tess_write_export_certificate(tess_result* r, const double* xyz,
                                          size_t count, FILE* stream) {
  tm rounded;
  tess_result view;
  tess_status status;
  if (!r || !xyz || !stream) return TESS_INVALID_INPUT;
  status = export_mesh(r, xyz, count, &rounded);
  if (status == TESS_OK) {
    view = *r;
    view.mesh = rounded;
    status = tess_write_certificate(&view, stream);
  }
  tm_clear(&rounded);
  return status;
}

tess_status tess_triangulate_exact(const tess_exact_input* in,
                                   const tess_options* opts,
                                   tess_result** out) {
  tess_options o = opts ? *opts : tess_default_options();
  tess_result* r;
  tm* m;
  size_t i, j;
  diagnostic_start(o.diagnostic);
  if (!out) return TESS_INVALID_INPUT;
  *out = NULL;
  if (!in || !in->xyz || !in->ring_offsets || in->vertex_count < 3 ||
      in->vertex_count > SIZE_MAX / 3 || !in->ring_count ||
      in->ring_count > in->vertex_count / 3 || o.chart_axis < -1 ||
      o.chart_axis > 2 || (!!o.allocator.allocate != !!o.allocator.release) ||
      o.max_limbs > (size_t)INT_MAX / 64)
    return TESS_INVALID_INPUT;
  if (in->ring_offsets[0] ||
      in->ring_offsets[in->ring_count] != in->vertex_count)
    return TESS_INVALID_INPUT;
  for (i = 0; i < in->ring_count; i++)
    if (in->ring_offsets[i] > in->ring_offsets[i + 1] ||
        in->ring_offsets[i + 1] - in->ring_offsets[i] < 3)
      return TESS_INVALID_INPUT;
  if ((o.max_bytes ? o.max_bytes : tess_default_options().max_bytes) <
      sizeof(*r)) {
    if (o.diagnostic) o.diagnostic->status = TESS_RESOURCE_LIMIT;
    return TESS_RESOURCE_LIMIT;
  }
  r = o.allocator.allocate ? o.allocator.allocate(sizeof(*r), o.allocator.user)
                           : malloc(sizeof(*r));
  if (!r) {
    if (o.diagnostic) o.diagnostic->status = TESS_ALLOCATION_FAILURE;
    return TESS_ALLOCATION_FAILURE;
  }
  memset(r, 0, sizeof(*r));
  m = &r->mesh;
  tm_init(m);
  m->c.allocator = o.allocator;
  if (o.max_vertices) m->max_vertices = o.max_vertices;
  if (o.max_faces) m->max_faces = o.max_faces;
  if (o.max_limbs) m->c.max_limbs = o.max_limbs;
  m->c.max_bytes =
      (o.max_bytes ? o.max_bytes : tess_default_options().max_bytes) -
      sizeof(*r);
  if (o.max_operations) m->c.max_ops = o.max_operations;
  if (in->vertex_count > m->max_vertices) {
    m->c.status = TESS_RESOURCE_LIMIT;
    diagnostic_finish(o.diagnostic, r);
    tess_result_free(r);
    return TESS_RESOURCE_LIMIT;
  }
  m->vcap = m->nv = in->vertex_count;
  m->v = tx_alloc(&m->c, m->nv, sizeof(tv));
  if (!m->v) m->nv = 0;
  for (i = 0; i < m->nv && !m->c.status; i++) {
    for (j = 0; j < 3; j++)
      qr_import(&m->c, &m->v[i].p[j], &in->xyz[3 * i + j]);
    if (m->c.status == TESS_INVALID_INPUT) {
      m->diagnostic.reason = TESS_DIAG_COORDINATE;
      m->diagnostic.vertex_a = i;
    }
    m->v[i].source = i;
    m->v[i].id = i;
    m->next_id = m->nv;
  }
  m->nr = in->ring_count;
  m->rings = tx_alloc(&m->c, m->nr + 1, sizeof(size_t));
  if (m->rings)
    for (i = 0; i <= m->nr; i++) m->rings[i] = in->ring_offsets[i];
  if (!m->c.status && tg_prepare(m, o.chart_axis, o.strict_planar)) tg_seed(m);
  if (!m->c.status) freeze(r, o);
  diagnostic_finish(o.diagnostic, r);
  if (m->c.status) {
    tess_status status = m->c.status;
    tess_result_free(r);
    return status;
  }
  *out = r;
  return TESS_OK;
}
tess_status tess_coordinate(const tess_result* r, size_t vertex, int axis,
                            tess_rational* out) {
  const qr* q;
  if (!r || !out || vertex >= r->mesh.nv || axis < 0 || axis > 2)
    return TESS_INVALID_INPUT;
  q = &r->mesh.v[vertex].p[axis];
  *out = (tess_rational){q->n.sign, q->n.v, q->n.n, q->d.v, q->d.n};
  return TESS_OK;
}
size_t tess_vertex_source(const tess_result* r, size_t vertex) {
  return r && vertex < r->mesh.nv ? r->mesh.v[vertex].source : SIZE_MAX;
}
size_t tess_constraint_count(const tess_result* r) {
  size_t i, n = 0;
  if (r)
    for (i = 0; i < r->mesh.ne; i++) n += r->mesh.e[i].constraint != 0;
  return n;
}
tess_status tess_constraint(const tess_result* r, size_t index,
                            size_t endpoints[2], size_t* source) {
  size_t i, n = 0;
  if (!r || !endpoints) return TESS_INVALID_INPUT;
  for (i = 0; i < r->mesh.ne; i++)
    if (r->mesh.e[i].constraint) {
      if (n++ == index) {
        endpoints[0] = r->mesh.e[i].a;
        endpoints[1] = r->mesh.e[i].b;
        if (source) *source = r->mesh.e[i].source;
        return TESS_OK;
      }
    }
  return TESS_INVALID_INPUT;
}

tess_status tess_measure(tess_result* r, const tess_rational* target,
                         tess_quality* report) {
  qr q = {0};
  tm work;
  tess_status status;
  size_t total;
  if (!r || !report) return TESS_INVALID_INPUT;
  memset(report, 0, sizeof(*report));
  work = r->mesh;
  tx_init(&work.c);
  work.c.allocator = r->mesh.c.allocator;
  work.c.max_bytes = r->mesh.c.max_bytes - r->mesh.c.bytes;
  work.c.max_ops = r->mesh.c.max_ops - r->mesh.c.ops;
  work.c.max_limbs = r->mesh.c.max_limbs;
  if (target) {
    qr_import(&work.c, &q, target);
    if (q.n.sign <= 0 && !work.c.status) work.c.status = TESS_INVALID_INPUT;
  }
  status = work.c.status ? work.c.status
                         : tg_quality(&work, target ? &q : NULL, report);
  qr_clear(&work.c, &q);
  r->mesh.c.ops += work.c.ops;
  total = r->mesh.c.bytes + r->seed.c.bytes + r->control.bytes + sizeof(*r) +
          work.c.peak;
  if (total > r->peak_bytes) r->peak_bytes = total;
  report->operations = r->mesh.c.ops + r->seed.c.ops + r->control_ops_total;
  report->peak_bytes = r->peak_bytes;
  return status;
}

size_t tess_vertex_id(const tess_result* r, size_t vertex) {
  return r && vertex < r->mesh.nv ? r->mesh.v[vertex].id : SIZE_MAX;
}
tess_status tess_constraint_parameter(const tess_result* r, size_t index,
                                      int endpoint, tess_rational* parameter) {
  size_t i, n = 0;
  const qr* q;
  if (!r || !parameter || (endpoint != 0 && endpoint != 1))
    return TESS_INVALID_INPUT;
  for (i = 0; i < r->mesh.ne; i++)
    if (r->mesh.e[i].constraint && n++ == index) {
      q = endpoint ? &r->mesh.e[i].tb : &r->mesh.e[i].ta;
      *parameter = (tess_rational){q->n.sign, q->n.v, q->n.n, q->d.v, q->d.n};
      return TESS_OK;
    }
  return TESS_INVALID_INPUT;
}

tess_status tess_target_area(const tess_result* r, tess_rational* out) {
  const qr* q;
  if (!r || !out || !r->remeshed) return TESS_INVALID_INPUT;
  q = &r->target;
  *out = (tess_rational){q->n.sign, q->n.v, q->n.n, q->d.v, q->d.n};
  return TESS_OK;
}
tess_status tess_result_quality(const tess_result* r, tess_quality* out) {
  if (!r || !out || r->remeshed != 2) return TESS_INVALID_INPUT;
  *out = r->quality;
  out->operations = r->mesh.c.ops + r->seed.c.ops + r->control_ops_total;
  out->peak_bytes = r->peak_bytes;
  return TESS_OK;
}

size_t tess_triangle_id(const tess_result* r, size_t index) {
  return r && index < r->mesh.nf ? r->mesh.f[index].id : SIZE_MAX;
}
tess_status tess_constraint_details(const tess_result* r, size_t index,
                                    tess_constraint_info* out) {
  size_t i, n = 0;
  if (!r || !out) return TESS_INVALID_INPUT;
  for (i = 0; i < r->mesh.ne; i++)
    if (r->mesh.e[i].constraint && n++ == index) {
      const te* e = &r->mesh.e[i];
      *out = (tess_constraint_info){e->a,     e->b,          e->source,
                                    e->owner, e->constraint, e->tag};
      return TESS_OK;
    }
  return TESS_INVALID_INPUT;
}

tess_status tess_reference_deviation(const tess_result* r, tess_rational* out) {
  const qr* q;
  if (!r || !out || r->remeshed != 2 || !r->deviation.d.n)
    return TESS_INVALID_INPUT;
  q = &r->deviation;
  *out = (tess_rational){q->n.sign, q->n.v, q->n.n, q->d.v, q->d.n};
  return TESS_OK;
}
