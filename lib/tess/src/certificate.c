/* SPDX-License-Identifier: MIT */
#include <inttypes.h>
#include <string.h>

#include "edits.h"
#include "result.h"
static void wn(FILE* f, size_t n) { fprintf(f, "%zu\n", n); }
static void source_write(FILE* f, size_t source) {
  wn(f, source == SIZE_MAX ? 0 : source + 1);
}
static size_t constraints(const tm* m) {
  size_t i, n = 0;
  for (i = 0; i < m->ne; i++) n += m->e[i].constraint != 0;
  return n;
}
static uint64_t bits(double value) {
  uint64_t u;
  memcpy(&u, &value, 8);
  return u;
}
static void wh(FILE* f, uint64_t value) {
  fprintf(f, "%016" PRIx64 "\n", value);
}
static tess_status wm(FILE* f, const tm* m, int v2, size_t max_bytes,
                      size_t max_ops) {
  size_t i, j, *order = NULL, n = 0;
  tx c;
  tx_init(&c);
  c.max_limbs = m->c.max_limbs;
  c.max_bytes = max_bytes;
  c.max_ops = max_ops;
  c.allocator = m->c.allocator;
  if (v2) {
    order = tx_alloc(&c, m->ne, sizeof(size_t));
    if (!order) return c.status;
    for (i = 0; i < m->ne; i++)
      if (m->e[i].constraint) order[n++] = i;
    for (i = 1; i < n; i++) {
      size_t value = order[i];
      j = i;
      while (j && (m->e[order[j - 1]].owner > m->e[value].owner ||
                   (m->e[order[j - 1]].owner == m->e[value].owner &&
                    qr_cmp(&c, &m->e[order[j - 1]].ta, &m->e[value].ta) > 0))) {
        order[j] = order[j - 1];
        j--;
      }
      order[j] = value;
    }
  }
  wn(f, m->nv);
  wn(f, m->nf);
  wn(f, constraints(m));
  wn(f, (size_t)m->axis);
  wn(f, (size_t)m->u);
  wn(f, (size_t)m->w);
  wn(f, m->orientation < 0 ? 0 : 1);
  wn(f, (size_t)m->planar);
  for (i = 0; i < m->nv; i++) {
    source_write(f, m->v[i].source);
    wn(f, (size_t)m->v[i].pinned);
    if (v2) wn(f, m->v[i].id);
    for (j = 0; j < 3; j++) {
      qr_write(f, &m->v[i].p[j]);
      fputc('\n', f);
    }
  }
  for (i = 0; i < m->nf; i++) {
    for (j = 0; j < 3; j++) wn(f, m->f[i].v[j]);
    if (v2) wn(f, m->f[i].id);
  }
  for (i = 0; i < (v2 ? n : m->ne); i++) {
    const te* e = &m->e[v2 ? order[i] : i];
    if (!e->constraint) continue;
    wn(f, e->a);
    wn(f, e->b);
    wn(f, (size_t)e->constraint);
    source_write(f, e->source);
    if (v2) {
      wn(f, e->owner);
      qr_write(f, &e->ta);
      fputc('\n', f);
      qr_write(f, &e->tb);
      fputc('\n', f);
      wh(f, e->tag);
    }
  }
  tx_free(&c, order, m->ne * sizeof(size_t));
  return c.status;
}
static void write_run(FILE* f, const tess_result* r) {
  const tess_remesh_options* o = &r->remesh_options;
  size_t i;
  fputs("RUN2\n", f);
  wn(f, o->target_count);
  qr_write(f, &r->target);
  fputc('\n', f);
  qr_write(f, &r->tolerance);
  fputc('\n', f);
  wn(f, !!o->subdivide_boundary);
  wn(f, !!o->subdivide_features);
  wn(f, o->boundary_owners != NULL);
  wn(f, o->boundary_owner_count);
  for (i = 0; i < o->boundary_owner_count; i++) wn(f, o->boundary_owners[i]);
  wh(f, bits(o->max_area_cv));
  wh(f, bits(o->min_fraction_target_band));
  wh(f, bits(o->min_angle_p05));
  wn(f, o->max_passes);
  wn(f, o->max_edits);
  wn(f, o->max_candidates);
  wn(f, r->options.max_vertices);
  wn(f, r->options.max_faces);
  wn(f, r->options.max_limbs);
  wn(f, r->options.max_bytes);
  wn(f, r->options.max_operations);
}
/* Conservative preflight bound: serialization is also subject to the
   configured byte limit, including when the destination is a nonseekable FILE.
 */
static int serial_add(size_t* used, size_t count, size_t width, size_t limit) {
  if (*used > limit || (width && count > (limit - *used) / width)) return 0;
  *used += count * width;
  return 1;
}
static int serial_q(size_t* used, const qr* q, size_t limit) {
  return serial_add(used, q->n.n, 8, limit) &&
         serial_add(used, q->d.n, 8, limit) && serial_add(used, 4, 1, limit);
}
static int serial_mesh(size_t* used, const tm* m, int v2, size_t limit) {
  const size_t nat = 3 * sizeof(size_t) + 2;
  size_t i, j;
  if (!serial_add(used, 8, nat, limit) ||
      !serial_add(used, m->nv, (v2 ? 3 : 2) * nat, limit) ||
      !serial_add(used, m->nf, (v2 ? 4 : 3) * nat, limit))
    return 0;
  for (i = 0; i < m->nv; i++)
    for (j = 0; j < 3; j++)
      if (!serial_q(used, &m->v[i].p[j], limit)) return 0;
  for (i = 0; i < m->ne; i++)
    if (m->e[i].constraint) {
      if (!serial_add(used, v2 ? 5 : 4, nat, limit)) return 0;
      if (v2 && (!serial_add(used, 17, 1, limit) ||
                 !serial_q(used, &m->e[i].ta, limit) ||
                 !serial_q(used, &m->e[i].tb, limit)))
        return 0;
    }
  return 1;
}
static int serialization_budget(const tess_result* r, int v2) {
  size_t used = 0, limit = r->options.max_bytes
                               ? r->options.max_bytes
                               : tess_default_options().max_bytes;
  if (!serial_add(&used, 1024, 1, limit) ||
      !serial_add(&used, r->seed.nr, 3 * sizeof(size_t) + 2, limit))
    return 0;
  if (v2 && (!serial_q(&used, &r->target, limit) ||
             !serial_q(&used, &r->tolerance, limit) ||
             !serial_add(&used, r->remesh_options.boundary_owner_count,
                         3 * sizeof(size_t) + 2, limit)))
    return 0;
  return serial_mesh(&used, &r->seed, v2, limit) &&
         serial_mesh(&used, &r->mesh, v2, limit);
}
tess_status tess_write_certificate(const tess_result* r, FILE* f) {
  size_t i;
  tess_status status;
  int v2;
  if (!r || !f) return TESS_INVALID_INPUT;
  v2 = r->remeshed != 0;
  if (v2 && !tx_binary64_supported()) return TESS_INVALID_INPUT;
  if (!serialization_budget(r, v2)) return TESS_RESOURCE_LIMIT;
  if (!v2)
    for (i = 0; i < r->seed.ne; i++)
      if (r->seed.e[i].constraint == 3 || r->seed.e[i].tag)
        return TESS_INVALID_INPUT;
  if (fputs(v2 ? "TESS2\n" TESS_SEED_POLICY "\n"
               : "TESS1\n" TESS_SEED_POLICY "\n",
            f) == EOF)
    return TESS_IO_ERROR;
  wn(f, (size_t)(r->options.chart_axis + 1));
  wn(f, !!r->options.strict_planar);
  wn(f, r->seed.nr);
  for (i = 0; i <= r->seed.nr; i++) wn(f, r->seed.rings[i]);
  if (v2) write_run(f, r);
  status = wm(f, &r->seed, v2, r->mesh.c.max_bytes - r->mesh.c.bytes,
              r->mesh.c.max_ops - r->mesh.c.ops);
  if (status) return status;
  status = wm(f, &r->mesh, v2, r->mesh.c.max_bytes - r->mesh.c.bytes,
              r->mesh.c.max_ops - r->mesh.c.ops);
  if (status) return status;
  if (fputs("END\n", f) == EOF || ferror(f)) return TESS_IO_ERROR;
  return TESS_OK;
}
typedef struct {
  const char *p, *end;
} reader;
static int literal(tx* c, reader* r, const char* s) {
  size_t n = strlen(s);
  if ((size_t)(r->end - r->p) < n || memcmp(r->p, s, n)) {
    c->status = TESS_CERTIFICATE_REJECTED;
    return 0;
  }
  r->p += n;
  return 1;
}
static size_t rn(tx* c, reader* r, size_t maximum) {
  size_t n = 0;
  const char* start = r->p;
  if (c->status) return 0;
  while (r->p < r->end && *r->p != '\n') {
    unsigned d = (unsigned char)*r->p - '0';
    if (d > 9 || n > maximum / 10 || (n == maximum / 10 && d > maximum % 10)) {
      c->status = TESS_CERTIFICATE_REJECTED;
      return 0;
    }
    n = n * 10 + d;
    r->p++;
  }
  if (r->p == r->end || r->p == start || (r->p - start > 1 && *start == '0')) {
    c->status = TESS_CERTIFICATE_REJECTED;
    return 0;
  }
  r->p++;
  return n;
}
static size_t source_read(tx* c, reader* r) {
  size_t n = rn(c, r, SIZE_MAX);
  return n ? n - 1 : SIZE_MAX;
}
static uint64_t rh(tx* c, reader* r) {
  uint64_t n = 0;
  size_t i;
  if (c->status) return 0;
  if ((size_t)(r->end - r->p) < 17 || r->p[16] != '\n') {
    c->status = TESS_CERTIFICATE_REJECTED;
    return 0;
  }
  for (i = 0; i < 16; i++) {
    unsigned char h = (unsigned char)r->p[i];
    unsigned d;
    if (h >= '0' && h <= '9')
      d = h - '0';
    else if (h >= 'a' && h <= 'f')
      d = h - 'a' + 10;
    else {
      c->status = TESS_CERTIFICATE_REJECTED;
      return 0;
    }
    n = (n << 4) | d;
  }
  r->p += 17;
  return n;
}
static void rz(tx* c, reader* r, zi* z, char delimiter) {
  const char* start;
  size_t digits, i;
  int negative = 0;
  if (c->status) return;
  if (r->p < r->end && *r->p == '-') {
    negative = 1;
    r->p++;
  }
  start = r->p;
  while (r->p < r->end && *r->p != delimiter) {
    char h = *r->p;
    if (!((h >= '0' && h <= '9') || (h >= 'a' && h <= 'f'))) {
      c->status = TESS_CERTIFICATE_REJECTED;
      return;
    }
    r->p++;
    if ((size_t)(r->p - start) > c->max_limbs * 8) {
      c->status = TESS_RESOURCE_LIMIT;
      return;
    }
  }
  digits = (size_t)(r->p - start);
  if (r->p == r->end || !digits) {
    c->status = TESS_CERTIFICATE_REJECTED;
    return;
  }
  r->p++;
  if (digits == 1 && *start == '0' && !negative) return;
  if (digits % 8) {
    c->status = TESS_CERTIFICATE_REJECTED;
    return;
  }
  z->n = digits / 8;
  z->v = tx_alloc(c, z->n, sizeof(uint32_t));
  if (!z->v) {
    z->n = 0;
    return;
  }
  z->sign = negative ? -1 : 1;
  for (i = 0; i < digits; i++) {
    char h = start[digits - 1 - i];
    unsigned x = h <= '9' ? (unsigned)(h - '0') : (unsigned)(h - 'a' + 10);
    z->v[i / 8] |= (uint32_t)x << (4 * (i % 8));
  }
  if (!z->v[z->n - 1]) c->status = TESS_CERTIFICATE_REJECTED;
}
static void rq(tx* c, reader* r, qr* q) {
  zi n = {0}, d = {0};
  tess_rational parts;
  rz(c, r, &n, '/');
  rz(c, r, &d, '\n');
  if (!c->status) {
    parts = (tess_rational){n.sign, n.v, n.n, d.v, d.n};
    if (d.sign != 1)
      c->status = TESS_CERTIFICATE_REJECTED;
    else
      qr_import(c, q, &parts);
    if (!c->status && (zi_cmp(&q->n, &n) || zi_cmp(&q->d, &d)))
      c->status = TESS_CERTIFICATE_REJECTED;
  }
  zi_clear(c, &n);
  zi_clear(c, &d);
}
static int rm(tm* m, reader* r, const tm* request, int v2) {
  size_t nv, nf, ne, i, j, axis, u, w, orientation, planar;
  nv = rn(&m->c, r, m->max_vertices);
  nf = rn(&m->c, r, m->max_faces);
  if (nf > SIZE_MAX / 3 || nv > SIZE_MAX - 3 * nf) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  ne = rn(&m->c, r, nv + nf * 3);
  axis = rn(&m->c, r, 2);
  u = rn(&m->c, r, 2);
  w = rn(&m->c, r, 2);
  orientation = rn(&m->c, r, 1);
  planar = rn(&m->c, r, 1);
  if (nv < request->rings[request->nr] || !nf || axis == u || axis == w ||
      u == w) {
    m->c.status = TESS_CERTIFICATE_REJECTED;
    return 0;
  }
  m->axis = (int)axis;
  m->u = (int)u;
  m->w = (int)w;
  m->orientation = orientation ? 1 : -1;
  m->planar = (int)planar;
  m->nr = request->nr;
  m->rings = tx_alloc(&m->c, m->nr + 1, sizeof(size_t));
  if (m->rings) memcpy(m->rings, request->rings, (m->nr + 1) * sizeof(size_t));
  m->v = tx_alloc(&m->c, nv, sizeof(tv));
  if (m->v) {
    m->nv = m->vcap = nv;
    for (i = 0; i < nv && !m->c.status; i++) {
      m->v[i].source = source_read(&m->c, r);
      m->v[i].pinned = (int)rn(&m->c, r, 1);
      m->v[i].id = v2 ? rn(&m->c, r, SIZE_MAX - 1) : i;
      for (j = 0; j < 3; j++) rq(&m->c, r, &m->v[i].p[j]);
    }
  }
  m->f = tx_alloc(&m->c, nf, sizeof(tf));
  if (m->f) {
    m->nf = m->fcap = nf;
    for (i = 0; i < nf && !m->c.status; i++) {
      for (j = 0; j < 3; j++) m->f[i].v[j] = rn(&m->c, r, nv - 1);
      m->f[i].id = v2 ? rn(&m->c, r, SIZE_MAX - 1) : i;
    }
  }
  m->e = tx_alloc(&m->c, ne, sizeof(te));
  if (m->e) {
    m->ne = m->ecap = ne;
    for (i = 0; i < ne && !m->c.status; i++) {
      m->e[i].a = rn(&m->c, r, nv - 1);
      m->e[i].b = rn(&m->c, r, nv - 1);
      m->e[i].constraint = (int)rn(&m->c, r, v2 ? 3 : 2);
      m->e[i].source = source_read(&m->c, r);
      if (v2) {
        m->e[i].owner = rn(&m->c, r, SIZE_MAX);
        rq(&m->c, r, &m->e[i].ta);
        rq(&m->c, r, &m->e[i].tb);
        m->e[i].tag = rh(&m->c, r);
      } else {
        m->e[i].owner = i;
        qr_i64(&m->c, &m->e[i].ta, 0);
        qr_i64(&m->c, &m->e[i].tb, 1);
      }
      if (!m->e[i].constraint || m->e[i].a == m->e[i].b)
        m->c.status = TESS_CERTIFICATE_REJECTED;
    }
  }
  return !m->c.status;
}
static int edges_equal(tm* a, const te* e, size_t ne, int v2) {
  size_t i, j, n = 0;
  for (i = 0; i < a->ne; i++)
    if (a->e[i].constraint) {
      size_t matches = 0;
      n++;
      for (j = 0; j < ne; j++)
        if (a->e[i].constraint == e[j].constraint &&
            a->e[i].source == e[j].source && a->e[i].a == e[j].a &&
            a->e[i].b == e[j].b &&
            (!v2 || (a->e[i].owner == e[j].owner && a->e[i].tag == e[j].tag &&
                     !qr_cmp(&a->c, &a->e[i].ta, &e[j].ta) &&
                     !qr_cmp(&a->c, &a->e[i].tb, &e[j].tb))))
          matches++;
      if (matches != 1) return 0;
    }
  return n == ne;
}
static int same_input(tm* m, const tm* request) {
  size_t i, j;
  if (m->nv != request->nv) return 0;
  for (i = 0; i < m->nv; i++) {
    if (m->v[i].source != i || m->v[i].pinned != 1 ||
        m->v[i].id != request->v[i].id)
      return 0;
    for (j = 0; j < 3; j++)
      if (qr_cmp(&m->c, &m->v[i].p[j], &request->v[i].p[j])) return 0;
  }
  return !m->c.status;
}
static int seed_validate(tm* m, const tess_result* request, int v2) {
  te* e = m->e;
  size_t ne = m->ne, cap = m->ecap;
  int axis = m->axis, u = m->u, w = m->w, orientation = m->orientation,
      planar = m->planar, ok = 0;
  m->e = NULL;
  m->ne = m->ecap = 0;
  if (!same_input(m, &request->seed)) goto end;
  /* Every version binds the frozen reference connectivity. Version 2 also
     carries stable face IDs and complete constraint metadata. */
  {
    if (m->nf != request->seed.nf) goto end;
    for (size_t i = 0; i < m->nf; i++) {
      if (v2 && m->f[i].id != request->seed.f[i].id) goto end;
      for (size_t j = 0; j < 3; j++)
        if (m->f[i].v[j] != request->seed.f[i].v[j]) goto end;
    }
    m->e = e;
    m->ne = ne;
    m->ecap = cap;
    int bound = edges_equal(m, request->seed.e, request->seed.ne, v2);
    m->e = NULL;
    m->ne = m->ecap = 0;
    if (!bound) goto end;
  }

  if (!tg_prepare(m, request->options.chart_axis,
                  request->options.strict_planar))
    goto end;
  if (m->axis != axis || m->u != u || m->w != w ||
      m->orientation != orientation || m->planar != planar)
    goto end;
  if (!tg_protect_creases(m)) goto end;
  if (v2)
    for (size_t i = 0; i < request->seed.ne; i++) {
      const te* feature = &request->seed.e[i];
      if (feature->constraint == 3 || feature->tag)
        if (!tg_tag_seed_edge(m, feature->a, feature->b, feature->tag))
          goto end;
    }
  if (!edges_equal(m, e, ne, v2) || !tg_validate(m) || !tg_audit3(m)) goto end;
  ok = 1;
end:
  for (size_t i = 0; i < ne; i++) {
    qr_clear(&m->c, &e[i].ta);
    qr_clear(&m->c, &e[i].tb);
  }
  tx_free(&m->c, e, cap * sizeof(te));
  return ok;
}
static int read_run(tm* seed, reader* r, const tess_result* request, qr* target,
                    qr* tolerance) {
  const tess_remesh_options* o = &request->remesh_options;
  size_t i, n;
  tx* c = &seed->c;
  if (!literal(c, r, "RUN2\n")) return 0;
  if (rn(c, r, SIZE_MAX) != o->target_count) return 0;
  rq(c, r, target);
  rq(c, r, tolerance);
  if (qr_cmp(c, target, &request->target) ||
      qr_cmp(c, tolerance, &request->tolerance))
    return 0;
  if (rn(c, r, 1) != (size_t)!!o->subdivide_boundary ||
      rn(c, r, 1) != (size_t)!!o->subdivide_features ||
      rn(c, r, 1) != (size_t)(o->boundary_owners != NULL))
    return 0;
  n = rn(c, r, seed->max_vertices);
  if (n != o->boundary_owner_count) return 0;
  for (i = 0; i < n; i++)
    if (rn(c, r, SIZE_MAX) != o->boundary_owners[i]) return 0;
  if (rh(c, r) != bits(o->max_area_cv) ||
      rh(c, r) != bits(o->min_fraction_target_band) ||
      rh(c, r) != bits(o->min_angle_p05))
    return 0;
  if (rn(c, r, SIZE_MAX) != o->max_passes ||
      rn(c, r, SIZE_MAX) != o->max_edits ||
      rn(c, r, SIZE_MAX) != o->max_candidates)
    return 0;
  if (rn(c, r, SIZE_MAX) != request->options.max_vertices ||
      rn(c, r, SIZE_MAX) != request->options.max_faces ||
      rn(c, r, SIZE_MAX) != request->options.max_limbs ||
      rn(c, r, SIZE_MAX) != request->options.max_bytes ||
      rn(c, r, SIZE_MAX) != request->options.max_operations)
    return 0;
  return !c->status;
}
static int ids_unique(tm* m) {
  size_t i, j;
  for (i = 0; i < m->nv; i++)
    for (j = 0; j < i; j++)
      if (m->v[i].id == m->v[j].id) return 0;
  for (i = 0; i < m->nf; i++)
    for (j = 0; j < i; j++)
      if (m->f[i].id == m->f[j].id) return 0;
  return 1;
}
tess_status tess_check_certificate(const tess_result* request,
                                   const char* bytes, size_t length) {
  tm seed, out;
  reader r;
  size_t nr, i, axis, strict;
  qr zero = {0}, target = {0}, tolerance = {0};
  int v2 = 0;
  tess_status status = TESS_CERTIFICATE_REJECTED;
  tess_options o;
  if (!request || !bytes) return TESS_INVALID_INPUT;
  o = tess_default_options();
  tm_init(&seed);
  tm_init(&out);
  seed.c.allocator = out.c.allocator = request->options.allocator;
  seed.max_vertices = out.max_vertices = request->mesh.max_vertices;
  seed.max_faces = out.max_faces = request->mesh.max_faces;
  seed.c.max_limbs = out.c.max_limbs = request->mesh.c.max_limbs;
  seed.c.max_bytes =
      request->options.max_bytes ? request->options.max_bytes : o.max_bytes;
  seed.c.max_ops = request->options.max_operations
                       ? request->options.max_operations
                       : o.max_operations;
  if (length > seed.c.max_bytes) {
    status = TESS_RESOURCE_LIMIT;
    goto end;
  }
  r = (reader){bytes, bytes + length};
  if (length >= 6 && !memcmp(bytes, "TESS2\n", 6)) v2 = 1;
  if (v2 != (request->remeshed != 0)) goto end;
  if (!literal(&seed.c, &r,
               v2 ? "TESS2\n" TESS_SEED_POLICY "\n"
                  : "TESS1\n" TESS_SEED_POLICY "\n"))
    goto end;
  axis = rn(&seed.c, &r, 3);
  strict = rn(&seed.c, &r, 1);
  nr = rn(&seed.c, &r, seed.max_vertices / 3);
  if (axis != (size_t)(request->options.chart_axis + 1) ||
      strict != (size_t)!!request->options.strict_planar ||
      nr != request->seed.nr)
    goto end;
  for (i = 0; i <= nr; i++)
    if (rn(&seed.c, &r, request->seed.nv) != request->seed.rings[i]) goto end;
  if (v2 && !read_run(&seed, &r, request, &target, &tolerance)) goto end;
  if (!rm(&seed, &r, &request->seed, v2) || !seed_validate(&seed, request, v2))
    goto end;
  out.c.max_bytes = seed.c.max_bytes - seed.c.bytes;
  out.c.max_ops = seed.c.max_ops - seed.c.ops;
  if (!rm(&out, &r, &request->seed, v2)) goto end;
  if (!literal(&out.c, &r, "END\n") || r.p != r.end) goto end;
  if (out.axis != seed.axis || out.u != seed.u || out.w != seed.w ||
      out.orientation != seed.orientation || out.planar != seed.planar ||
      out.nv < seed.nv)
    goto end;
  if (!v2 && !edges_equal(&seed, out.e, out.ne, 0)) goto end;
  for (i = 0; i < seed.nv; i++) {
    size_t j;
    if (out.v[i].source != seed.v[i].source ||
        out.v[i].pinned != seed.v[i].pinned ||
        (v2 && out.v[i].id != seed.v[i].id))
      goto end;
    for (j = 0; j < 3; j++)
      if (qr_cmp(&out.c, &out.v[i].p[j], &seed.v[i].p[j])) goto end;
  }
  if (v2) {
    out.approximate = tolerance.n.sign > 0;
    if (!ids_unique(&out) || !ids_unique(&seed) ||
        !tg_check_chains(&out, &seed, &request->remesh_options))
      goto end;
  }
  if (!tg_validate(&out) || !tg_audit3(&out)) goto end;
  if (!v2) qr_i64(&out.c, &zero, 0);
  if (!tg_reference(&out, &seed, v2 ? &tolerance : &zero)) goto end;
  status = TESS_OK;
end:
  if (seed.c.status == TESS_RESOURCE_LIMIT ||
      seed.c.status == TESS_ALLOCATION_FAILURE)
    status = seed.c.status;
  if (out.c.status == TESS_RESOURCE_LIMIT ||
      out.c.status == TESS_ALLOCATION_FAILURE)
    status = out.c.status;
  qr_clear(&out.c, &zero);
  qr_clear(&seed.c, &target);
  qr_clear(&seed.c, &tolerance);
  tm_clear(&seed);
  tm_clear(&out);
  return status;
}
