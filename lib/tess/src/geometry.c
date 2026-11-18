/* SPDX-License-Identifier: MIT */
#include "geometry.h"

#include <stdlib.h>
#include <string.h>

#include "bounds.h"
void tm_init(tm* m) {
  memset(m, 0, sizeof(*m));
  tx_init(&m->c);
  m->diagnostic = (tess_diagnostic){.status = TESS_OK,
                                    .reason = TESS_DIAG_NONE,
                                    .axis = -1,
                                    .ring = SIZE_MAX,
                                    .other_ring = SIZE_MAX,
                                    .vertex_a = SIZE_MAX,
                                    .vertex_b = SIZE_MAX,
                                    .edge_a = SIZE_MAX,
                                    .edge_b = SIZE_MAX,
                                    .face_a = SIZE_MAX,
                                    .face_b = SIZE_MAX};
  m->max_vertices = 10000;
  m->max_faces = 20000;
  m->max_edits = 10000;
}
void tm_clear(tm* m) {
  size_t i, j;
  for (i = 0; i < m->nv; i++)
    for (j = 0; j < 3; j++) qr_clear(&m->c, &m->v[i].p[j]);
  tx_free(&m->c, m->v, m->vcap * sizeof(tv));
  tx_free(&m->c, m->f, m->fcap * sizeof(tf));
  for (i = 0; i < m->ne; i++) {
    qr_clear(&m->c, &m->e[i].ta);
    qr_clear(&m->c, &m->e[i].tb);
  }
  tx_free(&m->c, m->e, m->ecap * sizeof(te));
  tx_free(&m->c, m->rings, (m->nr + 1) * sizeof(size_t));
  {
    tx diagnostics = m->c;
    memset(m, 0, sizeof(*m));
    m->c = diagnostics;
  }
}
static int grow(tm* m, void** p, size_t* cap, size_t n, size_t s) {
  void* v;
  size_t nc;
  if (n <= *cap) return 1;
  nc = *cap ? *cap : 8;
  while (nc < n) {
    if (nc > SIZE_MAX / 2) {
      m->c.status = TESS_RESOURCE_LIMIT;
      return 0;
    }
    nc *= 2;
  }
  v = tx_alloc(&m->c, nc, s);
  if (!v) return 0;
  if (*p) memcpy(v, *p, *cap * s);
  tx_free(&m->c, *p, *cap * s);
  *p = v;
  *cap = nc;
  return 1;
}
int tg_add_vertex(tm* m, const double p[3], size_t source) {
  size_t j;
  if (m->nv >= m->max_vertices) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  if (!grow(m, (void**)&m->v, &m->vcap, m->nv + 1, sizeof(tv))) return 0;
  for (j = 0; j < 3; j++) qr_double(&m->c, &m->v[m->nv].p[j], p[j]);
  m->v[m->nv].source = source;
  m->v[m->nv].id = m->next_id++;
  m->nv++;
  return !m->c.status;
}
int tg_add_face(tm* m, size_t a, size_t b, size_t c) {
  tf* f;
  if (m->nf >= m->max_faces) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  if (!grow(m, (void**)&m->f, &m->fcap, m->nf + 1, sizeof(tf))) return 0;
  f = &m->f[m->nf++];
  f->id = m->next_face_id++;
  f->v[0] = a;
  f->v[1] = b;
  f->v[2] = c;
  return 1;
}
static int edge(tm* m, size_t a, size_t b, int constraint) {
  te* e;
  if (!grow(m, (void**)&m->e, &m->ecap, m->ne + 1, sizeof(te))) return 0;
  e = &m->e[m->ne++];
  e->a = a;
  e->b = b;
  e->constraint = constraint;
  e->source = m->ne - 1;
  e->owner = e->source;
  if (constraint) {
    qr_i64(&m->c, &e->ta, 0);
    qr_i64(&m->c, &e->tb, 1);
  }
  if (constraint == 1) m->v[a].pinned = m->v[b].pinned = 1;
  return 1;
}
int tg_orient_q(tm* m, const qr* ax, const qr* ay, const qr* bx, const qr* by,
                const qr* cx, const qr* cy) {
  qr x = {0}, y = {0}, u = {0}, v = {0}, p = {0}, q = {0};
  int s;
  tx* c = &m->c;
  qr_sub(c, &x, bx, ax);
  qr_sub(c, &y, by, ay);
  qr_sub(c, &u, cx, ax);
  qr_sub(c, &v, cy, ay);
  qr_mul(c, &p, &x, &v);
  qr_mul(c, &q, &y, &u);
  qr_sub(c, &p, &p, &q);
  s = p.n.sign;
  qr_clear(c, &x);
  qr_clear(c, &y);
  qr_clear(c, &u);
  qr_clear(c, &v);
  qr_clear(c, &p);
  qr_clear(c, &q);
  return s;
}
int tg_orient(tm* m, size_t a, size_t b, size_t c) {
  return tg_orient_q(m, &m->v[a].p[m->u], &m->v[a].p[m->w], &m->v[b].p[m->u],
                     &m->v[b].p[m->w], &m->v[c].p[m->u], &m->v[c].p[m->w]);
}
int tg_equal(tm* m, size_t a, size_t b, int projected) {
  int j;
  for (j = 0; j < 3; j++)
    if ((!projected || j != m->axis) &&
        qr_cmp(&m->c, &m->v[a].p[j], &m->v[b].p[j]))
      return 0;
  return 1;
}
static int between(tm* m, const qr* a, const qr* b, const qr* x) {
  int ab = qr_cmp(&m->c, a, b);
  return ab <= 0 ? (qr_cmp(&m->c, a, x) <= 0 && qr_cmp(&m->c, x, b) <= 0)
                 : (qr_cmp(&m->c, b, x) <= 0 && qr_cmp(&m->c, x, a) <= 0);
}
static int on(tm* m, size_t a, size_t b, size_t x) {
  return !tg_orient(m, a, b, x) &&
         between(m, &m->v[a].p[m->u], &m->v[b].p[m->u], &m->v[x].p[m->u]) &&
         between(m, &m->v[a].p[m->w], &m->v[b].p[m->w], &m->v[x].p[m->w]);
}
/* Intersection beyond the permitted shared indexed simplex. */
int tg_segments(tm* m, size_t a, size_t b, size_t c, size_t d) {
  int x, y, z, w;
  if ((a == c && b == d) || (a == d && b == c)) return 0;
  x = tg_orient(m, a, b, c);
  y = tg_orient(m, a, b, d);
  z = tg_orient(m, c, d, a);
  w = tg_orient(m, c, d, b);
  if (x * y < 0 && z * w < 0) return 1;
  if (!x && c != a && c != b && on(m, a, b, c)) return 1;
  if (!y && d != a && d != b && on(m, a, b, d)) return 1;
  if (!z && a != c && a != d && on(m, c, d, a)) return 1;
  if (!w && b != c && b != d && on(m, c, d, b)) return 1;
  return 0;
}
static int ring_point(tm* m, size_t start, size_t end, const qr* x,
                      const qr* y) {
  size_t i;
  int inside = 0;
  for (i = start; i < end && !m->c.status; i++) {
    size_t j = i + 1 == end ? start : i + 1;
    qr *a = m->v[i].p, *b = m->v[j].p;
    int s = tg_orient_q(m, &a[m->u], &a[m->w], &b[m->u], &b[m->w], x, y);
    int ay = qr_cmp(&m->c, &a[m->w], y), by = qr_cmp(&m->c, &b[m->w], y);
    if (!s && between(m, &a[m->u], &b[m->u], x) &&
        between(m, &a[m->w], &b[m->w], y))
      return -1;
    if ((ay <= 0 && by > 0 && s > 0) || (by <= 0 && ay > 0 && s < 0))
      inside = !inside;
  }
  return inside;
}
int tg_domain(tm* m, const qr* x, const qr* y) {
  size_t r;
  int p = ring_point(m, m->rings[0], m->rings[1], x, y);
  if (p != 1) return p;
  for (r = 1; r < m->nr; r++) {
    p = ring_point(m, m->rings[r], m->rings[r + 1], x, y);
    if (p < 0) return -1;
    if (p) return 0;
  }
  return 1;
}
static void area(tm* m, size_t a, size_t b, qr* out) {
  size_t i;
  qr p = {0}, q = {0};
  qr_i64(&m->c, out, 0);
  for (i = a; i < b && !m->c.status; i++) {
    size_t j = i + 1 == b ? a : i + 1;
    qr_mul(&m->c, &p, &m->v[i].p[m->u], &m->v[j].p[m->w]);
    qr_mul(&m->c, &q, &m->v[j].p[m->u], &m->v[i].p[m->w]);
    qr_sub(&m->c, &p, &p, &q);
    qr_add(&m->c, out, out, &p);
  }
  qr_clear(&m->c, &p);
  qr_clear(&m->c, &q);
}
static int planar(tm* m) {
  size_t b = 1, k, j;
  qr n[3] = {0}, ab[3] = {0}, ac[3] = {0}, p = {0}, q = {0}, sum = {0};
  int ok = 1;
  for (k = 2; k < m->rings[1]; k++)
    if (tg_orient(m, 0, b, k)) break;
  if (k == m->rings[1]) return 0;
  for (j = 0; j < 3; j++) {
    qr_sub(&m->c, &ab[j], &m->v[b].p[j], &m->v[0].p[j]);
    qr_sub(&m->c, &ac[j], &m->v[k].p[j], &m->v[0].p[j]);
  }
  for (j = 0; j < 3; j++) {
    qr_mul(&m->c, &p, &ab[(j + 1) % 3], &ac[(j + 2) % 3]);
    qr_mul(&m->c, &q, &ab[(j + 2) % 3], &ac[(j + 1) % 3]);
    qr_sub(&m->c, &n[j], &p, &q);
  }
  for (k = 0; k < m->nv && ok && !m->c.status; k++) {
    qr_i64(&m->c, &sum, 0);
    for (j = 0; j < 3; j++) {
      qr_sub(&m->c, &p, &m->v[k].p[j], &m->v[0].p[j]);
      qr_mul(&m->c, &p, &p, &n[j]);
      qr_add(&m->c, &sum, &sum, &p);
    }
    if (sum.n.sign) {
      ok = 0;
      m->diagnostic.reason = TESS_DIAG_NONPLANAR;
      m->diagnostic.vertex_a = k;
    }
  }
  for (j = 0; j < 3; j++) {
    qr_clear(&m->c, &n[j]);
    qr_clear(&m->c, &ab[j]);
    qr_clear(&m->c, &ac[j]);
  }
  qr_clear(&m->c, &p);
  qr_clear(&m->c, &q);
  qr_clear(&m->c, &sum);
  return ok;
}
static int domain_valid(tm* m) {
  size_t i, j, r, s;
  int outer = 0;
  qr a = {0};
  /* A previous attempt (e.g. another chart axis) may have left edge tangents. */
  for (i = 0; i < m->ne; i++) {
    qr_clear(&m->c, &m->e[i].ta);
    qr_clear(&m->c, &m->e[i].tb);
  }
  m->ne = 0;
  for (r = 0; r < m->nr; r++) {
    size_t st = m->rings[r], en = m->rings[r + 1];
    if (en - st < 3) return 0;
    area(m, st, en, &a);
    if (!a.n.sign) {
      m->diagnostic.reason = TESS_DIAG_RING_AREA;
      m->diagnostic.ring = r;
      qr_clear(&m->c, &a);
      return 0;
    }
    if (!r)
      outer = a.n.sign;
    else if (a.n.sign == outer) {
      m->diagnostic.reason = TESS_DIAG_RING_WINDING;
      m->diagnostic.ring = r;
      qr_clear(&m->c, &a);
      return 0;
    }
    for (i = st; i < en; i++)
      if (!edge(m, i, i + 1 == en ? st : i + 1, 1)) {
        qr_clear(&m->c, &a);
        return 0;
      }
  }
  qr_clear(&m->c, &a);
  for (i = 0; i < m->nv; i++)
    for (j = i + 1; j < m->nv; j++)
      if (tg_equal(m, i, j, 1)) {
        m->diagnostic.reason = TESS_DIAG_PROJECTION_COLLISION;
        m->diagnostic.vertex_a = i;
        m->diagnostic.vertex_b = j;
        return 0;
      }
  for (i = 0; i < m->ne; i++)
    for (j = i + 1; j < m->ne; j++)
      if (tg_segments(m, m->e[i].a, m->e[i].b, m->e[j].a, m->e[j].b)) {
        m->diagnostic.reason = TESS_DIAG_SEGMENT_CONTACT;
        m->diagnostic.edge_a = m->e[i].a;
        m->diagnostic.edge_b = m->e[j].a;
        return 0;
      }
  for (r = 1; r < m->nr; r++) {
    i = m->rings[r];
    if (ring_point(m, 0, m->rings[1], &m->v[i].p[m->u], &m->v[i].p[m->w]) !=
        1) {
      m->diagnostic.reason = TESS_DIAG_HOLE_OUTSIDE;
      m->diagnostic.ring = r;
      m->diagnostic.vertex_a = i;
      return 0;
    }
    for (s = 1; s < m->nr; s++)
      if (s != r && ring_point(m, m->rings[s], m->rings[s + 1],
                               &m->v[i].p[m->u], &m->v[i].p[m->w]) != 0) {
        m->diagnostic.reason = TESS_DIAG_HOLE_NESTING;
        m->diagnostic.ring = r;
        m->diagnostic.other_ring = s;
        m->diagnostic.vertex_a = i;
        return 0;
      }
  }
  m->orientation = outer;
  return !m->c.status;
}
int tg_prepare(tm* m, int requested_axis, int strict) {
  qr ar[3] = {0};
  int order[3] = {0, 1, 2}, i, j, ok = 0;
  if (!m->nr || m->rings[0] || m->rings[m->nr] != m->nv) {
    m->c.status = TESS_INVALID_INPUT;
    return 0;
  }
  for (i = 0; i < 3; i++) {
    m->u = (i + 1) % 3;
    m->w = (i + 2) % 3;
    area(m, 0, m->rings[1], &ar[i]);
    ar[i].n.sign = ar[i].n.n ? 1 : 0;
  }
  for (i = 0; i < 3; i++)
    for (j = i + 1; j < 3; j++) {
      int comparison = qr_cmp(&m->c, &ar[order[j]], &ar[order[i]]);
      if (comparison > 0 || (comparison == 0 && order[j] < order[i])) {
        int t = order[i];
        order[i] = order[j];
        order[j] = t;
      }
    }
  for (i = 0; i < 3; i++) qr_clear(&m->c, &ar[i]);
  for (i = 0; i < 3 && !m->c.status; i++) {
    int ax = requested_axis >= 0 ? requested_axis : order[i];
    m->axis = ax;
    m->diagnostic.axis = ax;
    m->diagnostic.charts_tried |= 1u << (unsigned)ax;
    m->diagnostic.reason = TESS_DIAG_NONE;
    m->diagnostic.ring = m->diagnostic.other_ring = SIZE_MAX;
    m->diagnostic.vertex_a = m->diagnostic.vertex_b = SIZE_MAX;
    m->diagnostic.edge_a = m->diagnostic.edge_b = SIZE_MAX;
    m->u = (ax + 1) % 3;
    m->w = (ax + 2) % 3;
    if (domain_valid(m)) {
      if (m->orientation < 0) {
        int t = m->u;
        m->u = m->w;
        m->w = t;
      }
      m->planar = planar(m);
      if (!strict || m->planar) {
        ok = 1;
        m->diagnostic.reason = TESS_DIAG_NONE;
        break;
      }
    }
    if (requested_axis >= 0) break;
  }
  if (!ok && !m->c.status) m->c.status = TESS_UNSUPPORTED_CHART;
  return ok && !m->c.status;
}
/* Maximal noncrossing graph. Boundary subdivisions forbid diagonals through
 * vertices. */
static int visible(tm* m, size_t a, size_t b) {
  size_t i;
  qr x = {0}, y = {0};
  int ok = 0;
  for (i = 0; i < m->ne; i++) {
    te e = m->e[i];
    if ((e.a == a && e.b == b) || (e.a == b && e.b == a)) return 0;
    if (tg_segments(m, a, b, e.a, e.b)) return 0;
  }
  for (i = 0; i < m->nv; i++)
    if (i != a && i != b && on(m, a, b, i)) return 0;
  qr_mid(&m->c, &x, &m->v[a].p[m->u], &m->v[b].p[m->u]);
  qr_mid(&m->c, &y, &m->v[a].p[m->w], &m->v[b].p[m->w]);
  ok = tg_domain(m, &x, &y) == 1;
  qr_clear(&m->c, &x);
  qr_clear(&m->c, &y);
  return ok;
}
/* Compare rays a->b and a->c counterclockwise without angles. */
static int angle(tm* m, size_t a, size_t b, size_t c) {
  int by = qr_cmp(&m->c, &m->v[b].p[m->w], &m->v[a].p[m->w]);
  int cy = qr_cmp(&m->c, &m->v[c].p[m->w], &m->v[a].p[m->w]);
  int bh = by > 0 ||
           (by == 0 && qr_cmp(&m->c, &m->v[b].p[m->u], &m->v[a].p[m->u]) > 0);
  int ch = cy > 0 ||
           (cy == 0 && qr_cmp(&m->c, &m->v[c].p[m->u], &m->v[a].p[m->u]) > 0);
  int s;
  if (bh != ch) return bh ? -1 : 1;
  s = tg_orient(m, a, b, c);
  return s > 0 ? -1 : s < 0 ? 1 : 0;
}
static size_t ha(tm* m, size_t h) {
  return h % 2 ? m->e[h / 2].b : m->e[h / 2].a;
}
static size_t hb(tm* m, size_t h) { return ha(m, h ^ 1); }
/* Closed segment intersection for constructed witness paths; any contact
   with a graph segment blocks the proposal. The source edge is skipped. */
static int witness_intersects(tm* m, const qr* x, const qr* y, const qr* u,
                              const qr* v, size_t a, size_t b) {
  const qr *r = m->v[a].p, *s = m->v[b].p;
  int p = tg_orient_q(m, x, y, u, v, &r[m->u], &r[m->w]);
  int q = tg_orient_q(m, x, y, u, v, &s[m->u], &s[m->w]);
  int c = tg_orient_q(m, &r[m->u], &r[m->w], &s[m->u], &s[m->w], x, y);
  int d = tg_orient_q(m, &r[m->u], &r[m->w], &s[m->u], &s[m->w], u, v);
  if (p * q < 0 && c * d < 0) return 1;
  if (!p && between(m, x, u, &r[m->u]) && between(m, y, v, &r[m->w])) return 1;
  if (!q && between(m, x, u, &s[m->u]) && between(m, y, v, &s[m->w])) return 1;
  if (!c && between(m, &r[m->u], &s[m->u], x) &&
      between(m, &r[m->w], &s[m->w], y))
    return 1;
  return !d && between(m, &r[m->u], &s[m->u], u) &&
         between(m, &r[m->w], &s[m->w], v);
}
static int left_domain(tm* m, size_t a, size_t b, int* inside) {
  qr x = {0}, y = {0}, dx = {0}, dy = {0}, step = {0}, zero = {0}, u = {0},
     v = {0}, term = {0};
  size_t attempt, e,
      limit = m->c.max_limbs > SIZE_MAX / 32 ? SIZE_MAX : m->c.max_limbs * 32;
  int ok = 0;
  qr_mid(&m->c, &x, &m->v[a].p[m->u], &m->v[b].p[m->u]);
  qr_mid(&m->c, &y, &m->v[a].p[m->w], &m->v[b].p[m->w]);
  qr_sub(&m->c, &dx, &m->v[a].p[m->w], &m->v[b].p[m->w]);
  qr_sub(&m->c, &dy, &m->v[b].p[m->u], &m->v[a].p[m->u]);
  qr_i64(&m->c, &step, 1);
  qr_i64(&m->c, &zero, 0);
  for (attempt = 0; attempt < limit && !m->c.status; attempt++) {
    int blocked = 0;
    qr_mul(&m->c, &term, &step, &dx);
    qr_add(&m->c, &u, &x, &term);
    qr_mul(&m->c, &term, &step, &dy);
    qr_add(&m->c, &v, &y, &term);
    for (e = 0; e < m->ne && !m->c.status; e++) {
      if ((m->e[e].a == a && m->e[e].b == b) ||
          (m->e[e].a == b && m->e[e].b == a))
        continue;
      if (witness_intersects(m, &x, &y, &u, &v, m->e[e].a, m->e[e].b)) {
        blocked = 1;
        break;
      }
    }
    if (!blocked && !m->c.status) {
      int location = tg_domain(m, &u, &v);
      if (location >= 0) {
        *inside = location;
        ok = 1;
        break;
      }
    }
    qr_mid(&m->c, &step, &zero, &step);
  }
  qr_clear(&m->c, &x);
  qr_clear(&m->c, &y);
  qr_clear(&m->c, &dx);
  qr_clear(&m->c, &dy);
  qr_clear(&m->c, &step);
  qr_clear(&m->c, &zero);
  qr_clear(&m->c, &u);
  qr_clear(&m->c, &v);
  qr_clear(&m->c, &term);
  if (!ok && !m->c.status) m->c.status = TESS_RESOURCE_LIMIT;
  return ok && !m->c.status;
}
int tg_seed(tm* m) {
  size_t a, b, h, k, n = m->nv;
  size_t* next = NULL;
  unsigned char* seen = NULL;
  for (a = 0; a < n && !m->c.status; a++)
    for (b = a + 1; b < n && !m->c.status; b++)
      if (visible(m, a, b)) edge(m, a, b, 0);
  if (m->c.status) return 0;
  next = tx_alloc(&m->c, m->ne * 2, sizeof(size_t));
  seen = tx_alloc(&m->c, m->ne * 2, 1);
  if (!next || !seen) goto end;
  for (h = 0; h < m->ne * 2 && !m->c.status; h++) {
    size_t best = SIZE_MAX, wrap = SIZE_MAX;
    a = ha(m, h);
    b = hb(m, h);
    for (k = 0; k < m->ne * 2; k++)
      if (ha(m, k) == b && k != (h ^ 1)) {
        size_t v = hb(m, k);
        if (wrap == SIZE_MAX || angle(m, b, hb(m, wrap), v) < 0) wrap = k;
        if (angle(m, b, v, a) < 0 &&
            (best == SIZE_MAX || angle(m, b, hb(m, best), v) < 0))
          best = k;
      }
    next[h] = best != SIZE_MAX ? best : wrap;
    if (next[h] == SIZE_MAX) {
      m->c.status = TESS_INTERNAL_ERROR;
      goto end;
    }
  }
  for (h = 0; h < m->ne * 2 && !m->c.status; h++)
    if (!seen[h]) {
      size_t cur = h, count = 0, vs[3] = {0};
      do {
        if (cur >= m->ne * 2 || seen[cur] || count > m->ne * 2) {
          m->c.status = TESS_INTERNAL_ERROR;
          goto end;
        }
        seen[cur] = 1;
        if (count < 3) vs[count] = ha(m, cur);
        count++;
        cur = next[cur];
      } while (cur != h);
      {
        int domain = 0;
        if (!left_domain(m, ha(m, h), hb(m, h), &domain)) goto end;
        if (domain) {
          if (count != 3 || tg_orient(m, vs[0], vs[1], vs[2]) <= 0) {
            if (!m->c.status) m->c.status = TESS_INTERNAL_ERROR;
            goto end;
          }
          tg_add_face(m, vs[0], vs[1], vs[2]);
        }
      }
    }
end:
  tx_free(&m->c, next, m->ne * 2 * sizeof(size_t));
  tx_free(&m->c, seen, m->ne * 2);
  return !m->c.status && tg_validate(m) &&
         tg_legalize(m, m->max_edits, &m->legalization_complete);
}
static int tri_inside(tm* m, size_t p, const tf* f) {
  int a = tg_orient(m, f->v[0], f->v[1], p),
      b = tg_orient(m, f->v[1], f->v[2], p),
      c = tg_orient(m, f->v[2], f->v[0], p);
  return a > 0 && b > 0 && c > 0;
}
/* Independent exhaustive intersection and normalized oriented boundary audit.
 */
int tg_validate_mode(tm* m, int accelerated) {
  tbounds* boxes = NULL;
  size_t i, j, k, l;
  int ok = 0;
  long long* balance = NULL;
  size_t n = m->nv;
  if (!m->nf || n > SIZE_MAX / n || n * n > SIZE_MAX / sizeof(*balance)) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  balance = tx_alloc(&m->c, n * n, sizeof(*balance));
  if (!balance) return 0;
  for (i = 0; i < m->nf && !m->c.status; i++) {
    tf* f = &m->f[i];
    for (k = 0; k < 3; k++)
      if (f->v[k] >= n) goto end;
    if (tg_orient(m, f->v[0], f->v[1], f->v[2]) <= 0) goto end;
    for (k = 0; k < 3; k++) {
      size_t a = f->v[k], b = f->v[(k + 1) % 3];
      if (++balance[a * n + b] > 1) goto end;
    }
  }
  if (accelerated) boxes = tg_bounds(m);
  for (i = 0; i < m->nf && !m->c.status; i++)
    for (j = i + 1; j < m->nf && !m->c.status; j++) {
      if (boxes && tg_boxes_separate(m, &boxes[i], &boxes[j],
                                     (1u << m->u) | (1u << m->w)))
        continue;
      tf *a = &m->f[i], *b = &m->f[j];
      for (k = 0; k < 3; k++) {
        if (tri_inside(m, a->v[k], b) || tri_inside(m, b->v[k], a)) goto end;
        for (l = 0; l < 3; l++)
          if (tg_segments(m, a->v[k], a->v[(k + 1) % 3], b->v[l],
                          b->v[(l + 1) % 3]))
            goto end;
      }
    }
  for (i = 0; i < m->ne; i++)
    if (m->e[i].constraint) {
      size_t a = m->e[i].a, b = m->e[i].b;
      if (a >= n || b >= n) goto end;
      if (m->e[i].constraint != 1) {
        if ((m->e[i].constraint != 2 && m->e[i].constraint != 3) ||
            balance[a * n + b] != 1 || balance[b * n + a] != 1)
          goto end;
        continue;
      }
      balance[a * n + b]--;
    }
  for (i = 0; i < n; i++)
    for (j = i + 1; j < n; j++)
      if (balance[i * n + j] != balance[j * n + i]) goto end;
  ok = !m->c.status && tg_topology(m, 1);
end:
  tx_free(&m->c, boxes, m->nf * sizeof(*boxes));
  tx_free(&m->c, balance, n * n * sizeof(*balance));
  if (!ok && !m->c.status) m->c.status = TESS_INVALID_INPUT;
  return ok;
}

int tg_protect_creases(tm* m) {
  size_t i, j, k, l, e, owner = m->nv;
  for (i = 0; i < m->nf && !m->c.status; i++)
    for (j = i + 1; j < m->nf && !m->c.status; j++)
      for (k = 0; k < 3; k++)
        for (l = 0; l < 3; l++) {
          size_t a = m->f[i].v[k], b = m->f[i].v[(k + 1) % 3],
                 d = m->f[j].v[(l + 2) % 3];
          if (m->f[j].v[l] != b || m->f[j].v[(l + 1) % 3] != a) continue;
          if (!tg_orient3(m, m->f[i].v[0], m->f[i].v[1], m->f[i].v[2], d))
            continue;
          for (e = 0; e < m->ne; e++)
            if ((m->e[e].a == a && m->e[e].b == b) ||
                (m->e[e].a == b && m->e[e].b == a))
              break;
          if (e == m->ne) {
            if (!edge(m, a, b, 2)) return 0;
          } else
            m->e[e].constraint = 2;
          m->e[e].source = SIZE_MAX;
          m->e[e].owner = owner++;
          qr_i64(&m->c, &m->e[e].ta, 0);
          qr_i64(&m->c, &m->e[e].tb, 1);
          m->e[e].a = a < b ? a : b;
          m->e[e].b = a < b ? b : a;
          m->v[a].pinned = m->v[b].pinned = 1;
        }
  return !m->c.status;
}

void tg_freeze_constraints(tm* m) {
  size_t read, write = 0;
  for (read = 0; read < m->ne; read++) {
    if (m->e[read].constraint) {
      if (write != read) {
        m->e[write] = m->e[read];
        memset(&m->e[read], 0, sizeof(te));
      }
      write++;
    } else {
      qr_clear(&m->c, &m->e[read].ta);
      qr_clear(&m->c, &m->e[read].tb);
      memset(&m->e[read], 0, sizeof(te));
    }
  }
  m->ne = write;
}

int tg_add_exact_vertex(tm* m, const qr point[3], size_t source, int pinned,
                        size_t* index) {
  size_t j;
  if (m->nv >= m->max_vertices || m->next_id == SIZE_MAX) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  if (!grow(m, (void**)&m->v, &m->vcap, m->nv + 1, sizeof(tv))) return 0;
  *index = m->nv++;
  m->v[*index].source = source;
  m->v[*index].id = m->next_id++;
  m->v[*index].pinned = pinned;
  for (j = 0; j < 3; j++) qr_copy(&m->c, &m->v[*index].p[j], &point[j]);
  return !m->c.status;
}
int tg_constraint_append(tm* m, const te* base, size_t a, size_t b,
                         const qr* ta, const qr* tb) {
  te t = {0};
  t.a = a;
  t.b = b;
  t.source = base->source;
  t.tag = base->tag;
  t.owner = base->owner;
  t.constraint = base->constraint;
  qr_copy(&m->c, &t.ta, ta);
  qr_copy(&m->c, &t.tb, tb);
  if (!grow(m, (void**)&m->e, &m->ecap, m->ne + 1, sizeof(te))) {
    qr_clear(&m->c, &t.ta);
    qr_clear(&m->c, &t.tb);
    return 0;
  }
  m->e[m->ne++] = t;
  return !m->c.status;
}

int tg_validate(tm* m) { return tg_validate_mode(m, 1); }
