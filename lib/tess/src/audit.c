/* SPDX-License-Identifier: MIT */
#include "bounds.h"
#include "geometry.h"
/* Independent rational 3D triangle-pair audit. No floating broad phase. */
static void plane(tm* m, qr* r, const tf* f, const qr p[3]) {
  qr v[3][3] = {0}, a = {0}, b = {0}, c = {0};
  size_t i, j;
  qr_i64(&m->c, r, 0);
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++) qr_sub(&m->c, &v[i][j], &m->v[f->v[i]].p[j], &p[j]);
  for (j = 0; j < 3; j++) {
    qr_mul(&m->c, &a, &v[1][(j + 1) % 3], &v[2][(j + 2) % 3]);
    qr_mul(&m->c, &b, &v[1][(j + 2) % 3], &v[2][(j + 1) % 3]);
    qr_sub(&m->c, &c, &a, &b);
    qr_mul(&m->c, &c, &c, &v[0][j]);
    qr_add(&m->c, r, r, &c);
  }
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++) qr_clear(&m->c, &v[i][j]);
  qr_clear(&m->c, &a);
  qr_clear(&m->c, &b);
  qr_clear(&m->c, &c);
}
static int project(tm* m, const tf* f) {
  int ax;
  for (ax = 0; ax < 3; ax++) {
    int u = (ax + 1) % 3, w = (ax + 2) % 3;
    tv *a = &m->v[f->v[0]], *b = &m->v[f->v[1]], *c = &m->v[f->v[2]];
    if (tg_orient_q(m, &a->p[u], &a->p[w], &b->p[u], &b->p[w], &c->p[u],
                    &c->p[w]))
      return ax;
  }
  return -1;
}
static int contains(tm* m, const tf* f, const qr p[3], int axis) {
  int u = (axis + 1) % 3, w = (axis + 2) % 3, positive = 0, negative = 0;
  size_t k;
  for (k = 0; k < 3; k++) {
    tv *a = &m->v[f->v[k]], *b = &m->v[f->v[(k + 1) % 3]];
    int s =
        tg_orient_q(m, &a->p[u], &a->p[w], &b->p[u], &b->p[w], &p[u], &p[w]);
    positive |= s > 0;
    negative |= s < 0;
  }
  return !(positive && negative);
}
static int eq(tm* m, const qr a[3], const qr b[3]) {
  size_t j;
  for (j = 0; j < 3; j++)
    if (qr_cmp(&m->c, &a[j], &b[j])) return 0;
  return 1;
}
static int allowed(tm* m, const tf* a, const tf* b, const qr p[3]) {
  size_t common[3], n = 0, i, j;
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++)
      if (a->v[i] == b->v[j]) common[n++] = a->v[i];
  for (i = 0; i < n; i++)
    if (eq(m, p, m->v[common[i]].p)) return 1;
  if (n == 2) {
    qr v = {0}, w = {0}, cross = {0}, q = {0}, da[3] = {0}, db[3] = {0};
    int ok = 1;
    for (j = 0; j < 3; j++) {
      qr *x = &m->v[common[0]].p[j], *y = &m->v[common[1]].p[j];
      int ab = qr_cmp(&m->c, x, y);
      if (ab <= 0
              ? (qr_cmp(&m->c, x, &p[j]) > 0 || qr_cmp(&m->c, &p[j], y) > 0)
              : (qr_cmp(&m->c, y, &p[j]) > 0 || qr_cmp(&m->c, &p[j], x) > 0))
        ok = 0;
      qr_sub(&m->c, &da[j], &p[j], x);
      qr_sub(&m->c, &db[j], y, x);
    }
    for (j = 0; j < 3; j++) {
      qr_mul(&m->c, &v, &da[(j + 1) % 3], &db[(j + 2) % 3]);
      qr_mul(&m->c, &w, &da[(j + 2) % 3], &db[(j + 1) % 3]);
      qr_sub(&m->c, &cross, &v, &w);
      if (cross.n.sign) ok = 0;
    }
    for (j = 0; j < 3; j++) {
      qr_clear(&m->c, &da[j]);
      qr_clear(&m->c, &db[j]);
    }
    qr_clear(&m->c, &v);
    qr_clear(&m->c, &w);
    qr_clear(&m->c, &cross);
    qr_clear(&m->c, &q);
    return ok;
  }
  return 0;
}
static int edges_against(tm* m, const tf* a, const tf* b, int projection) {
  size_t i, j;
  int ok = 1;
  for (i = 0; i < 3 && ok && !m->c.status; i++) {
    const qr *x = m->v[a->v[i]].p, *y = m->v[a->v[(i + 1) % 3]].p;
    qr dx = {0}, dy = {0}, den = {0}, t = {0}, p[3] = {0};
    plane(m, &dx, b, x);
    plane(m, &dy, b, y);
    if (!dx.n.sign && contains(m, b, x, projection) && !allowed(m, a, b, x))
      ok = 0;
    if (!dy.n.sign && contains(m, b, y, projection) && !allowed(m, a, b, y))
      ok = 0;
    if (dx.n.sign * dy.n.sign < 0) {
      qr_sub(&m->c, &den, &dx, &dy);
      qr_div(&m->c, &t, &dx, &den);
      for (j = 0; j < 3; j++) {
        qr_sub(&m->c, &p[j], &y[j], &x[j]);
        qr_mul(&m->c, &p[j], &p[j], &t);
        qr_add(&m->c, &p[j], &p[j], &x[j]);
      }
      if (contains(m, b, p, projection) && !allowed(m, a, b, p)) ok = 0;
    }
    for (j = 0; j < 3; j++) qr_clear(&m->c, &p[j]);
    qr_clear(&m->c, &dx);
    qr_clear(&m->c, &dy);
    qr_clear(&m->c, &den);
    qr_clear(&m->c, &t);
  }
  return ok && !m->c.status;
}
int tg_audit3_mode(tm* m, int accelerated) {
  tbounds* boxes = accelerated ? tg_bounds(m) : NULL;
  size_t i, j, k, l;
  int old_u = m->u, old_w = m->w, ok = 1;
  for (i = 0; i < m->nf && ok && !m->c.status; i++) {
    int pa = project(m, &m->f[i]);
    if (pa < 0) {
      m->diagnostic.reason = TESS_DIAG_DEGENERATE_TRIANGLE;
      m->diagnostic.face_a = i;
      m->diagnostic.face_b = SIZE_MAX;
      ok = 0;
      break;
    }
    for (j = i + 1; j < m->nf && ok && !m->c.status; j++) {
      if (boxes && tg_boxes_separate(m, &boxes[i], &boxes[j], 7)) continue;
      m->diagnostic.face_a = i;
      m->diagnostic.face_b = j;
      tf *a = &m->f[i], *b = &m->f[j];
      int pb = project(m, b), coplanar = 1;
      if (pb < 0) {
        m->diagnostic.reason = TESS_DIAG_DEGENERATE_TRIANGLE;
        m->diagnostic.face_a = j;
        m->diagnostic.face_b = SIZE_MAX;
        ok = 0;
        break;
      }
      for (k = 0; k < 3; k++) {
        qr d = {0};
        plane(m, &d, a, m->v[b->v[k]].p);
        if (d.n.sign) coplanar = 0;
        qr_clear(&m->c, &d);
      }
      if (coplanar) {
        m->u = (pa + 1) % 3;
        m->w = (pa + 2) % 3;
        for (k = 0; k < 3 && ok; k++) {
          const qr *x = m->v[a->v[k]].p, *y = m->v[b->v[k]].p;
          if (contains(m, b, x, pa) && !allowed(m, a, b, x)) ok = 0;
          if (contains(m, a, y, pa) && !allowed(m, a, b, y)) ok = 0;
          for (l = 0; l < 3 && ok; l++)
            if (tg_segments(m, a->v[k], a->v[(k + 1) % 3], b->v[l],
                            b->v[(l + 1) % 3]))
              ok = 0;
        } /* Identical triangles overlap beyond their common boundary. */
        {
          size_t shared = 0;
          for (k = 0; k < 3; k++)
            for (l = 0; l < 3; l++) shared += a->v[k] == b->v[l];
          if (shared == 3) ok = 0;
        }
      } else
        ok = edges_against(m, a, b, pb) && edges_against(m, b, a, pa);
    }
  }
  tx_free(&m->c, boxes, m->nf * sizeof(*boxes));
  m->u = old_u;
  m->w = old_w;
  if (!ok && !m->c.status) {
    m->c.status = TESS_INVALID_INPUT;
    if (m->diagnostic.reason != TESS_DIAG_DEGENERATE_TRIANGLE)
      m->diagnostic.reason = TESS_DIAG_TRIANGLE_CONTACT;
  }
  if (ok) m->diagnostic.face_a = m->diagnostic.face_b = SIZE_MAX;
  return ok && !m->c.status;
}

int tg_audit3(tm* m) { return tg_audit3_mode(m, 1); }
