/* SPDX-License-Identifier: MIT */
#include "geometry.h"
/* Enumerate all vertices of each closed triangle/triangle overlay cell.
   Collinear-overlap endpoints and isolated contacts are original vertices;
   proper crossings are constructed rationally. Affine extrema occur here. */
static void orient_value(tx* c, qr* r, const qr* ax, const qr* ay, const qr* bx,
                         const qr* by, const qr* cx, const qr* cy) {
  qr x = {0}, y = {0}, u = {0}, v = {0}, p = {0}, q = {0};
  qr_sub(c, &x, bx, ax);
  qr_sub(c, &y, by, ay);
  qr_sub(c, &u, cx, ax);
  qr_sub(c, &v, cy, ay);
  qr_mul(c, &p, &x, &v);
  qr_mul(c, &q, &y, &u);
  qr_sub(c, r, &p, &q);
  qr_clear(c, &x);
  qr_clear(c, &y);
  qr_clear(c, &u);
  qr_clear(c, &v);
  qr_clear(c, &p);
  qr_clear(c, &q);
}
static int inside(tm* m, const tm* mesh, const tf* f, const qr* x,
                  const qr* y) {
  size_t k;
  qr o = {0};
  int ok = 1;
  for (k = 0; k < 3 && ok && !m->c.status; k++) {
    const qr *a = mesh->v[f->v[k]].p, *b = mesh->v[f->v[(k + 1) % 3]].p;
    orient_value(&m->c, &o, &a[m->u], &a[m->w], &b[m->u], &b[m->w], x, y);
    if (o.n.sign < 0) ok = 0;
  }
  qr_clear(&m->c, &o);
  return ok && !m->c.status;
}
static void height(tm* m, const tm* mesh, const tf* f, const qr* x, const qr* y,
                   qr* h) {
  const qr *a = mesh->v[f->v[0]].p, *b = mesh->v[f->v[1]].p,
           *d = mesh->v[f->v[2]].p;
  qr det = {0}, weight = {0}, term = {0};
  size_t k;
  orient_value(&m->c, &det, &a[m->u], &a[m->w], &b[m->u], &b[m->w], &d[m->u],
               &d[m->w]);
  qr_i64(&m->c, h, 0);
  for (k = 0; k < 3 && !m->c.status; k++) {
    const qr *v = mesh->v[f->v[(k + 1) % 3]].p,
             *w = mesh->v[f->v[(k + 2) % 3]].p;
    orient_value(&m->c, &weight, x, y, &v[m->u], &v[m->w], &w[m->u], &w[m->w]);
    qr_mul(&m->c, &term, &weight, &mesh->v[f->v[k]].p[m->axis]);
    qr_add(&m->c, h, h, &term);
  }
  qr_div(&m->c, h, h, &det);
  qr_clear(&m->c, &det);
  qr_clear(&m->c, &weight);
  qr_clear(&m->c, &term);
}
static int check_point(tm* m, const tm* seed, const tf* a, const tf* b,
                       const qr* x, const qr* y, const qr* tolerance,
                       qr* maximum) {
  qr old = {0}, now = {0}, difference = {0};
  int ok;
  height(m, seed, a, x, y, &old);
  height(m, m, b, x, y, &now);
  qr_sub(&m->c, &difference, &old, &now);
  difference.n.sign = difference.n.n ? 1 : 0;
  ok = qr_cmp(&m->c, &difference, tolerance) <= 0 && !m->c.status;
  if (maximum && qr_cmp(&m->c, &difference, maximum) > 0)
    qr_copy(&m->c, maximum, &difference);
  qr_clear(&m->c, &old);
  qr_clear(&m->c, &now);
  qr_clear(&m->c, &difference);
  return ok;
}
static int crossing(tm* m, const tm* seed, const tf* a, const tf* b, size_t i,
                    size_t j, const qr* tolerance, qr* maximum) {
  const qr *p = seed->v[a->v[i]].p, *q = seed->v[a->v[(i + 1) % 3]].p,
           *r = m->v[b->v[j]].p, *s = m->v[b->v[(j + 1) % 3]].p;
  qr d0 = {0}, d1 = {0}, den = {0}, t = {0}, x = {0}, y = {0};
  int ok = 1, sign0, sign1;
  orient_value(&m->c, &d0, &r[m->u], &r[m->w], &s[m->u], &s[m->w], &p[m->u],
               &p[m->w]);
  orient_value(&m->c, &d1, &r[m->u], &r[m->w], &s[m->u], &s[m->w], &q[m->u],
               &q[m->w]);
  sign0 = d0.n.sign;
  sign1 = d1.n.sign;
  if (sign0 * sign1 < 0) {
    qr_sub(&m->c, &den, &d0, &d1);
    qr_div(&m->c, &t, &d0, &den);
    qr_sub(&m->c, &x, &q[m->u], &p[m->u]);
    qr_mul(&m->c, &x, &x, &t);
    qr_add(&m->c, &x, &x, &p[m->u]);
    qr_sub(&m->c, &y, &q[m->w], &p[m->w]);
    qr_mul(&m->c, &y, &y, &t);
    qr_add(&m->c, &y, &y, &p[m->w]);
    if (inside(m, seed, a, &x, &y) && inside(m, m, b, &x, &y))
      ok = check_point(m, seed, a, b, &x, &y, tolerance, maximum);
  }
  qr_clear(&m->c, &d0);
  qr_clear(&m->c, &d1);
  qr_clear(&m->c, &den);
  qr_clear(&m->c, &t);
  qr_clear(&m->c, &x);
  qr_clear(&m->c, &y);
  return ok && !m->c.status;
}
int tg_reference_measure(tm* m, const tm* seed, const qr* tolerance,
                         qr* maximum) {
  size_t i, j, k, l;
  if (maximum) qr_i64(&m->c, maximum, 0);
  if (tolerance->n.sign < 0 || m->axis != seed->axis || m->u != seed->u ||
      m->w != seed->w)
    return 0;
  for (i = 0; i < seed->nf && !m->c.status; i++)
    for (j = 0; j < m->nf && !m->c.status; j++) {
      const tf *a = &seed->f[i], *b = &m->f[j];
      for (k = 0; k < 3; k++) {
        const qr *p = seed->v[a->v[k]].p, *q = m->v[b->v[k]].p;
        if (inside(m, m, b, &p[m->u], &p[m->w]) &&
            !check_point(m, seed, a, b, &p[m->u], &p[m->w], tolerance, maximum))
          return 0;
        if (inside(m, seed, a, &q[m->u], &q[m->w]) &&
            !check_point(m, seed, a, b, &q[m->u], &q[m->w], tolerance, maximum))
          return 0;
        for (l = 0; l < 3; l++)
          if (!crossing(m, seed, a, b, k, l, tolerance, maximum)) return 0;
      }
    }
  return !m->c.status;
}
int tg_reference(tm* m, const tm* seed, const qr* tolerance) {
  return tg_reference_measure(m, seed, tolerance, NULL);
}
int tg_reference_height(tm* m, const tm* seed, const qr* x, const qr* y,
                        qr* out) {
  size_t i;
  for (i = 0; i < seed->nf && !m->c.status; i++)
    if (inside(m, seed, &seed->f[i], x, y)) {
      height(m, seed, &seed->f[i], x, y, out);
      return !m->c.status;
    }
  return 0;
}
