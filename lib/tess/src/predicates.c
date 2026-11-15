/* SPDX-License-Identifier: MIT */
#include "geometry.h"
static void det3(tx* c, qr* r, qr a[3][3]) {
  qr p = {0}, q = {0}, v = {0};
  size_t j;
  qr_i64(c, r, 0);
  for (j = 0; j < 3; j++) {
    qr_mul(c, &p, &a[1][(j + 1) % 3], &a[2][(j + 2) % 3]);
    qr_mul(c, &q, &a[1][(j + 2) % 3], &a[2][(j + 1) % 3]);
    qr_sub(c, &v, &p, &q);
    qr_mul(c, &v, &v, &a[0][j]);
    qr_add(c, r, r, &v);
  }
  qr_clear(c, &p);
  qr_clear(c, &q);
  qr_clear(c, &v);
}
int tg_orient3(tm* m, size_t a, size_t b, size_t c, size_t d) {
  qr mat[3][3] = {0}, v = {0};
  size_t ids[3] = {a, b, c}, i, j;
  int s;
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++)
      qr_sub(&m->c, &mat[i][j], &m->v[ids[i]].p[j], &m->v[d].p[j]);
  det3(&m->c, &v, mat);
  s = v.n.sign;
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++) qr_clear(&m->c, &mat[i][j]);
  qr_clear(&m->c, &v);
  return s;
}
int tg_incircle(tm* m, size_t a, size_t b, size_t c, size_t d) {
  qr mat[3][3] = {0}, v = {0}, p = {0}, q = {0};
  size_t ids[3] = {a, b, c}, i, j;
  int s;
  for (i = 0; i < 3; i++) {
    qr_sub(&m->c, &mat[i][0], &m->v[ids[i]].p[m->u], &m->v[d].p[m->u]);
    qr_sub(&m->c, &mat[i][1], &m->v[ids[i]].p[m->w], &m->v[d].p[m->w]);
    qr_mul(&m->c, &p, &mat[i][0], &mat[i][0]);
    qr_mul(&m->c, &q, &mat[i][1], &mat[i][1]);
    qr_add(&m->c, &mat[i][2], &p, &q);
  }
  det3(&m->c, &v, mat);
  s = v.n.sign * tg_orient(m, a, b, c);
  for (i = 0; i < 3; i++)
    for (j = 0; j < 3; j++) qr_clear(&m->c, &mat[i][j]);
  qr_clear(&m->c, &v);
  qr_clear(&m->c, &p);
  qr_clear(&m->c, &q);
  return s;
}
