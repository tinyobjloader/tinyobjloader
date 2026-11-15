/* SPDX-License-Identifier: MIT */
#include "bounds.h"
tbounds* tg_bounds(tm* m) {
  tbounds* out = tx_alloc(&m->c, m->nf, sizeof(*out));
  size_t i, j, k;
  if (!out) return NULL;
  for (i = 0; i < m->nf && !m->c.status; i++) {
    for (k = 0; k < 3; k++)
      if (m->f[i].v[k] >= m->nv) {
        m->c.status = TESS_INVALID_INPUT;
        break;
      }
    if (m->c.status) break;
    for (j = 0; j < 3; j++) {
      size_t lo = m->f[i].v[0], hi = lo;
      for (k = 1; k < 3; k++) {
        size_t v = m->f[i].v[k];
        if (qr_cmp(&m->c, &m->v[v].p[j], &m->v[lo].p[j]) < 0) lo = v;
        if (qr_cmp(&m->c, &m->v[v].p[j], &m->v[hi].p[j]) > 0) hi = v;
      }
      out[i].low[j] = lo;
      out[i].high[j] = hi;
    }
  }
  return out;
}
/* Closed exact boxes: equality is retained. On a resource error qr_cmp returns
   zero and the sticky error prevents acceptance; uncertain pairs are kept. */
int tg_boxes_separate(tm* m, const tbounds* a, const tbounds* b,
                      unsigned axes) {
  size_t j;
  for (j = 0; j < 3; j++)
    if (axes & (1u << j)) {
      if (qr_cmp(&m->c, &m->v[a->high[j]].p[j], &m->v[b->low[j]].p[j]) < 0)
        return 1;
      if (qr_cmp(&m->c, &m->v[b->high[j]].p[j], &m->v[a->low[j]].p[j]) < 0)
        return 1;
    }
  return 0;
}
