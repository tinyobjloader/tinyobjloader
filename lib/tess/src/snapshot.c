/* SPDX-License-Identifier: MIT */
#include <string.h>

#include "result.h"
int tm_clone(tm* d, const tm* s) {
  size_t i, j;
  tm_init(d);
  d->c.allocator = s->c.allocator;
  d->c.max_bytes = s->c.max_bytes - s->c.bytes;
  d->c.max_ops = s->c.max_ops - s->c.ops;
  d->c.max_limbs = s->c.max_limbs;
  d->max_vertices = s->max_vertices;
  d->max_faces = s->max_faces;
  d->max_edits = s->max_edits;
  d->next_id = s->next_id;
  d->next_face_id = s->next_face_id;
  d->axis = s->axis;
  d->u = s->u;
  d->w = s->w;
  d->orientation = s->orientation;
  d->planar = s->planar;
  d->approximate = s->approximate;
  d->legalization_complete = s->legalization_complete;
  d->v = tx_alloc(&d->c, s->nv, sizeof(tv));
  if (d->v) {
    d->nv = d->vcap = s->nv;
    for (i = 0; i < s->nv && !d->c.status; i++) {
      d->v[i].source = s->v[i].source;
      d->v[i].id = s->v[i].id;
      d->v[i].pinned = s->v[i].pinned;
      for (j = 0; j < 3; j++) qr_copy(&d->c, &d->v[i].p[j], &s->v[i].p[j]);
    }
  }
  d->f = tx_alloc(&d->c, s->nf, sizeof(tf));
  if (d->f) {
    d->nf = d->fcap = s->nf;
    memcpy(d->f, s->f, s->nf * sizeof(tf));
  }
  d->e = tx_alloc(&d->c, s->ne, sizeof(te));
  if (d->e) {
    d->ne = d->ecap = s->ne;
    for (i = 0; i < s->ne && !d->c.status; i++) {
      d->e[i] = s->e[i];
      d->e[i].ta = (qr){0};
      d->e[i].tb = (qr){0};
      qr_copy(&d->c, &d->e[i].ta, &s->e[i].ta);
      qr_copy(&d->c, &d->e[i].tb, &s->e[i].tb);
    }
    /* Clear untouched shallow-free slots on an early allocation failure. */
  }
  d->nr = s->nr;
  d->rings = tx_alloc(&d->c, s->nr + 1, sizeof(size_t));
  if (d->rings) memcpy(d->rings, s->rings, (s->nr + 1) * sizeof(size_t));
  return !d->c.status;
}
