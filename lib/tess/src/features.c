/* SPDX-License-Identifier: MIT */
#include "edits.h"

/* Only existing seed edges are admitted; no interior constraint insertion. */
int tg_tag_seed_edge(tm* m, size_t a, size_t b, uint64_t tag) {
  size_t i, j, edge = SIZE_MAX, owner = 0;
  int found = 0;
  te base = {0};
  if (a >= m->nv || b >= m->nv || a == b) return 0;
  for (i = 0; i < m->nf; i++)
    for (j = 0; j < 3; j++)
      if ((m->f[i].v[j] == a && m->f[i].v[(j + 1) % 3] == b) ||
          (m->f[i].v[j] == b && m->f[i].v[(j + 1) % 3] == a))
        found = 1;
  if (!found) return 0;
  for (i = 0; i < m->ne; i++) {
    if (m->e[i].owner == SIZE_MAX) {
      m->c.status = TESS_RESOURCE_LIMIT;
      return 0;
    }
    if (m->e[i].owner >= owner) owner = m->e[i].owner + 1;
    if ((m->e[i].a == a && m->e[i].b == b) ||
        (m->e[i].a == b && m->e[i].b == a))
      edge = i;
  }
  if (edge != SIZE_MAX) {
    m->e[edge].tag = tag;
    if (m->e[edge].constraint != 1) m->e[edge].constraint = 3;
  } else {
    base.a = a < b ? a : b;
    base.b = a < b ? b : a;
    base.constraint = 3;
    base.source = SIZE_MAX;
    base.owner = owner;
    base.tag = tag;
    qr_i64(&m->c, &base.ta, 0);
    qr_i64(&m->c, &base.tb, 1);
    tg_constraint_append(m, &base, base.a, base.b, &base.ta, &base.tb);
    qr_clear(&m->c, &base.ta);
    qr_clear(&m->c, &base.tb);
  }
  m->v[a].pinned = m->v[b].pinned = 1;
  return !m->c.status;
}

tess_status tess_set_seed_features(tess_result* r,
                                   const tess_seed_feature* features,
                                   size_t count, const size_t* pinned,
                                   size_t pinned_count) {
  tm stage, reference;
  size_t i, j, oldops, oldseedops, byte_limit, op_limit, extra, peak;
  tess_status status = TESS_OK;
  if (!r || r->remeshed || (!features && count) || (!pinned && pinned_count) ||
      count > 3 * r->seed.nf || pinned_count > r->seed.nv)
    return TESS_INVALID_INPUT;
  for (i = 0; i < pinned_count; i++)
    if (pinned[i] >= r->seed.nv) return TESS_INVALID_INPUT;
  for (i = 0; i < count; i++)
    for (j = 0; j < i; j++)
      if ((features[i].a == features[j].a && features[i].b == features[j].b) ||
          (features[i].a == features[j].b && features[i].b == features[j].a))
        return TESS_INVALID_INPUT;
  if (r->mesh.c.status) return r->mesh.c.status;
  if (!count && !pinned_count) return TESS_OK;
  oldops = r->mesh.c.ops;
  oldseedops = r->seed.c.ops;
  byte_limit = r->mesh.c.max_bytes + r->seed.c.bytes;
  op_limit = r->mesh.c.max_ops;
  tm_init(&reference);
  tm_clone(&stage, &r->mesh);
  for (i = 0; i < count && !stage.c.status; i++)
    if (!tg_tag_seed_edge(&stage, features[i].a, features[i].b,
                          features[i].tag)) {
      if (!stage.c.status) stage.c.status = TESS_INVALID_INPUT;
    }
  for (i = 0; i < pinned_count && !stage.c.status; i++)
    stage.v[pinned[i]].pinned = 1;
  if (!stage.c.status && (!tg_validate(&stage) || !tg_audit3(&stage)))
    if (!stage.c.status) stage.c.status = TESS_INVALID_INPUT;
  if (!stage.c.status) tm_clone(&reference, &stage);
  status = stage.c.status ? stage.c.status : reference.c.status;
  extra = stage.c.ops + reference.c.ops;
  peak = r->mesh.c.bytes + r->seed.c.bytes + stage.c.bytes + reference.c.peak +
         sizeof(*r);
  if (peak > r->peak_bytes) r->peak_bytes = peak;
  if (!status) {
    tm_clear(&r->mesh);
    tm_clear(&r->seed);
    r->mesh = stage;
    r->seed = reference;
    r->mesh.c.max_bytes = byte_limit - r->seed.c.bytes;
    r->mesh.c.max_ops = op_limit;
    r->mesh.c.ops = oldops + extra;
    r->seed.c.ops = oldseedops;
    r->mesh.c.peak = r->mesh.c.bytes;
  } else {
    tm_clear(&stage);
    tm_clear(&reference);
    r->mesh.c.ops = oldops + extra;
  }
  return status;
}
