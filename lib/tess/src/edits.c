/* SPDX-License-Identifier: MIT */
#include "edits.h"

#include <stdlib.h>
#include <string.h>
static size_t constraint(tm* m, size_t a, size_t b) {
  size_t i;
  for (i = 0; i < m->ne; i++)
    if (m->e[i].constraint && ((m->e[i].a == a && m->e[i].b == b) ||
                               (m->e[i].a == b && m->e[i].b == a)))
      return i;
  return SIZE_MAX;
}
static int may_split(const te* e, const tess_remesh_options* o) {
  size_t i;
  if (e->constraint == 2 || e->constraint == 3)
    return o->subdivide_features != 0;
  if (!o->subdivide_boundary) return 0;
  if (!o->boundary_owners) return 1;
  for (i = 0; i < o->boundary_owner_count; i++)
    if (o->boundary_owners[i] == e->owner) return 1;
  return 0;
}
static int midpoint(tm* m, size_t a, size_t b, int pinned, size_t* index) {
  qr p[3] = {0};
  size_t j;
  int ok;
  for (j = 0; j < 3; j++) qr_mid(&m->c, &p[j], &m->v[a].p[j], &m->v[b].p[j]);
  ok = tg_add_exact_vertex(m, p, SIZE_MAX, pinned, index);
  for (j = 0; j < 3; j++) qr_clear(&m->c, &p[j]);
  return ok;
}
int tg_split_edge(tm* m, size_t a, size_t b, const tess_remesh_options* o) {
  size_t i, k, oldnf = m->nf, n = 0, v, owner = constraint(m, a, b);
  if (owner != SIZE_MAX && !may_split(&m->e[owner], o)) return 0;
  for (i = 0; i < oldnf; i++)
    for (k = 0; k < 3; k++)
      if ((m->f[i].v[k] == a && m->f[i].v[(k + 1) % 3] == b) ||
          (m->f[i].v[k] == b && m->f[i].v[(k + 1) % 3] == a))
        n++;
  if (!n || n > 2) return 0;
  if (!midpoint(m, a, b, owner != SIZE_MAX, &v)) return 0;
  for (i = 0; i < oldnf && !m->c.status; i++) {
    tf f = m->f[i];
    for (k = 0; k < 3; k++)
      if ((f.v[k] == a && f.v[(k + 1) % 3] == b) ||
          (f.v[k] == b && f.v[(k + 1) % 3] == a)) {
        m->f[i] = (tf){.v = {f.v[k], v, f.v[(k + 2) % 3]}, .id = f.id};
        tg_add_face(m, v, f.v[(k + 1) % 3], f.v[(k + 2) % 3]);
        break;
      }
  }
  if (owner != SIZE_MAX && !m->c.status) {
    qr t = {0}, end = {0};
    te base = m->e[owner];
    size_t oldb = base.b;
    qr_mid(&m->c, &t, &base.ta, &base.tb);
    qr_copy(&m->c, &end, &base.tb);
    if (tg_constraint_append(m, &base, v, oldb, &t, &end)) {
      m->e[owner].b = v;
      qr_copy(&m->c, &m->e[owner].tb, &t);
    }
    qr_clear(&m->c, &t);
    qr_clear(&m->c, &end);
  }
  return !m->c.status;
}
int tg_split_face(tm* m, size_t face) {
  tf f;
  qr p[3] = {0}, three = {0};
  size_t j, v;
  int ok;
  if (face >= m->nf) return 0;
  f = m->f[face];
  qr_i64(&m->c, &three, 3);
  for (j = 0; j < 3; j++) {
    qr_add(&m->c, &p[j], &m->v[f.v[0]].p[j], &m->v[f.v[1]].p[j]);
    qr_add(&m->c, &p[j], &p[j], &m->v[f.v[2]].p[j]);
    qr_div(&m->c, &p[j], &p[j], &three);
  }
  ok = tg_add_exact_vertex(m, p, SIZE_MAX, 0, &v);
  for (j = 0; j < 3; j++) qr_clear(&m->c, &p[j]);
  qr_clear(&m->c, &three);
  if (!ok) return 0;
  m->f[face] = (tf){.v = {f.v[0], f.v[1], v}, .id = f.id};
  tg_add_face(m, f.v[1], f.v[2], v);
  tg_add_face(m, f.v[2], f.v[0], v);
  return !m->c.status;
}
int tg_flip_edge(tm* m, size_t a, size_t b) {
  size_t i, k, faces[2] = {0}, opposite[2] = {0}, n = 0;
  if (constraint(m, a, b) != SIZE_MAX) return 0;
  for (i = 0; i < m->nf; i++)
    for (k = 0; k < 3; k++)
      if (m->f[i].v[k] == a && m->f[i].v[(k + 1) % 3] == b) {
        faces[0] = i;
        opposite[0] = m->f[i].v[(k + 2) % 3];
        n |= 1;
      } else if (m->f[i].v[k] == b && m->f[i].v[(k + 1) % 3] == a) {
        faces[1] = i;
        opposite[1] = m->f[i].v[(k + 2) % 3];
        n |= 2;
      }
  if (n != 3 || tg_orient(m, opposite[0], opposite[1], b) <= 0 ||
      tg_orient(m, opposite[1], opposite[0], a) <= 0)
    return 0;
  m->f[faces[0]].v[0] = opposite[0];
  m->f[faces[0]].v[1] = opposite[1];
  m->f[faces[0]].v[2] = b;
  m->f[faces[1]].v[0] = opposite[1];
  m->f[faces[1]].v[1] = opposite[0];
  m->f[faces[1]].v[2] = a;
  return !m->c.status;
}
int tg_relocate(tm* m, const tm* seed, size_t vertex, unsigned step) {
  size_t i, j, count = 0;
  unsigned char* neighbor = NULL;
  qr x = {0}, y = {0}, n = {0}, height = {0};
  int ok = 0;
  if (vertex >= m->nv || m->v[vertex].pinned || step > 16) return 0;
  neighbor = tx_alloc(&m->c, m->nv, 1);
  if (!neighbor) return 0;
  for (i = 0; i < m->nf; i++)
    for (j = 0; j < 3; j++)
      if (m->f[i].v[j] == vertex) {
        neighbor[m->f[i].v[(j + 1) % 3]] = 1;
        neighbor[m->f[i].v[(j + 2) % 3]] = 1;
      }
  qr_i64(&m->c, &x, 0);
  qr_i64(&m->c, &y, 0);
  for (i = 0; i < m->nv && !m->c.status; i++)
    if (neighbor[i]) {
      count++;
      qr_add(&m->c, &x, &x, &m->v[i].p[m->u]);
      qr_add(&m->c, &y, &y, &m->v[i].p[m->w]);
    }
  if (!count) goto end;
  qr_size(&m->c, &n, count);
  qr_div(&m->c, &x, &x, &n);
  qr_div(&m->c, &y, &y, &n);
  for (i = 0; i < step; i++) {
    qr_mid(&m->c, &x, &x, &m->v[vertex].p[m->u]);
    qr_mid(&m->c, &y, &y, &m->v[vertex].p[m->w]);
  }
  if (!tg_reference_height(m, seed, &x, &y, &height)) goto end;
  qr_copy(&m->c, &m->v[vertex].p[m->u], &x);
  qr_copy(&m->c, &m->v[vertex].p[m->w], &y);
  qr_copy(&m->c, &m->v[vertex].p[m->axis], &height);
  ok = !m->c.status;
end:
  tx_free(&m->c, neighbor, m->nv);
  qr_clear(&m->c, &x);
  qr_clear(&m->c, &y);
  qr_clear(&m->c, &n);
  qr_clear(&m->c, &height);
  return ok;
}
int tg_collapse_edge(tm* m, const tm* seed, size_t a, size_t b) {
  size_t i, k, incidence = 0, opposite[2] = {0}, common = 0, write = 0;
  unsigned char *na = NULL, *nb = NULL;
  qr x = {0}, y = {0}, height = {0};
  int ok = 0;
  if (a >= m->nv || b >= m->nv || a == b || m->v[a].pinned || m->v[b].pinned ||
      constraint(m, a, b) != SIZE_MAX)
    return 0;
  if (m->v[a].id > m->v[b].id) {
    size_t t = a;
    a = b;
    b = t;
  }
  na = tx_alloc(&m->c, m->nv, 1);
  nb = tx_alloc(&m->c, m->nv, 1);
  if (!na || !nb) goto end;
  for (i = 0; i < m->nf; i++) {
    int hasA = 0, hasB = 0;
    for (k = 0; k < 3; k++) {
      hasA |= m->f[i].v[k] == a;
      hasB |= m->f[i].v[k] == b;
    }
    if (hasA)
      for (k = 0; k < 3; k++) na[m->f[i].v[k]] = 1;
    if (hasB)
      for (k = 0; k < 3; k++) nb[m->f[i].v[k]] = 1;
    if (hasA && hasB) {
      if (incidence == 2) goto end;
      for (k = 0; k < 3; k++)
        if (m->f[i].v[k] != a && m->f[i].v[k] != b)
          opposite[incidence++] = m->f[i].v[k];
    }
  }
  if (incidence != 2 || opposite[0] == opposite[1]) goto end;
  for (i = 0; i < m->nv; i++)
    if (i != a && i != b && na[i] && nb[i]) {
      common++;
      if (i != opposite[0] && i != opposite[1]) goto end;
    }
  if (common != 2) goto end;
  qr_mid(&m->c, &x, &m->v[a].p[m->u], &m->v[b].p[m->u]);
  qr_mid(&m->c, &y, &m->v[a].p[m->w], &m->v[b].p[m->w]);
  if (!tg_reference_height(m, seed, &x, &y, &height)) goto end;
  qr_copy(&m->c, &m->v[a].p[m->u], &x);
  qr_copy(&m->c, &m->v[a].p[m->w], &y);
  qr_copy(&m->c, &m->v[a].p[m->axis], &height);
  for (i = 0; i < m->nf; i++) {
    tf f = m->f[i];
    int hasA = 0, hasB = 0;
    for (k = 0; k < 3; k++) {
      hasA |= f.v[k] == a;
      hasB |= f.v[k] == b;
    }
    if (hasA && hasB) continue;
    for (k = 0; k < 3; k++)
      if (f.v[k] == b) f.v[k] = a;
    m->f[write++] = f;
  }
  m->nf = write;
  ok = !m->c.status;
end:
  tx_free(&m->c, na, m->nv);
  tx_free(&m->c, nb, m->nv);
  qr_clear(&m->c, &x);
  qr_clear(&m->c, &y);
  qr_clear(&m->c, &height);
  return ok;
}

typedef struct {
  size_t a, b, mid;
} split_record;
static int split_order(const void* a, const void* b) {
  const split_record *x = a, *y = b;
  if (x->a != y->a) return x->a > y->a ? 1 : -1;
  return x->b > y->b ? 1 : x->b < y->b ? -1 : 0;
}
static size_t split_find(const split_record* edges, size_t n, size_t a,
                         size_t b) {
  size_t low = 0, high = n;
  if (a > b) {
    size_t t = a;
    a = b;
    b = t;
  }
  while (low < high) {
    size_t mid = low + (high - low) / 2;
    if (edges[mid].a < a || (edges[mid].a == a && edges[mid].b < b))
      low = mid + 1;
    else
      high = mid;
  }
  return low < n && edges[low].a == a && edges[low].b == b ? low : SIZE_MAX;
}
int tg_red_refine(tm* m, const tess_remesh_options* o) {
  split_record* edges = NULL;
  tf* faces = NULL;
  size_t oldnf = m->nf, oldne = m->ne, ne = 0, i, j;
  int ok = 0;
  if (oldnf > SIZE_MAX / 4 || oldnf * 4 > m->max_faces) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  for (i = 0; i < oldne; i++)
    if (m->e[i].constraint && !may_split(&m->e[i], o)) return 0;
  edges = tx_alloc(&m->c, oldnf * 3, sizeof(*edges));
  faces = tx_alloc(&m->c, oldnf, sizeof(tf));
  if (!edges || !faces) goto end;
  memcpy(faces, m->f, oldnf * sizeof(tf));
  for (i = 0; i < oldnf; i++)
    for (j = 0; j < 3; j++) {
      size_t a = faces[i].v[j], b = faces[i].v[(j + 1) % 3];
      edges[i * 3 + j] = (split_record){a < b ? a : b, a < b ? b : a, 0};
    }
  qsort(edges, oldnf * 3, sizeof(*edges), split_order);
  for (i = 0; i < oldnf * 3; i++)
    if (!ne || edges[i].a != edges[ne - 1].a || edges[i].b != edges[ne - 1].b)
      edges[ne++] = edges[i];
  for (i = 0; i < ne && !m->c.status; i++)
    if (!midpoint(m, edges[i].a, edges[i].b,
                  constraint(m, edges[i].a, edges[i].b) != SIZE_MAX,
                  &edges[i].mid))
      goto end;
  m->nf = 0;
  for (i = 0; i < oldnf && !m->c.status; i++) {
    size_t a = faces[i].v[0], b = faces[i].v[1], c = faces[i].v[2],
           ab = edges[split_find(edges, ne, a, b)].mid,
           bc = edges[split_find(edges, ne, b, c)].mid,
           ca = edges[split_find(edges, ne, c, a)].mid;
    size_t first = m->nf;
    tg_add_face(m, a, ab, ca);
    if (m->nf > first) m->f[first].id = faces[i].id;
    tg_add_face(m, ab, b, bc);
    tg_add_face(m, ca, bc, c);
    tg_add_face(m, ab, bc, ca);
  }
  for (i = 0; i < oldne && !m->c.status; i++) {
    te base = m->e[i];
    size_t edge = split_find(edges, ne, base.a, base.b), mid;
    qr parameter = {0}, end = {0};
    if (edge == SIZE_MAX) {
      m->c.status = TESS_INTERNAL_ERROR;
      goto end;
    }
    mid = edges[edge].mid;
    qr_mid(&m->c, &parameter, &base.ta, &base.tb);
    qr_copy(&m->c, &end, &base.tb);
    if (tg_constraint_append(m, &base, mid, base.b, &parameter, &end)) {
      m->e[i].b = mid;
      qr_copy(&m->c, &m->e[i].tb, &parameter);
    }
    qr_clear(&m->c, &parameter);
    qr_clear(&m->c, &end);
  }
  ok = !m->c.status;
end:
  tx_free(&m->c, edges, oldnf * 3 * sizeof(*edges));
  tx_free(&m->c, faces, oldnf * sizeof(tf));
  return ok;
}
int tg_compact(tm* m) {
  size_t *map = NULL, i, j, n = 0;
  unsigned char* used = NULL;
  int ok = 0;
  map = tx_alloc(&m->c, m->nv, sizeof(size_t));
  used = tx_alloc(&m->c, m->nv, 1);
  if (!map || !used) goto end;
  for (i = 0; i < m->nf; i++)
    for (j = 0; j < 3; j++) {
      if (m->f[i].v[j] >= m->nv) goto end;
      used[m->f[i].v[j]] = 1;
    }
  for (i = 0; i < m->ne; i++)
    if (m->e[i].a >= m->nv || m->e[i].b >= m->nv || !used[m->e[i].a] ||
        !used[m->e[i].b])
      goto end;
  for (i = 0; i < m->nv; i++) {
    if (used[i])
      map[i] = n++;
    else if (m->v[i].pinned)
      goto end;
  }
  for (i = 0; i < m->nv; i++)
    if (used[i]) {
      if (map[i] != i) {
        m->v[map[i]] = m->v[i];
        memset(&m->v[i], 0, sizeof(tv));
      }
    } else {
      for (j = 0; j < 3; j++) qr_clear(&m->c, &m->v[i].p[j]);
      memset(&m->v[i], 0, sizeof(tv));
    }
  for (i = 0; i < m->nf; i++)
    for (j = 0; j < 3; j++) m->f[i].v[j] = map[m->f[i].v[j]];
  for (i = 0; i < m->ne; i++) {
    m->e[i].a = map[m->e[i].a];
    m->e[i].b = map[m->e[i].b];
  }
  ok = 1;
end:
  tx_free(&m->c, map, m->nv * sizeof(size_t));
  tx_free(&m->c, used, m->nv);
  if (ok) m->nv = n;
  return ok && !m->c.status;
}
static int chain_point(tm* m, const tm* seed, const te* original, size_t vertex,
                       const qr* parameter) {
  qr delta = {0}, point = {0};
  size_t j;
  int ok = 1;
  if (vertex >= m->nv) return 0;
  for (j = 0; j < 3 && ok && !m->c.status; j++) {
    qr_sub(&m->c, &delta, &seed->v[original->b].p[j],
           &seed->v[original->a].p[j]);
    qr_mul(&m->c, &point, &delta, parameter);
    qr_add(&m->c, &point, &point, &seed->v[original->a].p[j]);
    if (qr_cmp(&m->c, &point, &m->v[vertex].p[j])) ok = 0;
  }
  qr_clear(&m->c, &delta);
  qr_clear(&m->c, &point);
  return ok && !m->c.status;
}
int tg_check_chains(tm* m, const tm* seed, const tess_remesh_options* o) {
  size_t i, j, k, *order = NULL;
  qr zero = {0}, one = {0};
  int ok = 0;
  if (m->nv < seed->nv) return 0;
  for (i = 0; i < seed->nv; i++) {
    if (!m->v[i].pinned || m->v[i].source != seed->v[i].source) return 0;
    for (j = 0; j < 3; j++)
      if (qr_cmp(&m->c, &m->v[i].p[j], &seed->v[i].p[j])) return 0;
  }
  order = tx_alloc(&m->c, m->ne, sizeof(size_t));
  qr_i64(&m->c, &zero, 0);
  qr_i64(&m->c, &one, 1);
  if (!order) goto end;
  for (i = 0; i < m->ne; i++) {
    size_t matches = 0;
    for (j = 0; j < seed->ne; j++)
      if (m->e[i].owner == seed->e[j].owner &&
          m->e[i].constraint == seed->e[j].constraint &&
          m->e[i].source == seed->e[j].source && m->e[i].tag == seed->e[j].tag)
        matches++;
    if (matches != 1) goto end;
  }
  for (i = 0; i < seed->ne && !m->c.status; i++) {
    const te* original = &seed->e[i];
    size_t n = 0;
    for (j = 0; j < m->ne; j++)
      if (m->e[j].owner == original->owner) order[n++] = j;
    if (!n) {
      if (original->constraint == 2 && m->approximate) continue;
      goto end;
    }
    if (!may_split(original, o) && n != 1) goto end;
    for (j = 1; j < n; j++) {
      size_t value = order[j];
      k = j;
      while (k && qr_cmp(&m->c, &m->e[order[k - 1]].ta, &m->e[value].ta) > 0) {
        order[k] = order[k - 1];
        k--;
      }
      order[k] = value;
    }
    if (m->e[order[0]].a != original->a ||
        m->e[order[n - 1]].b != original->b ||
        qr_cmp(&m->c, &m->e[order[0]].ta, &zero) ||
        qr_cmp(&m->c, &m->e[order[n - 1]].tb, &one))
      goto end;
    for (j = 0; j < n && !m->c.status; j++) {
      te* segment = &m->e[order[j]];
      if (qr_cmp(&m->c, &segment->ta, &segment->tb) >= 0) goto end;
      if (j && (m->e[order[j - 1]].b != segment->a ||
                qr_cmp(&m->c, &m->e[order[j - 1]].tb, &segment->ta)))
        goto end;
      if (!chain_point(m, seed, original, segment->a, &segment->ta) ||
          !chain_point(m, seed, original, segment->b, &segment->tb))
        goto end;
    }
  }
  ok = !m->c.status;
end:
  tx_free(&m->c, order, m->ne * sizeof(size_t));
  qr_clear(&m->c, &zero);
  qr_clear(&m->c, &one);
  return ok;
}

int tg_edge_may_split(tm* m, size_t a, size_t b, const tess_remesh_options* o) {
  size_t e = constraint(m, a, b);
  return e == SIZE_MAX || may_split(&m->e[e], o);
}
