/* SPDX-License-Identifier: MIT */
#include <stdlib.h>
#include <string.h>

#include "geometry.h"
typedef struct {
  size_t a, b, from, to, face;
} incidence;
static int cmp(const void* a, const void* b) {
  const incidence *x = a, *y = b;
  if (x->a != y->a) return x->a > y->a ? 1 : -1;
  if (x->b != y->b) return x->b > y->b ? 1 : -1;
  return x->face > y->face ? 1 : x->face < y->face ? -1 : 0;
}
/* Check oriented edge manifoldness and connected vertex links independently of
   geometric intersection checks. For a patch, also check connectedness/Euler.
 */
int tg_topology(tm* m, int patch) {
  incidence* e = NULL;
  size_t *parent = NULL, *degree = NULL, *queue = NULL, *head = NULL,
         *to = NULL, *next = NULL;
  unsigned char *boundary = NULL, *seen = NULL;
  size_t i, j, k, ne = 0, active = 0, components = 0, n = m->nv, nf = m->nf;
  int ok = 0;
  if (nf > SIZE_MAX / 3) {
    m->c.status = TESS_RESOURCE_LIMIT;
    return 0;
  }
  e = tx_alloc(&m->c, nf * 3, sizeof(*e));
  parent = tx_alloc(&m->c, nf, sizeof(size_t));
  degree = tx_alloc(&m->c, n, sizeof(size_t));
  queue = tx_alloc(&m->c, n, sizeof(size_t));
  head = tx_alloc(&m->c, n, sizeof(size_t));
  to = tx_alloc(&m->c, nf * 2, sizeof(size_t));
  next = tx_alloc(&m->c, nf * 2, sizeof(size_t));
  boundary = tx_alloc(&m->c, n, 1);
  seen = tx_alloc(&m->c, n, 1);
  if (m->c.status) goto end;
  for (i = 0; i < nf; i++) {
    parent[i] = i;
    for (j = 0; j < 3; j++) {
      size_t a = m->f[i].v[j], b = m->f[i].v[(j + 1) % 3];
      incidence* x = &e[i * 3 + j];
      if (a >= n || b >= n || a == b) goto end;
      x->a = a < b ? a : b;
      x->b = a < b ? b : a;
      x->from = a;
      x->to = b;
      x->face = i;
    }
  }
  qsort(e, nf * 3, sizeof(*e), cmp);
  for (i = 0; i < nf * 3; i = j) {
    for (j = i + 1; j < nf * 3 && e[j].a == e[i].a && e[j].b == e[i].b; j++) {
    }
    if (j - i > 2) goto end;
    ne++;
    if (j - i == 1) {
      boundary[e[i].a] = boundary[e[i].b] = 1;
    } else {
      size_t a = e[i].face, b = e[i + 1].face;
      if (e[i].from == e[i + 1].from) goto end;
      while (parent[a] != a) a = parent[a];
      while (parent[b] != b) b = parent[b];
      if (a != b) parent[b] = a;
    }
  }
  for (i = 0; i < nf; i++)
    if (parent[i] == i) components++;
  for (i = 0; i < n && !m->c.status; i++) {
    size_t edges = 0, start = SIZE_MAX, vertices = 0, ends = 0, q0 = 0, q1 = 0;
    memset(degree, 0, n * sizeof(size_t));
    memset(seen, 0, n);
    for (j = 0; j < n; j++) head[j] = SIZE_MAX;
    for (j = 0; j < nf; j++)
      for (k = 0; k < 3; k++)
        if (m->f[j].v[k] == i) {
          size_t a = m->f[j].v[(k + 1) % 3], b = m->f[j].v[(k + 2) % 3];
          degree[a]++;
          degree[b]++;
          to[edges] = b;
          next[edges] = head[a];
          head[a] = edges++;
          to[edges] = a;
          next[edges] = head[b];
          head[b] = edges++;
        }
    if (!edges) continue;
    active++;
    for (j = 0; j < n; j++)
      if (degree[j]) {
        vertices++;
        start = j;
        if (degree[j] == 1)
          ends++;
        else if (degree[j] != 2)
          goto end;
      }
    if (boundary[i] ? ends != 2 : ends != 0) goto end;
    queue[q1++] = start;
    seen[start] = 1;
    while (q0 < q1) {
      size_t v = queue[q0++], h;
      for (h = head[v]; h != SIZE_MAX; h = next[h])
        if (!seen[to[h]]) {
          seen[to[h]] = 1;
          queue[q1++] = to[h];
        }
    }
    if (q1 != vertices) goto end;
  }
  if (patch) { /* V-E+F = 1-h, written without unsigned subtraction. */
    if (components != 1 || active > SIZE_MAX - nf || ne > SIZE_MAX - 2 ||
        m->nr > ne + 2 || active + nf != ne + 2 - m->nr)
      goto end;
  }
  ok = !m->c.status;
end:
  tx_free(&m->c, e, nf * 3 * sizeof(*e));
  tx_free(&m->c, parent, nf * sizeof(size_t));
  tx_free(&m->c, degree, n * sizeof(size_t));
  tx_free(&m->c, queue, n * sizeof(size_t));
  tx_free(&m->c, head, n * sizeof(size_t));
  tx_free(&m->c, to, nf * 2 * sizeof(size_t));
  tx_free(&m->c, next, nf * 2 * sizeof(size_t));
  tx_free(&m->c, boundary, n);
  tx_free(&m->c, seen, n);
  if (!ok && !m->c.status) m->c.status = TESS_INVALID_INPUT;
  return ok;
}
