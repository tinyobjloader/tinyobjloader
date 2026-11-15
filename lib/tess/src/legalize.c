/* SPDX-License-Identifier: MIT */
#include "geometry.h"
/* Stable first-violation Lawson schedule; cocircular diagonals are retained. */
int tg_legalize(tm* m, size_t fuel, int* complete) {
  size_t i, j, k, l, n = 0;
  int changed = 1;
  if (complete) *complete = 0;
  while (changed && !m->c.status) {
    changed = 0;
    for (i = 0; i < m->nf && !changed && !m->c.status; i++)
      for (j = i + 1; j < m->nf && !changed && !m->c.status; j++)
        for (k = 0; k < 3 && !changed; k++)
          for (l = 0; l < 3 && !changed; l++) {
            tf a = m->f[i], b = m->f[j];
            size_t x = a.v[k], y = a.v[(k + 1) % 3], p = a.v[(k + 2) % 3],
                   q = b.v[(l + 2) % 3], e;
            int constrained = 0;
            if (b.v[l] != y || b.v[(l + 1) % 3] != x) continue;
            for (e = 0; e < m->ne; e++)
              if (m->e[e].constraint && ((m->e[e].a == x && m->e[e].b == y) ||
                                         (m->e[e].a == y && m->e[e].b == x))) {
                constrained = 1;
                break;
              }
            if (constrained || tg_orient(m, p, q, y) <= 0 ||
                tg_orient(m, q, p, x) <= 0)
              continue;
            if (tg_incircle(m, x, y, p, q) <= 0) continue;
            if (m->c.status) return 0;
            if (n == fuel) return tg_validate(m);
            m->f[i] = (tf){.v = {p, q, y}, .id = a.id};
            m->f[j] = (tf){.v = {q, p, x}, .id = b.id};
            if (!tg_validate(m)) {
              m->f[i] = a;
              m->f[j] = b;
              return 0;
            }
            n++;
            changed = 1;
          }
  }
  if (complete) *complete = !m->c.status;
  return !m->c.status && tg_validate(m);
}
