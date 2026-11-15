#include <stdio.h>

#include "geometry.h"
static int run(const double (*v)[3], size_t n, const size_t* rings, size_t nr,
               size_t faces, int valid) {
  tm m;
  size_t i;
  int ok;
  tm_init(&m);
  for (i = 0; i < n; i++) tg_add_vertex(&m, v[i], i);
  m.nr = nr;
  m.rings = tx_alloc(&m.c, nr + 1, sizeof(size_t));
  for (i = 0; i <= nr; i++) m.rings[i] = rings[i];
  ok = tg_prepare(&m, -1, 0) && tg_seed(&m);
  if (ok != valid || (ok && m.nf != faces)) {
    fprintf(stderr, "got ok=%d faces=%zu status=%d expected=%d/%zu\n", ok, m.nf,
            m.c.status, valid, faces);
    tm_clear(&m);
    return 0;
  }
  tm_clear(&m);
  return 1;
}
int main(void) {
  const double square[][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0}};
  const double hole[][3] = {{0, 0, 0}, {4, 0, 0}, {4, 4, 0}, {0, 4, 0},
                            {1, 1, 0}, {1, 2, 0}, {2, 2, 0}, {2, 1, 0}};
  const double col[][3] = {{0, 0, 0}, {1, 0, 0}, {2, 0, 0},
                           {2, 2, 0}, {1, 1, 0}, {0, 2, 0}};
  const double bad[][3] = {{0, 0, 0}, {1, 1, 0}, {0, 1, 0}, {1, 0, 0}};
  size_t r[] = {0, 4}, h[] = {0, 4, 8}, c[] = {0, 6};
  return !(run(square, 4, r, 1, 2, 1) && run(hole, 8, h, 2, 8, 1) &&
           run(col, 6, c, 1, 4, 1) && run(bad, 4, r, 1, 0, 0));
}
