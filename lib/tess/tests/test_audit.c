#include <stdio.h>

#include "geometry.h"
static int test(const double (*p)[3], const size_t f[2][3], int expect) {
  tm m;
  size_t i;
  int ok;
  tm_init(&m);
  for (i = 0; i < 6; i++) tg_add_vertex(&m, p[i], i);
  for (i = 0; i < 2; i++) tg_add_face(&m, f[i][0], f[i][1], f[i][2]);
  ok = tg_audit3(&m);
  if (ok != expect) fprintf(stderr, "audit expected %d got %d\n", expect, ok);
  tm_clear(&m);
  return ok == expect;
}
int main(void) {
  const size_t separate[2][3] = {{0, 1, 2}, {3, 4, 5}},
               shared[2][3] = {{0, 1, 2}, {1, 0, 3}};
  const double disjoint[6][3] = {{0, 0, 0}, {2, 0, 0}, {0, 2, 0},
                                 {0, 0, 1}, {2, 0, 1}, {0, 2, 1}};
  const double cross[6][3] = {{0, 0, 0},    {2, 0, 0},   {0, 2, 0},
                              {.5, .5, -1}, {.5, .5, 1}, {1, .5, 0}};
  const double overlap[6][3] = {{0, 0, 0},     {2, 0, 0},   {0, 2, 0},
                                {.25, .25, 0}, {1, .25, 0}, {.25, 1, 0}};
  const double adjacent[6][3] = {{0, 0, 0}, {2, 0, 0}, {0, 2, 0},
                                 {0, 0, 2}, {0, 0, 0}, {0, 0, 0}};
  const double contact[6][3] = {{0, 0, 0}, {2, 0, 0}, {0, 2, 0},
                                {0, 0, 0}, {0, 0, 1}, {1, 0, 1}};
  return !(test(disjoint, separate, 1) && test(cross, separate, 0) &&
           test(overlap, separate, 0) && test(adjacent, shared, 1) &&
           test(contact, separate, 0));
}
