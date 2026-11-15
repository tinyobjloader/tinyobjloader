#include <stdio.h>
#include <string.h>

#include "geometry.h"
int main(void) {
  char op[12];
  while (scanf("%11s", op) == 1) {
    tm m;
    size_t i, j;
    int sign;
    tm_init(&m);
    m.axis = 2;
    m.u = 0;
    m.w = 1;
    for (i = 0; i < 4; i++) {
      double point[3];
      for (j = 0; j < 3; j++)
        if (scanf("%la", &point[j]) != 1) return 2;
      if (!tg_add_vertex(&m, point, i)) return 3;
    }
    if (!strcmp(op, "orient3"))
      sign = tg_orient3(&m, 0, 1, 2, 3);
    else if (!strcmp(op, "incircle"))
      sign = tg_incircle(&m, 0, 1, 2, 3);
    else if (!strcmp(op, "segments"))
      sign = tg_segments(&m, 0, 1, 2, 3);
    else
      return 4;
    if (m.c.status) {
      fprintf(stderr, "predicate resource/error %d\n", m.c.status);
      return 5;
    }
    printf("%d\n", sign);
    tm_clear(&m);
    if (m.c.bytes) return 6;
  }
  return 0;
}
