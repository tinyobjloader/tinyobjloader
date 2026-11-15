#include <math.h>
#include <stdio.h>
#include <string.h>

#include "geometry.h"

static int emit_sign(tm *m, int sign) {
  if (m->c.status) {
    fprintf(stderr, "predicate resource/error %d\n", m->c.status);
    tm_clear(m);
    return m->c.bytes ? 6 : 5;
  }
  if (printf("%d\n", sign) < 0) {
    tm_clear(m);
    return 6;
  }
  tm_clear(m);
  return m->c.bytes ? 6 : 0;
}

static int process_tricontact(void) {
  double point[6][3];
  size_t i, j;
  tm m;
  tm_init(&m);
  m.axis = 2;
  m.u = 0;
  m.w = 1;
  for (i = 0; i < 6; i++) {
    for (j = 0; j < 3; j++)
      if (scanf("%la", &point[i][j]) != 1 || !isfinite(point[i][j])) {
        tm_clear(&m);
        return 2;
      }
    if (!tg_add_vertex(&m, point[i], i)) {
      tm_clear(&m);
      return 3;
    }
  }
  if (!tg_add_face(&m, 0, 1, 2) || !tg_add_face(&m, 3, 4, 5)) {
    tm_clear(&m);
    return 3;
  }
  {
    int valid = tg_audit3(&m);
    if (m.c.status && m.c.status != TESS_INVALID_INPUT) {
      fprintf(stderr, "predicate resource/error %d\n", m.c.status);
      tm_clear(&m);
      return m.c.bytes ? 6 : 5;
    }
    if (printf("%d\n", m.c.status || !valid ? 0 : 1) < 0) {
      tm_clear(&m);
      return 6;
    }
    tm_clear(&m);
    return m.c.bytes ? 6 : 0;
  }
}

static int process_indexed(void) {
  static const double zero[3] = {0., 0., 0.};
  double point[4][3];
  double vertices[1024][3];
  size_t ids[4];
  int present[1024] = {0};
  size_t i, j, max_id = 0;
  tm m;
  tm_init(&m);
  m.axis = 2;
  m.u = 0;
  m.w = 1;
  for (i = 0; i < 4; i++) {
    for (j = 0; j < 3; j++)
      if (scanf("%la", &point[i][j]) != 1 || !isfinite(point[i][j])) {
        tm_clear(&m);
        return 2;
      }
  }
  for (i = 0; i < 4; i++) {
    if (scanf("%zu", &ids[i]) != 1) {
      tm_clear(&m);
      return 2;
    }
    if (ids[i] >= 1024) {
      tm_clear(&m);
      return 3;
    }
    if (ids[i] > max_id) max_id = ids[i];
    if (present[ids[i]]) {
      for (j = 0; j < 3; j++)
        if (vertices[ids[i]][j] != point[i][j]) {
          tm_clear(&m);
          return 2;
        }
    } else {
      for (j = 0; j < 3; j++) vertices[ids[i]][j] = point[i][j];
      present[ids[i]] = 1;
    }
  }
  for (i = 0; i <= max_id; i++)
    if (!tg_add_vertex(&m, present[i] ? vertices[i] : zero, i)) {
      tm_clear(&m);
      return 3;
    }
  return emit_sign(&m, tg_segments(&m, ids[0], ids[1], ids[2], ids[3]));
}

int main(void) {
  char op[16];
  while (scanf("%15s", op) == 1) {
    if (!strcmp(op, "indexedsegments")) {
      int status = process_indexed();
      if (status) return status;
      continue;
    }
    if (!strcmp(op, "tricontact")) {
      int status = process_tricontact();
      if (status) return status;
      continue;
    }
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
        if (scanf("%la", &point[j]) != 1) {
          tm_clear(&m);
          return 2;
        }
      if (!tg_add_vertex(&m, point, i)) {
        tm_clear(&m);
        return 3;
      }
    }
    if (!strcmp(op, "orient3"))
      sign = tg_orient3(&m, 0, 1, 2, 3);
    else if (!strcmp(op, "incircle"))
      sign = tg_incircle(&m, 0, 1, 2, 3);
    else if (!strcmp(op, "orient2"))
      sign = tg_orient(&m, 0, 1, 2);
    else if (!strcmp(op, "onsegment"))
      sign = tg_segments(&m, 0, 1, 2, 2);
    else if (!strcmp(op, "segments"))
      sign = tg_segments(&m, 0, 1, 2, 3);
    else {
      tm_clear(&m);
      return 4;
    }
    {
      int status = emit_sign(&m, sign);
      if (status) return status;
    }
  }
  return 0;
}
