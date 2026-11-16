#include <math.h>
#include <stdio.h>
#include <string.h>

#include "geometry.h"

static void print_zi_hex_body(const zi *z) {
  size_t i = z->n;
  int started = 0;
  if (!z->n) {
    printf("0");
    return;
  }
  while (i) {
    uint32_t limb = z->v[i - 1];
    if (!started) {
      printf("%x", limb);
      started = 1;
    } else {
      printf("%08x", limb);
    }
    --i;
  }
}

static void print_qr_hex(const qr *q) {
  if (q->n.sign < 0) printf("-");
  printf("0x");
  print_zi_hex_body(&q->n);
  printf("/0x");
  print_zi_hex_body(&q->d);
}

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

static int process_planecut(void) {
  double point[5][3];
  size_t i, j;
  tm m;
  qr p[3];
  tm_init(&m);
  m.axis = 2;
  m.u = 0;
  m.w = 1;
  for (i = 0; i < 5; i++)
    for (j = 0; j < 3; j++)
      if (scanf("%la", &point[i][j]) != 1 || !isfinite(point[i][j])) {
        tm_clear(&m);
        return 2;
      }
  for (i = 0; i < 5; i++)
    if (!tg_add_vertex(&m, point[i], i)) {
      tm_clear(&m);
      return 3;
    }
  {
    int cut = tg_plane_cut(&m, 0, 1, 2, 3, 4, p);
    if (m.c.status) {
      fprintf(stderr, "predicate resource/error %d\n", m.c.status);
      tm_clear(&m);
      return m.c.bytes ? 6 : 5;
    }
    if (cut) {
      if (printf("1 ") < 0) goto bad_output;
      print_qr_hex(&p[0]);
      if (printf(" ") < 0) goto bad_output;
      print_qr_hex(&p[1]);
      if (printf(" ") < 0) goto bad_output;
      print_qr_hex(&p[2]);
      if (printf("\n") < 0) goto bad_output;
    } else if (printf("0\n") < 0)
      goto bad_output;
    for (j = 0; j < 3; j++) qr_clear(&m.c, &p[j]);
    tm_clear(&m);
    return m.c.bytes ? 6 : 0;
  }
bad_output:
  for (j = 0; j < 3; j++) qr_clear(&m.c, &p[j]);
  tm_clear(&m);
  return 6;
}

static int process_contains2(void) {
  double point[4][3] = {{0., 0., 0.}};
  double two[2];
  size_t i, j;
  tm m;
  tm_init(&m);
  m.axis = 2;
  m.u = 0;
  m.w = 1;
  for (i = 0; i < 4; i++) {
    for (j = 0; j < 2; j++)
      if (scanf("%la", &two[j]) != 1 || !isfinite(two[j])) {
        tm_clear(&m);
        return 2;
      }
    point[i][0] = two[0];
    point[i][1] = two[1];
    point[i][2] = 0.;
  }
  for (i = 0; i < 4; i++)
    if (!tg_add_vertex(&m, point[i], i)) {
      tm_clear(&m);
      return 3;
    }
  return emit_sign(&m, tg_projected_contains(&m, 0, 1, 2, 3, 2));
}

static int process_triaudit(void) {
  double point[6][3];
  size_t face[2][3];
  size_t i, j, k;
  tm m;
  tm_init(&m);
  m.axis = 2;
  m.u = 0;
  m.w = 1;
  for (i = 0; i < 6; i++)
    for (j = 0; j < 3; j++)
      if (scanf("%la", &point[i][j]) != 1 || !isfinite(point[i][j])) {
        tm_clear(&m);
        return 2;
      }
  for (k = 0; k < 2; k++)
    for (j = 0; j < 3; j++) {
      if (scanf("%zu", &face[k][j]) != 1 || face[k][j] >= 6) {
        tm_clear(&m);
        return 2;
      }
    }
  for (i = 0; i < 6; i++)
    if (!tg_add_vertex(&m, point[i], i)) {
      tm_clear(&m);
      return 3;
    }
  if (!tg_add_face(&m, face[0][0], face[0][1], face[0][2]) ||
      !tg_add_face(&m, face[1][0], face[1][1], face[1][2])) {
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
    if (!strcmp(op, "planecut")) {
      int status = process_planecut();
      if (status) return status;
      continue;
    }
    if (!strcmp(op, "contains2")) {
      int status = process_contains2();
      if (status) return status;
      continue;
    }
    if (!strcmp(op, "triaudit")) {
      int status = process_triaudit();
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
