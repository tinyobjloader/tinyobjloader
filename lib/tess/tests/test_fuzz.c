/* Reproducible seed construction and randomized staged edit sequences. */
#include <stdio.h>
#include <string.h>

#include "edits.h"
static uint32_t state = UINT32_C(0x0c11beef);
static uint32_t random32(void) {
  state ^= state << 13;
  state ^= state >> 17;
  state ^= state << 5;
  return state;
}
int main(void) {
  const int directions[8][2] = {{1, 0},  {1, 1},   {0, 1},  {-1, 1},
                                {-1, 0}, {-1, -1}, {0, -1}, {1, -1}};
  size_t fixture;
  for (fixture = 0; fixture < 12; fixture++) {
    double xyz[36];
    size_t offsets[] = {0, 8, 12}, i, j, steps;
    tess_input input = {xyz, 8, offsets, 1};
    tess_options options = tess_default_options();
    tess_remesh_options edit = tess_default_remesh_options();
    tess_result* r = NULL;
    options.chart_axis = 2;
    options.max_operations = 2000000000;
    options.max_faces = 128;
    options.max_vertices = 128;
    for (i = 0; i < 8; i++) {
      int radius = 2 + (int)(random32() % 5);
      xyz[3 * i] = directions[i][0] * radius;
      xyz[3 * i + 1] = directions[i][1] * radius;
      xyz[3 * i + 2] = fixture % 3 == 0 ? (double)(random32() % 5) / 16 : 0;
    }
    if (fixture % 3 == 1) {
      const double hole[] = {-.25, -.25, 0, -.25, .25,  0,
                             .25,  .25,  0, .25,  -.25, 0};
      memcpy(xyz + 24, hole, sizeof(hole));
      input.vertex_count = 12;
      input.ring_count = 2;
    }
    if (tess_triangulate(&input, &options, &r) != TESS_OK) {
      fprintf(stderr, "seed fuzz fixture %zu state %u\n", fixture, state);
      return 1;
    }
    edit.subdivide_boundary = edit.subdivide_features = 1;
    for (steps = 0; steps < 24; steps++) {
      tm stage;
      tm* m = &r->mesh;
      size_t ops = m->c.ops, limit = m->c.max_ops, bytes = m->c.max_bytes;
      size_t face = random32() % m->nf, a = m->f[face].v[0],
             b = m->f[face].v[1];
      int changed = 0;
      unsigned operation = random32() % 5;
      tm_clone(&stage, m);
      if (!stage.c.status) switch (operation) {
          case 0:
            changed = tg_split_edge(&stage, a, b, &edit);
            break;
          case 1:
            changed = tg_split_face(&stage, face);
            break;
          case 2:
            changed = tg_flip_edge(&stage, a, b);
            break;
          case 3:
            changed = tg_collapse_edge(&stage, &r->seed, a, b);
            break;
          default:
            changed = tg_relocate(&stage, &r->seed, random32() % m->nv,
                                  random32() % 5);
            break;
        }
      if (changed && !stage.c.status && tg_compact(&stage) &&
          tg_check_chains(&stage, &r->seed, &edit) && tg_validate(&stage) &&
          tg_audit3(&stage)) {
        qr zero = {0};
        qr_i64(&stage.c, &zero, 0);
        changed = tg_reference(&stage, &r->seed, &zero);
        qr_clear(&stage.c, &zero);
      } else
        changed = 0;
      if (changed && !stage.c.status) {
        size_t next = ops + stage.c.ops;
        tm_clear(m);
        *m = stage;
        m->c.ops = next;
        m->c.max_ops = limit;
        m->c.max_bytes = bytes;
      } else {
        m->c.ops += stage.c.ops;
        tm_clear(&stage);
      }
      if (m->c.ops >= m->c.max_ops) {
        fprintf(stderr, "fuzz resource fixture %zu step %zu\n", fixture, steps);
        return 2;
      }
      for (i = 0; i < r->seed.nv; i++)
        for (j = 0; j < 3; j++)
          if (qr_cmp(&m->c, &m->v[i].p[j], &r->seed.v[i].p[j])) return 3;
    }
    if (!tg_validate(&r->mesh) || !tg_audit3(&r->mesh)) return 4;
    tess_result_free(r);
  }
  fprintf(stderr, "seed/edit fuzz initial=0x0c11beef final=%u\n", state);
  return 0;
}
