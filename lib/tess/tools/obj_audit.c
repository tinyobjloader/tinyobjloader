/* SPDX-License-Identifier: MIT */
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "geometry.h"
#include "obj_number.h"
#include "tiny_obj_c.h"
int main(int argc, char** argv) {
  tobj_scene_d input = {0};
  tobj_load_config config = tobj_default_config();
  tm mesh;
  size_t i, j, k, face = 0;
  int result = 1;
  const char* path = NULL;
  tm_init(&mesh);
  for (i = 1; i < (size_t)argc; i++) {
    if (!strcmp(argv[i], "--max-operations")) {
      char* end;
      uintmax_t n;
      if (++i == (size_t)argc || !argv[i][0] || argv[i][0] == '-') {
        result = 2;
        goto end;
      }
      errno = 0;
      n = strtoumax(argv[i], &end, 10);
      if (errno || *end || !n || n > SIZE_MAX) {
        result = 2;
        goto end;
      }
      mesh.c.max_ops = (size_t)n;
    } else if (path) {
      result = 2;
      goto end;
    } else
      path = argv[i];
  }
  if (!path) {
    result = 2;
    goto end;
  }
  config.triangulate = false;
  config.store_vertex_colors = false;
  config.num_threads = 1;
  config.max_vertices = mesh.max_vertices;
  config.max_faces = mesh.max_faces;
  config.max_input_bytes = mesh.c.max_bytes;
  tess_obj_numbers_reset();
  if (tobj_load_obj_from_file_d(&input, path, &config, NULL) != TOBJ_OK ||
      tess_obj_numbers_error())
    goto end;
  for (i = 0; i < input.attrib.vertices.count / 3; i++)
    if (!tg_add_vertex(&mesh, &input.attrib.vertices.ptr[3 * i], i)) goto end;
  for (i = 0; i < input.num_shapes; i++) {
    tobj_mesh_d* part = &input.shapes[i].mesh;
    size_t position = 0;
    for (j = 0; j < part->num_faces; j++, face++) {
      size_t ids[3];
      if (part->num_face_vertices[j] != 3 || position > part->num_indices ||
          part->num_indices - position < 3) {
        fprintf(stderr, "audit requires triangular faces; source face %zu\n",
                face);
        goto end;
      }
      for (k = 0; k < 3; k++) {
        int id = part->indices[position + k].vertex_index;
        if (id < 0 || (size_t)id >= mesh.nv) goto end;
        ids[k] = (size_t)id;
      }
      position += 3;
      if (!tg_add_face(&mesh, ids[0], ids[1], ids[2])) goto end;
    }
  }
  if (!mesh.nf || !tg_audit3(&mesh) || !tg_topology(&mesh, 0)) goto end;
  printf(
      "audited %zu triangles: exact 3D intersections, incidence and vertex "
      "links\n",
      mesh.nf);
  result = 0;
end:
  if (result)
    fprintf(
        stderr, "OBJ audit failed: %s (reason %d, faces %zu/%zu)\n",
        tess_status_string(mesh.c.status ? mesh.c.status : TESS_INVALID_INPUT),
        mesh.diagnostic.reason, mesh.diagnostic.face_a, mesh.diagnostic.face_b);
  if (mesh.c.status == TESS_RESOURCE_LIMIT ||
      mesh.c.status == TESS_ALLOCATION_FAILURE)
    result = 3;
  if (result == 2)
    fprintf(stderr,
            "usage: tess_obj_audit [--max-operations N] triangles.obj\n");
  tm_clear(&mesh);
  tobj_scene_free_d(&input);
  return result;
}
