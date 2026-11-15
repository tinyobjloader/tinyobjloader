/* SPDX-License-Identifier: MIT */
#ifndef TESS_EDITS_H
#define TESS_EDITS_H
#include "result.h"
int tg_add_exact_vertex(tm* m, const qr point[3], size_t source, int pinned,
                        size_t* index);
int tg_split_edge(tm* m, size_t a, size_t b,
                  const tess_remesh_options* options);
int tg_split_face(tm* m, size_t face);
int tg_flip_edge(tm* m, size_t a, size_t b);
int tg_collapse_edge(tm* m, const tm* reference, size_t a, size_t b);
int tg_relocate(tm* m, const tm* reference, size_t vertex, unsigned step);
int tg_red_refine(tm* m, const tess_remesh_options* options);
int tg_compact(tm* m);
int tg_check_chains(tm* m, const tm* reference,
                    const tess_remesh_options* options);
int tg_edge_may_split(tm* m, size_t a, size_t b,
                      const tess_remesh_options* options);
#endif
