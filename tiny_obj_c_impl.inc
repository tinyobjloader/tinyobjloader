/*
 * tiny_obj_c_impl.inc -- per-precision OBJ parser + scene teardown.
 *
 * Included twice from tiny_obj_c.c with (TOBJ_REAL, TOBJ_SUF) = (float, _f)
 * and (double, _d). Every file-scope name is suffixed via TOBJ_T() so the two
 * inclusions do not collide in the single translation unit. Do not include
 * directly.
 */

/* ----------------------------------------------------------------------- */
/* builder                                                                 */
/* ----------------------------------------------------------------------- */

typedef struct TOBJ_T(tobj_builder) {
  const tobj_allocator *alloc;
  tobj_arena *arena;
  tobj_diag *diag;
  const tobj_load_config *cfg;
  tobj_caps caps;
  tobj_result err;
  size_t line; /* 1-based current line for diagnostics */

  bool triangulate;

  /* attrib temp vectors (reals / structs) */
  tobj_vec av;   /* vertices xyz */
  tobj_vec avw;  /* vertex weights (lazy) */
  tobj_vec avn;  /* normals xyz */
  tobj_vec avt;  /* texcoords uv */
  tobj_vec avtw; /* texcoord w (lazy) */
  tobj_vec acol; /* colors rgb (lazy) */
  bool color_seen;

  /* materials + name->id map (filled by the .mtl parser) */
  tobj_vec materials;   /* TOBJ_T(tobj_material) */
  tobj_vec matmap_key;  /* const char* (interned) */
  tobj_vec matmap_id;   /* int */
  tobj_vec mat_unknown; /* tobj_pending_kv */

  /* finalized shapes */
  tobj_vec shapes; /* TOBJ_T(tobj_shape) */

  /* current shape accumulation */
  const char *cur_name;
  bool cur_has_prims;
  tobj_vec m_idx;    /* tobj_index */
  tobj_vec m_fv;     /* unsigned face-vertex counts */
  tobj_vec m_mid;    /* int material ids */
  tobj_vec m_sg;     /* unsigned smoothing ids */
  tobj_vec l_idx;    /* tobj_index */
  tobj_vec l_cnt;    /* int per-line counts */
  tobj_vec p_idx;    /* tobj_index */

  /* per-face scratch (reused) */
  tobj_vec corners;  /* tobj_index */
  tobj_vec ringpos;  /* TOBJ_REAL */
  tobj_vec tris;     /* uint32_t */
  tobj_vec tscratch; /* uint8_t */

  /* free-form geometry (only used when cfg->parse_freeform) */
  tobj_vec ff_vp;      /* reals (global parameter vertices) */
  int ff_vp_comps;
  bool ff_present;     /* any free-form element in current shape */
  bool ff_active;      /* between curv/curv2/surf and end */
  int ff_kind;         /* 1=curv 2=curv2 3=surf */
  tobj_cstype ff_cstype;
  bool ff_rational;
  int ff_degu, ff_degv;
  TOBJ_REAL ff_u0, ff_u1, ff_s0, ff_s1, ff_t0, ff_t1;
  tobj_vec ff_cp_int;  /* int control points (curv: v idx, curv2: vp idx) */
  tobj_vec ff_cp_idx;  /* tobj_index control points (surf) */
  tobj_vec ff_knu;     /* reals (parm u) */
  tobj_vec ff_knv;     /* reals (parm v) */
  tobj_vec ff_trim;    /* TOBJ_T(tobj_trim_loop) */
  tobj_vec ff_hole;
  tobj_vec ff_scrv;
  tobj_vec sh_curves;   /* TOBJ_T(tobj_curve) */
  tobj_vec sh_curves2;  /* TOBJ_T(tobj_curve2) */
  tobj_vec sh_surfaces; /* TOBJ_T(tobj_surface) */

  /* parser state */
  int cur_material;
  unsigned cur_smooth;

  /* multithreading pass 2: vertices already parsed; indices resolve against
   * running counts instead of the (already full) attrib arrays */
  bool prefilled;
  size_t run_numv, run_numvt, run_numvn, run_numvp;
} TOBJ_T(tobj_builder);

/* Counts used for index fixup: running counts in MT pass 2, else live counts. */
static size_t TOBJ_T(cnt_v)(TOBJ_T(tobj_builder) * b) {
  return b->prefilled ? b->run_numv : b->av.count / 3u;
}
static size_t TOBJ_T(cnt_vt)(TOBJ_T(tobj_builder) * b) {
  return b->prefilled ? b->run_numvt : b->avt.count / 2u;
}
static size_t TOBJ_T(cnt_vn)(TOBJ_T(tobj_builder) * b) {
  return b->prefilled ? b->run_numvn : b->avn.count / 3u;
}

static bool TOBJ_T(b_fail)(TOBJ_T(tobj_builder) * b, tobj_result e) {
  if (b->err == TOBJ_OK) b->err = e;
  return false;
}

static void TOBJ_T(b_warn)(TOBJ_T(tobj_builder) * b, const char *msg) {
  tobj_diag_append(b->diag, b->alloc, TOBJ_SEV_WARNING, b->line, msg);
}

/* ----------------------------------------------------------------------- */
/* index fixup (1-based -> 0-based, negative -> relative)                  */
/* ----------------------------------------------------------------------- */

static bool TOBJ_T(fix_index)(int idx, size_t n, int *out) {
  if (idx > 0) {
    *out = idx - 1;
    return true;
  }
  if (idx == 0) {
    *out = -1;
    return false; /* zero index: invalid per spec */
  }
  long long r = (long long)n + idx;
  if (r < 0) {
    *out = -1;
    return false;
  }
  *out = (int)r;
  return true;
}

/* Parse one corner "v[/[vt][/vn]]" against explicit counts. Returns true if a
 * (possibly relative) vertex index was parsed and is in range. */
static bool TOBJ_T(parse_corner_n)(const char *tok, size_t len, size_t numv,
                                   size_t numvt, size_t numvn,
                                   tobj_index *out) {
  out->vertex_index = -1;
  out->normal_index = -1;
  out->texcoord_index = -1;

  tobj_cursor c;
  tobj_cur_init(&c, tok, len);
  int vi;
  if (!tobj_scan_int(&c.p, c.end, &vi)) return false;
  bool ok = TOBJ_T(fix_index)(vi, numv, &out->vertex_index);
  if (c.p < c.end && *c.p == '/') {
    c.p++;
    if (c.p < c.end && *c.p != '/') {
      int ti;
      if (tobj_scan_int(&c.p, c.end, &ti))
        TOBJ_T(fix_index)(ti, numvt, &out->texcoord_index);
    }
    if (c.p < c.end && *c.p == '/') {
      c.p++;
      int ni;
      if (tobj_scan_int(&c.p, c.end, &ni))
        TOBJ_T(fix_index)(ni, numvn, &out->normal_index);
    }
  }
  return ok;
}

/* Parse one face/line/point corner using the builder's current counts. */
static void TOBJ_T(parse_corner)(TOBJ_T(tobj_builder) * b, const char *tok,
                                 size_t len, tobj_index *out) {
  bool ok = TOBJ_T(parse_corner_n)(tok, len, TOBJ_T(cnt_v)(b),
                                   TOBJ_T(cnt_vt)(b), TOBJ_T(cnt_vn)(b), out);
  if (!ok && out->vertex_index < 0)
    TOBJ_T(b_warn)(b, "tinyobjc: invalid vertex index in face\n");
}

/* ----------------------------------------------------------------------- */
/* optional parallel-array helpers (lazy with backfill)                    */
/* ----------------------------------------------------------------------- */

static bool TOBJ_T(opt_push)(tobj_vec *v, size_t comps, size_t vidx,
                             const TOBJ_REAL *vals, const TOBJ_REAL *deflt,
                             bool present, const tobj_allocator *a) {
  if (!present && v->count == 0) return true; /* stay empty */
  /* backfill defaults up to vidx entries */
  while (v->count / comps < vidx) {
    if (!tobj_vec_append(v, deflt, comps, a)) return false;
  }
  const TOBJ_REAL *src = present ? vals : deflt;
  return tobj_vec_append(v, src, comps, a);
}

/* ----------------------------------------------------------------------- */
/* directive handlers                                                      */
/* ----------------------------------------------------------------------- */

static bool TOBJ_T(handle_v)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  double nums[8];
  int n = 0;
  while (n < 8) {
    double d;
    const char *save = c->p;
    if (!tobj_scan_double(&c->p, c->end, &d)) {
      c->p = save;
      break;
    }
    nums[n++] = d;
  }
  if (n < 3) {
    TOBJ_T(b_warn)(b, "tinyobjc: 'v' with fewer than 3 components\n");
    while (n < 3) nums[n++] = 0.0;
  }
  if (b->av.count / 3u >= b->caps.vertices) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
  size_t vidx = b->av.count / 3u;
  TOBJ_REAL xyz[3] = {(TOBJ_REAL)nums[0], (TOBJ_REAL)nums[1], (TOBJ_REAL)nums[2]};
  if (!tobj_vec_append(&b->av, xyz, 3, b->alloc)) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);

  /* weight: only the 4-number form carries a vertex weight */
  bool has_w = (n == 4);
  TOBJ_REAL w = has_w ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1;
  TOBJ_REAL wdef = (TOBJ_REAL)1;
  if (!TOBJ_T(opt_push)(&b->avw, 1, vidx, &w, &wdef, has_w, b->alloc))
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);

  /* color: the 6/7-number form carries r g b */
  if (b->cfg->store_vertex_colors) {
    bool has_c = (n >= 6);
    TOBJ_REAL rgb[3];
    rgb[0] = has_c ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1;
    rgb[1] = has_c ? (TOBJ_REAL)nums[4] : (TOBJ_REAL)1;
    rgb[2] = has_c ? (TOBJ_REAL)nums[5] : (TOBJ_REAL)1;
    TOBJ_REAL white[3] = {(TOBJ_REAL)1, (TOBJ_REAL)1, (TOBJ_REAL)1};
    if (has_c) b->color_seen = true;
    if (!TOBJ_T(opt_push)(&b->acol, 3, vidx, rgb, white, has_c, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  }
  return true;
}

static bool TOBJ_T(handle_vn)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  TOBJ_REAL xyz[3] = {0, 0, 0};
  double d;
  for (int i = 0; i < 3; i++)
    if (tobj_scan_double(&c->p, c->end, &d)) xyz[i] = (TOBJ_REAL)d;
  if (!tobj_vec_append(&b->avn, xyz, 3, b->alloc)) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  return true;
}

static bool TOBJ_T(handle_vt)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  double d;
  TOBJ_REAL uv[2] = {0, 0};
  int n = 0;
  for (; n < 2; n++) {
    if (!tobj_scan_double(&c->p, c->end, &d)) break;
    uv[n] = (TOBJ_REAL)d;
  }
  size_t tidx = b->avt.count / 2u;
  if (!tobj_vec_append(&b->avt, uv, 2, b->alloc)) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  bool has_w = tobj_scan_double(&c->p, c->end, &d);
  TOBJ_REAL w = has_w ? (TOBJ_REAL)d : (TOBJ_REAL)0;
  TOBJ_REAL wdef = (TOBJ_REAL)0;
  if (!TOBJ_T(opt_push)(&b->avtw, 1, tidx, &w, &wdef, has_w, b->alloc))
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  return true;
}

/* Append triangulated/raw face corners to the current shape mesh. */
static bool TOBJ_T(emit_face)(TOBJ_T(tobj_builder) * b, size_t arity) {
  const tobj_index *corners = (const tobj_index *)b->corners.data;
  bool do_tri = b->triangulate && arity > 3u;

  if (!do_tri) {
    if (b->m_idx.count + arity > b->caps.indices)
      return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
    if (!tobj_vec_append(&b->m_idx, corners, arity, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    unsigned fv = (unsigned)tobj_size_to_int(arity);
    if (!tobj_vec_append(&b->m_fv, &fv, 1, b->alloc) ||
        !tobj_vec_append(&b->m_mid, &b->cur_material, 1, b->alloc) ||
        !tobj_vec_append(&b->m_sg, &b->cur_smooth, 1, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    b->cur_has_prims = true;
    return true;
  }

  /* triangulate */
  size_t numv = TOBJ_T(cnt_v)(b);
  bool pos_ok = true;
  for (size_t k = 0; k < arity; k++) {
    int vi = corners[k].vertex_index;
    if (vi < 0 || (size_t)vi >= numv) {
      pos_ok = false;
      break;
    }
  }

  uint32_t ntri = (uint32_t)(arity - 2u);
  b->tris.count = 0;
  if (!tobj_vec_reserve(&b->tris, (size_t)ntri * 3u, b->alloc))
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  uint32_t *tri = (uint32_t *)b->tris.data;

  if (pos_ok) {
    b->ringpos.count = 0;
    if (!tobj_vec_reserve(&b->ringpos, arity * 3u, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    TOBJ_REAL *rp = (TOBJ_REAL *)b->ringpos.data;
    const TOBJ_REAL *vsrc = (const TOBJ_REAL *)b->av.data;
    for (size_t k = 0; k < arity; k++) {
      size_t vi = (size_t)corners[k].vertex_index;
      rp[3 * k + 0] = vsrc[3 * vi + 0];
      rp[3 * k + 1] = vsrc[3 * vi + 1];
      rp[3 * k + 2] = vsrc[3 * vi + 2];
    }
    size_t need_scratch = tobj_tess_scratch_size((uint32_t)arity);
    if (!tobj_vec_reserve(&b->tscratch, need_scratch, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);

    TOBJ_T(tobj_tess_desc) desc;
    tobj_memset(&desc, 0, sizeof desc);
    desc.points = rp;
    desc.n = (uint32_t)arity;
    desc.out_indices = tri;
    desc.out_cap = ntri * 3u;
    desc.scratch = b->tscratch.data;
    desc.scratch_size = need_scratch;
    tobj_tess_result res;
    TOBJ_T(tobj_tess_polygon)(&desc, &res);
    ntri = res.num_triangles;
    if (res.status == TOBJ_TESS_DEGENERATE_BESTEFFORT)
      TOBJ_T(b_warn)(b, "tinyobjc: degenerate polygon triangulated best-effort\n");
  } else {
    TOBJ_T(b_warn)(b, "tinyobjc: face with invalid vertex index; fan fallback\n");
    for (uint32_t t = 0; t < ntri; t++) {
      tri[3 * t + 0] = 0;
      tri[3 * t + 1] = t + 1;
      tri[3 * t + 2] = t + 2;
    }
  }

  if (b->m_idx.count + (size_t)ntri * 3u > b->caps.indices)
    return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
  for (uint32_t t = 0; t < ntri; t++) {
    tobj_index tidx[3];
    tidx[0] = corners[tri[3 * t + 0]];
    tidx[1] = corners[tri[3 * t + 1]];
    tidx[2] = corners[tri[3 * t + 2]];
    unsigned fv = 3;
    if (!tobj_vec_append(&b->m_idx, tidx, 3, b->alloc) ||
        !tobj_vec_append(&b->m_fv, &fv, 1, b->alloc) ||
        !tobj_vec_append(&b->m_mid, &b->cur_material, 1, b->alloc) ||
        !tobj_vec_append(&b->m_sg, &b->cur_smooth, 1, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  }
  b->cur_has_prims = true;
  return true;
}

static bool TOBJ_T(handle_f)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  b->corners.count = 0;
  const char *tok;
  size_t tlen;
  size_t arity = 0;
  while (tobj_next_token(c, &tok, &tlen)) {
    if (arity >= b->caps.arity) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
    tobj_index *slot = (tobj_index *)tobj_vec_push(&b->corners, b->alloc);
    if (!slot) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    TOBJ_T(parse_corner)(b, tok, tlen, slot);
    arity++;
  }
  if (arity < 3) {
    TOBJ_T(b_warn)(b, "tinyobjc: degenerate face (<3 vertices)\n");
    return true;
  }
  if (b->m_fv.count >= b->caps.faces) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
  return TOBJ_T(emit_face)(b, arity);
}

static bool TOBJ_T(handle_l)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  const char *tok;
  size_t tlen;
  size_t cnt = 0;
  size_t start = b->l_idx.count;
  while (tobj_next_token(c, &tok, &tlen)) {
    if (cnt >= b->caps.arity) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
    tobj_index idx;
    TOBJ_T(parse_corner)(b, tok, tlen, &idx);
    if (!tobj_vec_append(&b->l_idx, &idx, 1, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    cnt++;
  }
  if (cnt < 2) {
    b->l_idx.count = start; /* roll back */
    TOBJ_T(b_warn)(b, "tinyobjc: degenerate line (<2 vertices)\n");
    return true;
  }
  int icnt = tobj_size_to_int(cnt);
  if (!tobj_vec_append(&b->l_cnt, &icnt, 1, b->alloc))
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  b->cur_has_prims = true;
  return true;
}

static bool TOBJ_T(handle_p)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  const char *tok;
  size_t tlen;
  while (tobj_next_token(c, &tok, &tlen)) {
    tobj_index idx;
    TOBJ_T(parse_corner)(b, tok, tlen, &idx);
    if (!tobj_vec_append(&b->p_idx, &idx, 1, b->alloc))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    b->cur_has_prims = true;
  }
  return true;
}

/* ----------------------------------------------------------------------- */
/* shape finalize                                                          */
/* ----------------------------------------------------------------------- */

#define TOBJ_FIN(dst_ptr, dst_cnt, vec, T)                       \
  do {                                                           \
    (dst_cnt) = (vec).count;                                     \
    (dst_ptr) = (T *)tobj_vec_finalize(&(vec), b->arena, 16);    \
    if ((vec).count && !(dst_ptr)) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC); \
    (vec).count = 0;                                             \
  } while (0)

static bool TOBJ_T(ff_finalize_elem)(TOBJ_T(tobj_builder) * b); /* fwd */

static bool TOBJ_T(finalize_shape)(TOBJ_T(tobj_builder) * b) {
  if (b->ff_active && !TOBJ_T(ff_finalize_elem)(b)) return false;
  bool has_ff = b->sh_curves.count || b->sh_curves2.count ||
                b->sh_surfaces.count;
  if (!b->cur_has_prims && b->m_fv.count == 0 && b->l_cnt.count == 0 &&
      b->p_idx.count == 0 && !has_ff) {
    /* nothing to emit, but keep the name for the next group */
    return true;
  }
  if (b->shapes.count >= b->caps.shapes) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);

  TOBJ_T(tobj_shape) sh;
  tobj_memset(&sh, 0, sizeof sh);
  sh.name = b->cur_name ? b->cur_name : tobj_intern(b->arena, "", 0);
  if (!sh.name) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);

  size_t nf;
  TOBJ_FIN(sh.mesh.indices, sh.mesh.num_indices, b->m_idx, tobj_index);
  TOBJ_FIN(sh.mesh.num_face_vertices, nf, b->m_fv, unsigned);
  sh.mesh.num_faces = nf;
  TOBJ_FIN(sh.mesh.material_ids, nf, b->m_mid, int);
  TOBJ_FIN(sh.mesh.smoothing_group_ids, nf, b->m_sg, unsigned);

  TOBJ_FIN(sh.lines.indices, sh.lines.num_indices, b->l_idx, tobj_index);
  TOBJ_FIN(sh.lines.num_line_vertices, sh.lines.num_lines, b->l_cnt, int);

  TOBJ_FIN(sh.points.indices, sh.points.num_indices, b->p_idx, tobj_index);

  /* free-form geometry, if any accumulated for this shape */
  if (b->sh_curves.count || b->sh_curves2.count || b->sh_surfaces.count) {
    TOBJ_T(tobj_freeform) *ff = (TOBJ_T(tobj_freeform) *)tobj_arena_alloc(
        b->arena, sizeof(*ff), 16);
    if (!ff) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    tobj_memset(ff, 0, sizeof *ff);
    ff->vp.components = b->ff_vp_comps;
    ff->vp.uvw.count = b->ff_vp.count;
    ff->vp.uvw.ptr = (TOBJ_REAL *)tobj_arena_dup(
        b->arena, b->ff_vp.data, b->ff_vp.count * sizeof(TOBJ_REAL), 16);
    if (b->ff_vp.count && !ff->vp.uvw.ptr)
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    TOBJ_FIN(ff->curves, ff->num_curves, b->sh_curves, TOBJ_T(tobj_curve));
    TOBJ_FIN(ff->curves2, ff->num_curves2, b->sh_curves2, TOBJ_T(tobj_curve2));
    TOBJ_FIN(ff->surfaces, ff->num_surfaces, b->sh_surfaces,
             TOBJ_T(tobj_surface));
    sh.freeform = ff;
  }

  TOBJ_T(tobj_shape) *slot = (TOBJ_T(tobj_shape) *)tobj_vec_push(&b->shapes, b->alloc);
  if (!slot) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  *slot = sh;
  b->cur_has_prims = false;
  return true;
}

/* Start a new shape group with the given (interned) name. */
static bool TOBJ_T(new_group)(TOBJ_T(tobj_builder) * b, const char *name) {
  if (!TOBJ_T(finalize_shape)(b)) return false;
  b->cur_name = name;
  return true;
}

/* ----------------------------------------------------------------------- */
/* material support                                                        */
/* ----------------------------------------------------------------------- */

static void TOBJ_T(texopt_init)(TOBJ_T(tobj_texture_option) * t, tobj_arena *ar) {
  tobj_memset(t, 0, sizeof *t);
  t->type = TOBJ_TEXTURE_TYPE_NONE;
  t->sharpness = (TOBJ_REAL)1;
  t->brightness = (TOBJ_REAL)0;
  t->contrast = (TOBJ_REAL)1;
  t->scale[0] = t->scale[1] = t->scale[2] = (TOBJ_REAL)1;
  t->texture_resolution = -1;
  t->clamp = false;
  t->blendu = true;
  t->blendv = true;
  t->imfchan = 'm';
  t->bump_multiplier = (TOBJ_REAL)1;
  t->colorspace = tobj_intern(ar, "", 0);
}

static void TOBJ_T(material_init)(TOBJ_T(tobj_material) * m, tobj_arena *ar) {
  tobj_memset(m, 0, sizeof *m);
  m->shininess = (TOBJ_REAL)1;
  m->ior = (TOBJ_REAL)1;
  m->dissolve = (TOBJ_REAL)1;
  m->illum = 0;
  const char *empty = tobj_intern(ar, "", 0);
  m->name = empty;
  m->ambient_texname = m->diffuse_texname = m->specular_texname = empty;
  m->specular_highlight_texname = m->bump_texname = m->displacement_texname = empty;
  m->alpha_texname = m->reflection_texname = empty;
  m->roughness_texname = m->metallic_texname = m->sheen_texname = empty;
  m->emissive_texname = m->normal_texname = empty;
  TOBJ_T(texopt_init)(&m->ambient_texopt, ar);
  TOBJ_T(texopt_init)(&m->diffuse_texopt, ar);
  TOBJ_T(texopt_init)(&m->specular_texopt, ar);
  TOBJ_T(texopt_init)(&m->specular_highlight_texopt, ar);
  TOBJ_T(texopt_init)(&m->bump_texopt, ar);
  TOBJ_T(texopt_init)(&m->displacement_texopt, ar);
  TOBJ_T(texopt_init)(&m->alpha_texopt, ar);
  TOBJ_T(texopt_init)(&m->reflection_texopt, ar);
  TOBJ_T(texopt_init)(&m->roughness_texopt, ar);
  TOBJ_T(texopt_init)(&m->metallic_texopt, ar);
  TOBJ_T(texopt_init)(&m->sheen_texopt, ar);
  TOBJ_T(texopt_init)(&m->emissive_texopt, ar);
  TOBJ_T(texopt_init)(&m->normal_texopt, ar);
}

static int TOBJ_T(mat_find)(TOBJ_T(tobj_builder) * b, const char *name,
                            size_t len) {
  const char **keys = (const char **)b->matmap_key.data;
  const int *ids = (const int *)b->matmap_id.data;
  for (size_t i = 0; i < b->matmap_key.count; i++) {
    if (tobj_slice_eq(name, len, keys[i])) return ids[i];
  }
  return -1;
}

/* Read up to `n` reals from the cursor into dst (missing left untouched). */
static void TOBJ_T(read_reals)(tobj_cursor *c, TOBJ_REAL *dst, int n) {
  double d;
  for (int i = 0; i < n; i++) {
    if (!tobj_scan_double(&c->p, c->end, &d)) break;
    dst[i] = (TOBJ_REAL)d;
  }
}

/* Trim leading/trailing spaces of the cursor remainder and intern it. */
static const char *TOBJ_T(intern_rest)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  const char *p = c->p, *e = c->end;
  while (p < e && tobj_is_space(*p)) p++;
  while (e > p && tobj_is_space(e[-1])) e--;
  return tobj_intern(b->arena, p, (size_t)(e - p));
}

static bool TOBJ_T(tok_onoff)(const char *t, size_t l, bool *out) {
  if (tobj_slice_eq(t, l, "on")) {
    *out = true;
    return true;
  }
  if (tobj_slice_eq(t, l, "off")) {
    *out = false;
    return true;
  }
  return false;
}

/* Parse "[-options ...] filename" into texopt (+ interned name). Mirrors the
 * C++ ParseTextureNameAndOption. The cursor is consumed up to the filename. */
static const char *TOBJ_T(parse_texopt)(TOBJ_T(tobj_builder) * b, tobj_cursor *c,
                                        TOBJ_T(tobj_texture_option) * opt) {
  const char *tok;
  size_t tl;
  for (;;) {
    const char *save = c->p;
    if (!tobj_next_token(c, &tok, &tl)) {
      c->p = save;
      break;
    }
    if (tl == 0 || tok[0] != '-') {
      c->p = save; /* not an option: filename begins here */
      break;
    }
    if (tobj_slice_eq(tok, tl, "-blendu")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl)) TOBJ_T(tok_onoff)(v, vl, &opt->blendu);
    } else if (tobj_slice_eq(tok, tl, "-blendv")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl)) TOBJ_T(tok_onoff)(v, vl, &opt->blendv);
    } else if (tobj_slice_eq(tok, tl, "-clamp")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl)) TOBJ_T(tok_onoff)(v, vl, &opt->clamp);
    } else if (tobj_slice_eq(tok, tl, "-bm")) {
      TOBJ_T(read_reals)(c, &opt->bump_multiplier, 1);
    } else if (tobj_slice_eq(tok, tl, "-boost")) {
      TOBJ_T(read_reals)(c, &opt->sharpness, 1);
    } else if (tobj_slice_eq(tok, tl, "-o")) {
      TOBJ_T(read_reals)(c, opt->origin_offset, 3);
    } else if (tobj_slice_eq(tok, tl, "-s")) {
      TOBJ_T(read_reals)(c, opt->scale, 3);
    } else if (tobj_slice_eq(tok, tl, "-t")) {
      TOBJ_T(read_reals)(c, opt->turbulence, 3);
    } else if (tobj_slice_eq(tok, tl, "-mm")) {
      TOBJ_T(read_reals)(c, &opt->brightness, 1);
      TOBJ_T(read_reals)(c, &opt->contrast, 1);
    } else if (tobj_slice_eq(tok, tl, "-texres")) {
      int v = -1;
      tobj_scan_int(&c->p, c->end, &v);
      opt->texture_resolution = v;
    } else if (tobj_slice_eq(tok, tl, "-imfchan")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl) && vl >= 1) opt->imfchan = v[0];
    } else if (tobj_slice_eq(tok, tl, "-type")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl)) {
        if (tobj_slice_eq(v, vl, "sphere"))
          opt->type = TOBJ_TEXTURE_TYPE_SPHERE;
        else if (tobj_slice_eq(v, vl, "cube_top"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_TOP;
        else if (tobj_slice_eq(v, vl, "cube_bottom"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_BOTTOM;
        else if (tobj_slice_eq(v, vl, "cube_front"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_FRONT;
        else if (tobj_slice_eq(v, vl, "cube_back"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_BACK;
        else if (tobj_slice_eq(v, vl, "cube_left"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_LEFT;
        else if (tobj_slice_eq(v, vl, "cube_right"))
          opt->type = TOBJ_TEXTURE_TYPE_CUBE_RIGHT;
      }
    } else if (tobj_slice_eq(tok, tl, "-colorspace")) {
      const char *v;
      size_t vl;
      if (tobj_next_token(c, &v, &vl))
        opt->colorspace = tobj_intern(b->arena, v, vl);
    } else {
      /* unknown option flag: skip just the flag token */
    }
  }
  return TOBJ_T(intern_rest)(b, c);
}

/* Record an unrecognized "key value" .mtl line for material `mi`. */
static bool TOBJ_T(push_unknown)(TOBJ_T(tobj_builder) * b, size_t mi,
                                 const char *key, size_t keylen,
                                 tobj_cursor *c) {
  tobj_pending_kv *kv = (tobj_pending_kv *)tobj_vec_push(&b->mat_unknown, b->alloc);
  if (!kv) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  kv->mat_index = mi;
  kv->key = tobj_intern(b->arena, key, keylen);
  kv->value = TOBJ_T(intern_rest)(b, c);
  if (!kv->key || !kv->value) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  return true;
}

/* If map_Kd was given but Kd was not, default diffuse to 0.6 (C++ parity). */
static void TOBJ_T(apply_kd_default)(TOBJ_T(tobj_material) * m, bool kd_seen) {
  if (!kd_seen && m->diffuse_texname && m->diffuse_texname[0] != '\0') {
    m->diffuse[0] = m->diffuse[1] = m->diffuse[2] = (TOBJ_REAL)0.6;
  }
}

/* Full .mtl parser. */
static bool TOBJ_T(parse_mtl_buffer)(TOBJ_T(tobj_builder) * b,
                                     const uint8_t *data, size_t len) {
  tobj_vec lines;
  tobj_vec_init(&lines, sizeof(tobj_line));
  if (!tobj_build_line_index(data, len, &lines, b->alloc)) {
    tobj_vec_free(&lines, b->alloc);
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  }
  const char *base = (const char *)data;
  int cur = -1;
  bool kd_seen = false;
  for (size_t i = 0; i < lines.count && b->err == TOBJ_OK; i++) {
    tobj_line *ln = (tobj_line *)tobj_vec_at(&lines, i);
    if (ln->len > b->caps.line_bytes) continue;
    tobj_cursor c;
    tobj_cur_init(&c, base + ln->pos, ln->len);
    const char *tok;
    size_t tl;
    if (!tobj_next_token(&c, &tok, &tl)) continue;
    if (tl && tok[0] == '#') continue;

    if (tobj_slice_eq(tok, tl, "newmtl")) {
      if (cur >= 0)
        TOBJ_T(apply_kd_default)(
            (TOBJ_T(tobj_material) *)tobj_vec_at(&b->materials, (size_t)cur),
            kd_seen);
      if (b->materials.count >= b->caps.materials) {
        TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
        break;
      }
      TOBJ_T(tobj_material) *m =
          (TOBJ_T(tobj_material) *)tobj_vec_push(&b->materials, b->alloc);
      if (!m) {
        TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
        break;
      }
      TOBJ_T(material_init)(m, b->arena);
      m->name = TOBJ_T(intern_rest)(b, &c);
      cur = (int)(b->materials.count - 1);
      kd_seen = false;
      const char **k = (const char **)tobj_vec_push(&b->matmap_key, b->alloc);
      int *id = (int *)tobj_vec_push(&b->matmap_id, b->alloc);
      if (!k || !id) {
        TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
        break;
      }
      *k = m->name;
      *id = cur;
      continue;
    }
    if (cur < 0) continue;
    TOBJ_T(tobj_material) *m =
        (TOBJ_T(tobj_material) *)tobj_vec_at(&b->materials, (size_t)cur);

    if (tobj_slice_eq(tok, tl, "Ka")) {
      TOBJ_T(read_reals)(&c, m->ambient, 3);
    } else if (tobj_slice_eq(tok, tl, "Kd")) {
      TOBJ_T(read_reals)(&c, m->diffuse, 3);
      kd_seen = true;
    } else if (tobj_slice_eq(tok, tl, "Ks")) {
      TOBJ_T(read_reals)(&c, m->specular, 3);
    } else if (tobj_slice_eq(tok, tl, "Ke")) {
      TOBJ_T(read_reals)(&c, m->emission, 3);
    } else if (tobj_slice_eq(tok, tl, "Kt") || tobj_slice_eq(tok, tl, "Tf")) {
      TOBJ_T(read_reals)(&c, m->transmittance, 3);
    } else if (tobj_slice_eq(tok, tl, "Ns")) {
      TOBJ_T(read_reals)(&c, &m->shininess, 1);
    } else if (tobj_slice_eq(tok, tl, "Ni")) {
      TOBJ_T(read_reals)(&c, &m->ior, 1);
    } else if (tobj_slice_eq(tok, tl, "d")) {
      TOBJ_T(read_reals)(&c, &m->dissolve, 1);
    } else if (tobj_slice_eq(tok, tl, "Tr")) {
      TOBJ_REAL tr = 0;
      TOBJ_T(read_reals)(&c, &tr, 1);
      m->dissolve = (TOBJ_REAL)1 - tr;
    } else if (tobj_slice_eq(tok, tl, "illum")) {
      int v = 0;
      tobj_scan_int(&c.p, c.end, &v);
      m->illum = v;
    } else if (tobj_slice_eq(tok, tl, "Pr")) {
      TOBJ_T(read_reals)(&c, &m->roughness, 1);
    } else if (tobj_slice_eq(tok, tl, "Pm")) {
      TOBJ_T(read_reals)(&c, &m->metallic, 1);
    } else if (tobj_slice_eq(tok, tl, "Ps")) {
      TOBJ_T(read_reals)(&c, &m->sheen, 1);
    } else if (tobj_slice_eq(tok, tl, "Pc")) {
      TOBJ_T(read_reals)(&c, &m->clearcoat_thickness, 1);
    } else if (tobj_slice_eq(tok, tl, "Pcr")) {
      TOBJ_T(read_reals)(&c, &m->clearcoat_roughness, 1);
    } else if (tobj_slice_eq(tok, tl, "aniso")) {
      TOBJ_T(read_reals)(&c, &m->anisotropy, 1);
    } else if (tobj_slice_eq(tok, tl, "anisor")) {
      TOBJ_T(read_reals)(&c, &m->anisotropy_rotation, 1);
    } else if (tobj_slice_eq(tok, tl, "map_Ka")) {
      m->ambient_texname = TOBJ_T(parse_texopt)(b, &c, &m->ambient_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Kd")) {
      m->diffuse_texname = TOBJ_T(parse_texopt)(b, &c, &m->diffuse_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Ks")) {
      m->specular_texname = TOBJ_T(parse_texopt)(b, &c, &m->specular_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Ns")) {
      m->specular_highlight_texname =
          TOBJ_T(parse_texopt)(b, &c, &m->specular_highlight_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_d")) {
      m->alpha_texname = TOBJ_T(parse_texopt)(b, &c, &m->alpha_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_bump") ||
               tobj_slice_eq(tok, tl, "map_Bump") ||
               tobj_slice_eq(tok, tl, "bump")) {
      m->bump_texopt.imfchan = 'l';
      m->bump_texname = TOBJ_T(parse_texopt)(b, &c, &m->bump_texopt);
    } else if (tobj_slice_eq(tok, tl, "disp")) {
      m->displacement_texname =
          TOBJ_T(parse_texopt)(b, &c, &m->displacement_texopt);
    } else if (tobj_slice_eq(tok, tl, "refl")) {
      m->reflection_texname = TOBJ_T(parse_texopt)(b, &c, &m->reflection_texopt);
    } else if (tobj_slice_eq(tok, tl, "norm")) {
      m->normal_texname = TOBJ_T(parse_texopt)(b, &c, &m->normal_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Pr")) {
      m->roughness_texname = TOBJ_T(parse_texopt)(b, &c, &m->roughness_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Pm")) {
      m->metallic_texname = TOBJ_T(parse_texopt)(b, &c, &m->metallic_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Ps")) {
      m->sheen_texname = TOBJ_T(parse_texopt)(b, &c, &m->sheen_texopt);
    } else if (tobj_slice_eq(tok, tl, "map_Ke")) {
      m->emissive_texname = TOBJ_T(parse_texopt)(b, &c, &m->emissive_texopt);
    } else {
      /* unknown parameter: store key -> rest of line */
      if (!TOBJ_T(push_unknown)(b, (size_t)cur, tok, tl, &c)) break;
    }
  }

  if (cur >= 0)
    TOBJ_T(apply_kd_default)(
        (TOBJ_T(tobj_material) *)tobj_vec_at(&b->materials, (size_t)cur),
        kd_seen);
  tobj_vec_free(&lines, b->alloc);
  return b->err == TOBJ_OK;
}

static bool TOBJ_T(handle_mtllib)(TOBJ_T(tobj_builder) * b, tobj_cursor *c) {
  if (!b->cfg->mtl_resolver) {
    TOBJ_T(b_warn)(b, "tinyobjc: mtllib present but no material resolver\n");
    return true;
  }
  const char *tok;
  size_t tl;
  while (tobj_next_token(c, &tok, &tl)) {
    char *name = (char *)tobj_arena_alloc(b->arena, tl + 1, 1);
    if (!name) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    tobj_memcpy(name, tok, tl);
    name[tl] = '\0';
    tobj_mtl_source src;
    tobj_memset(&src, 0, sizeof src);
    tobj_result r =
        b->cfg->mtl_resolver(b->cfg->mtl_resolver_user_data, name, &src);
    if (r != TOBJ_OK) {
      TOBJ_T(b_warn)(b, "tinyobjc: failed to resolve mtllib\n");
      continue;
    }
    TOBJ_T(parse_mtl_buffer)(b, src.data, src.len);
    if (src.release) src.release(src.release_ud, src.data, src.len);
    if (b->err != TOBJ_OK) return false;
  }
  return true;
}

/* ----------------------------------------------------------------------- */
/* free-form geometry (parse & retain; no NURBS evaluation)                */
/* ----------------------------------------------------------------------- */

static void TOBJ_T(ff_reset_elem)(TOBJ_T(tobj_builder) * b) {
  b->ff_active = false;
  b->ff_kind = 0;
  b->ff_cp_int.count = 0;
  b->ff_cp_idx.count = 0;
  b->ff_knu.count = 0;
  b->ff_knv.count = 0;
  b->ff_trim.count = 0;
  b->ff_hole.count = 0;
  b->ff_scrv.count = 0;
}

static bool TOBJ_T(ff_finalize_elem)(TOBJ_T(tobj_builder) * b) {
  if (!b->ff_active) return true;
  if (b->ff_kind == 1) { /* curv */
    TOBJ_T(tobj_curve) *cv =
        (TOBJ_T(tobj_curve) *)tobj_vec_push(&b->sh_curves, b->alloc);
    if (!cv) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    cv->type = b->ff_cstype;
    cv->rational = b->ff_rational;
    cv->degree = b->ff_degu;
    cv->u0 = b->ff_u0;
    cv->u1 = b->ff_u1;
    cv->num_control_points = b->ff_cp_int.count;
    cv->control_points = (int *)tobj_vec_finalize(&b->ff_cp_int, b->arena, 16);
    cv->num_knots = b->ff_knu.count;
    cv->knots = (TOBJ_REAL *)tobj_vec_finalize(&b->ff_knu, b->arena, 16);
    if ((cv->num_control_points && !cv->control_points) ||
        (cv->num_knots && !cv->knots))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  } else if (b->ff_kind == 2) { /* curv2 */
    TOBJ_T(tobj_curve2) *cv =
        (TOBJ_T(tobj_curve2) *)tobj_vec_push(&b->sh_curves2, b->alloc);
    if (!cv) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    cv->type = b->ff_cstype;
    cv->rational = b->ff_rational;
    cv->degree = b->ff_degu;
    cv->num_control_points = b->ff_cp_int.count;
    cv->control_points = (int *)tobj_vec_finalize(&b->ff_cp_int, b->arena, 16);
    cv->num_knots = b->ff_knu.count;
    cv->knots = (TOBJ_REAL *)tobj_vec_finalize(&b->ff_knu, b->arena, 16);
    if ((cv->num_control_points && !cv->control_points) ||
        (cv->num_knots && !cv->knots))
      return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  } else if (b->ff_kind == 3) { /* surf */
    TOBJ_T(tobj_surface) *sf =
        (TOBJ_T(tobj_surface) *)tobj_vec_push(&b->sh_surfaces, b->alloc);
    if (!sf) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    sf->type = b->ff_cstype;
    sf->rational = b->ff_rational;
    sf->degu = b->ff_degu;
    sf->degv = b->ff_degv;
    sf->s0 = b->ff_s0;
    sf->s1 = b->ff_s1;
    sf->t0 = b->ff_t0;
    sf->t1 = b->ff_t1;
    sf->num_control_points = b->ff_cp_idx.count;
    sf->control_points =
        (tobj_index *)tobj_vec_finalize(&b->ff_cp_idx, b->arena, 16);
    sf->num_knots_u = b->ff_knu.count;
    sf->knots_u = (TOBJ_REAL *)tobj_vec_finalize(&b->ff_knu, b->arena, 16);
    sf->num_knots_v = b->ff_knv.count;
    sf->knots_v = (TOBJ_REAL *)tobj_vec_finalize(&b->ff_knv, b->arena, 16);
    sf->num_trims = b->ff_trim.count;
    sf->trims = (TOBJ_T(tobj_trim_loop) *)tobj_vec_finalize(&b->ff_trim,
                                                            b->arena, 16);
    sf->num_holes = b->ff_hole.count;
    sf->holes = (TOBJ_T(tobj_trim_loop) *)tobj_vec_finalize(&b->ff_hole,
                                                            b->arena, 16);
    sf->num_scrvs = b->ff_scrv.count;
    sf->scrvs = (TOBJ_T(tobj_trim_loop) *)tobj_vec_finalize(&b->ff_scrv,
                                                            b->arena, 16);
  }
  b->ff_present = true;
  TOBJ_T(ff_reset_elem)(b);
  return true;
}

static void TOBJ_T(ff_loops)(TOBJ_T(tobj_builder) * b, tobj_cursor *c,
                             tobj_vec *dst) {
  double u0, u1;
  int idx;
  while (tobj_scan_double(&c->p, c->end, &u0)) {
    if (!tobj_scan_double(&c->p, c->end, &u1)) break;
    if (!tobj_scan_int(&c->p, c->end, &idx)) break;
    TOBJ_T(tobj_trim_loop) *t =
        (TOBJ_T(tobj_trim_loop) *)tobj_vec_push(dst, b->alloc);
    if (!t) {
      TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
      return;
    }
    t->u0 = (TOBJ_REAL)u0;
    t->u1 = (TOBJ_REAL)u1;
    t->curve2_index = idx;
  }
}

static bool TOBJ_T(handle_freeform)(TOBJ_T(tobj_builder) * b, const char *tok,
                                    size_t tl, tobj_cursor *c) {
  if (tobj_slice_eq(tok, tl, "vp")) {
    double d;
    int n = 0;
    TOBJ_REAL uvw[3] = {0, 0, 0};
    for (; n < 3; n++) {
      if (!tobj_scan_double(&c->p, c->end, &d)) break;
      uvw[n] = (TOBJ_REAL)d;
    }
    if (n < 1) return true;
    if (n > b->ff_vp_comps) b->ff_vp_comps = n;
    return tobj_vec_append(&b->ff_vp, uvw, (size_t)n, b->alloc)
               ? true
               : TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  }
  if (tobj_slice_eq(tok, tl, "cstype")) {
    const char *t2;
    size_t l2;
    b->ff_rational = false;
    b->ff_cstype = TOBJ_CSTYPE_NONE;
    while (tobj_next_token(c, &t2, &l2)) {
      if (tobj_slice_eq(t2, l2, "rat"))
        b->ff_rational = true;
      else if (tobj_slice_eq(t2, l2, "bmatrix"))
        b->ff_cstype = TOBJ_CSTYPE_BMATRIX;
      else if (tobj_slice_eq(t2, l2, "bezier"))
        b->ff_cstype = TOBJ_CSTYPE_BEZIER;
      else if (tobj_slice_eq(t2, l2, "bspline"))
        b->ff_cstype = TOBJ_CSTYPE_BSPLINE;
      else if (tobj_slice_eq(t2, l2, "cardinal"))
        b->ff_cstype = TOBJ_CSTYPE_CARDINAL;
      else if (tobj_slice_eq(t2, l2, "taylor"))
        b->ff_cstype = TOBJ_CSTYPE_TAYLOR;
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "deg")) {
    int du = 0, dv = 0;
    if (tobj_scan_int(&c->p, c->end, &du)) b->ff_degu = du;
    if (tobj_scan_int(&c->p, c->end, &dv)) b->ff_degv = dv;
    return true;
  }
  if (tobj_slice_eq(tok, tl, "curv")) {
    TOBJ_T(ff_reset_elem)(b);
    b->ff_active = true;
    b->ff_kind = 1;
    double a, bb;
    b->ff_u0 = tobj_scan_double(&c->p, c->end, &a) ? (TOBJ_REAL)a : (TOBJ_REAL)0;
    b->ff_u1 = tobj_scan_double(&c->p, c->end, &bb) ? (TOBJ_REAL)bb : (TOBJ_REAL)0;
    int vi;
    size_t numv = TOBJ_T(cnt_v)(b);
    while (tobj_scan_int(&c->p, c->end, &vi)) {
      int r;
      TOBJ_T(fix_index)(vi, numv, &r);
      if (!tobj_vec_append(&b->ff_cp_int, &r, 1, b->alloc))
        return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "curv2")) {
    TOBJ_T(ff_reset_elem)(b);
    b->ff_active = true;
    b->ff_kind = 2;
    int vi;
    size_t numvp = b->prefilled
                       ? b->run_numvp
                       : (b->ff_vp_comps ? b->ff_vp.count / (size_t)b->ff_vp_comps
                                         : 0);
    while (tobj_scan_int(&c->p, c->end, &vi)) {
      int r;
      TOBJ_T(fix_index)(vi, numvp, &r);
      if (!tobj_vec_append(&b->ff_cp_int, &r, 1, b->alloc))
        return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "surf")) {
    TOBJ_T(ff_reset_elem)(b);
    b->ff_active = true;
    b->ff_kind = 3;
    double s0, s1, t0, t1;
    b->ff_s0 = tobj_scan_double(&c->p, c->end, &s0) ? (TOBJ_REAL)s0 : 0;
    b->ff_s1 = tobj_scan_double(&c->p, c->end, &s1) ? (TOBJ_REAL)s1 : 0;
    b->ff_t0 = tobj_scan_double(&c->p, c->end, &t0) ? (TOBJ_REAL)t0 : 0;
    b->ff_t1 = tobj_scan_double(&c->p, c->end, &t1) ? (TOBJ_REAL)t1 : 0;
    const char *t2;
    size_t l2;
    while (tobj_next_token(c, &t2, &l2)) {
      tobj_index idx;
      TOBJ_T(parse_corner_n)(t2, l2, TOBJ_T(cnt_v)(b), TOBJ_T(cnt_vt)(b),
                             TOBJ_T(cnt_vn)(b), &idx);
      if (!tobj_vec_append(&b->ff_cp_idx, &idx, 1, b->alloc))
        return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "parm")) {
    const char *t2;
    size_t l2;
    if (!tobj_next_token(c, &t2, &l2)) return true;
    tobj_vec *dst = tobj_slice_eq(t2, l2, "v") ? &b->ff_knv : &b->ff_knu;
    double d;
    while (tobj_scan_double(&c->p, c->end, &d)) {
      TOBJ_REAL r = (TOBJ_REAL)d;
      if (!tobj_vec_append(dst, &r, 1, b->alloc))
        return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "trim")) {
    TOBJ_T(ff_loops)(b, c, &b->ff_trim);
    return b->err == TOBJ_OK;
  }
  if (tobj_slice_eq(tok, tl, "hole")) {
    TOBJ_T(ff_loops)(b, c, &b->ff_hole);
    return b->err == TOBJ_OK;
  }
  if (tobj_slice_eq(tok, tl, "scrv")) {
    TOBJ_T(ff_loops)(b, c, &b->ff_scrv);
    return b->err == TOBJ_OK;
  }
  if (tobj_slice_eq(tok, tl, "end")) {
    return TOBJ_T(ff_finalize_elem)(b);
  }
  /* sp / con / bmat / step etc.: recognized but not retained */
  return true;
}

/* ----------------------------------------------------------------------- */
/* line dispatch                                                           */
/* ----------------------------------------------------------------------- */

static bool TOBJ_T(dispatch_line)(TOBJ_T(tobj_builder) * b, const char *p,
                                  size_t len) {
  if (len > b->caps.line_bytes) return TOBJ_T(b_fail)(b, TOBJ_ERR_LIMIT_EXCEEDED);
  tobj_cursor c;
  tobj_cur_init(&c, p, len);
  const char *tok;
  size_t tl;
  if (!tobj_next_token(&c, &tok, &tl)) return true;
  if (tok[0] == '#') return true;

  /* In MT pass 2 the vertex data is already parsed; just advance the running
   * counts used for relative-index resolution. */
  if (b->prefilled) {
    if (tobj_slice_eq(tok, tl, "v")) {
      b->run_numv++;
      return true;
    }
    if (tobj_slice_eq(tok, tl, "vn")) {
      b->run_numvn++;
      return true;
    }
    if (tobj_slice_eq(tok, tl, "vt")) {
      b->run_numvt++;
      return true;
    }
    if (tobj_slice_eq(tok, tl, "vp")) {
      b->run_numvp++;
      return true;
    }
  }

  if (tobj_slice_eq(tok, tl, "v")) return TOBJ_T(handle_v)(b, &c);
  if (tobj_slice_eq(tok, tl, "vn")) return TOBJ_T(handle_vn)(b, &c);
  if (tobj_slice_eq(tok, tl, "vt")) return TOBJ_T(handle_vt)(b, &c);
  if (tobj_slice_eq(tok, tl, "f")) return TOBJ_T(handle_f)(b, &c);
  if (tobj_slice_eq(tok, tl, "l")) return TOBJ_T(handle_l)(b, &c);
  if (tobj_slice_eq(tok, tl, "p")) return TOBJ_T(handle_p)(b, &c);
  if (tobj_slice_eq(tok, tl, "g") || tobj_slice_eq(tok, tl, "o")) {
    const char *name = TOBJ_T(intern_rest)(b, &c);
    if (!name) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    return TOBJ_T(new_group)(b, name);
  }
  if (tobj_slice_eq(tok, tl, "s")) {
    const char *st;
    size_t sl;
    if (tobj_next_token(&c, &st, &sl)) {
      if (tobj_slice_eq(st, sl, "off")) {
        b->cur_smooth = 0;
      } else {
        const char *q = st;
        int v = 0;
        tobj_scan_int(&q, st + sl, &v);
        b->cur_smooth = v > 0 ? (unsigned)v : 0u;
      }
    }
    return true;
  }
  if (tobj_slice_eq(tok, tl, "usemtl")) {
    const char *name = c.p;
    while (name < c.end && tobj_is_space(*name)) name++;
    const char *e = c.end;
    while (e > name && tobj_is_space(e[-1])) e--;
    int id = TOBJ_T(mat_find)(b, name, (size_t)(e - name));
    if (id < 0) TOBJ_T(b_warn)(b, "tinyobjc: usemtl references unknown material\n");
    b->cur_material = id;
    return true;
  }
  if (tobj_slice_eq(tok, tl, "mtllib")) return TOBJ_T(handle_mtllib)(b, &c);
  if (b->cfg->parse_freeform) return TOBJ_T(handle_freeform)(b, tok, tl, &c);
  /* unrecognized directive: silently skipped */
  return true;
}

/* ----------------------------------------------------------------------- */
/* public entry points                                                     */
/* ----------------------------------------------------------------------- */

/* Group pending unknown params by material, sort by key, attach to materials. */
static bool TOBJ_T(finalize_unknowns)(TOBJ_T(tobj_builder) * b) {
  if (b->mat_unknown.count == 0) return true;
  const tobj_pending_kv *pend = (const tobj_pending_kv *)b->mat_unknown.data;
  for (size_t mi = 0; mi < b->materials.count; mi++) {
    size_t cnt = 0;
    for (size_t j = 0; j < b->mat_unknown.count; j++)
      if (pend[j].mat_index == mi) cnt++;
    if (cnt == 0) continue;
    tobj_kv *arr = (tobj_kv *)tobj_arena_alloc(b->arena, cnt * sizeof(tobj_kv),
                                               16);
    if (!arr) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
    size_t w = 0;
    for (size_t j = 0; j < b->mat_unknown.count; j++) {
      if (pend[j].mat_index != mi) continue;
      /* stable insertion sort by key; equal keys keep insertion order */
      size_t pos = w;
      while (pos > 0 && tobj_strcmp(arr[pos - 1].key, pend[j].key) > 0) {
        arr[pos] = arr[pos - 1];
        pos--;
      }
      arr[pos].key = pend[j].key;
      arr[pos].value = pend[j].value;
      w++;
    }
    TOBJ_T(tobj_material) *m =
        (TOBJ_T(tobj_material) *)tobj_vec_at(&b->materials, mi);
    m->unknown_params = arr;
    m->num_unknown_params = w;
  }
  return true;
}

static void TOBJ_T(builder_init)(TOBJ_T(tobj_builder) * b) {
  tobj_vec_init(&b->av, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->avw, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->avn, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->avt, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->avtw, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->acol, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->materials, sizeof(TOBJ_T(tobj_material)));
  tobj_vec_init(&b->matmap_key, sizeof(const char *));
  tobj_vec_init(&b->matmap_id, sizeof(int));
  tobj_vec_init(&b->mat_unknown, sizeof(tobj_pending_kv));
  tobj_vec_init(&b->shapes, sizeof(TOBJ_T(tobj_shape)));
  tobj_vec_init(&b->m_idx, sizeof(tobj_index));
  tobj_vec_init(&b->m_fv, sizeof(unsigned));
  tobj_vec_init(&b->m_mid, sizeof(int));
  tobj_vec_init(&b->m_sg, sizeof(unsigned));
  tobj_vec_init(&b->l_idx, sizeof(tobj_index));
  tobj_vec_init(&b->l_cnt, sizeof(int));
  tobj_vec_init(&b->p_idx, sizeof(tobj_index));
  tobj_vec_init(&b->corners, sizeof(tobj_index));
  tobj_vec_init(&b->ringpos, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->tris, sizeof(uint32_t));
  tobj_vec_init(&b->tscratch, 1);
  tobj_vec_init(&b->ff_vp, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->ff_cp_int, sizeof(int));
  tobj_vec_init(&b->ff_cp_idx, sizeof(tobj_index));
  tobj_vec_init(&b->ff_knu, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->ff_knv, sizeof(TOBJ_REAL));
  tobj_vec_init(&b->ff_trim, sizeof(TOBJ_T(tobj_trim_loop)));
  tobj_vec_init(&b->ff_hole, sizeof(TOBJ_T(tobj_trim_loop)));
  tobj_vec_init(&b->ff_scrv, sizeof(TOBJ_T(tobj_trim_loop)));
  tobj_vec_init(&b->sh_curves, sizeof(TOBJ_T(tobj_curve)));
  tobj_vec_init(&b->sh_curves2, sizeof(TOBJ_T(tobj_curve2)));
  tobj_vec_init(&b->sh_surfaces, sizeof(TOBJ_T(tobj_surface)));
  b->ff_degu = 0;
  b->ff_degv = 0;
}

static void TOBJ_T(builder_dispose)(TOBJ_T(tobj_builder) * b) {
  const tobj_allocator *a = b->alloc;
  tobj_vec_free(&b->av, a);
  tobj_vec_free(&b->avw, a);
  tobj_vec_free(&b->avn, a);
  tobj_vec_free(&b->avt, a);
  tobj_vec_free(&b->avtw, a);
  tobj_vec_free(&b->acol, a);
  tobj_vec_free(&b->materials, a);
  tobj_vec_free(&b->matmap_key, a);
  tobj_vec_free(&b->matmap_id, a);
  tobj_vec_free(&b->mat_unknown, a);
  tobj_vec_free(&b->shapes, a);
  tobj_vec_free(&b->m_idx, a);
  tobj_vec_free(&b->m_fv, a);
  tobj_vec_free(&b->m_mid, a);
  tobj_vec_free(&b->m_sg, a);
  tobj_vec_free(&b->l_idx, a);
  tobj_vec_free(&b->l_cnt, a);
  tobj_vec_free(&b->p_idx, a);
  tobj_vec_free(&b->corners, a);
  tobj_vec_free(&b->ringpos, a);
  tobj_vec_free(&b->tris, a);
  tobj_vec_free(&b->tscratch, a);
  tobj_vec_free(&b->ff_vp, a);
  tobj_vec_free(&b->ff_cp_int, a);
  tobj_vec_free(&b->ff_cp_idx, a);
  tobj_vec_free(&b->ff_knu, a);
  tobj_vec_free(&b->ff_knv, a);
  tobj_vec_free(&b->ff_trim, a);
  tobj_vec_free(&b->ff_hole, a);
  tobj_vec_free(&b->ff_scrv, a);
  tobj_vec_free(&b->sh_curves, a);
  tobj_vec_free(&b->sh_curves2, a);
  tobj_vec_free(&b->sh_surfaces, a);
}

void TOBJ_T(tobj_scene_free)(TOBJ_T(tobj_scene) * s) {
  if (!s) return;
  if (s->arena) {
    tobj_arena *ar = (tobj_arena *)s->arena;
    tobj_allocator a = s->allocator;
    tobj_arena_destroy(ar);
    tobj_free(&a, ar, sizeof(tobj_arena));
  }
  tobj_memset(s, 0, sizeof *s);
}

const char *TOBJ_T(tobj_material_get_param)(const TOBJ_T(tobj_material) * m,
                                            const char *key) {
  if (!m || !key) return NULL;
  size_t lo = 0, hi = m->num_unknown_params;
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2;
    const char *k = m->unknown_params[mid].key;
    /* strcmp without libc */
    size_t i = 0;
    int cmp = 0;
    for (;; i++) {
      unsigned char a = (unsigned char)k[i], bb = (unsigned char)key[i];
      if (a != bb) {
        cmp = (int)a - (int)bb;
        break;
      }
      if (!a) break;
    }
    if (cmp == 0) return m->unknown_params[mid].value;
    if (cmp < 0)
      lo = mid + 1;
    else
      hi = mid;
  }
  return NULL;
}

#ifdef TOBJ_ENABLE_MULTITHREADING
/* Per-thread vertex-parse output (MT pass 1). */
typedef struct TOBJ_T(tobj_tls) {
  const char *base;
  const tobj_line *lines;
  size_t lo, hi;
  const tobj_allocator *alloc;
  bool store_colors;
  bool parse_vp;
  bool oom;
  tobj_vec lv, lvw, lvw_has, lcol, lcol_has, lvn, lvt, lvtw, lvtw_has, lvp;
  int vp_comps;
} TOBJ_T(tobj_tls);

static void TOBJ_T(mt_worker)(void *arg) {
  TOBJ_T(tobj_tls) *w = (TOBJ_T(tobj_tls) *)arg;
  const tobj_allocator *a = w->alloc;
  for (size_t i = w->lo; i < w->hi && !w->oom; i++) {
    const tobj_line *ln = &w->lines[i];
    tobj_cursor c;
    tobj_cur_init(&c, w->base + ln->pos, ln->len);
    const char *tok;
    size_t tl;
    if (!tobj_next_token(&c, &tok, &tl)) continue;
    if (tobj_slice_eq(tok, tl, "v")) {
      double nums[8];
      int n = 0;
      while (n < 8) {
        double d;
        const char *s = c.p;
        if (!tobj_scan_double(&c.p, c.end, &d)) {
          c.p = s;
          break;
        }
        nums[n++] = d;
      }
      while (n < 3) nums[n++] = 0.0;
      TOBJ_REAL xyz[3] = {(TOBJ_REAL)nums[0], (TOBJ_REAL)nums[1],
                          (TOBJ_REAL)nums[2]};
      uint8_t wh = (n == 4);
      TOBJ_REAL wv = wh ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1;
      if (!tobj_vec_append(&w->lv, xyz, 3, a) ||
          !tobj_vec_append(&w->lvw, &wv, 1, a) ||
          !tobj_vec_append(&w->lvw_has, &wh, 1, a)) {
        w->oom = true;
        return;
      }
      if (w->store_colors) {
        uint8_t ch = (n >= 6);
        TOBJ_REAL rgb[3] = {ch ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1,
                            ch ? (TOBJ_REAL)nums[4] : (TOBJ_REAL)1,
                            ch ? (TOBJ_REAL)nums[5] : (TOBJ_REAL)1};
        if (!tobj_vec_append(&w->lcol, rgb, 3, a) ||
            !tobj_vec_append(&w->lcol_has, &ch, 1, a)) {
          w->oom = true;
          return;
        }
      }
    } else if (tobj_slice_eq(tok, tl, "vn")) {
      TOBJ_REAL xyz[3] = {0, 0, 0};
      double d;
      for (int k = 0; k < 3; k++)
        if (tobj_scan_double(&c.p, c.end, &d)) xyz[k] = (TOBJ_REAL)d;
      if (!tobj_vec_append(&w->lvn, xyz, 3, a)) {
        w->oom = true;
        return;
      }
    } else if (tobj_slice_eq(tok, tl, "vt")) {
      double d;
      TOBJ_REAL uv[2] = {0, 0};
      int n = 0;
      for (; n < 2; n++) {
        if (!tobj_scan_double(&c.p, c.end, &d)) break;
        uv[n] = (TOBJ_REAL)d;
      }
      uint8_t wh = (uint8_t)tobj_scan_double(&c.p, c.end, &d);
      TOBJ_REAL wv = wh ? (TOBJ_REAL)d : (TOBJ_REAL)0;
      if (!tobj_vec_append(&w->lvt, uv, 2, a) ||
          !tobj_vec_append(&w->lvtw, &wv, 1, a) ||
          !tobj_vec_append(&w->lvtw_has, &wh, 1, a)) {
        w->oom = true;
        return;
      }
    } else if (w->parse_vp && tobj_slice_eq(tok, tl, "vp")) {
      double d;
      int n = 0;
      TOBJ_REAL uvw[3] = {0, 0, 0};
      for (; n < 3; n++) {
        if (!tobj_scan_double(&c.p, c.end, &d)) break;
        uvw[n] = (TOBJ_REAL)d;
      }
      if (n < 1) continue;
      if (n > w->vp_comps) w->vp_comps = n;
      if (!tobj_vec_append(&w->lvp, uvw, (size_t)n, a)) {
        w->oom = true;
        return;
      }
    }
  }
}

/* Reconstruct a lazy optional array (weights/colors/texcoord-w) from the
 * per-thread (value,has) streams, reproducing the single-threaded semantics
 * exactly: empty until the first present entry, then dense with backfill. */
static bool TOBJ_T(mt_lazy)(tobj_vec *dst, size_t comps, const TOBJ_REAL *dflt,
                            TOBJ_T(tobj_tls) * tls, int T, int kind,
                            const tobj_allocator *a) {
  bool started = false;
  size_t gi = 0;
  for (int t = 0; t < T; t++) {
    tobj_vec *vval = (kind == 0) ? &tls[t].lvw
                                 : (kind == 1) ? &tls[t].lcol : &tls[t].lvtw;
    tobj_vec *vhas = (kind == 0) ? &tls[t].lvw_has
                                 : (kind == 1) ? &tls[t].lcol_has
                                               : &tls[t].lvtw_has;
    size_t cnt = vhas->count;
    const TOBJ_REAL *val = (const TOBJ_REAL *)vval->data;
    const uint8_t *has = (const uint8_t *)vhas->data;
    for (size_t j = 0; j < cnt; j++, gi++) {
      if (has[j] || started) {
        if (!started) {
          for (size_t k = 0; k < gi; k++)
            if (!tobj_vec_append(dst, dflt, comps, a)) return false;
          started = true;
        }
        if (!tobj_vec_append(dst, &val[j * comps], comps, a)) return false;
      }
    }
  }
  return true;
}

/* MT pass 1: parse v/vn/vt/vp in parallel and merge into the builder's attrib
 * arrays, reproducing single-threaded output exactly. Sets b->prefilled. */
static bool TOBJ_T(mt_prepass)(TOBJ_T(tobj_builder) * b, const tobj_vec *lines,
                               const char *base, int T) {
  const tobj_allocator *a = b->alloc;
  TOBJ_T(tobj_tls) *tls =
      (TOBJ_T(tobj_tls) *)tobj_alloc(a, (size_t)T * sizeof(*tls), 16);
  tobj_thunk *thunks = (tobj_thunk *)tobj_alloc(a, (size_t)T * sizeof(*thunks),
                                                16);
  if (!tls || !thunks) {
    if (tls) tobj_free(a, tls, (size_t)T * sizeof(*tls));
    if (thunks) tobj_free(a, thunks, (size_t)T * sizeof(*thunks));
    return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  }
  size_t nlines = lines->count;
  const tobj_line *ld = (const tobj_line *)lines->data;
  for (int t = 0; t < T; t++) {
    tobj_memset(&tls[t], 0, sizeof tls[t]);
    tls[t].base = base;
    tls[t].lines = ld;
    tls[t].lo = (size_t)t * nlines / (size_t)T;
    tls[t].hi = (size_t)(t + 1) * nlines / (size_t)T;
    tls[t].alloc = a;
    tls[t].store_colors = b->cfg->store_vertex_colors;
    tls[t].parse_vp = b->cfg->parse_freeform;
    tobj_vec_init(&tls[t].lv, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lvw, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lvw_has, 1);
    tobj_vec_init(&tls[t].lcol, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lcol_has, 1);
    tobj_vec_init(&tls[t].lvn, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lvt, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lvtw, sizeof(TOBJ_REAL));
    tobj_vec_init(&tls[t].lvtw_has, 1);
    tobj_vec_init(&tls[t].lvp, sizeof(TOBJ_REAL));
    thunks[t].fn = TOBJ_T(mt_worker);
    thunks[t].arg = &tls[t];
  }

  tobj_run_parallel(thunks, T);

  bool ok = true;
  for (int t = 0; t < T; t++)
    if (tls[t].oom) ok = false;

  /* merge plain arrays in thread (= file) order */
  for (int t = 0; ok && t < T; t++) {
    if (!tobj_vec_append(&b->av, tls[t].lv.data, tls[t].lv.count, a) ||
        !tobj_vec_append(&b->avn, tls[t].lvn.data, tls[t].lvn.count, a) ||
        !tobj_vec_append(&b->avt, tls[t].lvt.data, tls[t].lvt.count, a))
      ok = false;
    if (ok && b->cfg->parse_freeform && tls[t].lvp.count) {
      if (!tobj_vec_append(&b->ff_vp, tls[t].lvp.data, tls[t].lvp.count, a))
        ok = false;
      if (tls[t].vp_comps > b->ff_vp_comps) b->ff_vp_comps = tls[t].vp_comps;
    }
  }
  /* reconstruct lazy optional arrays */
  if (ok) {
    TOBJ_REAL d1 = (TOBJ_REAL)1, d0 = (TOBJ_REAL)0;
    TOBJ_REAL white[3] = {(TOBJ_REAL)1, (TOBJ_REAL)1, (TOBJ_REAL)1};
    if (!TOBJ_T(mt_lazy)(&b->avw, 1, &d1, tls, T, 0, a)) ok = false;
    if (ok && b->cfg->store_vertex_colors &&
        !TOBJ_T(mt_lazy)(&b->acol, 3, white, tls, T, 1, a))
      ok = false;
    if (ok && !TOBJ_T(mt_lazy)(&b->avtw, 1, &d0, tls, T, 2, a)) ok = false;
  }

  for (int t = 0; t < T; t++) {
    tobj_vec_free(&tls[t].lv, a);
    tobj_vec_free(&tls[t].lvw, a);
    tobj_vec_free(&tls[t].lvw_has, a);
    tobj_vec_free(&tls[t].lcol, a);
    tobj_vec_free(&tls[t].lcol_has, a);
    tobj_vec_free(&tls[t].lvn, a);
    tobj_vec_free(&tls[t].lvt, a);
    tobj_vec_free(&tls[t].lvtw, a);
    tobj_vec_free(&tls[t].lvtw_has, a);
    tobj_vec_free(&tls[t].lvp, a);
  }
  tobj_free(a, tls, (size_t)T * sizeof(*tls));
  tobj_free(a, thunks, (size_t)T * sizeof(*thunks));
  if (!ok) return TOBJ_T(b_fail)(b, TOBJ_ERR_ALLOC);
  b->prefilled = true;
  return true;
}
#endif /* TOBJ_ENABLE_MULTITHREADING */

tobj_result TOBJ_T(tobj_load_obj_from_memory)(TOBJ_T(tobj_scene) * out,
                                              const uint8_t *buf, size_t len,
                                              const tobj_load_config *cfg,
                                              tobj_diag *diag) {
  if (!out) return TOBJ_ERR_INVALID_ARG;
  tobj_memset(out, 0, sizeof *out);
  if (!buf && len) return TOBJ_ERR_INVALID_ARG;

  tobj_load_config defcfg;
  if (!cfg) {
    defcfg = tobj_default_config();
    cfg = &defcfg;
  }
  if (len > tobj_resolve_caps(cfg).input_bytes) return TOBJ_ERR_LIMIT_EXCEEDED;

  tobj_allocator alloc;
  if (!tobj_resolve_allocator(&cfg->allocator, &alloc))
    return TOBJ_ERR_INVALID_ARG;

  tobj_arena *arena = (tobj_arena *)tobj_alloc(&alloc, sizeof(tobj_arena), 16);
  if (!arena) return TOBJ_ERR_ALLOC;
  tobj_arena_init(arena, &alloc, cfg->use_arena ? (size_t)(1u << 20) : 0);

  TOBJ_T(tobj_builder) b;
  tobj_memset(&b, 0, sizeof b);
  b.alloc = &alloc;
  b.arena = arena;
  b.diag = diag;
  b.cfg = cfg;
  b.caps = tobj_resolve_caps(cfg);
  b.err = TOBJ_OK;
  b.triangulate = cfg->triangulate;
  b.cur_material = -1;
  b.cur_smooth = 0;
  b.cur_name = NULL;
  TOBJ_T(builder_init)(&b);

  tobj_vec lines;
  tobj_vec_init(&lines, sizeof(tobj_line));
  if (!tobj_build_line_index(buf, len, &lines, &alloc)) {
    b.err = TOBJ_ERR_ALLOC;
  }

  const char *base = (const char *)buf;

#ifdef TOBJ_ENABLE_MULTITHREADING
  if (b.err == TOBJ_OK) {
    int T = cfg->num_threads < 0 ? (int)tobj_hw_threads() : cfg->num_threads;
    if (T > 64) T = 64;
    /* Only worth threading on sizeable inputs. */
    if (T > 1 && lines.count >= (size_t)(256 * T)) {
      TOBJ_T(mt_prepass)(&b, &lines, base, T);
    }
  }
#endif

  for (size_t i = 0; i < lines.count && b.err == TOBJ_OK; i++) {
    tobj_line *ln = (tobj_line *)tobj_vec_at(&lines, i);
    b.line = i + 1;
    TOBJ_T(dispatch_line)(&b, base + ln->pos, ln->len);
  }

  if (b.err == TOBJ_OK) TOBJ_T(finalize_shape)(&b);

  /* vertex color fallback: fill white if requested and none present */
  if (b.err == TOBJ_OK && cfg->store_vertex_colors &&
      cfg->vertex_color_fallback && b.acol.count == 0) {
    size_t numv = b.av.count / 3u;
    TOBJ_REAL white[3] = {(TOBJ_REAL)1, (TOBJ_REAL)1, (TOBJ_REAL)1};
    for (size_t i = 0; i < numv && b.err == TOBJ_OK; i++) {
      if (!tobj_vec_append(&b.acol, white, 3, &alloc)) b.err = TOBJ_ERR_ALLOC;
    }
  }

  if (b.err == TOBJ_OK) {
#define TOBJ_FIN_BUF(field, vec)                                        \
  do {                                                                  \
    out->attrib.field.count = (vec).count;                              \
    out->attrib.field.ptr =                                             \
        (TOBJ_REAL *)tobj_vec_finalize(&(vec), arena, 16);              \
    if ((vec).count && !out->attrib.field.ptr) b.err = TOBJ_ERR_ALLOC;  \
  } while (0)
    TOBJ_FIN_BUF(vertices, b.av);
    TOBJ_FIN_BUF(vertex_weights, b.avw);
    TOBJ_FIN_BUF(normals, b.avn);
    TOBJ_FIN_BUF(texcoords, b.avt);
    TOBJ_FIN_BUF(texcoord_ws, b.avtw);
    TOBJ_FIN_BUF(colors, b.acol);
#undef TOBJ_FIN_BUF
  }

  if (b.err == TOBJ_OK) TOBJ_T(finalize_unknowns)(&b);

  if (b.err == TOBJ_OK) {
    out->num_shapes = b.shapes.count;
    out->shapes = (TOBJ_T(tobj_shape) *)tobj_vec_finalize(
        &b.shapes, arena, 16);
    if (b.shapes.count && !out->shapes) b.err = TOBJ_ERR_ALLOC;
    out->num_materials = b.materials.count;
    out->materials = (TOBJ_T(tobj_material) *)tobj_vec_finalize(
        &b.materials, arena, 16);
    if (b.materials.count && !out->materials) b.err = TOBJ_ERR_ALLOC;
  }

  TOBJ_T(builder_dispose)(&b);
  tobj_vec_free(&lines, &alloc);

  if (b.err != TOBJ_OK) {
    tobj_arena_destroy(arena);
    tobj_free(&alloc, arena, sizeof(tobj_arena));
    tobj_memset(out, 0, sizeof *out);
    return b.err;
  }

  out->allocator = alloc;
  out->arena = arena;
  out->strpool = NULL;
  return TOBJ_OK;
}

tobj_result TOBJ_T(tobj_load_obj_from_io)(TOBJ_T(tobj_scene) * out,
                                          const tobj_io_callbacks *io,
                                          const tobj_load_config *cfg,
                                          tobj_diag *diag) {
  if (!out) return TOBJ_ERR_INVALID_ARG;
  tobj_memset(out, 0, sizeof *out);
  if (!io || !io->read) return TOBJ_ERR_INVALID_ARG;

  tobj_load_config cc = cfg ? *cfg : tobj_default_config();
  tobj_allocator alloc;
  if (!tobj_resolve_allocator(&cc.allocator, &alloc))
    return TOBJ_ERR_INVALID_ARG;
  cc.allocator = alloc;

  tobj_caps caps = tobj_resolve_caps(&cc);
  tobj_vec buf;
  tobj_vec_init(&buf, 1);
  tobj_result r = TOBJ_OK;

  for (;;) {
    size_t remain = caps.input_bytes - buf.count;
    if (remain == 0) {
      uint8_t extra;
      size_t got = 0;
      r = io->read(io->user_data, &extra, 1, &got);
      if (r == TOBJ_OK && got != 0) r = TOBJ_ERR_LIMIT_EXCEEDED;
      break;
    }
    size_t want = remain < (size_t)(64u * 1024u) ? remain
                                                  : (size_t)(64u * 1024u);
    size_t old = buf.count;
    if (!tobj_vec_reserve(&buf, old + want, &alloc)) {
      r = TOBJ_ERR_ALLOC;
      break;
    }
    size_t got = 0;
    r = io->read(io->user_data, (uint8_t *)buf.data + old, want, &got);
    if (r != TOBJ_OK) break;
    if (got > want) {
      r = TOBJ_ERR_IO;
      break;
    }
    if (got == 0) break;
    buf.count = old + got;
  }

  if (io->close) io->close(io->user_data);
  if (r == TOBJ_OK)
    r = TOBJ_T(tobj_load_obj_from_memory)(out, (const uint8_t *)buf.data,
                                          buf.count, &cc, diag);
  tobj_vec_free(&buf, &alloc);
  return r;
}

#ifdef TOBJ_ENABLE_FILE_IO
tobj_result TOBJ_T(tobj_load_obj_from_file)(TOBJ_T(tobj_scene) * out,
                                            const char *path,
                                            const tobj_load_config *cfg,
                                            tobj_diag *diag) {
  if (!out) return TOBJ_ERR_INVALID_ARG;
  tobj_memset(out, 0, sizeof *out);
  if (!path) return TOBJ_ERR_INVALID_ARG;

  tobj_load_config cc = cfg ? *cfg : tobj_default_config();
  tobj_allocator alloc;
  if (!tobj_resolve_allocator(&cc.allocator, &alloc))
    return TOBJ_ERR_INVALID_ARG;
  cc.allocator = alloc;

  tobj_file_buf fb;
  tobj_result r = tobj_file_open(&fb, path, &alloc,
                                 tobj_resolve_caps(&cc).input_bytes);
  if (r != TOBJ_OK) return r;

  size_t dlen;
  char *basedir = tobj_dirname_dup(path, &alloc, &dlen);
  if (!basedir) {
    tobj_file_close(&fb);
    return TOBJ_ERR_ALLOC;
  }
  tobj_file_res_ctx ctx;
  ctx.basedir = basedir;
  ctx.alloc = alloc;
  ctx.max_bytes = tobj_resolve_caps(&cc).input_bytes;
  if (!cc.mtl_resolver) {
    cc.mtl_resolver = tobj_file_material_resolver;
    cc.mtl_resolver_user_data = &ctx;
  }

  r = TOBJ_T(tobj_load_obj_from_memory)(out, fb.data, fb.len, &cc, diag);

  tobj_free(&alloc, basedir, dlen + 1);
  tobj_file_close(&fb);
  return r;
}
#endif /* TOBJ_ENABLE_FILE_IO */

/* ----------------------------------------------------------------------- */
/* standalone .mtl parsing                                                 */
/* ----------------------------------------------------------------------- */

tobj_result TOBJ_T(tobj_parse_mtl_from_memory)(TOBJ_T(tobj_material_list) * out,
                                               const uint8_t *buf, size_t len,
                                               const tobj_load_config *cfg,
                                               tobj_diag *diag) {
  if (!out) return TOBJ_ERR_INVALID_ARG;
  tobj_memset(out, 0, sizeof *out);
  if (!buf && len) return TOBJ_ERR_INVALID_ARG;

  tobj_load_config defcfg;
  if (!cfg) {
    defcfg = tobj_default_config();
    cfg = &defcfg;
  }
  if (len > tobj_resolve_caps(cfg).input_bytes) return TOBJ_ERR_LIMIT_EXCEEDED;
  tobj_allocator alloc;
  if (!tobj_resolve_allocator(&cfg->allocator, &alloc))
    return TOBJ_ERR_INVALID_ARG;
  tobj_arena *arena = (tobj_arena *)tobj_alloc(&alloc, sizeof(tobj_arena), 16);
  if (!arena) return TOBJ_ERR_ALLOC;
  tobj_arena_init(arena, &alloc, 0);

  TOBJ_T(tobj_builder) b;
  tobj_memset(&b, 0, sizeof b);
  b.alloc = &alloc;
  b.arena = arena;
  b.diag = diag;
  b.cfg = cfg;
  b.caps = tobj_resolve_caps(cfg);
  b.err = TOBJ_OK;
  TOBJ_T(builder_init)(&b);

  TOBJ_T(parse_mtl_buffer)(&b, buf, len);
  if (b.err == TOBJ_OK) TOBJ_T(finalize_unknowns)(&b);

  if (b.err == TOBJ_OK) {
    out->count = b.materials.count;
    out->items = (TOBJ_T(tobj_material) *)tobj_vec_finalize(&b.materials,
                                                            arena, 16);
    if (b.materials.count && !out->items) b.err = TOBJ_ERR_ALLOC;
  }

  TOBJ_T(builder_dispose)(&b);

  if (b.err != TOBJ_OK) {
    tobj_arena_destroy(arena);
    tobj_free(&alloc, arena, sizeof(tobj_arena));
    tobj_memset(out, 0, sizeof *out);
    return b.err;
  }
  out->allocator = alloc;
  out->strpool = arena;
  return TOBJ_OK;
}

void TOBJ_T(tobj_material_list_free)(TOBJ_T(tobj_material_list) * list) {
  if (!list) return;
  if (list->strpool) {
    tobj_arena *ar = (tobj_arena *)list->strpool;
    tobj_allocator a = list->allocator;
    tobj_arena_destroy(ar);
    tobj_free(&a, ar, sizeof(tobj_arena));
  }
  tobj_memset(list, 0, sizeof *list);
}

/* ----------------------------------------------------------------------- */
/* streaming callback API                                                  */
/* ----------------------------------------------------------------------- */

tobj_result TOBJ_T(tobj_load_obj_with_callbacks)(
    const uint8_t *buf, size_t len, const TOBJ_T(tobj_callbacks) * cb,
    const tobj_load_config *cfg, tobj_diag *diag) {
  if (!cb) return TOBJ_ERR_INVALID_ARG;
  if (!buf && len) return TOBJ_ERR_INVALID_ARG;

  tobj_load_config defcfg;
  if (!cfg) {
    defcfg = tobj_default_config();
    cfg = &defcfg;
  }
  if (len > tobj_resolve_caps(cfg).input_bytes) return TOBJ_ERR_LIMIT_EXCEEDED;
  tobj_allocator alloc;
  if (!tobj_resolve_allocator(&cfg->allocator, &alloc))
    return TOBJ_ERR_INVALID_ARG;
  tobj_arena *arena = (tobj_arena *)tobj_alloc(&alloc, sizeof(tobj_arena), 16);
  if (!arena) return TOBJ_ERR_ALLOC;
  tobj_arena_init(arena, &alloc, 0);

  TOBJ_T(tobj_builder) b;
  tobj_memset(&b, 0, sizeof b);
  b.alloc = &alloc;
  b.arena = arena;
  b.diag = diag;
  b.cfg = cfg;
  b.caps = tobj_resolve_caps(cfg);
  b.err = TOBJ_OK;
  TOBJ_T(builder_init)(&b);
  void *ud = cb->user_data;

  tobj_vec lines;
  tobj_vec_init(&lines, sizeof(tobj_line));
  if (!tobj_build_line_index(buf, len, &lines, &alloc)) b.err = TOBJ_ERR_ALLOC;

  size_t numv = 0, numvt = 0, numvn = 0;
  const char *base = (const char *)buf;

  for (size_t i = 0; i < lines.count && b.err == TOBJ_OK; i++) {
    tobj_line *ln = (tobj_line *)tobj_vec_at(&lines, i);
    b.line = i + 1;
    if (ln->len > b.caps.line_bytes) {
      b.err = TOBJ_ERR_LIMIT_EXCEEDED;
      break;
    }
    tobj_cursor c;
    tobj_cur_init(&c, base + ln->pos, ln->len);
    const char *tok;
    size_t tl;
    if (!tobj_next_token(&c, &tok, &tl)) continue;
    if (tok[0] == '#') continue;

    if (tobj_slice_eq(tok, tl, "v")) {
      double nums[8];
      int n = 0;
      while (n < 8) {
        double d;
        const char *save = c.p;
        if (!tobj_scan_double(&c.p, c.end, &d)) {
          c.p = save;
          break;
        }
        nums[n++] = d;
      }
      while (n < 3) nums[n++] = 0.0;
      TOBJ_REAL w = (n == 4) ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1;
      if (cb->vertex_cb)
        cb->vertex_cb(ud, (TOBJ_REAL)nums[0], (TOBJ_REAL)nums[1],
                      (TOBJ_REAL)nums[2], w);
      if (cb->vertex_color_cb) {
        bool hc = n >= 6;
        cb->vertex_color_cb(ud, (TOBJ_REAL)nums[0], (TOBJ_REAL)nums[1],
                            (TOBJ_REAL)nums[2],
                            hc ? (TOBJ_REAL)nums[3] : (TOBJ_REAL)1,
                            hc ? (TOBJ_REAL)nums[4] : (TOBJ_REAL)1,
                            hc ? (TOBJ_REAL)nums[5] : (TOBJ_REAL)1, hc);
      }
      numv++;
    } else if (tobj_slice_eq(tok, tl, "vn")) {
      double d;
      TOBJ_REAL xyz[3] = {0, 0, 0};
      for (int k = 0; k < 3; k++)
        if (tobj_scan_double(&c.p, c.end, &d)) xyz[k] = (TOBJ_REAL)d;
      if (cb->normal_cb) cb->normal_cb(ud, xyz[0], xyz[1], xyz[2]);
      numvn++;
    } else if (tobj_slice_eq(tok, tl, "vt")) {
      double d;
      TOBJ_REAL uvw[3] = {0, 0, 0};
      for (int k = 0; k < 3; k++)
        if (tobj_scan_double(&c.p, c.end, &d)) uvw[k] = (TOBJ_REAL)d;
      if (cb->texcoord_cb) cb->texcoord_cb(ud, uvw[0], uvw[1], uvw[2]);
      numvt++;
    } else if (tobj_slice_eq(tok, tl, "f") || tobj_slice_eq(tok, tl, "l") ||
               tobj_slice_eq(tok, tl, "p")) {
      char kind = tok[0];
      b.corners.count = 0;
      const char *t2;
      size_t l2;
      while (tobj_next_token(&c, &t2, &l2)) {
        tobj_index *slot = (tobj_index *)tobj_vec_push(&b.corners, &alloc);
        if (!slot) {
          b.err = TOBJ_ERR_ALLOC;
          break;
        }
        TOBJ_T(parse_corner_n)(t2, l2, numv, numvt, numvn, slot);
      }
      if (b.err != TOBJ_OK) break;
      int nidx = tobj_size_to_int(b.corners.count);
      const tobj_index *ci = (const tobj_index *)b.corners.data;
      if (kind == 'f' && cb->index_cb && nidx >= 3)
        cb->index_cb(ud, ci, nidx);
      else if (kind == 'l' && cb->line_cb && nidx >= 2)
        cb->line_cb(ud, ci, nidx);
      else if (kind == 'p' && cb->point_cb && nidx >= 1)
        cb->point_cb(ud, ci, nidx);
    } else if (tobj_slice_eq(tok, tl, "g") || tobj_slice_eq(tok, tl, "o")) {
      const char *name = TOBJ_T(intern_rest)(&b, &c);
      if (!name) {
        b.err = TOBJ_ERR_ALLOC;
        break;
      }
      if (tok[0] == 'o') {
        if (cb->object_cb) cb->object_cb(ud, name);
      } else {
        if (cb->group_cb) {
          const char *names[1] = {name};
          cb->group_cb(ud, names, 1);
        }
      }
    } else if (tobj_slice_eq(tok, tl, "usemtl")) {
      const char *p = c.p, *e = c.end;
      while (p < e && tobj_is_space(*p)) p++;
      while (e > p && tobj_is_space(e[-1])) e--;
      int id = TOBJ_T(mat_find)(&b, p, (size_t)(e - p));
      if (cb->usemtl_cb) {
        const char *name = tobj_intern(arena, p, (size_t)(e - p));
        cb->usemtl_cb(ud, name, id);
      }
    } else if (tobj_slice_eq(tok, tl, "mtllib")) {
      if (cfg->mtl_resolver) {
        const char *t2;
        size_t l2;
        size_t before = b.materials.count;
        while (tobj_next_token(&c, &t2, &l2)) {
          char *name = (char *)tobj_arena_alloc(arena, l2 + 1, 1);
          if (!name) {
            b.err = TOBJ_ERR_ALLOC;
            break;
          }
          tobj_memcpy(name, t2, l2);
          name[l2] = '\0';
          tobj_mtl_source src;
          tobj_memset(&src, 0, sizeof src);
          if (cfg->mtl_resolver(cfg->mtl_resolver_user_data, name, &src) ==
              TOBJ_OK) {
            TOBJ_T(parse_mtl_buffer)(&b, src.data, src.len);
            if (src.release) src.release(src.release_ud, src.data, src.len);
          }
        }
        if (b.err == TOBJ_OK && cb->mtllib_cb && b.materials.count > before) {
          cb->mtllib_cb(ud, (const TOBJ_T(tobj_material) *)b.materials.data,
                        tobj_size_to_int(b.materials.count));
        }
      }
    }
  }

  TOBJ_T(builder_dispose)(&b);
  tobj_vec_free(&lines, &alloc);
  tobj_arena_destroy(arena);
  tobj_free(&alloc, arena, sizeof(tobj_arena));
  return b.err;
}
