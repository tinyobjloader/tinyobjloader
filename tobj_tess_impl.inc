/*
 * tobj_tess_impl.inc -- per-precision projection + dispatch.
 * Included twice from tobj_tess.c. Do not include directly.
 */

/* Project the 3D ring into w->p2d (double). Returns 1 normally, 0 if the
 * polygon is fully degenerate (collinear/zero-area) and a bbox fallback was
 * used. Never fails. */
static int TOBJ_TESS_T(tobj_tess_project)(const TOBJ_TESS_REAL *pts, uint32_t n,
                                          const TOBJ_TESS_REAL *given_normal,
                                          uint32_t flags, tobj_tess_work *w) {
  double cx = (double)pts[0], cy = (double)pts[1], cz = (double)pts[2];
  double coordmax = 0.0;
  for (uint32_t i = 0; i < 3u * n; i++) {
    double a = tobj_dabs((double)pts[i]);
    if (a > coordmax) coordmax = a;
  }

  double nx = 0, ny = 0, nz = 0;
  if (flags & TOBJ_TESS_FLAG_NORMAL_GIVEN) {
    nx = (double)given_normal[0];
    ny = (double)given_normal[1];
    nz = (double)given_normal[2];
  } else {
    for (uint32_t k = 0; k < n; k++) {
      uint32_t j = (k + 1u) % n;
      double ax = (double)pts[3 * k], ay = (double)pts[3 * k + 1],
             az = (double)pts[3 * k + 2];
      double bx = (double)pts[3 * j], by = (double)pts[3 * j + 1],
             bz = (double)pts[3 * j + 2];
      nx += (ay - by) * (az + bz);
      ny += (az - bz) * (ax + bx);
      nz += (ax - bx) * (ay + by);
    }
  }
  double len2 = nx * nx + ny * ny + nz * nz;
  double cm2 = coordmax * coordmax;
  double thresh = cm2 * cm2 * TOBJ_TESS_REL_N;

  if (tobj_is_finite(len2) && len2 > thresh && len2 > 0.0) {
    /* in-plane basis (unnormalized: only orientation signs matter) */
    double wx = nx, wy = ny, wz = nz;
    double ax = tobj_dabs(wx), ay = tobj_dabs(wy), az = tobj_dabs(wz);
    double sx = 0, sy = 0, sz = 0;
    if (ax <= ay && ax <= az)
      sx = 1;
    else if (ay <= az)
      sy = 1;
    else
      sz = 1;
    /* u = w x s, v = w x u */
    double ux = wy * sz - wz * sy;
    double uy = wz * sx - wx * sz;
    double uz = wx * sy - wy * sx;
    double vx = wy * uz - wz * uy;
    double vy = wz * ux - wx * uz;
    double vz = wx * uy - wy * ux;
    for (uint32_t k = 0; k < n; k++) {
      double dx = (double)pts[3 * k] - cx;
      double dy = (double)pts[3 * k + 1] - cy;
      double dz = (double)pts[3 * k + 2] - cz;
      w->p2d[2 * k] = dx * ux + dy * uy + dz * uz;
      w->p2d[2 * k + 1] = dx * vx + dy * vy + dz * vz;
    }
    return 1;
  }

  /* Fallback: drop the smallest-extent axis, keep the other two raw axes. */
  double mn[3], mx[3];
  mn[0] = mx[0] = (double)pts[0];
  mn[1] = mx[1] = (double)pts[1];
  mn[2] = mx[2] = (double)pts[2];
  for (uint32_t k = 0; k < n; k++) {
    for (int c = 0; c < 3; c++) {
      double v = (double)pts[3 * k + c];
      if (v < mn[c]) mn[c] = v;
      if (v > mx[c]) mx[c] = v;
    }
  }
  double span[3] = {mx[0] - mn[0], mx[1] - mn[1], mx[2] - mn[2]};
  int drop = 0;
  if (span[1] < span[0]) drop = 1;
  if (span[2] < span[drop]) drop = 2;
  int a0 = (drop == 0) ? 1 : 0;
  int a1 = (drop == 2) ? 1 : 2;
  for (uint32_t k = 0; k < n; k++) {
    w->p2d[2 * k] = (double)pts[3 * k + a0] - (drop == 0 ? cy : cx);
    w->p2d[2 * k + 1] =
        (double)pts[3 * k + a1] - ((drop == 2) ? cy : cz);
  }
  return 0;
}

tobj_tess_status TOBJ_TESS_T(tobj_tess_polygon)(
    const TOBJ_TESS_T(tobj_tess_desc) * desc, tobj_tess_result *result) {
  result->indices = NULL;
  result->num_triangles = 0;
  result->indices_allocated = 0;
  result->status = TOBJ_TESS_INVALID;

  if (!desc || !desc->points) return TOBJ_TESS_INVALID;
  uint32_t n = desc->n;
  if (n < 3) return TOBJ_TESS_INVALID;

  /* reject non-finite coordinates */
  for (uint32_t i = 0; i < 3u * n; i++) {
    if (!tobj_is_finite((double)desc->points[i])) return TOBJ_TESS_INVALID;
  }

  uint32_t tri = n - 2u;
  uint32_t need_out = tri * 3u;

  /* resolve output buffer */
  uint32_t *out = NULL;
  int out_alloc = 0;
  if (desc->out_indices && desc->out_cap >= need_out) {
    out = desc->out_indices;
  } else if (desc->alloc && desc->alloc->alloc) {
    out = (uint32_t *)desc->alloc->alloc(desc->alloc->ud,
                                         need_out * sizeof(uint32_t));
    if (!out) {
      result->status = TOBJ_TESS_OOM;
      return TOBJ_TESS_OOM;
    }
    out_alloc = 1;
  } else {
    result->status = TOBJ_TESS_OOM;
    return TOBJ_TESS_OOM;
  }

  /* resolve scratch */
  size_t need_scratch = tobj_tess_scratch_size(n);
  void *scratch = NULL;
  int scratch_alloc = 0;
  unsigned char stackbuf[TOBJ_TESS_STACK_BYTES];
  if (desc->scratch && desc->scratch_size >= need_scratch) {
    scratch = desc->scratch;
  } else if (n <= TOBJ_TESS_STACK_N && need_scratch <= sizeof(stackbuf)) {
    scratch = stackbuf;
  } else if (desc->alloc && desc->alloc->alloc) {
    scratch = desc->alloc->alloc(desc->alloc->ud, need_scratch);
    if (!scratch) {
      if (out_alloc) desc->alloc->free(desc->alloc->ud, out);
      result->status = TOBJ_TESS_OOM;
      return TOBJ_TESS_OOM;
    }
    scratch_alloc = 1;
  } else {
    if (out_alloc && desc->alloc) desc->alloc->free(desc->alloc->ud, out);
    result->status = TOBJ_TESS_OOM;
    return TOBJ_TESS_OOM;
  }

  tobj_tess_work w;
  tobj_tess_work_bind(&w, scratch, need_scratch, n);

  int proj_ok =
      TOBJ_TESS_T(tobj_tess_project)(desc->points, n, desc->normal,
                                     desc->flags, &w);

  tobj_tess_status status;
  uint32_t k = 0;

  if (n == 3) {
    tobj_tess_emit(out, &k, 0, 1, 2);
    double ar = tobj_dabs(tobj_orient2d(&w.p2d[0], &w.p2d[2], &w.p2d[4]));
    double scale = tobj_tess_scale2d(w.p2d, n);
    status = ar <= scale * scale * TOBJ_TESS_REL ? TOBJ_TESS_DEGENERATE_BESTEFFORT
                                                 : TOBJ_TESS_OK;
  } else if (n == 4) {
    double scale = tobj_tess_scale2d(w.p2d, n);
    double eps = scale * scale * TOBJ_TESS_REL;
    const double *p0 = &w.p2d[0], *p1 = &w.p2d[2], *p2 = &w.p2d[4],
                 *p3 = &w.p2d[6];
    double o012 = tobj_orient2d(p0, p1, p2);
    double o023 = tobj_orient2d(p0, p2, p3);
    double o123 = tobj_orient2d(p1, p2, p3);
    double o130 = tobj_orient2d(p1, p3, p0);
    int d02 = (tobj_dabs(o012) > eps && tobj_dabs(o023) > eps &&
               ((o012 > 0) == (o023 > 0)));
    int d13 = (tobj_dabs(o123) > eps && tobj_dabs(o130) > eps &&
               ((o123 > 0) == (o130 > 0)));
    int split02;
    status = TOBJ_TESS_OK;
    if (d02 && !d13) {
      split02 = 1;
    } else if (d13 && !d02) {
      split02 = 0;
    } else {
      /* convex (both internal) or degenerate (neither): shorter 3D diagonal */
      const TOBJ_TESS_REAL *q = desc->points;
      double e02x = (double)q[6] - (double)q[0];
      double e02y = (double)q[7] - (double)q[1];
      double e02z = (double)q[8] - (double)q[2];
      double e13x = (double)q[9] - (double)q[3];
      double e13y = (double)q[10] - (double)q[4];
      double e13z = (double)q[11] - (double)q[5];
      double s02 = e02x * e02x + e02y * e02y + e02z * e02z;
      double s13 = e13x * e13x + e13y * e13y + e13z * e13z;
      split02 = s02 <= s13;
      if (!d02 && !d13) status = TOBJ_TESS_DEGENERATE_BESTEFFORT;
    }
    if (split02) {
      tobj_tess_emit(out, &k, 0, 1, 2);
      tobj_tess_emit(out, &k, 0, 2, 3);
    } else {
      tobj_tess_emit(out, &k, 0, 1, 3);
      tobj_tess_emit(out, &k, 1, 2, 3);
    }
  } else {
    status = tobj_tess_run2d(&w, n, out, desc->flags);
  }

  if (!proj_ok && status == TOBJ_TESS_OK) status = TOBJ_TESS_DEGENERATE_BESTEFFORT;

  if (scratch_alloc) desc->alloc->free(desc->alloc->ud, scratch);

  result->indices = out;
  result->num_triangles = tri;
  result->indices_allocated = out_alloc;
  result->status = status;
  return status;
}
