/* SPDX-License-Identifier: MIT */
#include <math.h>
#include <string.h>

#include "edits.h"
#include "metrics.h"

tess_remesh_options tess_default_remesh_options(void) {
  tess_remesh_options o = {0};
  o.target_count = 128;
  o.max_passes = 8;
  o.max_edits = 10000;
  o.max_candidates = 100000;
  o.max_area_cv = .30;
  o.min_fraction_target_band = .90;
  o.min_angle_p05 = 20;
  return o;
}
static void peak(tess_result* r, size_t extra) {
  size_t total =
      r->mesh.c.bytes + r->seed.c.bytes + r->control.bytes + sizeof(*r);
  if (extra > SIZE_MAX - total)
    total = SIZE_MAX;
  else
    total += extra;
  if (total > r->peak_bytes) r->peak_bytes = total;
}
static void measure_peak(tess_result* r) {
  size_t extra = r->mesh.c.peak - r->mesh.c.bytes;
  peak(r, extra);
  r->mesh.c.peak = r->mesh.c.bytes;
}
static void clear_control(tx* c, qr* target, qr* tol, qr* split, qr* batch,
                          size_t* owners, size_t n) {
  qr_clear(c, target);
  qr_clear(c, tol);
  qr_clear(c, split);
  qr_clear(c, batch);
  tx_free(c, owners, n * sizeof(size_t));
}
static tess_status configure(tess_result* r, tess_remesh_options o) {
  tx c;
  tm work;
  qr target = {0}, tol = {0}, split = {0}, batch = {0}, factor = {0};
  size_t *owners = NULL, i, j,
         choices = (o.target_count != 0) + (o.target_area != 0) +
                   (o.exact_target_area != NULL),
         oldbytes = r->control.bytes;
  int valid = 1;
  tess_status status;
  tx_init(&c);
  c.allocator = r->mesh.c.allocator;
  c.max_bytes = r->mesh.c.max_bytes - r->mesh.c.bytes;
  c.max_ops = r->mesh.c.max_ops - r->mesh.c.ops;
  c.max_limbs = r->mesh.c.max_limbs;
  if (choices != 1 || !isfinite(o.target_area) || o.target_area < 0 ||
      !isfinite(o.height_tolerance) || o.height_tolerance < 0 ||
      !isfinite(o.max_area_cv) || o.max_area_cv < 0 ||
      !isfinite(o.min_fraction_target_band) || o.min_fraction_target_band < 0 ||
      o.min_fraction_target_band > 1 || !isfinite(o.min_angle_p05) ||
      o.min_angle_p05 < 0 || o.min_angle_p05 >= 180 ||
      (!o.boundary_owners && o.boundary_owner_count) ||
      o.boundary_owner_count > r->seed.ne)
    return TESS_INVALID_INPUT;
  if (o.exact_height_tolerance && o.height_tolerance != 0)
    return TESS_INVALID_INPUT;
  if (o.boundary_owner_count) {
    owners = tx_alloc(&c, o.boundary_owner_count, sizeof(size_t));
    if (owners)
      for (i = 0; i < o.boundary_owner_count; i++) {
        int found = 0;
        owners[i] = o.boundary_owners[i];
        for (j = 0; j < r->seed.ne; j++)
          if (r->seed.e[j].constraint == 1 && r->seed.e[j].owner == owners[i])
            found = 1;
        if (!found) valid = 0;
      }
  }
  if (o.exact_target_area)
    qr_import(&c, &target, o.exact_target_area);
  else if (o.target_count) {
    memset(&work, 0, sizeof(work));
    work.c = c;
    tg_count_target(&work, &r->seed, o.target_count, &target);
    c = work.c;
  } else
    qr_double(&c, &target, o.target_area);
  if (o.exact_height_tolerance)
    qr_import(&c, &tol, o.exact_height_tolerance);
  else
    qr_double(&c, &tol, o.height_tolerance);
  if (target.n.sign <= 0 || tol.n.sign < 0) valid = 0;
  qr_mul(&c, &split, &target, &target);
  qr_i64(&c, &factor, 9);
  qr_mul(&c, &split, &split, &factor);
  qr_i64(&c, &factor, 4);
  qr_div(&c, &split, &split, &factor);
  qr_mul(&c, &batch, &target, &target);
  qr_mul(&c, &batch, &batch, &factor);
  qr_clear(&c, &factor);
  peak(r, c.peak);
  if (!valid && !c.status) c.status = TESS_INVALID_INPUT;
  if (c.status) {
    status = c.status;
    r->mesh.c.ops += c.ops;
    r->control_ops_total += 0;
    clear_control(&c, &target, &tol, &split, &batch, owners,
                  o.boundary_owner_count);
    return status;
  }
  r->mesh.c.max_bytes += oldbytes;
  r->mesh.c.max_bytes -= c.bytes;
  r->mesh.c.max_ops -= c.ops;
  r->control_ops_total += c.ops;
  clear_control(&r->control, &r->target, &r->tolerance, &r->split_threshold,
                &r->batch_threshold, r->allowed_owners, r->allowed_count);
  r->control = c;
  r->target = target;
  r->tolerance = tol;
  r->split_threshold = split;
  r->batch_threshold = batch;
  r->allowed_owners = owners;
  r->allowed_count = o.boundary_owner_count;
  o.exact_target_area = NULL;
  o.exact_height_tolerance = NULL;
  o.boundary_owners =
      o.boundary_owners ? (owners ? owners : &r->allowed_count) : NULL;
  r->remesh_options = o;
  r->remeshed = 1;
  r->mesh.approximate = tol.n.sign > 0;
  return TESS_OK;
}
static int targets_met(const tess_quality* q, const tess_remesh_options* o) {
  return q->area_cv <= o->max_area_cv &&
         q->fraction_target_band >= o->min_fraction_target_band &&
         q->min_angle_p05 >= o->min_angle_p05;
}
/* For count-preserving flips/relocations the unchanged face terms cancel.
   This local delta ranks proposals before computing global percentiles and the
   rounded global checkpoint objective. It is only a heuristic rejection gate;
   every accepted proposal still passes the complete independent validators. */
static int local_rank(tm* stage, const tm* old, int kind, size_t a, size_t b,
                      const qr* target, long double* delta) {
  size_t i, j, k, changed = 0;
  *delta = 0;
  if ((kind != 4 && kind != 5) || stage->nf != old->nf) return 0;
  for (i = 0; i < old->nf && !stage->c.status; i++) {
    int hasA = 0, hasB = 0;
    long double before, after;
    for (k = 0; k < 3; k++) {
      hasA |= old->f[i].v[k] == a;
      hasB |= old->f[i].v[k] == b;
    }
    if (!hasA || (kind == 4 && !hasB)) continue;
    for (j = 0; j < stage->nf && stage->f[j].id != old->f[i].id; j++) {
    }
    if (j == stage->nf) return 0;
    if (!tg_face_objective(&stage->c, old->v, &old->f[i], target, &before) ||
        !tg_face_objective(&stage->c, stage->v, &stage->f[j], target, &after))
      return 0;
    *delta += after - before;
    changed++;
  }
  return changed != 0 && isfinite(*delta) && !stage->c.status;
}
static int candidate(tess_result* r, int kind, size_t a, size_t b,
                     unsigned step, tess_run_report* report,
                     tess_quality* current) {
  tm stage;
  tm* m = &r->mesh;
  size_t oldops = m->c.ops, oldlimit = m->c.max_ops,
         oldbyteslimit = m->c.max_bytes, allocations = m->c.allocations,
         oldnv = m->nv;
  int edited = 0, valid = 0, improves = 0;
  tess_quality quality;
  tess_status cause;
  report->candidates++;
  tm_clone(&stage, m);
  if (!stage.c.status) {
    switch (kind) {
      case 0:
        edited = tg_red_refine(&stage, &r->remesh_options);
        break;
      case 1:
        edited = tg_split_edge(&stage, a, b, &r->remesh_options);
        break;
      case 2:
        edited = tg_split_face(&stage, a);
        break;
      case 3:
        edited = tg_collapse_edge(&stage, &r->seed, a, b);
        break;
      case 4:
        edited = tg_flip_edge(&stage, a, b);
        break;
      case 5:
        edited = tg_relocate(&stage, &r->seed, a, step);
        break;
      default:
        stage.c.status = TESS_INTERNAL_ERROR;
    }
  }
  if (edited && !stage.c.status) {
    size_t i;
    for (i = oldnv; i < stage.nv && !stage.c.status; i++) {
      qr h = {0};
      if (!tg_reference_height(&stage, &r->seed, &stage.v[i].p[stage.u],
                               &stage.v[i].p[stage.w], &h)) {
        qr_clear(&stage.c, &h);
        edited = 0;
        break;
      }
      qr_copy(&stage.c, &stage.v[i].p[stage.axis], &h);
      qr_clear(&stage.c, &h);
    }
  }
  if (edited && !stage.c.status && tg_compact(&stage) &&
      tg_check_chains(&stage, &r->seed, &r->remesh_options) &&
      tg_validate(&stage) && tg_reference(&stage, &r->seed, &r->tolerance))
    valid = 1;
  if (valid) {
    long double delta;
    int ranked = local_rank(&stage, m, kind, a, b, &r->target, &delta);
    if (!stage.c.status && (!ranked || delta < 0)) {
      tess_status measured = tg_quality(&stage, &r->target, &quality);
      if (measured != TESS_OK)
        stage.c.status = measured;
      else if (isfinite(quality.objective) &&
               quality.objective < current->objective)
        improves = 1;
    }
  }
  peak(r, stage.c.peak);
  cause = stage.c.status;
  if (improves && !cause) {
    size_t newops = oldops + stage.c.ops;
    tm_clear(m);
    *m = stage;
    m->c.max_ops = oldlimit;
    m->c.max_bytes = oldbyteslimit;
    m->c.ops = newops;
    m->c.allocations += allocations;
    m->c.peak = m->c.bytes;
    *current = quality;
    r->quality = quality;
    report->edits++;
    switch (kind) {
      case 0:
        report->batches++;
        report->edge_splits += m->nv - oldnv;
        break;
      case 1:
        report->edge_splits++;
        break;
      case 2:
        report->face_splits++;
        break;
      case 3:
        report->collapses++;
        break;
      case 4:
        report->flips++;
        break;
      case 5:
        report->relocations++;
        break;
    }
    return 1;
  }
  m->c.ops = oldops + stage.c.ops;
  m->c.allocations += stage.c.allocations;
  tm_clear(&stage);
  if (cause == TESS_RESOURCE_LIMIT || cause == TESS_ALLOCATION_FAILURE ||
      cause == TESS_INTERNAL_ERROR) {
    report->stop_reason = cause;
    return -1;
  }
  if (valid)
    report->objective_rejections++;
  else
    report->validity_rejections++;
  return 0;
}
static int blocked_face(size_t id, const size_t* blocked, size_t n) {
  size_t i;
  for (i = 0; i < n; i++)
    if (blocked[i] == id) return 1;
  return 0;
}
static size_t largest_face(tess_result* r, const qr* threshold,
                           const size_t* blocked, size_t nb) {
  tm* m = &r->mesh;
  qr area = {0}, best = {0};
  size_t i, index = SIZE_MAX;
  for (i = 0; i < m->nf && !m->c.status; i++) {
    if (blocked_face(m->f[i].id, blocked, nb)) continue;
    tg_triangle_squared(&m->c, m->v, &m->f[i], &area);
    if (qr_cmp(&m->c, &area, threshold) <= 0) continue;
    if (index == SIZE_MAX || qr_cmp(&m->c, &area, &best) > 0 ||
        (!qr_cmp(&m->c, &area, &best) && m->f[i].id < m->f[index].id)) {
      index = i;
      qr_copy(&m->c, &best, &area);
    }
  }
  qr_clear(&m->c, &area);
  qr_clear(&m->c, &best);
  measure_peak(r);
  return index;
}
static int all_large(tess_result* r) {
  tm* m = &r->mesh;
  qr area = {0};
  size_t i;
  int yes = 1;
  for (i = 0; i < m->nf && !m->c.status; i++) {
    tg_triangle_squared(&m->c, m->v, &m->f[i], &area);
    if (qr_cmp(&m->c, &area, &r->batch_threshold) <= 0) {
      yes = 0;
      break;
    }
  }
  qr_clear(&m->c, &area);
  measure_peak(r);
  return yes && !m->c.status;
}
static int longest_split_edge(tess_result* r, size_t face, size_t* a,
                              size_t* b) {
  tm* m = &r->mesh;
  qr length = {0}, best = {0};
  size_t k;
  int found = 0;
  for (k = 0; k < 3 && !m->c.status; k++) {
    size_t x = m->f[face].v[k], y = m->f[face].v[(k + 1) % 3];
    if (!tg_edge_may_split(m, x, y, &r->remesh_options)) continue;
    tg_length_squared(&m->c, m->v, x, y, &length);
    if (!found || qr_cmp(&m->c, &length, &best) > 0) {
      *a = x;
      *b = y;
      found = 1;
      qr_copy(&m->c, &best, &length);
    }
  }
  qr_clear(&m->c, &length);
  qr_clear(&m->c, &best);
  measure_peak(r);
  return found && !m->c.status;
}
static int next_edge(tm* m, size_t lastA, size_t lastB, int first, size_t* a,
                     size_t* b) {
  size_t i, k, bestA = SIZE_MAX, bestB = SIZE_MAX;
  int found = 0;
  for (i = 0; i < m->nf; i++)
    for (k = 0; k < 3; k++) {
      size_t x = m->f[i].v[k], y = m->f[i].v[(k + 1) % 3], idX = m->v[x].id,
             idY = m->v[y].id;
      if (idX > idY) {
        size_t t = x;
        x = y;
        y = t;
        t = idX;
        idX = idY;
        idY = t;
      }
      if (!first && (idX < lastA || (idX == lastA && idY <= lastB))) continue;
      if (!found || idX < bestA || (idX == bestA && idY < bestB)) {
        bestA = idX;
        bestB = idY;
        *a = x;
        *b = y;
        found = 1;
      }
    }
  return found;
}
static void drop_implicit(tm* m) {
  size_t i, n = 0;
  for (i = 0; i < m->ne; i++)
    if (m->e[i].constraint == 2) {
      qr_clear(&m->c, &m->e[i].ta);
      qr_clear(&m->c, &m->e[i].tb);
      memset(&m->e[i], 0, sizeof(te));
    } else {
      if (i != n) {
        m->e[n] = m->e[i];
        memset(&m->e[i], 0, sizeof(te));
      }
      n++;
    }
  m->ne = n;
}

tess_status tess_remesh(tess_result* r, const tess_remesh_options* options,
                        tess_run_report* out) {
  tess_run_report report = {0};
  tess_remesh_options o = options ? *options : tess_default_remesh_options();
  tess_quality current;
  tm* m;
  size_t full_ops, pass;
  int stop = 0;
  tess_status status;
  if (!r) return TESS_INVALID_INPUT;
  if (r->remeshed == 2) {
    report.outcome = TESS_INVALID_INPUT;
    if (out) *out = report;
    return TESS_INVALID_INPUT;
  }
  if (r->remeshed == 1 && options) {
    report.outcome = TESS_INVALID_INPUT;
    if (out) *out = report;
    return TESS_INVALID_INPUT;
  }
  m = &r->mesh;
  if (m->c.status) return m->c.status;
  status = r->remeshed == 1 ? TESS_OK : configure(r, o);
  if (status != TESS_OK) {
    report.outcome = report.stop_reason = status;
    goto finish;
  }
  o = r->remesh_options;
  r->remeshed = 2;
  if (m->approximate) drop_implicit(m);
  status = tg_quality(m, &r->target, &current);
  measure_peak(r);
  if (status != TESS_OK) {
    report.outcome = report.stop_reason = status;
    goto finish;
  }
  r->quality = current;
  full_ops = m->c.max_ops;
  m->c.max_ops -= (m->c.max_ops - m->c.ops) / 3;
  for (pass = 0; pass < o.max_passes && !stop; pass++) {
    size_t before = report.edits, blocked[256], nb = 0, a = 0, b = 0, face,
           attempt, oldvertices;
    int result, canBatch = 1;
    if (targets_met(&current, &o)) break;
    report.passes++;
    if (report.edits >= o.max_edits || report.candidates >= o.max_candidates)
      break;
    for (attempt = 0; attempt < m->ne; attempt++)
      if (!tg_edge_may_split(m, m->e[attempt].a, m->e[attempt].b, &o)) {
        canBatch = 0;
        report.constraint_rejections++;
        break;
      }
    if (canBatch && all_large(r)) {
      result = candidate(r, 0, 0, 0, 0, &report, &current);
      if (result < 0) {
        stop = 1;
        break;
      }
      if (result > 0) continue;
    }
    for (attempt = 0; attempt < 256 && report.edits < o.max_edits &&
                      report.candidates < o.max_candidates;
         attempt++) {
      face = largest_face(r, &r->split_threshold, blocked, nb);
      if (face == SIZE_MAX || m->c.status) break;
      if (longest_split_edge(r, face, &a, &b))
        result = candidate(r, 1, a, b, 0, &report, &current);
      else
        result = 0;
      if (result < 0) {
        stop = 1;
        break;
      }
      if (result > 0) {
        if (targets_met(&current, &o)) {
          stop = 1;
          break;
        }
        continue;
      }
      if (report.candidates >= o.max_candidates) break;
      result = candidate(r, 2, face, 0, 0, &report, &current);
      if (result < 0) {
        stop = 1;
        break;
      }
      if (result > 0) {
        if (targets_met(&current, &o)) {
          stop = 1;
          break;
        }
        continue;
      }
      blocked[nb++] = m->f[face].id;
      if (nb == 256) break;
    }
    if (stop) break;
    {
      size_t lastA = 0, lastB = 0;
      int first = 1;
      for (attempt = 0; attempt < 256 && report.edits < o.max_edits &&
                        report.candidates < o.max_candidates;
           attempt++) {
        qr length = {0};
        long double l, target = qr_approx(&r->target);
        if (!next_edge(m, lastA, lastB, first, &a, &b)) break;
        first = 0;
        lastA = m->v[a].id;
        lastB = m->v[b].id;
        if (m->v[a].pinned || m->v[b].pinned) continue;
        tg_length_squared(&m->c, m->v, a, b, &length);
        l = qr_approx(&length);
        qr_clear(&m->c, &length);
        measure_peak(r);
        if (!(l < target / sqrtl(3.0L))) continue;
        result = candidate(r, 3, a, b, 0, &report, &current);
        if (result < 0) {
          stop = 1;
          break;
        }
      }
    }
    if (stop) break;
    {
      size_t lastA = 0, lastB = 0, limit = m->nf * 3;
      int first = 1;
      for (attempt = 0; attempt < limit && report.edits < o.max_edits &&
                        report.candidates < o.max_candidates;
           attempt++) {
        if (!next_edge(m, lastA, lastB, first, &a, &b)) break;
        first = 0;
        lastA = m->v[a].id;
        lastB = m->v[b].id;
        result = candidate(r, 4, a, b, 0, &report, &current);
        if (result < 0) {
          stop = 1;
          break;
        }
      }
    }
    if (stop) break;
    oldvertices = m->nv;
    for (a = 0; a < oldvertices && report.edits < o.max_edits &&
                report.candidates < o.max_candidates;
         a++)
      if (!m->v[a].pinned) {
        unsigned step;
        for (step = 0; step < 5 && report.candidates < o.max_candidates;
             step++) {
          result = candidate(r, 5, a, 0, step, &report, &current);
          if (result < 0) {
            stop = 1;
            break;
          }
          if (result > 0) break;
        }
        if (stop) break;
      }
    if (m->c.status) {
      report.stop_reason = m->c.status;
      stop = 1;
    }
    if (report.edits == before) break;
  }
  m->c.max_ops = full_ops;
  if (m->c.status == TESS_RESOURCE_LIMIT ||
      m->c.status == TESS_ALLOCATION_FAILURE)
    m->c.status = TESS_OK;
  if (!tg_check_chains(m, &r->seed, &o) || !tg_validate(m) ||
      !tg_reference_measure(m, &r->seed, &r->tolerance, &r->deviation) ||
      !tg_audit3(m)) {
    report.outcome = m->c.status ? m->c.status : TESS_INTERNAL_ERROR;
    report.stop_reason = report.outcome;
    goto finish;
  }
  measure_peak(r);
  r->quality = current;
  if (!tx_report_double(qr_approx(&r->deviation),
                        &r->quality.max_reference_deviation)) {
    report.outcome = report.stop_reason = TESS_RESOURCE_LIMIT;
    goto finish;
  }
  report.outcome = targets_met(&current, &o) ? TESS_VALID_TARGETS_MET
                                             : TESS_VALID_TARGETS_UNMET;
  if (report.outcome == TESS_VALID_TARGETS_MET)
    report.termination = TESS_STOP_TARGETS_MET;
  else if (report.stop_reason == TESS_RESOURCE_LIMIT)
    report.termination = TESS_STOP_RESOURCE;
  else if (report.stop_reason == TESS_ALLOCATION_FAILURE)
    report.termination = TESS_STOP_ALLOCATION;
  else if (report.passes >= o.max_passes || report.edits >= o.max_edits ||
           report.candidates >= o.max_candidates)
    report.termination = TESS_STOP_BUDGET;
  else
    report.termination = report.constraint_rejections ? TESS_STOP_CONSTRAINTS
                                                      : TESS_STOP_STAGNATION;
finish:
  if (report.outcome != TESS_VALID_TARGETS_MET &&
      report.outcome != TESS_VALID_TARGETS_UNMET)
    report.termination =
        report.outcome == TESS_RESOURCE_LIMIT       ? TESS_STOP_RESOURCE
        : report.outcome == TESS_ALLOCATION_FAILURE ? TESS_STOP_ALLOCATION
                                                    : TESS_STOP_ERROR;
  if (out) *out = report;
  return report.outcome;
}

tess_status tess_prepare_remesh(tess_result* r,
                                const tess_remesh_options* options) {
  tess_remesh_options o = options ? *options : tess_default_remesh_options();
  if (!r || r->remeshed) return TESS_INVALID_INPUT;
  if (r->mesh.c.status) return r->mesh.c.status;
  return configure(r, o);
}
