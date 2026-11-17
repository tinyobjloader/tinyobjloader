/*
 * tobj_subd.c — see tobj_subd.h. Mirrors formal/Subd (Lean `TobjSubd`).
 */
#include "tobj_subd.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  const char *p;
  size_t n;
} sl;

typedef struct {
  char *p;
  size_t n, cap;
  int oom;
} sb;

static void sb_put(sb *b, const char *s, size_t n) {
  if (b->oom) return;
  if (b->n + n + 1 > b->cap) {
    size_t cap = b->cap ? b->cap : 256;
    while (cap < b->n + n + 1) cap *= 2;
    char *q = (char *)realloc(b->p, cap);
    if (!q) {
      b->oom = 1;
      return;
    }
    b->p = q;
    b->cap = cap;
  }
  if (n) memcpy(b->p + b->n, s, n);
  b->n += n;
  b->p[b->n] = '\0';
}
static void sb_puts(sb *b, const char *s) { sb_put(b, s, strlen(s)); }
static void sb_putz(sb *b, size_t v) {
  char tmp[32];
  size_t i = sizeof(tmp);
  do {
    tmp[--i] = (char)('0' + v % 10);
    v /= 10;
  } while (v);
  sb_put(b, tmp + i, sizeof(tmp) - i);
}
static char *sb_take(sb *b) {
  if (b->oom) {
    free(b->p);
    return NULL;
  }
  if (!b->p) {
    char *e = (char *)malloc(1);
    if (e) e[0] = '\0';
    return e;
  }
  return b->p;
}

static char *dup_sl(sl s) {
  char *p = (char *)malloc(s.n + 1);
  if (!p) return NULL;
  if (s.n) memcpy(p, s.p, s.n);
  p[s.n] = '\0';
  return p;
}
static int sl_eq(sl a, const char *b) {
  size_t n = strlen(b);
  return a.n == n && (n == 0 || memcmp(a.p, b, n) == 0);
}
static int is_blank(char c) { return c == ' ' || c == '\t'; }
static int is_digit(char c) { return c >= '0' && c <= '9'; }

static int grow(void **arr, size_t *count, size_t elem) {
  void *q = realloc(*arr, (*count + 1) * elem);
  if (!q) return 0;
  *arr = q;
  (*count)++;
  return 1;
}
#define PUSH(arr, count, T, v)                                    \
  do {                                                            \
    if (!grow((void **)&(arr), &(count), sizeof(T))) return -1;   \
    (arr)[(count)-1] = (v);                                       \
  } while (0)

/* ---------------------------------------------------------------- tokens
 * Lean: TobjSubd.lineTokens */

typedef struct {
  sl *t;
  size_t n, cap;
  int oom;
} toks;

static void tokenize(sl line, toks *out) {
  out->n = 0;
  size_t i = 0;
  while (i < line.n) {
    if (is_blank(line.p[i])) {
      i++;
      continue;
    }
    size_t j = i;
    while (j < line.n && !is_blank(line.p[j])) j++;
    if (out->n == out->cap) {
      size_t cap = out->cap ? out->cap * 2 : 16;
      sl *q = (sl *)realloc(out->t, cap * sizeof(sl));
      if (!q) {
        out->oom = 1;
        return;
      }
      out->t = q;
      out->cap = cap;
    }
    out->t[out->n].p = line.p + i;
    out->t[out->n].n = j - i;
    out->n++;
    i = j;
  }
}

static sl drop_cr(sl l) {
  if (l.n && l.p[l.n - 1] == '\r') l.n--;
  return l;
}

/* ---------------------------------------------------------------- numbers
 * Lean: TobjSubd.parseInt? / isDecimal / parseCounts? */

#define BIG_INT ((long long)1 << 60) /* larger magnitudes saturate */

/* [+-]?[0-9]+ ; 0 = not an integer */
static int parse_int(sl s, long long *out) {
  size_t i = 0;
  int neg = 0;
  if (i < s.n && (s.p[i] == '+' || s.p[i] == '-')) neg = s.p[i++] == '-';
  if (i >= s.n) return 0;
  long long v = 0;
  for (; i < s.n; i++) {
    if (!is_digit(s.p[i])) return 0;
    v = v < BIG_INT / 10 ? v * 10 + (s.p[i] - '0') : BIG_INT;
  }
  *out = neg ? -v : v;
  return 1;
}

/* [+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)([eE][+-]?[0-9]+)? */
static int is_decimal(sl s) {
  size_t i = 0, d = 0;
  if (i < s.n && (s.p[i] == '+' || s.p[i] == '-')) i++;
  while (i < s.n && is_digit(s.p[i])) i++, d++;
  if (i < s.n && s.p[i] == '.') {
    i++;
    while (i < s.n && is_digit(s.p[i])) i++, d++;
  }
  if (d == 0) return 0;
  if (i < s.n && (s.p[i] == 'e' || s.p[i] == 'E')) {
    i++;
    if (i < s.n && (s.p[i] == '+' || s.p[i] == '-')) i++;
    size_t e = 0;
    while (i < s.n && is_digit(s.p[i])) i++, e++;
    if (e == 0) return 0;
  }
  return i == s.n;
}

#define MAX_COUNT 8192

/* `ni/nf/ns`, each [0-9]+ and <= MAX_COUNT */
static int parse_counts(sl s, size_t c[3]) {
  size_t k = 0, i = 0;
  for (; k < 3; k++) {
    size_t v = 0, d = 0;
    while (i < s.n && is_digit(s.p[i])) {
      if (v <= MAX_COUNT) v = v * 10 + (size_t)(s.p[i] - '0');
      i++, d++;
    }
    if (d == 0 || v > MAX_COUNT) return 0;
    c[k] = v;
    if (k < 2) {
      if (i >= s.n || s.p[i] != '/') return 0;
      i++;
    }
  }
  return i == s.n;
}

double tobj_subd_sharpness(const char *text) {
  double v = strtod(text, NULL);
  return v > 0 ? v : 0; /* also maps NaN to 0 */
}

/* ---------------------------------------------------------------- faces */

typedef struct {
  size_t a, b;
} edge;

static int edge_cmp(const void *x, const void *y) {
  const edge *p = (const edge *)x, *q = (const edge *)y;
  if (p->a != q->a) return p->a < q->a ? -1 : 1;
  if (p->b != q->b) return p->b < q->b ? -1 : 1;
  return 0;
}
static int size_cmp(const void *x, const void *y) {
  size_t p = *(const size_t *)x, q = *(const size_t *)y;
  return p < q ? -1 : p > q;
}

typedef struct {
  edge *edges;
  size_t num_edges;
  size_t *verts;
  size_t num_verts;
  size_t num_faces;
  int all_tris;
} topo;

static int build_topo(const unsigned int *fvc, size_t nf, const int *vi, topo *t) {
  memset(t, 0, sizeof(*t));
  t->num_faces = nf;
  t->all_tris = 1;
  size_t total = 0;
  for (size_t f = 0; f < nf; f++) total += fvc[f];
  if (total) {
    t->edges = (edge *)malloc(total * sizeof(edge));
    t->verts = (size_t *)malloc(total * sizeof(size_t));
    if (!t->edges || !t->verts) return -1;
  }
  size_t o = 0;
  for (size_t f = 0; f < nf; f++) {
    size_t n = fvc[f];
    if (n != 3) t->all_tris = 0;
    for (size_t k = 0; k < n; k++) {
      size_t a = (size_t)vi[o + k], b = (size_t)vi[o + (k + 1) % n];
      t->verts[t->num_verts++] = a;
      edge e = {a < b ? a : b, a < b ? b : a};
      t->edges[t->num_edges++] = e;
    }
    o += n;
  }
  if (t->num_edges) qsort(t->edges, t->num_edges, sizeof(edge), edge_cmp);
  if (t->num_verts) qsort(t->verts, t->num_verts, sizeof(size_t), size_cmp);
  return 0;
}

static int has_edge(const topo *t, size_t a, size_t b) {
  edge k = {a, b};
  return t->num_edges &&
         bsearch(&k, t->edges, t->num_edges, sizeof(edge), edge_cmp) != NULL;
}
static int has_vert(const topo *t, size_t v) {
  return t->num_verts &&
         bsearch(&v, t->verts, t->num_verts, sizeof(size_t), size_cmp) != NULL;
}

/* ---------------------------------------------------------------- tags
 * Lean: TobjSubd.step / check */

static int add_err(tobj_subd *s, const char *e) {
  size_t n = strlen(e);
  sl x = {e, n};
  char *d = dup_sl(x);
  if (!d) return -1;
  PUSH(s->errors, s->num_errors, char *, d);
  return 0;
}

/* sharpness text: negative -> "0" */
static char *sharp_text(sl t) {
  if (t.n && t.p[0] == '-') {
    sl z = {"0", 1};
    return dup_sl(z);
  }
  return dup_sl(t);
}

static int set_crease(tobj_subd *s, size_t a, size_t b, sl sh) {
  char *v = sharp_text(sh);
  if (!v) return -1;
  for (size_t i = 0; i < s->num_creases; i++)
    if (s->creases[i].v0 == a && s->creases[i].v1 == b) {
      free(s->creases[i].sharpness);
      s->creases[i].sharpness = v;
      return 0;
    }
  tobj_subd_crease c = {a, b, v};
  if (!grow((void **)&s->creases, &s->num_creases, sizeof(c))) {
    free(v);
    return -1;
  }
  s->creases[s->num_creases - 1] = c;
  return 0;
}

static int set_corner(tobj_subd *s, size_t v, sl sh) {
  char *x = sharp_text(sh);
  if (!x) return -1;
  for (size_t i = 0; i < s->num_corners; i++)
    if (s->corners[i].v == v) {
      free(s->corners[i].sharpness);
      s->corners[i].sharpness = x;
      return 0;
    }
  tobj_subd_corner c = {v, x};
  if (!grow((void **)&s->corners, &s->num_corners, sizeof(c))) {
    free(x);
    return -1;
  }
  s->corners[s->num_corners - 1] = c;
  return 0;
}

static int add_hole(tobj_subd *s, size_t f) {
  for (size_t i = 0; i < s->num_holes; i++)
    if (s->holes[i] == f) return 0;
  PUSH(s->holes, s->num_holes, size_t, f);
  return 0;
}

/* scalar tag: 1 on success with *v set, 0 if it was an error (recorded) */
static int scalar(tobj_subd *s, int *slot, int v, const char *name) {
  (void)name;
  if (*slot != TOBJ_SUBD_UNSET) return add_err(s, "repeated scalar tag") ? -1 : 0;
  *slot = v;
  return 1;
}

static int counts_are(const size_t c[3], size_t a, size_t b, size_t d) {
  return c[0] == a && c[1] == b && c[2] == d;
}

/* One `t` line (tokens without the leading `t`). */
static int step(tobj_subd *s, const topo *t, const sl *a, size_t na, int *seen_dup_guard) {
  (void)seen_dup_guard;
  if (na < 2) return add_err(s, "t: expected <name> <ni>/<nf>/<ns>");
  sl name = a[0];
  size_t c[3];
  if (!parse_counts(a[1], c)) return add_err(s, "t: bad counts");
  if (na - 2 != c[0] + c[1] + c[2]) return add_err(s, "t: argument count");
  const sl *ints = a + 2, *flts = a + 2 + c[0], *strs = a + 2 + c[0] + c[1];
  long long iv[1];
  for (size_t i = 0; i < c[0]; i++)
    if (!parse_int(ints[i], iv)) return add_err(s, "t: bad integer");
  for (size_t i = 0; i < c[1]; i++)
    if (!is_decimal(flts[i])) return add_err(s, "t: bad decimal");

  if (sl_eq(name, "crease")) {
    if (!(c[0] >= 2 && c[0] % 2 == 0 && c[2] == 0 && (c[1] == 1 || c[1] == c[0] / 2)))
      return add_err(s, "crease: counts");
    for (size_t k = 0; k < c[0] / 2; k++) {
      long long x, y;
      parse_int(ints[2 * k], &x);
      parse_int(ints[2 * k + 1], &y);
      if (x < 0 || y < 0 || x == y) {
        if (add_err(s, "crease: bad edge")) return -1;
        continue;
      }
      size_t lo = (size_t)(x < y ? x : y), hi = (size_t)(x < y ? y : x);
      if (!has_edge(t, lo, hi)) {
        if (add_err(s, "crease: not an edge of the mesh")) return -1;
        continue;
      }
      if (set_crease(s, lo, hi, flts[c[1] == 1 ? 0 : k])) return -1;
    }
    return 0;
  }
  if (sl_eq(name, "corner")) {
    if (!(c[0] >= 1 && c[2] == 0 && (c[1] == 1 || c[1] == c[0])))
      return add_err(s, "corner: counts");
    for (size_t k = 0; k < c[0]; k++) {
      long long x;
      parse_int(ints[k], &x);
      if (x < 0 || !has_vert(t, (size_t)x)) {
        if (add_err(s, "corner: vertex not in the mesh")) return -1;
        continue;
      }
      if (set_corner(s, (size_t)x, flts[c[1] == 1 ? 0 : k])) return -1;
    }
    return 0;
  }
  if (sl_eq(name, "hole")) {
    if (!(c[0] >= 1 && c[1] == 0 && c[2] == 0)) return add_err(s, "hole: counts");
    for (size_t k = 0; k < c[0]; k++) {
      long long x;
      parse_int(ints[k], &x);
      if (x < 0 || (unsigned long long)x >= t->num_faces) {
        if (add_err(s, "hole: not a face of the mesh")) return -1;
        continue;
      }
      if (add_hole(s, (size_t)x)) return -1;
    }
    return 0;
  }
  if (sl_eq(name, "interpolateboundary") || sl_eq(name, "facevaryinginterpolateboundary") ||
      sl_eq(name, "facevaryingpropagatecorners")) {
    if (!counts_are(c, 1, 0, 0)) return add_err(s, "t: expected 1/0/0");
    if (sl_eq(name, "facevaryingpropagatecorners")) return 0; /* obsolete */
    long long x;
    parse_int(ints[0], &x);
    int fvar = sl_eq(name, "facevaryinginterpolateboundary");
    if (x < 0 || x > (fvar ? 5 : 2)) return add_err(s, "t: value out of range");
    int r = scalar(s, fvar ? &s->fvar_interp_boundary : &s->interp_boundary, (int)x, "");
    return r < 0 ? -1 : 0;
  }
  if (sl_eq(name, "scheme") || sl_eq(name, "creasemethod") || sl_eq(name, "smoothtriangles")) {
    if (!counts_are(c, 0, 0, 1)) return add_err(s, "t: expected 0/0/1");
    sl v = strs[0];
    int *slot, x = -1;
    if (sl_eq(name, "scheme")) {
      slot = &s->scheme;
      x = sl_eq(v, "catmark") ? TOBJ_SUBD_CATMARK
          : sl_eq(v, "loop")  ? TOBJ_SUBD_LOOP
          : sl_eq(v, "bilinear") ? TOBJ_SUBD_BILINEAR : -1;
    } else if (sl_eq(name, "creasemethod")) {
      slot = &s->crease_method;
      x = sl_eq(v, "normal") ? TOBJ_SUBD_CREASE_NORMAL
          : sl_eq(v, "chaikin") ? TOBJ_SUBD_CREASE_CHAIKIN : -1;
    } else {
      slot = &s->smooth_triangles;
      x = sl_eq(v, "catmark") ? TOBJ_SUBD_TRI_CATMARK
          : sl_eq(v, "smooth") ? TOBJ_SUBD_TRI_SMOOTH : -1;
    }
    if (x < 0) return add_err(s, "t: unknown value");
    int r = scalar(s, slot, x, "");
    return r < 0 ? -1 : 0;
  }
  /* unknown tag: kept as its canonical line */
  sb b = {0};
  sb_puts(&b, "t");
  for (size_t i = 0; i < na; i++) {
    sb_puts(&b, " ");
    sb_put(&b, a[i].p, a[i].n);
  }
  char *line = sb_take(&b);
  if (!line) return -1;
  if (!grow((void **)&s->unknown, &s->num_unknown, sizeof(char *))) {
    free(line);
    return -1;
  }
  s->unknown[s->num_unknown - 1] = line;
  return 0;
}

int tobj_subd_parse_lines(const char *const *lines, size_t num_lines,
                          const unsigned int *face_vertex_counts, size_t num_faces,
                          const int *vertex_indices, tobj_subd *out) {
  memset(out, 0, sizeof(*out));
  out->scheme = out->interp_boundary = out->fvar_interp_boundary = TOBJ_SUBD_UNSET;
  out->crease_method = out->smooth_triangles = TOBJ_SUBD_UNSET;
  topo t;
  toks tk = {0};
  int rc = build_topo(face_vertex_counts, num_faces, vertex_indices, &t);
  for (size_t i = 0; rc == 0 && i < num_lines; i++) {
    sl l = {lines[i], strlen(lines[i])};
    tokenize(drop_cr(l), &tk);
    if (tk.oom) {
      rc = -1;
      break;
    }
    if (tk.n == 0 || !sl_eq(tk.t[0], "t")) continue;
    rc = step(out, &t, tk.t + 1, tk.n - 1, NULL);
  }
  if (rc == 0 && out->smooth_triangles != TOBJ_SUBD_UNSET && out->scheme != TOBJ_SUBD_UNSET &&
      out->scheme != TOBJ_SUBD_CATMARK)
    rc = add_err(out, "smoothtriangles: catmark scheme only");
  if (rc == 0 && out->scheme == TOBJ_SUBD_LOOP && !t.all_tris)
    rc = add_err(out, "scheme loop: all faces must be triangles");
  free(tk.t);
  free(t.edges);
  free(t.verts);
  if (rc) {
    tobj_subd_free(out);
    return -1;
  }
  out->ok = out->num_errors == 0;
  return 0;
}

void tobj_subd_free(tobj_subd *s) {
  for (size_t i = 0; i < s->num_creases; i++) free(s->creases[i].sharpness);
  for (size_t i = 0; i < s->num_corners; i++) free(s->corners[i].sharpness);
  for (size_t i = 0; i < s->num_unknown; i++) free(s->unknown[i]);
  for (size_t i = 0; i < s->num_errors; i++) free(s->errors[i]);
  free(s->creases);
  free(s->corners);
  free(s->holes);
  free(s->unknown);
  free(s->errors);
  memset(s, 0, sizeof(*s));
}

/* ---------------------------------------------------------------- writer
 * Lean: TobjSubd.print */

static const char *const kScheme[] = {"catmark", "loop", "bilinear"};
static const char *const kCrease[] = {"normal", "chaikin"};
static const char *const kTri[] = {"catmark", "smooth"};

static void to_lines(sb *b, const tobj_subd *s) {
  if (!s->ok) return;
  if (s->scheme != TOBJ_SUBD_UNSET) {
    sb_puts(b, "t scheme 0/0/1 ");
    sb_puts(b, kScheme[s->scheme]);
    sb_puts(b, "\n");
  }
  if (s->interp_boundary != TOBJ_SUBD_UNSET) {
    sb_puts(b, "t interpolateboundary 1/0/0 ");
    sb_putz(b, (size_t)s->interp_boundary);
    sb_puts(b, "\n");
  }
  if (s->fvar_interp_boundary != TOBJ_SUBD_UNSET) {
    sb_puts(b, "t facevaryinginterpolateboundary 1/0/0 ");
    sb_putz(b, (size_t)s->fvar_interp_boundary);
    sb_puts(b, "\n");
  }
  if (s->crease_method != TOBJ_SUBD_UNSET) {
    sb_puts(b, "t creasemethod 0/0/1 ");
    sb_puts(b, kCrease[s->crease_method]);
    sb_puts(b, "\n");
  }
  if (s->smooth_triangles != TOBJ_SUBD_UNSET) {
    sb_puts(b, "t smoothtriangles 0/0/1 ");
    sb_puts(b, kTri[s->smooth_triangles]);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < s->num_creases; i++) {
    sb_puts(b, "t crease 2/1/0 ");
    sb_putz(b, s->creases[i].v0);
    sb_puts(b, " ");
    sb_putz(b, s->creases[i].v1);
    sb_puts(b, " ");
    sb_puts(b, s->creases[i].sharpness);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < s->num_corners; i++) {
    sb_puts(b, "t corner 1/1/0 ");
    sb_putz(b, s->corners[i].v);
    sb_puts(b, " ");
    sb_puts(b, s->corners[i].sharpness);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < s->num_holes; i += MAX_COUNT) {
    size_t n = s->num_holes - i < MAX_COUNT ? s->num_holes - i : MAX_COUNT;
    sb_puts(b, "t hole ");
    sb_putz(b, n);
    sb_puts(b, "/0/0");
    for (size_t k = 0; k < n; k++) {
      sb_puts(b, " ");
      sb_putz(b, s->holes[i + k]);
    }
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < s->num_unknown; i++) {
    sb_puts(b, s->unknown[i]);
    sb_puts(b, "\n");
  }
}

char *tobj_subd_to_lines(const tobj_subd *s, size_t *out_len) {
  sb b = {0};
  to_lines(&b, s);
  char *r = sb_take(&b);
  if (r && out_len) *out_len = b.n;
  return r;
}

/* ---------------------------------------------------------------- .obj subset
 * Lean: TobjSubd.parseObj / dumpObj */

typedef struct {
  char **lines;
  size_t num_lines;
  unsigned int *fvc;
  size_t num_faces;
  int *vi;
  size_t num_vi;
} omesh;

static void omesh_free(omesh *m) {
  for (size_t i = 0; i < m->num_lines; i++) free(m->lines[i]);
  free(m->lines);
  free(m->fvc);
  free(m->vi);
}

/* Face vertex: integer before the first '/', 1-based or negative-relative. */
static int face_vertex(sl tok, size_t nverts, int *out) {
  size_t j = 0;
  while (j < tok.n && tok.p[j] != '/') j++;
  sl d = {tok.p, j};
  long long v;
  if (!parse_int(d, &v)) return 0;
  long long idx = v > 0 ? v - 1 : (long long)nverts + v;
  if (v == 0 || idx < 0 || (unsigned long long)idx >= nverts) return 0;
  *out = (int)idx;
  return 1;
}

static int dump_obj(sb *b, const char *text, size_t len) {
  omesh *ms = NULL;
  size_t nm = 0, nverts = 0, pos = 0;
  toks tk = {0};
  int rc = 0;
  omesh empty;
  memset(&empty, 0, sizeof(empty));
  if (!grow((void **)&ms, &nm, sizeof(omesh))) return -1;
  ms[0] = empty;
  for (;;) {
    size_t e = pos;
    while (e < len && text[e] != '\n') e++;
    sl l = {text + pos, e - pos};
    l = drop_cr(l);
    tokenize(l, &tk);
    if (tk.oom) {
      rc = -1;
      break;
    }
    if (tk.n) {
      sl kw = tk.t[0];
      omesh *m = &ms[nm - 1];
      if (sl_eq(kw, "v")) {
        nverts++;
      } else if (sl_eq(kw, "o") || sl_eq(kw, "g")) {
        if (!grow((void **)&ms, &nm, sizeof(omesh))) {
          rc = -1;
          break;
        }
        ms[nm - 1] = empty;
      } else if (sl_eq(kw, "t")) {
        char *d = dup_sl(l);
        if (!d || !grow((void **)&m->lines, &m->num_lines, sizeof(char *))) {
          free(d);
          rc = -1;
          break;
        }
        m->lines[m->num_lines - 1] = d;
      } else if (sl_eq(kw, "f") && tk.n >= 4) {
        size_t n = tk.n - 1, k;
        int *q = (int *)realloc(m->vi, (m->num_vi + n) * sizeof(int));
        if (!q) {
          rc = -1;
          break;
        }
        m->vi = q;
        for (k = 0; k < n; k++)
          if (!face_vertex(tk.t[1 + k], nverts, &m->vi[m->num_vi + k])) break;
        if (k == n) {
          unsigned int c = (unsigned int)n;
          if (!grow((void **)&m->fvc, &m->num_faces, sizeof(unsigned int))) {
            rc = -1;
            break;
          }
          m->fvc[m->num_faces - 1] = c;
          m->num_vi += n;
        }
      }
    }
    if (e >= len) break;
    pos = e + 1;
  }
  for (size_t i = 0; rc == 0 && i < nm; i++) {
    omesh *m = &ms[i];
    if (!m->num_faces && !m->num_lines) continue;
    tobj_subd s;
    if (tobj_subd_parse_lines((const char *const *)m->lines, m->num_lines, m->fvc,
                              m->num_faces, m->vi, &s)) {
      rc = -1;
      break;
    }
    sb_puts(b, "mesh ");
    sb_putz(b, i);
    sb_puts(b, s.ok ? " ok=1\n" : " ok=0\n");
    to_lines(b, &s);
    tobj_subd_free(&s);
  }
  for (size_t i = 0; i < nm; i++) omesh_free(&ms[i]);
  free(ms);
  free(tk.t);
  return rc;
}

char *tobj_subd_dump_obj(const char *text, size_t len, size_t *out_len) {
  sb b = {0};
  if (dump_obj(&b, text, len)) {
    free(b.p);
    return NULL;
  }
  char *r = sb_take(&b);
  if (r && out_len) *out_len = b.n;
  return r;
}
