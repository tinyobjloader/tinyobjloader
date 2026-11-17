/*
 * tobj_mtlx — MaterialX-in-MTL extension (see tobj_mtlx.h, doc/mtlx-mtl.md).
 *
 * Every function below mirrors a definition of the Lean model in
 * formal/Mtlx/TobjMtlx (named in the comment); keep them in sync.
 */
#include "tobj_mtlx.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------------------------------------------------------------- strings */

typedef struct {
  const char *p;
  size_t n;
} sl; /* borrowed slice */

typedef struct {
  char *p;
  size_t n, cap;
  int oom;
} sb; /* growable string */

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

static char *dup_sl(sl s) {
  char *p = (char *)malloc(s.n + 1);
  if (!p) return NULL;
  if (s.n) memcpy(p, s.p, s.n);
  p[s.n] = '\0';
  return p;
}
static char *dup_cstr(const char *s) {
  sl x = {s, strlen(s)};
  return dup_sl(x);
}
static int sl_eq(sl a, const char *b) {
  size_t n = strlen(b);
  return a.n == n && (n == 0 || memcmp(a.p, b, n) == 0);
}
static int str_eq(const char *a, const char *b) {
  if (!a || !b) return a == b;
  return strcmp(a, b) == 0;
}

/* push one element onto a (ptr,count) array of type T */
static int grow(void **arr, size_t *count, size_t elem) {
  void *q = realloc(*arr, (*count + 1) * elem);
  if (!q) return 0;
  *arr = q;
  (*count)++;
  return 1;
}

/* ---------------------------------------------------------------- lexer
 * Lean: TobjMtlx.Syntax */

static int is_blank(char c) { return c == ' ' || c == '\t'; }

typedef struct {
  sl *t;
  size_t n, cap;
  int oom;
} toks;

static void toks_push(toks *v, sl s) {
  if (v->oom) return;
  if (v->n == v->cap) {
    size_t cap = v->cap ? v->cap * 2 : 8;
    sl *q = (sl *)realloc(v->t, cap * sizeof(sl));
    if (!q) {
      v->oom = 1;
      return;
    }
    v->t = q;
    v->cap = cap;
  }
  v->t[v->n++] = s;
}

/* Lean `tokenize`: 0 = ok, 1 = unterminated quote. */
static int tokenize(sl line, toks *out) {
  size_t i = 0;
  out->n = 0;
  while (i < line.n) {
    char c = line.p[i];
    if (is_blank(c)) {
      i++;
    } else if (c == '"') {
      size_t j = i + 1;
      while (j < line.n && line.p[j] != '"') j++;
      if (j >= line.n) return 1;
      sl t = {line.p + i + 1, j - i - 1};
      toks_push(out, t);
      i = j + 1;
    } else {
      size_t j = i;
      while (j < line.n && !is_blank(line.p[j])) j++;
      sl t = {line.p + i, j - i};
      toks_push(out, t);
      i = j;
    }
  }
  return 0;
}

/* Lean `restAfterKeyword` */
static sl rest_after_keyword(sl l) {
  size_t i = 0, e = l.n;
  while (i < e && is_blank(l.p[i])) i++;
  while (i < e && !is_blank(l.p[i])) i++;
  while (i < e && is_blank(l.p[i])) i++;
  while (e > i && is_blank(l.p[e - 1])) e--;
  sl r = {l.p + i, e - i};
  return r;
}

/* ---------------------------------------------------------------- values
 * Lean: MtlxSpec.Value (parseInt / parseDec / parseValue) */

static int is_digit(char c) { return c >= '0' && c <= '9'; }
static int is_space(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}
static sl trim(sl s) {
  while (s.n && is_space(s.p[0])) s.p++, s.n--;
  while (s.n && is_space(s.p[s.n - 1])) s.n--;
  return s;
}
static int all_digits_nonempty(const char *p, size_t n) {
  if (n == 0) return 0;
  for (size_t i = 0; i < n; i++)
    if (!is_digit(p[i])) return 0;
  return 1;
}
static sl strip_sign(sl s) {
  if (s.n && (s.p[0] == '-' || s.p[0] == '+')) s.p++, s.n--;
  return s;
}
static int parse_int_ok(sl s) {
  s = strip_sign(s);
  return all_digits_nonempty(s.p, s.n);
}
static int parse_float_ok(sl s) {
  sl body = strip_sign(s);
  size_t e = 0;
  while (e < body.n && body.p[e] != 'e' && body.p[e] != 'E') e++;
  /* mantissa = body[0,e); digits before the first '.', digits after it */
  size_t dot = 0;
  while (dot < e && body.p[dot] != '.') dot++;
  size_t ndig = 0;
  for (size_t i = 0; i < e; i++) {
    if (i == dot) continue;
    if (!is_digit(body.p[i])) return 0;
    ndig++;
  }
  if (ndig == 0) return 0;
  if (e == body.n) return 1;
  sl ex = {body.p + e + 1, body.n - e - 1};
  return parse_int_ok(ex);
}

/* Lean `splitOn ','` then `trim` each field, all must satisfy `f`;
 * returns the field count or -1. `array` = Lean `arrayFields` (blank -> 0). */
static long fields_ok(sl s, int (*f)(sl), int array) {
  if (array && trim(s).n == 0) return 0;
  long count = 0;
  size_t start = 0;
  for (size_t i = 0; i <= s.n; i++) {
    if (i == s.n || s.p[i] == ',') {
      sl fld = {s.p + start, i - start};
      if (!f(trim(fld))) return -1;
      count++;
      start = i + 1;
    }
  }
  return count;
}

typedef struct {
  const char *name;
  int arity;  /* fixed-size aggregate, 0 = none */
  int stride; /* float array stride, 0 = none */
} tyinfo;

static const tyinfo kTypes[] = {
    {"integer", 0, 0},     {"boolean", 0, 0},      {"float", 0, 0},
    {"color3", 3, 0},      {"color4", 4, 0},       {"vector2", 2, 0},
    {"vector3", 3, 0},     {"vector4", 4, 0},      {"matrix33", 9, 0},
    {"matrix44", 16, 0},   {"string", 0, 0},       {"filename", 0, 0},
    {"integerarray", 0, 0}, {"floatarray", 0, 1},  {"color3array", 0, 3},
    {"color4array", 0, 4}, {"vector2array", 0, 2}, {"vector3array", 0, 3},
    {"vector4array", 0, 4}, {"stringarray", 0, 0}};

static const tyinfo *find_ty(const char *t) {
  for (size_t i = 0; i < sizeof(kTypes) / sizeof(kTypes[0]); i++)
    if (strcmp(kTypes[i].name, t) == 0) return &kTypes[i];
  return NULL;
}

/* Lean `(parseValue (Ty.ofString ty) v).isSome` */
static int parse_value_ok(const char *ty, const char *v) {
  sl s = {v, strlen(v)};
  const tyinfo *t = find_ty(ty);
  if (!t) return 0;
  if (!strcmp(ty, "integer")) return parse_int_ok(trim(s));
  if (!strcmp(ty, "boolean")) return sl_eq(s, "true") || sl_eq(s, "false");
  if (!strcmp(ty, "float")) return parse_float_ok(trim(s));
  if (!strcmp(ty, "string") || !strcmp(ty, "filename") ||
      !strcmp(ty, "stringarray"))
    return 1;
  if (!strcmp(ty, "integerarray")) return fields_ok(s, parse_int_ok, 1) >= 0;
  if (t->arity) return fields_ok(s, parse_float_ok, 0) == t->arity;
  if (t->stride) {
    long n = fields_ok(s, parse_float_ok, 1);
    return n >= 0 && n % t->stride == 0;
  }
  return 0;
}

/* ---------------------------------------------------------------- names
 * Lean: MtlxSpec.Name, TobjMtlx.sanitize */

static int is_alpha(unsigned char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}
static int name_start(unsigned char c) { return is_alpha(c) || c == '_'; }
static int name_char(unsigned char c) {
  return is_alpha(c) || is_digit((char)c) || c == '_';
}
static int valid_name(const char *s) {
  if (!s || !*s || !name_start((unsigned char)s[0])) return 0;
  for (const char *p = s + 1; *p; p++)
    if (!name_char((unsigned char)*p)) return 0;
  return 1;
}

/* Lean works on code points: one non-ASCII character becomes one '_'. */
static char *sanitize(const char *n) {
  sb b = {0};
  for (const unsigned char *p = (const unsigned char *)n; *p; p++) {
    if ((*p & 0xC0) == 0x80) continue; /* UTF-8 continuation byte */
    char c = name_char(*p) ? (char)*p : '_';
    sb_put(&b, &c, 1);
  }
  if (b.oom) {
    free(b.p);
    return NULL;
  }
  if (b.n == 0) {
    free(b.p);
    return dup_cstr("_");
  }
  if (!name_start((unsigned char)b.p[0])) {
    sb c = {0};
    sb_put(&c, "_", 1);
    sb_put(&c, b.p, b.n);
    free(b.p);
    if (c.oom) {
      free(c.p);
      return NULL;
    }
    return c.p;
  }
  return b.p;
}

/* ---------------------------------------------------------------- parse
 * Lean: TobjMtlx.step / parseMtl */

#define PUSH(arr, cnt, T, val)                                  \
  do {                                                          \
    if (!grow((void **)&(arr), &(cnt), sizeof(T))) return -1;   \
    (arr)[(cnt)-1] = (val);                                     \
  } while (0)

static int add_err(tobj_mtlx_material *m, const char *e) {
  char *s = dup_cstr(e);
  if (!s) return -1;
  PUSH(m->errors, m->num_errors, char *, s);
  return 0;
}

/* Lean `splitDot`: returns index of the first '.', or -1. */
static long dot_at(sl t) {
  for (size_t i = 0; i < t.n; i++)
    if (t.p[i] == '.') return (long)i;
  return -1;
}

/* Lean `isRef`: `@x` is a connection, `@@x` a literal starting with '@'. */
static int is_ref(sl t) { return t.n >= 1 && t.p[0] == '@' && !(t.n >= 2 && t.p[1] == '@'); }
/* Lean `unescape` */
static sl unescape(sl t) {
  if (t.n >= 2 && t.p[0] == '@' && t.p[1] == '@') t.p++, t.n--;
  return t;
}

/* Lean `valueText` */
static char *value_text(sl ty, const sl *vs, size_t n, int *bad) {
  *bad = 0;
  for (size_t i = 0; i < n; i++)
    if (is_ref(vs[i])) {
      *bad = 1;
      return NULL;
    }
  if (sl_eq(ty, "string") || sl_eq(ty, "filename")) {
    if (n != 1) {
      *bad = 1;
      return NULL;
    }
    return dup_sl(unescape(vs[0]));
  }
  if (n == 0) {
    *bad = 1;
    return NULL;
  }
  sb b = {0};
  for (size_t i = 0; i < n; i++) {
    sl t = unescape(vs[i]);
    if (i) sb_put(&b, ", ", 2);
    sb_put(&b, t.p, t.n);
  }
  if (b.oom) {
    free(b.p);
    return NULL;
  }
  if (!b.p) return dup_cstr("");
  return b.p;
}

static int step(tobj_mtlx_material *m, const toks *tk) {
  if (tk->n == 0) return 0;
  sl kw = tk->t[0];
  const sl *a = tk->t + 1;
  size_t na = tk->n - 1;
  m->ext = 1;
  if (sl_eq(kw, "mtlx_version")) {
    if (na != 1) return add_err(m, "mtlx_version: expected 1 argument");
    char *v = dup_sl(a[0]);
    if (!v) return -1;
    PUSH(m->versions, m->num_versions, char *, v);
  } else if (sl_eq(kw, "mtlx_surface")) {
    if (na != 2) return add_err(m, "mtlx_surface: expected <name> <category>");
    char *n = dup_sl(a[0]), *c = dup_sl(a[1]);
    if (!n || !c) return free(n), free(c), -1;
    PUSH(m->surface, m->num_surface, char *, n);
    PUSH(m->surface, m->num_surface, char *, c);
  } else if (sl_eq(kw, "mtlx_node")) {
    if (na != 3)
      return add_err(m, "mtlx_node: expected <name> <category> <type>");
    tobj_mtlx_node d = {dup_sl(a[0]), dup_sl(a[1]), dup_sl(a[2])};
    if (!d.name || !d.category || !d.type) return -1;
    PUSH(m->nodes, m->num_nodes, tobj_mtlx_node, d);
  } else if (sl_eq(kw, "mtlx_input")) {
    const char *msg = "mtlx_input: expected <node>.<input> <type> <value>";
    if (na < 2) return add_err(m, msg);
    long d = dot_at(a[0]);
    if (na == 3 && is_ref(a[2])) { /* connection: @src[.out] */
      if (d < 0) return add_err(m, msg);
      sl r = {a[2].p + 1, a[2].n - 1};
      long ds = dot_at(r);
      tobj_mtlx_conn c;
      sl src = {r.p, ds < 0 ? r.n : (size_t)ds};
      sl node = {a[0].p, (size_t)d}, port = {a[0].p + d + 1, a[0].n - d - 1};
      c.src = dup_sl(src);
      c.src_out = NULL;
      if (ds >= 0) {
        sl o = {r.p + ds + 1, r.n - ds - 1};
        c.src_out = dup_sl(o);
        if (!c.src_out) return -1;
      }
      c.dst = dup_sl(node);
      c.port = dup_sl(port);
      c.type = dup_sl(a[1]);
      if (!c.src || !c.dst || !c.port || !c.type) return -1;
      PUSH(m->conns, m->num_conns, tobj_mtlx_conn, c);
      return 0;
    }
    int bad = 0;
    char *v = value_text(a[1], a + 2, na - 2, &bad);
    if (d < 0 || bad) {
      free(v);
      return add_err(m, msg);
    }
    if (!v) return -1;
    sl node = {a[0].p, (size_t)d}, port = {a[0].p + d + 1, a[0].n - d - 1};
    tobj_mtlx_input in = {dup_sl(node), dup_sl(port), dup_sl(a[1]), v};
    if (!in.node || !in.port || !in.type) return -1;
    PUSH(m->inputs, m->num_inputs, tobj_mtlx_input, in);
  } else if (sl_eq(kw, "mtlx_colorspace")) {
    const char *msg = "mtlx_colorspace: expected <node>.<input> <colorspace>";
    if (na != 2) return add_err(m, msg);
    long d = dot_at(a[0]);
    if (d < 0) return add_err(m, msg);
    sl node = {a[0].p, (size_t)d}, port = {a[0].p + d + 1, a[0].n - d - 1};
    tobj_mtlx_colorspace c = {dup_sl(node), dup_sl(port), dup_sl(a[1])};
    if (!c.node || !c.port || !c.colorspace) return -1;
    PUSH(m->colorspaces, m->num_colorspaces, tobj_mtlx_colorspace, c);
  } else if (sl_eq(kw, "mtlx_include")) {
    if (na != 1) return add_err(m, "mtlx_include: expected 1 argument");
    char *p = dup_sl(a[0]);
    if (!p) return -1;
    PUSH(m->includes, m->num_includes, char *, p);
  }
  return 0;
}

static int is_ext_keyword(sl kw) {
  return sl_eq(kw, "mtlx_version") || sl_eq(kw, "mtlx_surface") ||
         sl_eq(kw, "mtlx_node") || sl_eq(kw, "mtlx_input") ||
         sl_eq(kw, "mtlx_include") ||
         sl_eq(kw, "mtlx_colorspace");
}

/* ---------------------------------------------------------------- check
 * Lean: TobjMtlx.check */

static const char *node_ty(const tobj_mtlx_material *m, const char *n) {
  for (size_t i = 0; i < m->num_nodes; i++)
    if (str_eq(m->nodes[i].name, n)) return m->nodes[i].type;
  return NULL;
}
static const char *surf_name(const tobj_mtlx_material *m) {
  return m->num_surface ? m->surface[0] : "";
}
static int has_name(const tobj_mtlx_material *m, const char *n) {
  return str_eq(surf_name(m), n) || node_ty(m, n) != NULL;
}
/* Graph vertex index of a name in `lower m` (surface first, then nodes). */
static long vtx(const tobj_mtlx_material *m, const char *n) {
  if (str_eq(surf_name(m), n)) return 0;
  for (size_t i = 0; i < m->num_nodes; i++)
    if (str_eq(m->nodes[i].name, n)) return (long)i + 1;
  return -1;
}

/* DFS colouring: 0 white, 1 grey, 2 black. Iterative, explicit stack. */
static int acyclic(const tobj_mtlx_material *m) {
  size_t nv = m->num_nodes + 1;
  unsigned char *col = (unsigned char *)calloc(nv, 1);
  size_t *stk = (size_t *)malloc(nv * 2 * sizeof(size_t));
  if (!col || !stk) return free(col), free(stk), -1;
  int ok = 1;
  for (size_t s = 0; s < nv && ok; s++) {
    if (col[s]) continue;
    size_t sp = 0;
    stk[sp++] = s;
    stk[sp++] = 0; /* next edge index to examine */
    col[s] = 1;
    while (sp && ok) {
      size_t v = stk[sp - 2], *e = &stk[sp - 1];
      const char *vn = v == 0 ? surf_name(m) : m->nodes[v - 1].name;
      int pushed = 0;
      for (; *e < m->num_conns; (*e)++) {
        const tobj_mtlx_conn *c = &m->conns[*e];
        if (!str_eq(c->dst, vn)) continue;
        long w = vtx(m, c->src);
        if (w < 0) continue; /* unbound: rejected by connOk already */
        if (col[w] == 1) {
          ok = 0;
          break;
        }
        if (col[w] == 0) {
          (*e)++;
          col[w] = 1;
          stk[sp++] = (size_t)w;
          stk[sp++] = 0;
          pushed = 1;
          break;
        }
      }
      if (!ok || pushed) continue;
      col[v] = 2;
      sp -= 2;
    }
  }
  free(col);
  free(stk);
  return ok;
}

static int version_ok(const char *v) {
  const char *d = strchr(v, '.');
  if (!d) return 0;
  if (strchr(d + 1, '.')) return 0;
  return all_digits_nonempty(v, (size_t)(d - v)) &&
         all_digits_nonempty(d + 1, strlen(d + 1));
}

static int check(const tobj_mtlx_material *m) {
  if (m->num_errors) return 0;
  if (m->num_surface != 2) return 0; /* exactly one (name, category) pair */
  if (m->num_versions > 1) return 0;
  for (size_t i = 0; i < m->num_versions; i++)
    if (!version_ok(m->versions[i])) return 0;
  /* names: surface then nodes, all valid and distinct */
  if (!valid_name(surf_name(m))) return 0;
  for (size_t i = 0; i < m->num_nodes; i++) {
    if (!valid_name(m->nodes[i].name)) return 0;
    if (str_eq(m->nodes[i].name, surf_name(m))) return 0;
    for (size_t j = 0; j < i; j++)
      if (str_eq(m->nodes[i].name, m->nodes[j].name)) return 0;
  }
  if (!valid_name(m->surface[1])) return 0;
  for (size_t i = 0; i < m->num_nodes; i++)
    if (!valid_name(m->nodes[i].category) || !find_ty(m->nodes[i].type))
      return 0;
  for (size_t i = 0; i < m->num_inputs; i++) {
    const tobj_mtlx_input *in = &m->inputs[i];
    if (!has_name(m, in->node) || !valid_name(in->port) || !find_ty(in->type) ||
        !parse_value_ok(in->type, in->value))
      return 0;
    for (size_t j = 0; j < i; j++)
      if (str_eq(in->node, m->inputs[j].node) &&
          str_eq(in->port, m->inputs[j].port))
        return 0;
  }
  for (size_t i = 0; i < m->num_conns; i++) {
    const tobj_mtlx_conn *c = &m->conns[i];
    const char *st = node_ty(m, c->src);
    if (!st) return 0;
    if (c->src_out && strcmp(c->src_out, "out") != 0) return 0;
    if (!has_name(m, c->dst) || !valid_name(c->port)) return 0;
    if (!str_eq(st, c->type)) return 0;
    for (size_t j = 0; j < m->num_inputs; j++) /* one binding per input */
      if (str_eq(m->inputs[j].node, c->dst) && str_eq(m->inputs[j].port, c->port))
        return 0;
    for (size_t j = 0; j < i; j++)
      if (str_eq(c->dst, m->conns[j].dst) && str_eq(c->port, m->conns[j].port))
        return 0;
  }
  for (size_t i = 0; i < m->num_colorspaces; i++) {
    const tobj_mtlx_colorspace *c = &m->colorspaces[i];
    int found = 0;
    for (size_t j = 0; j < m->num_inputs && !found; j++)
      found = str_eq(m->inputs[j].node, c->node) && str_eq(m->inputs[j].port, c->port);
    if (!found || !valid_name(c->colorspace)) return 0;
    for (size_t j = 0; j < i; j++)
      if (str_eq(c->node, m->colorspaces[j].node) && str_eq(c->port, m->colorspaces[j].port))
        return 0;
  }
  return acyclic(m);
}

/* ---------------------------------------------------------------- driver */

int tobj_mtlx_parse(const char *text, size_t len, tobj_mtlx_doc *out) {
  memset(out, 0, sizeof(*out));
  toks tk = {0};
  size_t pos = 0;
  int rc = 0;
  for (;;) {
    size_t e = pos;
    while (e < len && text[e] != '\n') e++;
    sl l = {text + pos, e - pos};
    if (l.n && l.p[l.n - 1] == '\r') l.n--; /* Lean `dropCR` */
    size_t i = 0;
    while (i < l.n && is_blank(l.p[i])) i++;
    if (!(i < l.n && l.p[i] == '#')) {
      size_t j = i;
      while (j < l.n && !is_blank(l.p[j])) j++;
      sl kw = {l.p + i, j - i};
      if (sl_eq(kw, "newmtl")) {
        tobj_mtlx_material m;
        memset(&m, 0, sizeof(m));
        m.name = dup_sl(rest_after_keyword(l));
        if (!m.name || !grow((void **)&out->materials, &out->num_materials,
                             sizeof(m))) {
          free(m.name);
          rc = -1;
          break;
        }
        out->materials[out->num_materials - 1] = m;
      } else if (is_ext_keyword(kw) && out->num_materials) {
        tobj_mtlx_material *m = &out->materials[out->num_materials - 1];
        int t = tokenize(l, &tk);
        if (tk.oom) {
          rc = -1;
          break;
        }
        if (t) {
          m->ext = 1;
          if (add_err(m, "unterminated quote")) {
            rc = -1;
            break;
          }
        } else if (step(m, &tk)) {
          rc = -1;
          break;
        }
      }
    }
    if (e >= len) break;
    pos = e + 1;
  }
  free(tk.t);
  for (size_t i = 0; rc == 0 && i < out->num_materials; i++) {
    tobj_mtlx_material *m = &out->materials[i];
    if (m->ext) {
      int c = check(m);
      if (c < 0) rc = -1;
      m->ok = c > 0;
    }
  }
  if (rc) tobj_mtlx_free(out);
  return rc;
}

static void free_strs(char **s, size_t n) {
  for (size_t i = 0; i < n; i++) free(s[i]);
  free(s);
}

void tobj_mtlx_free(tobj_mtlx_doc *doc) {
  if (!doc) return;
  for (size_t i = 0; i < doc->num_materials; i++) {
    tobj_mtlx_material *m = &doc->materials[i];
    free(m->name);
    free_strs(m->versions, m->num_versions);
    free_strs(m->surface, m->num_surface);
    for (size_t j = 0; j < m->num_nodes; j++)
      free(m->nodes[j].name), free(m->nodes[j].category), free(m->nodes[j].type);
    free(m->nodes);
    for (size_t j = 0; j < m->num_inputs; j++)
      free(m->inputs[j].node), free(m->inputs[j].port), free(m->inputs[j].type),
          free(m->inputs[j].value);
    free(m->inputs);
    for (size_t j = 0; j < m->num_conns; j++)
      free(m->conns[j].src), free(m->conns[j].src_out), free(m->conns[j].dst),
          free(m->conns[j].port), free(m->conns[j].type);
    free(m->conns);
    free_strs(m->includes, m->num_includes);
    for (size_t j = 0; j < m->num_colorspaces; j++)
      free(m->colorspaces[j].node), free(m->colorspaces[j].port),
          free(m->colorspaces[j].colorspace);
    free(m->colorspaces);
    free_strs(m->errors, m->num_errors);
  }
  free(doc->materials);
  memset(doc, 0, sizeof(*doc));
}

/* ---------------------------------------------------------------- XML
 * Lean: TobjMtlx.toDoc + MtlxSpec.printXml */

static void put_attr(sb *b, const char *k, const char *v) {
  sb_puts(b, " ");
  sb_puts(b, k);
  sb_puts(b, "=\"");
  for (const char *p = v; *p; p++) {
    switch (*p) {
      case '"': sb_puts(b, "&quot;"); break;
      case '&': sb_puts(b, "&amp;"); break;
      case '<': sb_puts(b, "&lt;"); break;
      case '>': sb_puts(b, "&gt;"); break;
      default: sb_put(b, p, 1);
    }
  }
  sb_puts(b, "\"");
}

static void indent(sb *b, int d) {
  for (int i = 0; i < d; i++) sb_puts(b, "  ");
}

static void conn_input(sb *b, int d, const tobj_mtlx_material *m,
                       const char *M, int into_surface,
                       const tobj_mtlx_conn *c) {
  (void)m;
  indent(b, d);
  sb_puts(b, "<input");
  put_attr(b, "name", c->port);
  put_attr(b, "type", c->type);
  if (into_surface) {
    sb_puts(b, " nodegraph=\"NG_");
    sb_puts(b, M);
    sb_puts(b, "\" output=\"o_");
    sb_puts(b, c->src);
    sb_puts(b, "\"");
  } else {
    put_attr(b, "nodename", c->src);
  }
  sb_puts(b, "/>\n");
}

/* Lean `nodeInputs`; returns number of children written. */
static size_t node_inputs(sb *b, int d, const tobj_mtlx_material *m,
                          const char *M, const char *n, int into_surface,
                          int dry) {
  size_t k = 0;
  for (size_t i = 0; i < m->num_inputs; i++) {
    const tobj_mtlx_input *in = &m->inputs[i];
    if (!str_eq(in->node, n)) continue;
    k++;
    if (dry) continue;
    const tobj_mtlx_conn *c = NULL;
    for (size_t j = 0; j < m->num_conns && !c; j++)
      if (str_eq(m->conns[j].dst, n) && str_eq(m->conns[j].port, in->port))
        c = &m->conns[j];
    if (c) {
      conn_input(b, d, m, M, into_surface, c);
    } else {
      indent(b, d);
      sb_puts(b, "<input");
      put_attr(b, "name", in->port);
      put_attr(b, "type", in->type);
      put_attr(b, "value", in->value);
      for (size_t j = 0; j < m->num_colorspaces; j++)
        if (str_eq(m->colorspaces[j].node, n) && str_eq(m->colorspaces[j].port, in->port)) {
          put_attr(b, "colorspace", m->colorspaces[j].colorspace);
          break;
        }
      sb_puts(b, "/>\n");
    }
  }
  for (size_t j = 0; j < m->num_conns; j++) {
    const tobj_mtlx_conn *c = &m->conns[j];
    if (!str_eq(c->dst, n)) continue;
    int has_const = 0;
    for (size_t i = 0; i < m->num_inputs && !has_const; i++)
      has_const = str_eq(m->inputs[i].node, n) && str_eq(m->inputs[i].port, c->port);
    if (has_const) continue;
    k++;
    if (!dry) conn_input(b, d, m, M, into_surface, c);
  }
  return k;
}

static void open_elem(sb *b, int d, const char *tag) {
  indent(b, d);
  sb_puts(b, "<");
  sb_puts(b, tag);
}

static void mat_elems(sb *b, const tobj_mtlx_material *m, const char *M) {
  const char *sn = surf_name(m);
  if (m->num_nodes) {
    open_elem(b, 1, "nodegraph");
    sb_puts(b, " name=\"NG_");
    sb_puts(b, M);
    sb_puts(b, "\">\n");
    for (size_t i = 0; i < m->num_nodes; i++) {
      const tobj_mtlx_node *nd = &m->nodes[i];
      open_elem(b, 2, nd->category);
      put_attr(b, "name", nd->name);
      put_attr(b, "type", nd->type);
      if (node_inputs(b, 3, m, M, nd->name, 0, 1) == 0) {
        sb_puts(b, "/>\n");
      } else {
        sb_puts(b, ">\n");
        node_inputs(b, 3, m, M, nd->name, 0, 0);
        indent(b, 2);
        sb_puts(b, "</");
        sb_puts(b, nd->category);
        sb_puts(b, ">\n");
      }
    }
    /* Lean `surfaceSources` (first-occurrence dedup) */
    for (size_t j = 0; j < m->num_conns; j++) {
      const tobj_mtlx_conn *c = &m->conns[j];
      if (!str_eq(c->dst, sn)) continue;
      int seen = 0;
      for (size_t i = 0; i < j && !seen; i++)
        seen = str_eq(m->conns[i].dst, sn) && str_eq(m->conns[i].src, c->src);
      if (seen) continue;
      const char *ty = node_ty(m, c->src);
      open_elem(b, 2, "output");
      sb_puts(b, " name=\"o_");
      sb_puts(b, c->src);
      sb_puts(b, "\"");
      put_attr(b, "type", ty ? ty : "");
      put_attr(b, "nodename", c->src);
      sb_puts(b, "/>\n");
    }
    indent(b, 1);
    sb_puts(b, "</nodegraph>\n");
  }
  const char *cat = m->surface[1];
  open_elem(b, 1, cat);
  sb_puts(b, " name=\"SR_");
  sb_puts(b, M);
  sb_puts(b, "\" type=\"surfaceshader\"");
  if (node_inputs(b, 2, m, M, sn, 1, 1) == 0) {
    sb_puts(b, "/>\n");
  } else {
    sb_puts(b, ">\n");
    node_inputs(b, 2, m, M, sn, 1, 0);
    indent(b, 1);
    sb_puts(b, "</");
    sb_puts(b, cat);
    sb_puts(b, ">\n");
  }
  open_elem(b, 1, "surfacematerial");
  put_attr(b, "name", M);
  sb_puts(b, " type=\"material\">\n");
  indent(b, 2);
  sb_puts(b, "<input name=\"surfaceshader\" type=\"surfaceshader\" nodename=\"SR_");
  sb_puts(b, M);
  sb_puts(b, "\"/>\n");
  indent(b, 1);
  sb_puts(b, "</surfacematerial>\n");
}

static int accepted(const tobj_mtlx_material *m) { return m->ext && m->ok; }

static void to_xml(sb *b, const tobj_mtlx_doc *doc) {
  const char *ver = NULL;
  size_t nacc = 0;
  for (size_t i = 0; i < doc->num_materials; i++) {
    const tobj_mtlx_material *m = &doc->materials[i];
    if (!accepted(m)) continue;
    nacc++;
    if (!ver && m->num_versions) ver = m->versions[0];
  }
  sb_puts(b, "<?xml version=\"1.0\"?>\n<materialx");
  put_attr(b, "version", ver ? ver : "1.39");
  /* includes, first-occurrence dedup across accepted materials */
  size_t nincs = 0;
  for (size_t i = 0; i < doc->num_materials; i++)
    if (accepted(&doc->materials[i])) nincs += doc->materials[i].num_includes;
  if (nacc == 0) {
    sb_puts(b, "/>\n");
    return;
  }
  sb_puts(b, ">\n");
  if (nincs) {
    for (size_t i = 0; i < doc->num_materials; i++) {
      const tobj_mtlx_material *m = &doc->materials[i];
      if (!accepted(m)) continue;
      for (size_t k = 0; k < m->num_includes; k++) {
        int seen = 0;
        for (size_t i2 = 0; i2 <= i && !seen; i2++) {
          const tobj_mtlx_material *m2 = &doc->materials[i2];
          if (!accepted(m2)) continue;
          size_t lim = i2 == i ? k : m2->num_includes;
          for (size_t k2 = 0; k2 < lim && !seen; k2++)
            seen = str_eq(m2->includes[k2], m->includes[k]);
        }
        if (seen) continue;
        indent(b, 1);
        sb_puts(b, "<xi:include");
        put_attr(b, "href", m->includes[k]);
        sb_puts(b, "/>\n");
      }
    }
  }
  /* Lean `assignNames` / `uniqueName` */
  char **used = (char **)calloc(nacc, sizeof(char *));
  size_t nu = 0;
  if (!used) {
    b->oom = 1;
    return;
  }
  for (size_t i = 0; i < doc->num_materials && !b->oom; i++) {
    const tobj_mtlx_material *m = &doc->materials[i];
    if (!accepted(m)) continue;
    char *base = sanitize(m->name);
    if (!base) {
      b->oom = 1;
      break;
    }
    char *M = base;
    int taken = 0;
    for (size_t u = 0; u < nu && !taken; u++) taken = str_eq(used[u], base);
    if (taken) {
      M = NULL;
      for (size_t k = 2; k <= nu + 2 && !M; k++) {
        char suf[32];
        snprintf(suf, sizeof(suf), "_%zu", k);
        sb c = {0};
        sb_puts(&c, base);
        sb_puts(&c, suf);
        if (c.oom) break;
        int t2 = 0;
        for (size_t u = 0; u < nu && !t2; u++) t2 = str_eq(used[u], c.p);
        if (t2) free(c.p);
        else M = c.p;
      }
      free(base);
      if (!M) {
        b->oom = 1;
        break;
      }
    }
    used[nu++] = M;
    mat_elems(b, m, M);
  }
  for (size_t u = 0; u < nu; u++) free(used[u]);
  free(used);
  sb_puts(b, "</materialx>\n");
}

char *tobj_mtlx_to_xml(const tobj_mtlx_doc *doc, size_t *out_len) {
  sb b = {0};
  to_xml(&b, doc);
  if (b.oom) {
    free(b.p);
    return NULL;
  }
  if (out_len) *out_len = b.n;
  return b.p;
}

char *tobj_mtlx_dump(const tobj_mtlx_doc *doc, size_t *out_len) {
  sb b = {0};
  for (size_t i = 0; i < doc->num_materials; i++) {
    const tobj_mtlx_material *m = &doc->materials[i];
    sb_puts(&b, "mat ");
    sb_puts(&b, m->name);
    sb_puts(&b, m->ext ? " ext=1" : " ext=0");
    sb_puts(&b, accepted(m) ? " ok=1\n" : " ok=0\n");
  }
  to_xml(&b, doc);
  if (b.oom) {
    free(b.p);
    return NULL;
  }
  if (out_len) *out_len = b.n;
  return b.p;
}

/* ---------------------------------------------------------------- .mtl writer
 * Canonical extension lines; parse(to_mtl(doc)) has the same XML as doc. */

/* One token. `esc` re-adds the `@@` escape removed by the parser (values). */
static void put_tok(sb *b, const char *s, int esc) {
  int quote = *s == '\0' || *s == '"';
  for (const char *c = s; *c; c++)
    if (is_blank(*c) || *c == '\r') quote = 1;
  sb_puts(b, " ");
  if (quote) sb_puts(b, "\"");
  if (esc && *s == '@') sb_puts(b, "@");
  sb_puts(b, s);
  if (quote) sb_puts(b, "\"");
}

static void put_ep(sb *b, const char *kw, const char *node, const char *port) {
  sb_puts(b, kw);
  sb_puts(b, " ");
  sb_puts(b, node);
  sb_puts(b, ".");
  sb_puts(b, port);
}

static void mat_mtl(sb *b, const tobj_mtlx_material *m) {
  sb_puts(b, "newmtl ");
  sb_puts(b, m->name);
  /* the reader drops one trailing '\r' */
  size_t nl = strlen(m->name);
  if (nl && m->name[nl - 1] == '\r') sb_puts(b, "\r");
  sb_puts(b, "\n");
  if (!accepted(m)) return;
  for (size_t i = 0; i < m->num_versions; i++) {
    sb_puts(b, "mtlx_version");
    put_tok(b, m->versions[i], 0);
    sb_puts(b, "\n");
  }
  sb_puts(b, "mtlx_surface ");
  sb_puts(b, m->surface[0]);
  sb_puts(b, " ");
  sb_puts(b, m->surface[1]);
  sb_puts(b, "\n");
  for (size_t i = 0; i < m->num_nodes; i++) {
    sb_puts(b, "mtlx_node ");
    sb_puts(b, m->nodes[i].name);
    sb_puts(b, " ");
    sb_puts(b, m->nodes[i].category);
    sb_puts(b, " ");
    sb_puts(b, m->nodes[i].type);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < m->num_inputs; i++) {
    const tobj_mtlx_input *in = &m->inputs[i];
    put_ep(b, "mtlx_input", in->node, in->port);
    sb_puts(b, " ");
    sb_puts(b, in->type);
    if (str_eq(in->type, "string") || str_eq(in->type, "filename")) {
      put_tok(b, in->value, 1);
    } else { /* value text is the tokens joined with ", " */
      const char *p = in->value;
      for (;;) {
        const char *e = strstr(p, ", ");
        size_t n = e ? (size_t)(e - p) : strlen(p);
        sl piece = {p, n};
        char *t = dup_sl(piece);
        if (!t) {
          b->oom = 1;
          return;
        }
        put_tok(b, t, 1);
        free(t);
        if (!e) break;
        p = e + 2;
      }
    }
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < m->num_colorspaces; i++) {
    const tobj_mtlx_colorspace *c = &m->colorspaces[i];
    put_ep(b, "mtlx_colorspace", c->node, c->port);
    put_tok(b, c->colorspace, 0);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < m->num_conns; i++) {
    const tobj_mtlx_conn *c = &m->conns[i];
    put_ep(b, "mtlx_input", c->dst, c->port);
    sb_puts(b, " ");
    sb_puts(b, c->type);
    sb_puts(b, " @");
    sb_puts(b, c->src);
    if (c->src_out) {
      sb_puts(b, ".");
      sb_puts(b, c->src_out);
    }
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < m->num_includes; i++) {
    sb_puts(b, "mtlx_include");
    put_tok(b, m->includes[i], 0);
    sb_puts(b, "\n");
  }
}

char *tobj_mtlx_to_mtl(const tobj_mtlx_doc *doc, size_t *out_len) {
  sb b = {0};
  for (size_t i = 0; i < doc->num_materials; i++) mat_mtl(&b, &doc->materials[i]);
  if (!b.p && !b.oom) sb_puts(&b, "");
  if (b.oom) {
    free(b.p);
    return NULL;
  }
  if (out_len) *out_len = b.n;
  return b.p;
}

int tobj_mtlx_parse_lines(const char *name, const char *const *lines,
                          size_t num_lines, tobj_mtlx_doc *out) {
  sb b = {0};
  sb_puts(&b, "newmtl ");
  sb_puts(&b, name ? name : "");
  for (size_t i = 0; i < num_lines; i++) {
    sb_puts(&b, "\n");
    sb_puts(&b, lines[i]);
  }
  sb_puts(&b, "\n");
  if (b.oom) {
    free(b.p);
    memset(out, 0, sizeof(*out));
    return -1;
  }
  int rc = tobj_mtlx_parse(b.p, b.n, out);
  free(b.p);
  return rc;
}
