/*
 * tobj_skel.c — see tobj_skel.h. Mirrors formal/Skel (Lean `TobjSkel`).
 */
#include "tobj_skel.h"

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
static int is_alpha(char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }

/* ---------------------------------------------------------------- tokens
 * Lean: TobjSkel.lineTokens / dropCR (same as TobjSubd) */

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
      size_t cap = out->cap ? out->cap * 2 : 32;
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

/* ---------------------------------------------------------------- grammar */

/* Lean `isDecimal` (as in TobjSubd) */
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

/* Lean `validName`: [A-Za-z_][A-Za-z0-9_]* */
static int valid_name(sl s) {
  if (s.n == 0 || !(is_alpha(s.p[0]) || s.p[0] == '_')) return 0;
  for (size_t i = 1; i < s.n; i++)
    if (!(is_alpha(s.p[i]) || is_digit(s.p[i]) || s.p[i] == '_')) return 0;
  return 1;
}

/* Lean `parseInt?` (saturating; only compared with joint counts) */
#define BIG_INT ((long)1 << 40)
static int parse_int(sl s, long *out) {
  size_t i = 0;
  int neg = 0;
  if (i < s.n && (s.p[i] == '+' || s.p[i] == '-')) neg = s.p[i++] == '-';
  if (i >= s.n) return 0;
  long v = 0;
  for (; i < s.n; i++) {
    if (!is_digit(s.p[i])) return 0;
    v = v < BIG_INT / 10 ? v * 10 + (s.p[i] - '0') : BIG_INT;
  }
  *out = neg ? -v : v;
  return 1;
}

double tobj_skel_number(const char *text) { return strtod(text, NULL); }

/* ---------------------------------------------------------------- model
 * Lean: TobjSkel.step / finish */

static int add_err(tobj_skel *s, const char *e) {
  sl x = {e, strlen(e)};
  char *d = dup_sl(x);
  if (!d) return -1;
  char **q = (char **)realloc(s->errors, (s->num_errors + 1) * sizeof(char *));
  if (!q) {
    free(d);
    return -1;
  }
  s->errors = q;
  s->errors[s->num_errors++] = d;
  return 0;
}

static long find_joint(const tobj_skel *s, sl name) {
  for (size_t i = 0; i < s->num_joints; i++)
    if (sl_eq(name, s->joints[i].name)) return (long)i;
  return -1;
}

/* 16 decimal tokens -> owned texts, or NULL (error recorded by caller) */
static char **matrix(const sl *a, int *oom) {
  for (int k = 0; k < 16; k++)
    if (!is_decimal(a[k])) return NULL;
  char **m = (char **)calloc(16, sizeof(char *));
  if (!m) {
    *oom = 1;
    return NULL;
  }
  for (int k = 0; k < 16; k++) {
    m[k] = dup_sl(a[k]);
    if (!m[k]) {
      for (int j = 0; j < k; j++) free(m[j]);
      free(m);
      *oom = 1;
      return NULL;
    }
  }
  return m;
}

static void free_matrix(char **m) {
  if (!m) return;
  for (int k = 0; k < 16; k++) free(m[k]);
  free(m);
}

static int step(tobj_skel *s, sl kw, const sl *a, size_t na) {
  int oom = 0;
  if (sl_eq(kw, "skel_joint")) {
    if (!(na == 2 || na == 18)) return add_err(s, "skel_joint: expected <name> <parent> [16]");
    if (!valid_name(a[0])) return add_err(s, "skel_joint: invalid name");
    if (find_joint(s, a[0]) >= 0) return add_err(s, "skel_joint: repeated name");
    long parent = -1;
    if (!sl_eq(a[1], "-")) {
      parent = find_joint(s, a[1]);
      if (parent < 0) return add_err(s, "skel_joint: parent not declared earlier");
    }
    char **bind = NULL;
    if (na == 18) {
      bind = matrix(a + 2, &oom);
      if (oom) return -1;
      if (!bind) return add_err(s, "skel_joint: bad matrix");
    }
    tobj_skel_joint j;
    j.name = dup_sl(a[0]);
    j.parent = parent;
    j.bind = bind;
    j.rest = NULL;
    tobj_skel_joint *q =
        (tobj_skel_joint *)realloc(s->joints, (s->num_joints + 1) * sizeof(tobj_skel_joint));
    if (!j.name || !q) {
      free(j.name);
      free_matrix(bind);
      if (q) s->joints = q;
      return -1;
    }
    s->joints = q;
    s->joints[s->num_joints++] = j;
    return 0;
  }
  if (sl_eq(kw, "skel_rest")) {
    if (na != 17) return add_err(s, "skel_rest: expected <name> [16]");
    long j = find_joint(s, a[0]);
    if (j < 0) return add_err(s, "skel_rest: joint not declared earlier");
    if (s->joints[j].rest) return add_err(s, "skel_rest: repeated");
    char **m = matrix(a + 1, &oom);
    if (oom) return -1;
    if (!m) return add_err(s, "skel_rest: bad matrix");
    s->joints[j].rest = m;
    return 0;
  }
  /* skel_lib / skel_anim */
  int lib = sl_eq(kw, "skel_lib");
  char **path = lib ? &s->lib : &s->anim, **name = lib ? &s->lib_skeleton : &s->anim_name;
  if (!(na == 1 || na == 2)) return add_err(s, lib ? "skel_lib: expected <path> [<name>]"
                                                   : "skel_anim: expected <path> [<name>]");
  if (*path) return add_err(s, lib ? "skel_lib: repeated" : "skel_anim: repeated");
  *path = dup_sl(a[0]);
  if (!*path) return -1;
  if (na == 2) {
    *name = dup_sl(a[1]);
    if (!*name) return -1;
  }
  return 0;
}

static int is_skel_keyword(sl kw) {
  return sl_eq(kw, "skel_joint") || sl_eq(kw, "skel_rest") || sl_eq(kw, "skel_lib") ||
         sl_eq(kw, "skel_anim");
}

int tobj_skel_parse_lines(const char *const *lines, size_t num_lines, long max_joint_id,
                          tobj_skel *out) {
  memset(out, 0, sizeof(*out));
  toks tk = {0};
  int rc = 0;
  for (size_t i = 0; rc == 0 && i < num_lines; i++) {
    sl l = {lines[i], strlen(lines[i])};
    tokenize(drop_cr(l), &tk);
    if (tk.oom) {
      rc = -1;
      break;
    }
    if (tk.n == 0 || !is_skel_keyword(tk.t[0])) continue;
    out->ext = 1;
    rc = step(out, tk.t[0], tk.t + 1, tk.n - 1);
  }
  free(tk.t);
  if (rc == 0 && out->ext) {
    int missing = 0;
    for (size_t j = 0; j < out->num_joints; j++) missing |= out->joints[j].bind == NULL;
    if (missing && !out->lib) rc = add_err(out, "joint without bind matrix and no skel_lib");
    if (rc == 0 && max_joint_id >= 0 && (size_t)max_joint_id >= out->num_joints)
      rc = add_err(out, "vw: joint id without a skel_joint");
  }
  if (rc) {
    tobj_skel_free(out);
    return -1;
  }
  out->ok = out->ext && out->num_errors == 0;
  return 0;
}

void tobj_skel_free(tobj_skel *s) {
  for (size_t i = 0; i < s->num_joints; i++) {
    free(s->joints[i].name);
    free_matrix(s->joints[i].bind);
    free_matrix(s->joints[i].rest);
  }
  for (size_t i = 0; i < s->num_errors; i++) free(s->errors[i]);
  free(s->joints);
  free(s->errors);
  free(s->lib);
  free(s->lib_skeleton);
  free(s->anim);
  free(s->anim_name);
  memset(s, 0, sizeof(*s));
}

/* ---------------------------------------------------------------- writer
 * Lean: TobjSkel.printLines */

static void put_matrix(sb *b, char *const *m) {
  for (int k = 0; k < 16; k++) {
    sb_puts(b, " ");
    sb_puts(b, m[k]);
  }
}

static void to_lines(sb *b, const tobj_skel *s) {
  if (!s->ok) return;
  for (size_t i = 0; i < s->num_joints; i++) {
    const tobj_skel_joint *j = &s->joints[i];
    sb_puts(b, "skel_joint ");
    sb_puts(b, j->name);
    sb_puts(b, " ");
    sb_puts(b, j->parent < 0 ? "-" : s->joints[j->parent].name);
    if (j->bind) put_matrix(b, j->bind);
    sb_puts(b, "\n");
  }
  for (size_t i = 0; i < s->num_joints; i++) {
    const tobj_skel_joint *j = &s->joints[i];
    if (!j->rest) continue;
    sb_puts(b, "skel_rest ");
    sb_puts(b, j->name);
    put_matrix(b, j->rest);
    sb_puts(b, "\n");
  }
  if (s->lib) {
    sb_puts(b, "skel_lib ");
    sb_puts(b, s->lib);
    if (s->lib_skeleton) {
      sb_puts(b, " ");
      sb_puts(b, s->lib_skeleton);
    }
    sb_puts(b, "\n");
  }
  if (s->anim) {
    sb_puts(b, "skel_anim ");
    sb_puts(b, s->anim);
    if (s->anim_name) {
      sb_puts(b, " ");
      sb_puts(b, s->anim_name);
    }
    sb_puts(b, "\n");
  }
}

char *tobj_skel_to_lines(const tobj_skel *s, size_t *out_len) {
  sb b = {0};
  to_lines(&b, s);
  char *r = sb_take(&b);
  if (r && out_len) *out_len = b.n;
  return r;
}

/* ---------------------------------------------------------------- .obj subset
 * Lean: TobjSkel.dumpObj */

char *tobj_skel_dump_obj(const char *text, size_t len, size_t *out_len) {
  const char **lines = NULL;
  size_t nl = 0, pos = 0;
  long max_id = -1;
  toks tk = {0};
  char *copy = (char *)malloc(len + 1);
  if (!copy) return NULL;
  if (len) memcpy(copy, text, len);
  copy[len] = '\0';
  int oom = 0;
  for (;;) {
    size_t e = pos;
    while (e < len && copy[e] != '\n') e++;
    copy[e] = '\0';
    sl l = {copy + pos, e - pos};
    tokenize(drop_cr(l), &tk);
    if (tk.oom) {
      oom = 1;
      break;
    }
    if (tk.n && is_skel_keyword(tk.t[0])) {
      const char **q = (const char **)realloc(lines, (nl + 1) * sizeof(char *));
      if (!q) {
        oom = 1;
        break;
      }
      lines = q;
      lines[nl++] = copy + pos;
    } else if (tk.n && sl_eq(tk.t[0], "vw")) {
      /* vw <vertex> <joint> <weight> [<joint> <weight>]... */
      for (size_t k = 2; k < tk.n; k += 2) {
        long v;
        if (parse_int(tk.t[k], &v) && v > max_id) max_id = v;
      }
    }
    if (e >= len) break;
    pos = e + 1;
  }
  free(tk.t);
  sb b = {0};
  if (!oom) {
    tobj_skel s;
    if (tobj_skel_parse_lines(lines, nl, max_id, &s) != 0) {
      oom = 1;
    } else {
      if (!s.ext) {
        sb_puts(&b, "skel none\n");
      } else {
        sb_puts(&b, s.ok ? "skel ok=1 joints=" : "skel ok=0 joints=");
        sb_putz(&b, s.num_joints);
        sb_puts(&b, "\n");
        to_lines(&b, &s);
      }
      tobj_skel_free(&s);
    }
  }
  free(lines);
  free(copy);
  if (oom) {
    free(b.p);
    return NULL;
  }
  char *r = sb_take(&b);
  if (r && out_len) *out_len = b.n;
  return r;
}
