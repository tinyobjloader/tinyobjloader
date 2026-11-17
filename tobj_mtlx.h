/*
 * tobj_mtlx — MaterialX-in-MTL extension for tinyobjloader (C11).
 *
 * Parses the `mtlx_*` lines of a Wavefront .mtl file into a
 * MaterialX node graph per material, checks it, and writes the equivalent
 * MaterialX (.mtlx) document. See doc/mtlx-mtl.md for the format.
 *
 * The normative specification is the Lean 4 model in formal/Mtlx
 * (TobjMtlx.parseMtl / check / toDoc). `tobj_mtlx_dump` produces byte-for-byte
 * the output of the Lean reference executable `mtlxmtl`; the two are compared
 * by formal/Mtlx/tools/diff.sh.
 *
 * Requires libc (malloc). MIT license, same as tinyobjloader.
 */
#ifndef TOBJ_MTLX_H_
#define TOBJ_MTLX_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tobj_mtlx_node {
  char *name, *category, *type;
} tobj_mtlx_node;

typedef struct tobj_mtlx_input {
  char *node, *port, *type;
  char *value; /* canonical value text: numbers joined by ", " */
} tobj_mtlx_input;

typedef struct tobj_mtlx_conn {
  char *src;
  char *src_out; /* NULL when the source output was omitted */
  char *dst, *port;
  char *type; /* declared input type; must equal the source node's type */
} tobj_mtlx_conn;

typedef struct tobj_mtlx_colorspace {
  char *node, *port, *colorspace;
} tobj_mtlx_colorspace;

typedef struct tobj_mtlx_material {
  char *name;
  char **versions;            size_t num_versions;
  char **surface;             size_t num_surface; /* pairs: name, category */
  tobj_mtlx_node *nodes;      size_t num_nodes;
  tobj_mtlx_input *inputs;    size_t num_inputs;
  tobj_mtlx_conn *conns;      size_t num_conns;
  char **includes;            size_t num_includes;
  tobj_mtlx_colorspace *colorspaces; size_t num_colorspaces;
  char **errors;              size_t num_errors;
  int ext; /* the material uses the extension */
  int ok;  /* ext && well-formed (Lean `check`) */
} tobj_mtlx_material;

typedef struct tobj_mtlx_doc {
  tobj_mtlx_material *materials;
  size_t num_materials;
} tobj_mtlx_doc;

/* Parse a whole .mtl text (which must not contain NUL bytes: names and
 * values are returned as C strings). Returns 0 on success, -1 on allocation failure. */
int tobj_mtlx_parse(const char *text, size_t len, tobj_mtlx_doc *out);
void tobj_mtlx_free(tobj_mtlx_doc *doc);

/* Parse one material from its extension lines as stored by the loaders
 * (tobj_material.mtlx_lines, tinyobj::material_t::mtlx_lines). Equivalent to
 * tobj_mtlx_parse on "newmtl <name>\n" followed by the lines. */
int tobj_mtlx_parse_lines(const char *name, const char *const *lines,
                          size_t num_lines, tobj_mtlx_doc *out);

/* MaterialX document for the accepted materials. Returns a malloc'd
 * NUL-terminated string (caller frees) or NULL on allocation failure. */
char *tobj_mtlx_to_xml(const tobj_mtlx_doc *doc, size_t *out_len);

/* Canonical .mtl text: a `newmtl` line per material, followed, for accepted
 * materials, by their extension lines (version, surface, nodes, constant
 * inputs, colorspaces, connections, includes). Classic keys are not written.
 * Parsing the result gives the same tobj_mtlx_to_xml document. Returns a
 * malloc'd NUL-terminated string (caller frees) or NULL on allocation failure. */
char *tobj_mtlx_to_mtl(const tobj_mtlx_doc *doc, size_t *out_len);

/* `mat <name> ext=<0|1> ok=<0|1>` lines followed by the XML document. */
char *tobj_mtlx_dump(const tobj_mtlx_doc *doc, size_t *out_len);

#ifdef __cplusplus
}
#endif
#endif /* TOBJ_MTLX_H_ */
