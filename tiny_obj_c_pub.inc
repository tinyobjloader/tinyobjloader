/*
 * tiny_obj_c_pub.inc -- per-precision public types and prototypes.
 *
 * Included twice from tiny_obj_c.h with (TOBJ_REAL, TOBJ_SUF) set to
 * (float, _f) and (double, _d). Do not include directly.
 *
 * TOBJ_T(x) pastes the active suffix; e.g. TOBJ_T(tobj_scene) -> tobj_scene_f.
 */

typedef struct TOBJ_T(tobj_real_buf) {
  TOBJ_REAL *ptr;
  size_t count;
} TOBJ_T(tobj_real_buf);

typedef struct TOBJ_T(tobj_texture_option) {
  tobj_texture_type type;
  TOBJ_REAL sharpness;          /* -boost */
  TOBJ_REAL brightness;         /* -mm base */
  TOBJ_REAL contrast;           /* -mm gain */
  TOBJ_REAL origin_offset[3];   /* -o */
  TOBJ_REAL scale[3];           /* -s */
  TOBJ_REAL turbulence[3];      /* -t */
  int texture_resolution;       /* -texres (-1 = unset) */
  bool clamp;                   /* -clamp */
  bool blendu;                  /* -blendu (default on) */
  bool blendv;                  /* -blendv (default on) */
  char imfchan;                 /* -imfchan */
  TOBJ_REAL bump_multiplier;    /* -bm */
  const char *colorspace;       /* extension; interned, never NULL ("" if unset) */
} TOBJ_T(tobj_texture_option);

typedef struct TOBJ_T(tobj_material) {
  const char *name;

  TOBJ_REAL ambient[3];
  TOBJ_REAL diffuse[3];
  TOBJ_REAL specular[3];
  TOBJ_REAL transmittance[3];
  TOBJ_REAL emission[3];
  TOBJ_REAL shininess;
  TOBJ_REAL ior;
  TOBJ_REAL dissolve;           /* 1 = opaque */
  int illum;

  /* PBR extension. */
  TOBJ_REAL roughness;
  TOBJ_REAL metallic;
  TOBJ_REAL sheen;
  TOBJ_REAL clearcoat_thickness;
  TOBJ_REAL clearcoat_roughness;
  TOBJ_REAL anisotropy;
  TOBJ_REAL anisotropy_rotation;

  /* Classic texture maps. */
  const char *ambient_texname;
  const char *diffuse_texname;
  const char *specular_texname;
  const char *specular_highlight_texname;
  const char *bump_texname;
  const char *displacement_texname;
  const char *alpha_texname;
  const char *reflection_texname;
  /* PBR texture maps. */
  const char *roughness_texname;
  const char *metallic_texname;
  const char *sheen_texname;
  const char *emissive_texname;
  const char *normal_texname;

  TOBJ_T(tobj_texture_option) ambient_texopt;
  TOBJ_T(tobj_texture_option) diffuse_texopt;
  TOBJ_T(tobj_texture_option) specular_texopt;
  TOBJ_T(tobj_texture_option) specular_highlight_texopt;
  TOBJ_T(tobj_texture_option) bump_texopt;
  TOBJ_T(tobj_texture_option) displacement_texopt;
  TOBJ_T(tobj_texture_option) alpha_texopt;
  TOBJ_T(tobj_texture_option) reflection_texopt;
  TOBJ_T(tobj_texture_option) roughness_texopt;
  TOBJ_T(tobj_texture_option) metallic_texopt;
  TOBJ_T(tobj_texture_option) sheen_texopt;
  TOBJ_T(tobj_texture_option) emissive_texopt;
  TOBJ_T(tobj_texture_option) normal_texopt;

  /* Unknown parameters: sorted-by-key array, binary searchable. */
  tobj_kv *unknown_params;
  size_t num_unknown_params;
} TOBJ_T(tobj_material);

typedef struct TOBJ_T(tobj_joint_weight) {
  int joint_id;
  TOBJ_REAL weight;
} TOBJ_T(tobj_joint_weight);

typedef struct TOBJ_T(tobj_skin_weight) {
  int vertex_id;
  TOBJ_T(tobj_joint_weight) * weights;
  size_t num_weights;
} TOBJ_T(tobj_skin_weight);

typedef struct TOBJ_T(tobj_tag) {
  const char *name;
  int *int_values;
  size_t num_int_values;
  TOBJ_REAL *float_values;
  size_t num_float_values;
  const char **string_values;
  size_t num_string_values;
} TOBJ_T(tobj_tag);

typedef struct TOBJ_T(tobj_attrib) {
  TOBJ_T(tobj_real_buf) vertices;        /* xyz */
  TOBJ_T(tobj_real_buf) vertex_weights;  /* w (empty if none) */
  TOBJ_T(tobj_real_buf) normals;         /* xyz */
  TOBJ_T(tobj_real_buf) texcoords;       /* uv */
  TOBJ_T(tobj_real_buf) texcoord_ws;     /* w (empty if none) */
  TOBJ_T(tobj_real_buf) colors;          /* rgb (empty unless present/forced) */
  TOBJ_T(tobj_skin_weight) * skin_weights;
  size_t num_skin_weights;
} TOBJ_T(tobj_attrib);

typedef struct TOBJ_T(tobj_mesh) {
  tobj_index *indices;
  size_t num_indices;
  unsigned int *num_face_vertices;   /* per face; len == num_faces */
  int *material_ids;                 /* per face */
  unsigned int *smoothing_group_ids; /* per face; 0 = off */
  size_t num_faces;
  TOBJ_T(tobj_tag) * tags;
  size_t num_tags;
} TOBJ_T(tobj_mesh);

typedef struct TOBJ_T(tobj_lines) {
  tobj_index *indices;
  size_t num_indices;
  int *num_line_vertices; /* per polyline */
  size_t num_lines;
} TOBJ_T(tobj_lines);

typedef struct TOBJ_T(tobj_points) {
  tobj_index *indices;
  size_t num_indices;
} TOBJ_T(tobj_points);

/* ---- free-form geometry (parse & retain; no NURBS evaluation) ---------- */

typedef struct TOBJ_T(tobj_param_verts) { /* vp */
  TOBJ_T(tobj_real_buf) uvw; /* packed u[v[w]] */
  int components;            /* 1..3 */
} TOBJ_T(tobj_param_verts);

typedef struct TOBJ_T(tobj_curve) { /* curv */
  tobj_cstype type;
  bool rational;
  int degree;
  TOBJ_REAL u0, u1;
  int *control_points; /* resolved v indices */
  size_t num_control_points;
  TOBJ_REAL *knots; /* from parm u */
  size_t num_knots;
} TOBJ_T(tobj_curve);

typedef struct TOBJ_T(tobj_curve2) { /* curv2 (parameter space) */
  tobj_cstype type;
  bool rational;
  int degree;
  int *control_points; /* resolved vp indices */
  size_t num_control_points;
  TOBJ_REAL *knots;
  size_t num_knots;
} TOBJ_T(tobj_curve2);

typedef struct TOBJ_T(tobj_trim_loop) { /* trim/hole/scrv entry */
  TOBJ_REAL u0, u1;
  int curve2_index;
} TOBJ_T(tobj_trim_loop);

typedef struct TOBJ_T(tobj_surface) { /* surf */
  tobj_cstype type;
  bool rational;
  int degu, degv;
  TOBJ_REAL s0, s1, t0, t1;
  tobj_index *control_points; /* v/vt/vn refs */
  size_t num_control_points;
  TOBJ_REAL *knots_u;
  size_t num_knots_u;
  TOBJ_REAL *knots_v;
  size_t num_knots_v;
  TOBJ_T(tobj_trim_loop) * trims;
  size_t num_trims;
  TOBJ_T(tobj_trim_loop) * holes;
  size_t num_holes;
  TOBJ_T(tobj_trim_loop) * scrvs;
  size_t num_scrvs;
} TOBJ_T(tobj_surface);

typedef struct TOBJ_T(tobj_freeform) {
  TOBJ_T(tobj_param_verts) vp;
  TOBJ_T(tobj_curve) * curves;
  size_t num_curves;
  TOBJ_T(tobj_curve2) * curves2;
  size_t num_curves2;
  TOBJ_T(tobj_surface) * surfaces;
  size_t num_surfaces;
} TOBJ_T(tobj_freeform);

typedef struct TOBJ_T(tobj_shape) {
  const char *name;
  TOBJ_T(tobj_mesh) mesh;
  TOBJ_T(tobj_lines) lines;
  TOBJ_T(tobj_points) points;
  TOBJ_T(tobj_freeform) * freeform; /* NULL unless parse_freeform and present */
} TOBJ_T(tobj_shape);

typedef struct TOBJ_T(tobj_scene) {
  TOBJ_T(tobj_attrib) attrib;
  TOBJ_T(tobj_shape) * shapes;
  size_t num_shapes;
  TOBJ_T(tobj_material) * materials;
  size_t num_materials;
  /* bookkeeping for one-shot teardown (opaque to callers) */
  tobj_allocator allocator;
  void *arena;
  void *strpool;
} TOBJ_T(tobj_scene);

typedef struct TOBJ_T(tobj_material_list) {
  TOBJ_T(tobj_material) * items;
  size_t count;
  tobj_allocator allocator;
  void *strpool;
} TOBJ_T(tobj_material_list);

typedef struct TOBJ_T(tobj_callbacks) {
  void (*vertex_cb)(void *ud, TOBJ_REAL x, TOBJ_REAL y, TOBJ_REAL z,
                    TOBJ_REAL w);
  void (*vertex_color_cb)(void *ud, TOBJ_REAL x, TOBJ_REAL y, TOBJ_REAL z,
                          TOBJ_REAL r, TOBJ_REAL g, TOBJ_REAL b, bool has_color);
  void (*normal_cb)(void *ud, TOBJ_REAL x, TOBJ_REAL y, TOBJ_REAL z);
  void (*texcoord_cb)(void *ud, TOBJ_REAL x, TOBJ_REAL y, TOBJ_REAL z);
  void (*index_cb)(void *ud, const tobj_index *indices, int num_indices);
  void (*usemtl_cb)(void *ud, const char *name, int material_id);
  void (*mtllib_cb)(void *ud, const TOBJ_T(tobj_material) * materials, int num);
  void (*group_cb)(void *ud, const char *const *names, int num_names);
  void (*object_cb)(void *ud, const char *name);
  void (*line_cb)(void *ud, const tobj_index *indices, int num_indices);
  void (*point_cb)(void *ud, const tobj_index *indices, int num_indices);
  void *user_data;
} TOBJ_T(tobj_callbacks);

/* ---- entry points ------------------------------------------------------ */

TOBJ_API tobj_result TOBJ_T(tobj_load_obj_from_memory)(
    TOBJ_T(tobj_scene) * out, const uint8_t *buf, size_t len,
    const tobj_load_config *cfg, tobj_diag *diag);

TOBJ_API tobj_result TOBJ_T(tobj_load_obj_from_io)(
    TOBJ_T(tobj_scene) * out, const tobj_io_callbacks *io,
    const tobj_load_config *cfg, tobj_diag *diag);

#ifdef TOBJ_ENABLE_FILE_IO
TOBJ_API tobj_result TOBJ_T(tobj_load_obj_from_file)(
    TOBJ_T(tobj_scene) * out, const char *path, const tobj_load_config *cfg,
    tobj_diag *diag);
#endif

TOBJ_API tobj_result TOBJ_T(tobj_load_obj_with_callbacks)(
    const uint8_t *buf, size_t len, const TOBJ_T(tobj_callbacks) * cb,
    const tobj_load_config *cfg, tobj_diag *diag);

TOBJ_API void TOBJ_T(tobj_scene_free)(TOBJ_T(tobj_scene) * scene);

TOBJ_API tobj_result TOBJ_T(tobj_parse_mtl_from_memory)(
    TOBJ_T(tobj_material_list) * out, const uint8_t *buf, size_t len,
    const tobj_load_config *cfg, tobj_diag *diag);

TOBJ_API void TOBJ_T(tobj_material_list_free)(TOBJ_T(tobj_material_list) * list);

TOBJ_API const char *TOBJ_T(tobj_material_get_param)(
    const TOBJ_T(tobj_material) * m, const char *key);
