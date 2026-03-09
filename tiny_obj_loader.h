/*
The MIT License (MIT)

Copyright (c) 2012-Present, Syoyo Fujita and many contributors.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

//
// version 2.0.0 : Add new object oriented API. 1.x API is still provided.
//                 * Add python binding.
//                 * Support line primitive.
//                 * Support points primitive.
//                 * Support multiple search path for .mtl(v1 API).
//                 * Support vertex skinning weight `vw`(as an tinyobj
//                 extension). Note that this differs vertex weight([w]
//                 component in `v` line)
//                 * Support escaped whitespece in mtllib
//                 * Add robust triangulation using Mapbox
//                 earcut(TINYOBJLOADER_USE_MAPBOX_EARCUT).
// version 1.4.0 : Modifed ParseTextureNameAndOption API
// version 1.3.1 : Make ParseTextureNameAndOption API public
// version 1.3.0 : Separate warning and error message(breaking API of LoadObj)
// version 1.2.3 : Added color space extension('-colorspace') to tex opts.
// version 1.2.2 : Parse multiple group names.
// version 1.2.1 : Added initial support for line('l') primitive(PR #178)
// version 1.2.0 : Hardened implementation(#175)
// version 1.1.1 : Support smoothing groups(#162)
// version 1.1.0 : Support parsing vertex color(#144)
// version 1.0.8 : Fix parsing `g` tag just after `usemtl`(#138)
// version 1.0.7 : Support multiple tex options(#126)
// version 1.0.6 : Add TINYOBJLOADER_USE_DOUBLE option(#124)
// version 1.0.5 : Ignore `Tr` when `d` exists in MTL(#43)
// version 1.0.4 : Support multiple filenames for 'mtllib'(#112)
// version 1.0.3 : Support parsing texture options(#85)
// version 1.0.2 : Improve parsing speed by about a factor of 2 for large
// files(#105)
// version 1.0.1 : Fixes a shape is lost if obj ends with a 'usemtl'(#104)
// version 1.0.0 : Change data structure. Change license from BSD to MIT.
//

//
// Use this in *one* .cc
//   #define TINYOBJLOADER_IMPLEMENTATION
//   #include "tiny_obj_loader.h"
//

#ifndef TINY_OBJ_LOADER_H_
#define TINY_OBJ_LOADER_H_

#include <map>
#include <string>
#include <vector>

#if __cplusplus >= 201103L || (defined(_MSC_VER) && _MSC_VER >= 1900)
#include <cstdint>
#include <memory>
#include <type_traits>
#endif

namespace tinyobj {

// TODO(syoyo): Better C++11 detection for older compiler
#if __cplusplus > 199711L
#define TINYOBJ_OVERRIDE override
#else
#define TINYOBJ_OVERRIDE
#endif

#ifdef __clang__
#pragma clang diagnostic push
#if __has_warning("-Wzero-as-null-pointer-constant")
#pragma clang diagnostic ignored "-Wzero-as-null-pointer-constant"
#endif

#pragma clang diagnostic ignored "-Wpadded"

#endif

// https://en.wikipedia.org/wiki/Wavefront_.obj_file says ...
//
//  -blendu on | off                       # set horizontal texture blending
//  (default on)
//  -blendv on | off                       # set vertical texture blending
//  (default on)
//  -boost real_value                      # boost mip-map sharpness
//  -mm base_value gain_value              # modify texture map values (default
//  0 1)
//                                         #     base_value = brightness,
//                                         gain_value = contrast
//  -o u [v [w]]                           # Origin offset             (default
//  0 0 0)
//  -s u [v [w]]                           # Scale                     (default
//  1 1 1)
//  -t u [v [w]]                           # Turbulence                (default
//  0 0 0)
//  -texres resolution                     # texture resolution to create
//  -clamp on | off                        # only render texels in the clamped
//  0-1 range (default off)
//                                         #   When unclamped, textures are
//                                         repeated across a surface,
//                                         #   when clamped, only texels which
//                                         fall within the 0-1
//                                         #   range are rendered.
//  -bm mult_value                         # bump multiplier (for bump maps
//  only)
//
//  -imfchan r | g | b | m | l | z         # specifies which channel of the file
//  is used to
//                                         # create a scalar or bump texture.
//                                         r:red, g:green,
//                                         # b:blue, m:matte, l:luminance,
//                                         z:z-depth..
//                                         # (the default for bump is 'l' and
//                                         for decal is 'm')
//  bump -imfchan r bumpmap.tga            # says to use the red channel of
//  bumpmap.tga as the bumpmap
//
// For reflection maps...
//
//   -type sphere                           # specifies a sphere for a "refl"
//   reflection map
//   -type cube_top    | cube_bottom |      # when using a cube map, the texture
//   file for each
//         cube_front  | cube_back   |      # side of the cube is specified
//         separately
//         cube_left   | cube_right
//
// TinyObjLoader extension.
//
//   -colorspace SPACE                      # Color space of the texture. e.g.
//   'sRGB` or 'linear'
//

#ifdef TINYOBJLOADER_USE_DOUBLE
//#pragma message "using double"
typedef double real_t;
#else
//#pragma message "using float"
typedef float real_t;
#endif

typedef enum {
  TEXTURE_TYPE_NONE,  // default
  TEXTURE_TYPE_SPHERE,
  TEXTURE_TYPE_CUBE_TOP,
  TEXTURE_TYPE_CUBE_BOTTOM,
  TEXTURE_TYPE_CUBE_FRONT,
  TEXTURE_TYPE_CUBE_BACK,
  TEXTURE_TYPE_CUBE_LEFT,
  TEXTURE_TYPE_CUBE_RIGHT
} texture_type_t;

struct texture_option_t {
  texture_type_t type;      // -type (default TEXTURE_TYPE_NONE)
  real_t sharpness;         // -boost (default 1.0?)
  real_t brightness;        // base_value in -mm option (default 0)
  real_t contrast;          // gain_value in -mm option (default 1)
  real_t origin_offset[3];  // -o u [v [w]] (default 0 0 0)
  real_t scale[3];          // -s u [v [w]] (default 1 1 1)
  real_t turbulence[3];     // -t u [v [w]] (default 0 0 0)
  int texture_resolution;   // -texres resolution (No default value in the spec.
                            // We'll use -1)
  bool clamp;               // -clamp (default false)
  char imfchan;  // -imfchan (the default for bump is 'l' and for decal is 'm')
  bool blendu;   // -blendu (default on)
  bool blendv;   // -blendv (default on)
  real_t bump_multiplier;  // -bm (for bump maps only, default 1.0)

  // extension
  std::string colorspace;  // Explicitly specify color space of stored texel
                           // value. Usually `sRGB` or `linear` (default empty).
};

struct material_t {
  std::string name;

  real_t ambient[3];
  real_t diffuse[3];
  real_t specular[3];
  real_t transmittance[3];
  real_t emission[3];
  real_t shininess;
  real_t ior;       // index of refraction
  real_t dissolve;  // 1 == opaque; 0 == fully transparent
  // illumination model (see http://www.fileformat.info/format/material/)
  int illum;

  int dummy;  // Suppress padding warning.

  std::string ambient_texname;   // map_Ka. For ambient or ambient occlusion.
  std::string diffuse_texname;   // map_Kd
  std::string specular_texname;  // map_Ks
  std::string specular_highlight_texname;  // map_Ns
  std::string bump_texname;                // map_bump, map_Bump, bump
  std::string displacement_texname;        // disp
  std::string alpha_texname;               // map_d
  std::string reflection_texname;          // refl

  texture_option_t ambient_texopt;
  texture_option_t diffuse_texopt;
  texture_option_t specular_texopt;
  texture_option_t specular_highlight_texopt;
  texture_option_t bump_texopt;
  texture_option_t displacement_texopt;
  texture_option_t alpha_texopt;
  texture_option_t reflection_texopt;

  // PBR extension
  // http://exocortex.com/blog/extending_wavefront_mtl_to_support_pbr
  real_t roughness;            // [0, 1] default 0
  real_t metallic;             // [0, 1] default 0
  real_t sheen;                // [0, 1] default 0
  real_t clearcoat_thickness;  // [0, 1] default 0
  real_t clearcoat_roughness;  // [0, 1] default 0
  real_t anisotropy;           // aniso. [0, 1] default 0
  real_t anisotropy_rotation;  // anisor. [0, 1] default 0
  real_t pad0;
  std::string roughness_texname;  // map_Pr
  std::string metallic_texname;   // map_Pm
  std::string sheen_texname;      // map_Ps
  std::string emissive_texname;   // map_Ke
  std::string normal_texname;     // norm. For normal mapping.

  texture_option_t roughness_texopt;
  texture_option_t metallic_texopt;
  texture_option_t sheen_texopt;
  texture_option_t emissive_texopt;
  texture_option_t normal_texopt;

  int pad2;

  std::map<std::string, std::string> unknown_parameter;

#ifdef TINY_OBJ_LOADER_PYTHON_BINDING
  // For pybind11
  std::array<double, 3> GetDiffuse() {
    std::array<double, 3> values;
    values[0] = double(diffuse[0]);
    values[1] = double(diffuse[1]);
    values[2] = double(diffuse[2]);

    return values;
  }

  std::array<double, 3> GetSpecular() {
    std::array<double, 3> values;
    values[0] = double(specular[0]);
    values[1] = double(specular[1]);
    values[2] = double(specular[2]);

    return values;
  }

  std::array<double, 3> GetTransmittance() {
    std::array<double, 3> values;
    values[0] = double(transmittance[0]);
    values[1] = double(transmittance[1]);
    values[2] = double(transmittance[2]);

    return values;
  }

  std::array<double, 3> GetEmission() {
    std::array<double, 3> values;
    values[0] = double(emission[0]);
    values[1] = double(emission[1]);
    values[2] = double(emission[2]);

    return values;
  }

  std::array<double, 3> GetAmbient() {
    std::array<double, 3> values;
    values[0] = double(ambient[0]);
    values[1] = double(ambient[1]);
    values[2] = double(ambient[2]);

    return values;
  }

  void SetDiffuse(std::array<double, 3> &a) {
    diffuse[0] = real_t(a[0]);
    diffuse[1] = real_t(a[1]);
    diffuse[2] = real_t(a[2]);
  }

  void SetAmbient(std::array<double, 3> &a) {
    ambient[0] = real_t(a[0]);
    ambient[1] = real_t(a[1]);
    ambient[2] = real_t(a[2]);
  }

  void SetSpecular(std::array<double, 3> &a) {
    specular[0] = real_t(a[0]);
    specular[1] = real_t(a[1]);
    specular[2] = real_t(a[2]);
  }

  void SetTransmittance(std::array<double, 3> &a) {
    transmittance[0] = real_t(a[0]);
    transmittance[1] = real_t(a[1]);
    transmittance[2] = real_t(a[2]);
  }

  std::string GetCustomParameter(const std::string &key) {
    std::map<std::string, std::string>::const_iterator it =
        unknown_parameter.find(key);

    if (it != unknown_parameter.end()) {
      return it->second;
    }
    return std::string();
  }

#endif
};

struct tag_t {
  std::string name;

  std::vector<int> intValues;
  std::vector<real_t> floatValues;
  std::vector<std::string> stringValues;
};

struct joint_and_weight_t {
  int joint_id;
  real_t weight;
};

struct skin_weight_t {
  int vertex_id;  // Corresponding vertex index in `attrib_t::vertices`.
                  // Compared to `index_t`, this index must be positive and
                  // start with 0(does not allow relative indexing)
  std::vector<joint_and_weight_t> weightValues;
};

// Index struct to support different indices for vtx/normal/texcoord.
// -1 means not used.
struct index_t {
  int vertex_index;
  int normal_index;
  int texcoord_index;
};

struct mesh_t {
  std::vector<index_t> indices;
  std::vector<unsigned int>
      num_face_vertices;          // The number of vertices per
                                  // face. 3 = triangle, 4 = quad, ...
  std::vector<int> material_ids;  // per-face material ID
  std::vector<unsigned int> smoothing_group_ids;  // per-face smoothing group
                                                  // ID(0 = off. positive value
                                                  // = group id)
  std::vector<tag_t> tags;                        // SubD tag
};

// struct path_t {
//  std::vector<int> indices;  // pairs of indices for lines
//};

struct lines_t {
  // Linear flattened indices.
  std::vector<index_t> indices;        // indices for vertices(poly lines)
  std::vector<int> num_line_vertices;  // The number of vertices per line.
};

struct points_t {
  std::vector<index_t> indices;  // indices for points
};

struct shape_t {
  std::string name;
  mesh_t mesh;
  lines_t lines;
  points_t points;
};

// Vertex attributes
struct attrib_t {
  std::vector<real_t> vertices;  // 'v'(xyz)

  // For backward compatibility, we store vertex weight in separate array.
  std::vector<real_t> vertex_weights;  // 'v'(w)
  std::vector<real_t> normals;         // 'vn'
  std::vector<real_t> texcoords;       // 'vt'(uv)

  // For backward compatibility, we store texture coordinate 'w' in separate
  // array.
  std::vector<real_t> texcoord_ws;  // 'vt'(w)
  std::vector<real_t> colors;       // extension: vertex colors

  //
  // TinyObj extension.
  //

  // NOTE(syoyo): array index is based on the appearance order.
  // To get a corresponding skin weight for a specific vertex id `vid`,
  // Need to reconstruct a look up table: `skin_weight_t::vertex_id` == `vid`
  // (e.g. using std::map, std::unordered_map)
  std::vector<skin_weight_t> skin_weights;

  attrib_t() {}

  //
  // For pybind11
  //
  const std::vector<real_t> &GetVertices() const { return vertices; }

  const std::vector<real_t> &GetVertexWeights() const { return vertex_weights; }
};

struct callback_t {
  // W is optional and set to 1 if there is no `w` item in `v` line
  void (*vertex_cb)(void *user_data, real_t x, real_t y, real_t z, real_t w);
  void (*vertex_color_cb)(void *user_data, real_t x, real_t y, real_t z,
                          real_t r, real_t g, real_t b, bool has_color);
  void (*normal_cb)(void *user_data, real_t x, real_t y, real_t z);

  // y and z are optional and set to 0 if there is no `y` and/or `z` item(s) in
  // `vt` line.
  void (*texcoord_cb)(void *user_data, real_t x, real_t y, real_t z);

  // called per 'f' line. num_indices is the number of face indices(e.g. 3 for
  // triangle, 4 for quad)
  // 0 will be passed for undefined index in index_t members.
  void (*index_cb)(void *user_data, index_t *indices, int num_indices);
  // `name` material name, `material_id` = the array index of material_t[]. -1
  // if
  // a material not found in .mtl
  void (*usemtl_cb)(void *user_data, const char *name, int material_id);
  // `materials` = parsed material data.
  void (*mtllib_cb)(void *user_data, const material_t *materials,
                    int num_materials);
  // There may be multiple group names
  void (*group_cb)(void *user_data, const char **names, int num_names);
  void (*object_cb)(void *user_data, const char *name);

  callback_t()
      : vertex_cb(NULL),
        vertex_color_cb(NULL),
        normal_cb(NULL),
        texcoord_cb(NULL),
        index_cb(NULL),
        usemtl_cb(NULL),
        mtllib_cb(NULL),
        group_cb(NULL),
        object_cb(NULL) {}
};

class MaterialReader {
 public:
  MaterialReader() {}
  virtual ~MaterialReader();

  virtual bool operator()(const std::string &matId,
                          std::vector<material_t> *materials,
                          std::map<std::string, int> *matMap, std::string *warn,
                          std::string *err) = 0;
};

///
/// Read .mtl from a file.
///
class MaterialFileReader : public MaterialReader {
 public:
  // Path could contain separator(';' in Windows, ':' in Posix)
  explicit MaterialFileReader(const std::string &mtl_basedir)
      : m_mtlBaseDir(mtl_basedir) {}
  virtual ~MaterialFileReader() TINYOBJ_OVERRIDE {}
  virtual bool operator()(const std::string &matId,
                          std::vector<material_t> *materials,
                          std::map<std::string, int> *matMap, std::string *warn,
                          std::string *err) TINYOBJ_OVERRIDE;

 private:
  std::string m_mtlBaseDir;
};

///
/// Read .mtl from a stream.
///
class MaterialStreamReader : public MaterialReader {
 public:
  explicit MaterialStreamReader(std::istream &inStream)
      : m_inStream(inStream) {}
  virtual ~MaterialStreamReader() TINYOBJ_OVERRIDE {}
  virtual bool operator()(const std::string &matId,
                          std::vector<material_t> *materials,
                          std::map<std::string, int> *matMap, std::string *warn,
                          std::string *err) TINYOBJ_OVERRIDE;

 private:
  std::istream &m_inStream;
};

// v2 API
struct ObjReaderConfig {
  bool triangulate;  // triangulate polygon?

  // Currently not used.
  // "simple" or empty: Create triangle fan
  // "earcut": Use the algorithm based on Ear clipping
  std::string triangulation_method;

  /// Parse vertex color.
  /// If vertex color is not present, its filled with default value.
  /// false = no vertex color
  /// This will increase memory of parsed .obj
  bool vertex_color;

  ///
  /// Search path to .mtl file.
  /// Default = "" = search from the same directory of .obj file.
  /// Valid only when loading .obj from a file.
  ///
  std::string mtl_search_path;

  ObjReaderConfig()
      : triangulate(true), triangulation_method("simple"), vertex_color(true) {}
};

///
/// Wavefront .obj reader class(v2 API)
///
class ObjReader {
 public:
  ObjReader() : valid_(false) {}

  ///
  /// Load .obj and .mtl from a file.
  ///
  /// @param[in] filename wavefront .obj filename
  /// @param[in] config Reader configuration
  ///
  bool ParseFromFile(const std::string &filename,
                     const ObjReaderConfig &config = ObjReaderConfig());

  ///
  /// Parse .obj from a text string.
  /// Need to supply .mtl text string by `mtl_text`.
  /// This function ignores `mtllib` line in .obj text.
  ///
  /// @param[in] obj_text wavefront .obj filename
  /// @param[in] mtl_text wavefront .mtl filename
  /// @param[in] config Reader configuration
  ///
  bool ParseFromString(const std::string &obj_text, const std::string &mtl_text,
                       const ObjReaderConfig &config = ObjReaderConfig());

  ///
  /// .obj was loaded or parsed correctly.
  ///
  bool Valid() const { return valid_; }

  const attrib_t &GetAttrib() const { return attrib_; }

  const std::vector<shape_t> &GetShapes() const { return shapes_; }

  const std::vector<material_t> &GetMaterials() const { return materials_; }

  ///
  /// Warning message(may be filled after `Load` or `Parse`)
  ///
  const std::string &Warning() const { return warning_; }

  ///
  /// Error message(filled when `Load` or `Parse` failed)
  ///
  const std::string &Error() const { return error_; }

 private:
  bool valid_;

  attrib_t attrib_;
  std::vector<shape_t> shapes_;
  std::vector<material_t> materials_;

  std::string warning_;
  std::string error_;
};

/// ==>>========= Legacy v1 API =============================================

/// Loads .obj from a file.
/// 'attrib', 'shapes' and 'materials' will be filled with parsed shape data
/// 'shapes' will be filled with parsed shape data
/// Returns true when loading .obj become success.
/// Returns warning message into `warn`, and error message into `err`
/// 'mtl_basedir' is optional, and used for base directory for .mtl file.
/// In default(`NULL'), .mtl file is searched from an application's working
/// directory.
/// 'triangulate' is optional, and used whether triangulate polygon face in .obj
/// or not.
/// Option 'default_vcols_fallback' specifies whether vertex colors should
/// always be defined, even if no colors are given (fallback to white).
bool LoadObj(attrib_t *attrib, std::vector<shape_t> *shapes,
             std::vector<material_t> *materials, std::string *warn,
             std::string *err, const char *filename,
             const char *mtl_basedir = NULL, bool triangulate = true,
             bool default_vcols_fallback = true);

/// Loads .obj from a file with custom user callback.
/// .mtl is loaded as usual and parsed material_t data will be passed to
/// `callback.mtllib_cb`.
/// Returns true when loading .obj/.mtl become success.
/// Returns warning message into `warn`, and error message into `err`
/// See `examples/callback_api/` for how to use this function.
bool LoadObjWithCallback(std::istream &inStream, const callback_t &callback,
                         void *user_data = NULL,
                         MaterialReader *readMatFn = NULL,
                         std::string *warn = NULL, std::string *err = NULL);

/// Loads object from a std::istream, uses `readMatFn` to retrieve
/// std::istream for materials.
/// Returns true when loading .obj become success.
/// Returns warning and error message into `err`
bool LoadObj(attrib_t *attrib, std::vector<shape_t> *shapes,
             std::vector<material_t> *materials, std::string *warn,
             std::string *err, std::istream *inStream,
             MaterialReader *readMatFn = NULL, bool triangulate = true,
             bool default_vcols_fallback = true);

/// Loads materials into std::map
void LoadMtl(std::map<std::string, int> *material_map,
             std::vector<material_t> *materials, std::istream *inStream,
             std::string *warning, std::string *err);

///
/// Parse texture name and texture option for custom texture parameter through
/// material::unknown_parameter
///
/// @param[out] texname Parsed texture name
/// @param[out] texopt Parsed texopt
/// @param[in] linebuf Input string
///
bool ParseTextureNameAndOption(std::string *texname, texture_option_t *texopt,
                               const char *linebuf);

/// =<<========== Legacy v1 API =============================================

/// ==>>========= Optimized API (C++11 required) ============================
///
/// Enable compile options:
///   TINYOBJLOADER_USE_MULTITHREADING - multi-threaded parsing
///   TINYOBJLOADER_USE_SIMD           - SIMD-accelerated line scanning
///
/// These features require C++11 or later.
///

#if __cplusplus >= 201103L || (defined(_MSC_VER) && _MSC_VER >= 1900)

///
/// Arena-based memory allocator for reduced allocation overhead when
/// loading huge meshes.  Memory is freed in bulk when the arena is
/// destroyed or reset().  Individual deallocate() calls are no-ops.
///
class ArenaAllocator {
 public:
  explicit ArenaAllocator(size_t block_size = 1024 * 1024)
      : head_(nullptr), default_block_size_(block_size) {}

  ~ArenaAllocator() { destroy(); }

  ArenaAllocator(const ArenaAllocator &) = delete;
  ArenaAllocator &operator=(const ArenaAllocator &) = delete;

  void *allocate(size_t bytes,
                 size_t alignment = sizeof(void *));

  /// Free all memory at once.
  void reset();

 private:
  struct Block {
    unsigned char *data;
    size_t capacity;
    size_t used;
    Block *next;
  };

  Block *head_;
  size_t default_block_size_;

  Block *new_block(size_t min_bytes);
  void destroy();
};

///
/// STL-compatible allocator adapter backed by an ArenaAllocator.
/// deallocate() is a no-op — memory is released when the arena is reset.
///
template <typename T>
class arena_adapter {
 public:
  using value_type = T;
  using pointer = T *;
  using const_pointer = const T *;
  using size_type = std::size_t;
  using difference_type = std::ptrdiff_t;
  using propagate_on_container_copy_assignment = std::true_type;
  using propagate_on_container_move_assignment = std::true_type;
  using propagate_on_container_swap = std::true_type;

  explicit arena_adapter(ArenaAllocator *arena = nullptr) noexcept
      : arena_(arena) {}

  template <typename U>
  arena_adapter(const arena_adapter<U> &other) noexcept
      : arena_(other.arena()) {}

  T *allocate(size_t n) {
    if (arena_) {
      return static_cast<T *>(arena_->allocate(n * sizeof(T), alignof(T)));
    }
    return static_cast<T *>(::operator new(n * sizeof(T)));
  }

  void deallocate(T *p, size_t) noexcept {
    if (!arena_) {
      ::operator delete(p);
      return;
    }
    // Arena deallocation is a no-op; memory freed in bulk via reset().
  }

  ArenaAllocator *arena() const noexcept { return arena_; }

  template <typename U>
  bool operator==(const arena_adapter<U> &o) const noexcept {
    return arena_ == o.arena();
  }
  template <typename U>
  bool operator!=(const arena_adapter<U> &o) const noexcept {
    return arena_ != o.arena();
  }

  template <typename U>
  struct rebind {
    using other = arena_adapter<U>;
  };

 private:
  ArenaAllocator *arena_;
};

///
/// Template mesh type supporting custom allocators.
///
template <typename Alloc = std::allocator<char>>
struct basic_mesh_t {
  using index_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<index_t>;
  using uint_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<unsigned int>;
  using int_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<int>;

  std::vector<index_t, index_alloc> indices;
  std::vector<unsigned int, uint_alloc> num_face_vertices;
  std::vector<int, int_alloc> material_ids;
  std::vector<unsigned int, uint_alloc> smoothing_group_ids;
};

///
/// Template shape type supporting custom allocators.
///
template <typename Alloc = std::allocator<char>>
struct basic_shape_t {
  std::string name;
  basic_mesh_t<Alloc> mesh;
};

///
/// Template attrib type supporting custom allocators.
/// Flat arrays: vertices(xyz), normals(xyz), texcoords(uv).
///
template <typename Alloc = std::allocator<char>>
struct basic_attrib_t {
  using real_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<real_t>;
  using int_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<int>;
  using index_alloc =
      typename std::allocator_traits<Alloc>::template rebind_alloc<index_t>;

  std::vector<real_t, real_alloc> vertices;   // xyz
  std::vector<real_t, real_alloc> normals;    // xyz
  std::vector<real_t, real_alloc> texcoords;  // uv
  std::vector<real_t, real_alloc> colors;     // rgb (optional)
  std::vector<index_t, index_alloc> indices;  // face indices
  std::vector<int, int_alloc> face_num_verts; // verts per face
  std::vector<int, int_alloc> material_ids;   // per-face material
};

///
/// Configuration for the optimized loader.
///
struct OptLoadConfig {
  /// Number of threads.  -1 = hardware_concurrency, 0 or 1 = single-threaded.
  /// Effective only when TINYOBJLOADER_USE_MULTITHREADING is defined.
  int num_threads;

  bool triangulate;  ///< Triangulate polygons (fan triangulation).
  bool verbose;      ///< Print timing information to stdout.

  OptLoadConfig() : num_threads(-1), triangulate(true), verbose(false) {}
};

/// Optimized loader — parse from a raw memory buffer.
/// Supports multi-threading (TINYOBJLOADER_USE_MULTITHREADING) and
/// SIMD line scanning (TINYOBJLOADER_USE_SIMD).
bool LoadObjOpt(basic_attrib_t<> *attrib,
                std::vector<basic_shape_t<>> *shapes,
                std::vector<material_t> *materials,
                std::string *warn, std::string *err,
                const char *buf, size_t buf_len,
                const OptLoadConfig &config = OptLoadConfig());

/// Optimized loader — load from a file.
bool LoadObjOpt(basic_attrib_t<> *attrib,
                std::vector<basic_shape_t<>> *shapes,
                std::vector<material_t> *materials,
                std::string *warn, std::string *err,
                const char *filename,
                const char *mtl_basedir = nullptr,
                const OptLoadConfig &config = OptLoadConfig());

#endif  // C++11

/// =<<========== Optimized API =============================================

}  // namespace tinyobj

#endif  // TINY_OBJ_LOADER_H_

#ifdef TINYOBJLOADER_IMPLEMENTATION
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <limits>

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#endif

#ifdef TINYOBJLOADER_USE_MMAP
#if !defined(_WIN32)
// POSIX headers for mmap
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#endif
#endif  // TINYOBJLOADER_USE_MMAP
#include <set>
#include <sstream>
#include <utility>

#ifdef TINYOBJLOADER_USE_MAPBOX_EARCUT

#ifdef TINYOBJLOADER_DONOT_INCLUDE_MAPBOX_EARCUT
// Assume earcut.hpp is included outside of tiny_obj_loader.h
#else

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#endif

#include <array>

#include "mapbox/earcut.hpp"

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#endif

#endif  // TINYOBJLOADER_USE_MAPBOX_EARCUT

#ifdef _WIN32
// Converts a UTF-8 encoded string to a UTF-16 wide string for use with
// Windows file APIs that support Unicode paths (including paths longer than
// MAX_PATH when combined with the extended-length path prefix).
static std::wstring UTF8ToWchar(const std::string &str) {
  if (str.empty()) return std::wstring();
  int size_needed =
      MultiByteToWideChar(CP_UTF8, 0, str.c_str(),
                          static_cast<int>(str.size()), NULL, 0);
  if (size_needed == 0) return std::wstring();
  std::wstring wstr(static_cast<size_t>(size_needed), L'\0');
  int result =
      MultiByteToWideChar(CP_UTF8, 0, str.c_str(),
                          static_cast<int>(str.size()), &wstr[0], size_needed);
  if (result == 0) return std::wstring();
  return wstr;
}

// Prepends the Windows extended-length path prefix ("\\?\") to an absolute
// path when the path length meets or exceeds MAX_PATH (260 characters).
// This allows Windows APIs to handle paths up to 32767 characters long.
// UNC paths (starting with "\\") are converted to "\\?\UNC\" form.
static std::wstring LongPathW(const std::wstring &wpath) {
  const std::wstring kLongPathPrefix = L"\\\\?\\";
  const std::wstring kUNCPrefix = L"\\\\";
  const std::wstring kLongUNCPathPrefix = L"\\\\?\\UNC\\";

  // Already has the extended-length prefix; return as-is.
  if (wpath.size() >= kLongPathPrefix.size() &&
      wpath.substr(0, kLongPathPrefix.size()) == kLongPathPrefix) {
    return wpath;
  }

  // Only add the prefix when the path is long enough to require it.
  if (wpath.size() < MAX_PATH) {
    return wpath;
  }

  // Normalize forward slashes to backslashes: the extended-length "\\?\"
  // prefix requires backslash separators only.
  std::wstring normalized = wpath;
  for (std::wstring::size_type i = 0; i < normalized.size(); ++i) {
    if (normalized[i] == L'/') normalized[i] = L'\\';
  }

  // UNC path: "\\server\share\..." -> "\\?\UNC\server\share\..."
  if (normalized.size() >= kUNCPrefix.size() &&
      normalized.substr(0, kUNCPrefix.size()) == kUNCPrefix) {
    return kLongUNCPathPrefix + normalized.substr(kUNCPrefix.size());
  }

  // Absolute path with drive letter: "C:\..." -> "\\?\C:\..."
  if (normalized.size() >= 2 && normalized[1] == L':') {
    return kLongPathPrefix + normalized;
  }

  return normalized;
}
#endif  // _WIN32

#if __cplusplus >= 201103L || (defined(_MSC_VER) && _MSC_VER >= 1900)
#ifdef TINYOBJLOADER_USE_MULTITHREADING
#include <atomic>
#include <thread>
#endif
#ifdef TINYOBJLOADER_USE_SIMD
#if defined(__SSE2__) || defined(_M_X64) || defined(_M_AMD64) || \
    (defined(_M_IX86_FP) && _M_IX86_FP >= 2)
#define TINYOBJLOADER_SIMD_SSE2 1
#include <emmintrin.h>
#if defined(__AVX2__)
#define TINYOBJLOADER_SIMD_AVX2 1
#include <immintrin.h>
#endif
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
#define TINYOBJLOADER_SIMD_NEON 1
#include <arm_neon.h>
#endif
#endif  // TINYOBJLOADER_USE_SIMD
#endif  // C++11

namespace tinyobj {

MaterialReader::~MaterialReader() {}

// Byte-stream reader for bounds-checked text parsing.
// Replaces raw `const char*` token pointers with `(buf, len, idx)` triple.
// Every byte access is guarded by an EOF check.
class StreamReader {
 public:
// Maximum number of bytes StreamReader will buffer from std::istream.
// Define this macro to a larger value if your application needs to parse
// very large streamed OBJ/MTL content.
#ifndef TINYOBJLOADER_STREAM_READER_MAX_BYTES
#define TINYOBJLOADER_STREAM_READER_MAX_BYTES (size_t(256) * size_t(1024) * size_t(1024))
#endif

  StreamReader(const char *buf, size_t length)
      : buf_(buf), length_(length), idx_(0), line_num_(1), col_num_(1) {}

  // Build from std::istream by reading all content into an internal buffer.
  explicit StreamReader(std::istream &is) : buf_(NULL), length_(0), idx_(0), line_num_(1), col_num_(1) {
    const size_t max_stream_bytes = TINYOBJLOADER_STREAM_READER_MAX_BYTES;
    std::streampos start_pos = is.tellg();
    bool can_seek = (start_pos != std::streampos(-1));
    if (can_seek) {
      is.seekg(0, std::ios::end);
      std::streampos end_pos = is.tellg();
      if (end_pos >= start_pos) {
        std::streamoff remaining_off = static_cast<std::streamoff>(end_pos - start_pos);
        if (remaining_off < 0) {
          is.seekg(start_pos);
          push_error("failed to determine stream size\n");
          buf_ = "";
          length_ = 0;
          return;
        }
        is.seekg(start_pos);
        unsigned long long remaining_ull = static_cast<unsigned long long>(remaining_off);
        if (remaining_ull > static_cast<unsigned long long>((std::numeric_limits<size_t>::max)())) {
          std::stringstream ss;
          ss << "input stream too large for this platform (" << remaining_ull
             << " bytes exceeds size_t max " << (std::numeric_limits<size_t>::max)() << ")\n";
          push_error(ss.str());
          buf_ = "";
          length_ = 0;
          return;
        }
        size_t remaining_size = static_cast<size_t>(remaining_ull);
        if (remaining_size > max_stream_bytes) {
          std::stringstream ss;
          ss << "input stream too large (" << remaining_size
             << " bytes exceeds limit " << max_stream_bytes << " bytes)\n";
          push_error(ss.str());
          buf_ = "";
          length_ = 0;
          return;
        }
        owned_buf_.resize(remaining_size);
        if (remaining_size > 0) {
          is.read(&owned_buf_[0], static_cast<std::streamsize>(remaining_size));
        }
        size_t actually_read = static_cast<size_t>(is.gcount());
        owned_buf_.resize(actually_read);
      }
    }
    if (!can_seek || owned_buf_.empty()) {
      // Stream doesn't support seeking, or seek probing failed.
      if (can_seek) is.seekg(start_pos);
      is.clear();
      std::vector<char> content;
      char chunk[4096];
      size_t total_read = 0;
      while (is.good()) {
        is.read(chunk, static_cast<std::streamsize>(sizeof(chunk)));
        std::streamsize nread = is.gcount();
        if (nread <= 0) break;
        size_t n = static_cast<size_t>(nread);
        if (n > (max_stream_bytes - total_read)) {
          std::stringstream ss;
          ss << "input stream too large (exceeds limit " << max_stream_bytes
             << " bytes)\n";
          push_error(ss.str());
          owned_buf_.clear();
          buf_ = "";
          length_ = 0;
          return;
        }
        content.insert(content.end(), chunk, chunk + n);
        total_read += n;
      }
      owned_buf_.swap(content);
    }
    buf_ = owned_buf_.empty() ? "" : &owned_buf_[0];
    length_ = owned_buf_.size();
  }

  bool eof() const { return idx_ >= length_; }
  size_t tell() const { return idx_; }
  size_t size() const { return length_; }
  size_t line_num() const { return line_num_; }
  size_t col_num() const { return col_num_; }

  char peek() const {
    if (idx_ >= length_) return '\0';
    return buf_[idx_];
  }

  char get() {
    if (idx_ >= length_) return '\0';
    char c = buf_[idx_++];
    if (c == '\n') { line_num_++; col_num_ = 1; } else { col_num_++; }
    return c;
  }

  void advance(size_t n) {
    for (size_t i = 0; i < n && idx_ < length_; i++) {
      if (buf_[idx_] == '\n') { line_num_++; col_num_ = 1; } else { col_num_++; }
      idx_++;
    }
  }

  void skip_space() {
    while (idx_ < length_ && (buf_[idx_] == ' ' || buf_[idx_] == '\t')) {
      col_num_++;
      idx_++;
    }
  }

  void skip_space_and_cr() {
    while (idx_ < length_ && (buf_[idx_] == ' ' || buf_[idx_] == '\t' || buf_[idx_] == '\r')) {
      col_num_++;
      idx_++;
    }
  }

  void skip_line() {
    while (idx_ < length_) {
      char c = buf_[idx_];
      if (c == '\n') {
        idx_++;
        line_num_++;
        col_num_ = 1;
        return;
      }
      if (c == '\r') {
        idx_++;
        if (idx_ < length_ && buf_[idx_] == '\n') {
          idx_++;
        }
        line_num_++;
        col_num_ = 1;
        return;
      }
      col_num_++;
      idx_++;
    }
  }

  bool at_line_end() const {
    if (idx_ >= length_) return true;
    char c = buf_[idx_];
    return (c == '\n' || c == '\r' || c == '\0');
  }

  std::string read_line() {
    std::string result;
    while (idx_ < length_) {
      char c = buf_[idx_];
      if (c == '\n' || c == '\r') break;
      result += c;
      col_num_++;
      idx_++;
    }
    return result;
  }

  // Reads a whitespace-delimited token. Used by tests and as a general utility.
  std::string read_token() {
    skip_space();
    std::string result;
    while (idx_ < length_) {
      char c = buf_[idx_];
      if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
      result += c;
      col_num_++;
      idx_++;
    }
    return result;
  }

  bool match(const char *prefix, size_t len) const {
    if (len > length_ - idx_) return false;
    return (memcmp(buf_ + idx_, prefix, len) == 0);
  }

  bool char_at(size_t offset, char c) const {
    if (offset >= length_ - idx_) return false;
    return buf_[idx_ + offset] == c;
  }

  char peek_at(size_t offset) const {
    if (offset >= length_ - idx_) return '\0';
    return buf_[idx_ + offset];
  }

  const char *current_ptr() const {
    if (idx_ >= length_) return "";
    return buf_ + idx_;
  }

  size_t remaining() const {
    return (idx_ < length_) ? (length_ - idx_) : 0;
  }

  // Returns the full text of the current line (for diagnostic display).
  std::string current_line_text() const {
    // Scan backward to find line start
    size_t line_start = idx_;
    while (line_start > 0 && buf_[line_start - 1] != '\n' && buf_[line_start - 1] != '\r') {
      line_start--;
    }
    // Scan forward to find line end
    size_t line_end = idx_;
    while (line_end < length_ && buf_[line_end] != '\n' && buf_[line_end] != '\r') {
      line_end++;
    }
    return std::string(buf_ + line_start, line_end - line_start);
  }

  // Clang-style formatted error with file:line:col and caret.
  std::string format_error(const std::string &filename, const std::string &msg) const {
    std::stringstream line_ss, col_ss;
    line_ss << line_num_;
    col_ss << col_num_;
    std::string result;
    result += filename + ":" + line_ss.str() + ":" + col_ss.str() + ": error: " + msg + "\n";
    std::string line_text = current_line_text();
    result += line_text + "\n";
    // Build caret line preserving tab alignment
    std::string caret;
    size_t caret_pos = (col_num_ > 0) ? (col_num_ - 1) : 0;
    for (size_t i = 0; i < caret_pos && i < line_text.size(); i++) {
      caret += (line_text[i] == '\t') ? '\t' : ' ';
    }
    caret += "^";
    result += caret + "\n";
    return result;
  }

  std::string format_error(const std::string &msg) const {
    return format_error("<input>", msg);
  }

  // Error stack
  void push_error(const std::string &msg) {
    errors_.push_back(msg);
  }

  void push_formatted_error(const std::string &filename, const std::string &msg) {
    errors_.push_back(format_error(filename, msg));
  }

  bool has_errors() const { return !errors_.empty(); }

  std::string get_errors() const {
    std::string result;
    for (size_t i = 0; i < errors_.size(); i++) {
      result += errors_[i];
    }
    return result;
  }

  const std::vector<std::string> &error_stack() const { return errors_; }

  void clear_errors() { errors_.clear(); }

 private:
  const char *buf_;
  size_t length_;
  size_t idx_;
  size_t line_num_;
  size_t col_num_;
  std::vector<char> owned_buf_;
  std::vector<std::string> errors_;
};

#ifdef TINYOBJLOADER_USE_MMAP
// RAII wrapper for memory-mapped file I/O.
// Opens a file and maps it into memory; the mapping is released on destruction.
// For empty files, data is set to "" and is_mapped remains false so close()
// will not attempt to unmap a string literal.
struct MappedFile {
  const char *data;
  size_t size;
  bool is_mapped;  // true when data points to an actual mapped region
#if defined(_WIN32)
  HANDLE hFile;
  HANDLE hMapping;
#else
  void *mapped_ptr;
#endif

  MappedFile() : data(NULL), size(0), is_mapped(false)
#if defined(_WIN32)
    , hFile(INVALID_HANDLE_VALUE), hMapping(NULL)
#else
    , mapped_ptr(NULL)
#endif
  {}

  // Opens and maps the file. Returns true on success.
  bool open(const char *filepath) {
#if defined(_WIN32)
    std::wstring wfilepath = LongPathW(UTF8ToWchar(std::string(filepath)));
    hFile = CreateFileW(wfilepath.c_str(), GENERIC_READ, FILE_SHARE_READ, NULL,
                        OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (hFile == INVALID_HANDLE_VALUE) return false;
    LARGE_INTEGER fileSize;
    if (!GetFileSizeEx(hFile, &fileSize)) { close(); return false; }
    if (fileSize.QuadPart < 0) { close(); return false; }
    unsigned long long fsize = static_cast<unsigned long long>(fileSize.QuadPart);
    if (fsize > static_cast<unsigned long long>((std::numeric_limits<size_t>::max)())) {
      close();
      return false;
    }
    size = static_cast<size_t>(fsize);
    if (size == 0) { data = ""; return true; }  // valid but empty; is_mapped stays false
    hMapping = CreateFileMappingA(hFile, NULL, PAGE_READONLY, 0, 0, NULL);
    if (hMapping == NULL) { close(); return false; }
    data = static_cast<const char *>(MapViewOfFile(hMapping, FILE_MAP_READ, 0, 0, 0));
    if (!data) { close(); return false; }
    is_mapped = true;
    return true;
#else
    int fd = ::open(filepath, O_RDONLY);
    if (fd == -1) return false;
    struct stat sb;
    if (fstat(fd, &sb) != 0) { ::close(fd); return false; }
    if (sb.st_size < 0) { ::close(fd); return false; }
    if (static_cast<unsigned long long>(sb.st_size) >
        static_cast<unsigned long long>((std::numeric_limits<size_t>::max)())) {
      ::close(fd);
      return false;
    }
    size = static_cast<size_t>(sb.st_size);
    if (size == 0) { ::close(fd); data = ""; return true; }  // valid but empty
    mapped_ptr = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    ::close(fd);
    if (mapped_ptr == MAP_FAILED) { mapped_ptr = NULL; return false; }
    data = static_cast<const char *>(mapped_ptr);
    is_mapped = true;
    return true;
#endif
  }

  void close() {
#if defined(_WIN32)
    if (is_mapped && data) { UnmapViewOfFile(data); }
    data = NULL;
    is_mapped = false;
    if (hMapping != NULL) { CloseHandle(hMapping); hMapping = NULL; }
    if (hFile != INVALID_HANDLE_VALUE) { CloseHandle(hFile); hFile = INVALID_HANDLE_VALUE; }
#else
    if (is_mapped && mapped_ptr && mapped_ptr != MAP_FAILED) { munmap(mapped_ptr, size); }
    mapped_ptr = NULL;
    data = NULL;
    is_mapped = false;
#endif
    size = 0;
  }

  ~MappedFile() { close(); }

 private:
  MappedFile(const MappedFile &);             // non-copyable
  MappedFile &operator=(const MappedFile &);  // non-copyable
};
#endif  // TINYOBJLOADER_USE_MMAP


struct vertex_index_t {
  int v_idx, vt_idx, vn_idx;
  vertex_index_t() : v_idx(-1), vt_idx(-1), vn_idx(-1) {}
  explicit vertex_index_t(int idx) : v_idx(idx), vt_idx(idx), vn_idx(idx) {}
  vertex_index_t(int vidx, int vtidx, int vnidx)
      : v_idx(vidx), vt_idx(vtidx), vn_idx(vnidx) {}
};

// Internal data structure for face representation
// index + smoothing group.
struct face_t {
  unsigned int
      smoothing_group_id;  // smoothing group id. 0 = smoothing groupd is off.
  int pad_;
  std::vector<vertex_index_t> vertex_indices;  // face vertex indices.

  face_t() : smoothing_group_id(0), pad_(0) {}
};

// Internal data structure for line representation
struct __line_t {
  // l v1/vt1 v2/vt2 ...
  // In the specification, line primitrive does not have normal index, but
  // TinyObjLoader allow it
  std::vector<vertex_index_t> vertex_indices;
};

// Internal data structure for points representation
struct __points_t {
  // p v1 v2 ...
  // In the specification, point primitrive does not have normal index and
  // texture coord index, but TinyObjLoader allow it.
  std::vector<vertex_index_t> vertex_indices;
};

struct tag_sizes {
  tag_sizes() : num_ints(0), num_reals(0), num_strings(0) {}
  int num_ints;
  int num_reals;
  int num_strings;
};

struct obj_shape {
  std::vector<real_t> v;
  std::vector<real_t> vn;
  std::vector<real_t> vt;
};

//
// Manages group of primitives(face, line, points, ...)
struct PrimGroup {
  std::vector<face_t> faceGroup;
  std::vector<__line_t> lineGroup;
  std::vector<__points_t> pointsGroup;

  void clear() {
    faceGroup.clear();
    lineGroup.clear();
    pointsGroup.clear();
  }

  bool IsEmpty() const {
    return faceGroup.empty() && lineGroup.empty() && pointsGroup.empty();
  }

  // TODO(syoyo): bspline, surface, ...
};

// See
// http://stackoverflow.com/questions/6089231/getting-std-ifstream-to-handle-lf-cr-and-crlf
#define IS_SPACE(x) (((x) == ' ') || ((x) == '\t'))
#define IS_DIGIT(x) \
  (static_cast<unsigned int>((x) - '0') < static_cast<unsigned int>(10))
#define IS_NEW_LINE(x) (((x) == '\r') || ((x) == '\n') || ((x) == '\0'))

template <typename T>
static inline std::string toString(const T &t) {
  std::stringstream ss;
  ss << t;
  return ss.str();
}

static inline std::string removeUtf8Bom(const std::string& input) {
    // UTF-8 BOM = 0xEF,0xBB,0xBF
    if (input.size() >= 3 &&
        static_cast<unsigned char>(input[0]) == 0xEF &&
        static_cast<unsigned char>(input[1]) == 0xBB &&
        static_cast<unsigned char>(input[2]) == 0xBF) {
        return input.substr(3); // Skip BOM
    }
    return input;
}

// Trim trailing spaces and tabs from a string.
static inline std::string trimTrailingWhitespace(const std::string &s) {
  size_t end = s.find_last_not_of(" \t");
  if (end == std::string::npos) return "";
  return s.substr(0, end + 1);
}

struct warning_context {
  std::string *warn;
  size_t line_number;
  std::string filename;
};

// Make index zero-base, and also support relative index.
static inline bool fixIndex(int idx, int n, int *ret, bool allow_zero,
                            const warning_context &context) {
  if (!ret) {
    return false;
  }

  if (idx > 0) {
    (*ret) = idx - 1;
    return true;
  }

  if (idx == 0) {
    // zero is not allowed according to the spec.
    if (context.warn) {
      (*context.warn) +=
          context.filename + ":" + toString(context.line_number) +
          ": warning: zero value index found (will have a value of -1 for "
          "normal and tex indices)\n";
    }

    (*ret) = idx - 1;
    return allow_zero;
  }

  if (idx < 0) {
    (*ret) = n + idx;  // negative value = relative
    if ((*ret) < 0) {
      return false;  // invalid relative index
    }
    return true;
  }

  return false;  // never reach here.
}

static inline std::string parseString(const char **token) {
  std::string s;
  (*token) += strspn((*token), " \t");
  size_t e = strcspn((*token), " \t\r");
  s = std::string((*token), &(*token)[e]);
  (*token) += e;
  return s;
}

static inline int parseInt(const char **token) {
  (*token) += strspn((*token), " \t");
  int i = atoi((*token));
  (*token) += strcspn((*token), " \t\r");
  return i;
}

// Tries to parse a floating point number located at s.
//
// s_end should be a location in the string where reading should absolutely
// stop. For example at the end of the string, to prevent buffer overflows.
//
// Parses the following EBNF grammar:
//   sign    = "+" | "-" ;
//   END     = ? anything not in digit ?
//   digit   = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
//   integer = [sign] , digit , {digit} ;
//   decimal = integer , ["." , integer] ;
//   float   = ( decimal , END ) | ( decimal , ("E" | "e") , integer , END ) ;
//
//  Valid strings are for example:
//   -0  +3.1417e+2  -0.0E-3  1.0324  -1.41   11e2
//
// If the parsing is a success, result is set to the parsed value and true
// is returned.
//
// The function is greedy and will parse until any of the following happens:
//  - a non-conforming character is encountered.
//  - s_end is reached.
//
// The following situations triggers a failure:
//  - s >= s_end.
//  - parse failure.
//
static bool tryParseDouble(const char *s, const char *s_end, double *result) {
  if (s >= s_end) {
    return false;
  }

  double mantissa = 0.0;
  // This exponent is base 2 rather than 10.
  // However the exponent we parse is supposed to be one of ten,
  // thus we must take care to convert the exponent/and or the
  // mantissa to a * 2^E, where a is the mantissa and E is the
  // exponent.
  // To get the final double we will use ldexp, it requires the
  // exponent to be in base 2.
  int exponent = 0;

  // NOTE: THESE MUST BE DECLARED HERE SINCE WE ARE NOT ALLOWED
  // TO JUMP OVER DEFINITIONS.
  char sign = '+';
  char exp_sign = '+';
  char const *curr = s;

  // How many characters were read in a loop.
  int read = 0;
  // Tells whether a loop terminated due to reaching s_end.
  bool end_not_reached = false;
  bool leading_decimal_dots = false;

  /*
          BEGIN PARSING.
  */

  // Find out what sign we've got.
  if (*curr == '+' || *curr == '-') {
    sign = *curr;
    curr++;
    if ((curr != s_end) && (*curr == '.')) {
      // accept. Somethig like `.7e+2`, `-.5234`
      leading_decimal_dots = true;
    }
  } else if (IS_DIGIT(*curr)) { /* Pass through. */
  } else if (*curr == '.') {
    // accept. Somethig like `.7e+2`, `-.5234`
    leading_decimal_dots = true;
  } else {
    goto fail;
  }

  // Read the integer part.
  end_not_reached = (curr != s_end);
  if (!leading_decimal_dots) {
    while (end_not_reached && IS_DIGIT(*curr)) {
      mantissa *= 10;
      mantissa += static_cast<int>(*curr - 0x30);
      curr++;
      read++;
      end_not_reached = (curr != s_end);
    }

    // We must make sure we actually got something.
    if (read == 0) goto fail;
  }

  // We allow numbers of form "#", "###" etc.
  if (!end_not_reached) goto assemble;

  // Read the decimal part.
  if (*curr == '.') {
    curr++;
    read = 1;
    end_not_reached = (curr != s_end);
    while (end_not_reached && IS_DIGIT(*curr)) {
      static const double pow_lut[] = {
          1.0, 0.1, 0.01, 0.001, 0.0001, 0.00001, 0.000001, 0.0000001,
      };
      const int lut_entries = sizeof pow_lut / sizeof pow_lut[0];

      // NOTE: Don't use powf here, it will absolutely murder precision.
      mantissa += static_cast<int>(*curr - 0x30) *
                  (read < lut_entries ? pow_lut[read] : std::pow(10.0, -read));
      read++;
      curr++;
      end_not_reached = (curr != s_end);
    }
  } else if (*curr == 'e' || *curr == 'E') {
  } else {
    goto assemble;
  }

  if (!end_not_reached) goto assemble;

  // Read the exponent part.
  if (*curr == 'e' || *curr == 'E') {
    curr++;
    // Figure out if a sign is present and if it is.
    end_not_reached = (curr != s_end);
    if (end_not_reached && (*curr == '+' || *curr == '-')) {
      exp_sign = *curr;
      curr++;
    } else if (IS_DIGIT(*curr)) { /* Pass through. */
    } else {
      // Empty E is not allowed.
      goto fail;
    }

    read = 0;
    end_not_reached = (curr != s_end);
    while (end_not_reached && IS_DIGIT(*curr)) {
      // To avoid annoying MSVC's min/max macro definiton,
      // Use hardcoded int max value
      if (exponent >
          ((2147483647 - 9) / 10)) {  // (INT_MAX - 9) / 10, guards both multiply and add
        // Integer overflow
        goto fail;
      }
      exponent *= 10;
      exponent += static_cast<int>(*curr - 0x30);
      curr++;
      read++;
      end_not_reached = (curr != s_end);
    }
    exponent *= (exp_sign == '+' ? 1 : -1);
    if (read == 0) goto fail;
  }

assemble:
  *result = (sign == '+' ? 1 : -1) *
            (exponent ? std::ldexp(mantissa * std::pow(5.0, exponent), exponent)
                      : mantissa);
  return true;
fail:
  return false;
}

static inline real_t parseReal(const char **token, double default_value = 0.0) {
  (*token) += strspn((*token), " \t");
  const char *end = (*token) + strcspn((*token), " \t\r");
  double val = default_value;
  tryParseDouble((*token), end, &val);
  real_t f = static_cast<real_t>(val);
  (*token) = end;
  return f;
}

static inline bool parseReal(const char **token, real_t *out) {
  (*token) += strspn((*token), " \t");
  const char *end = (*token) + strcspn((*token), " \t\r");
  double val;
  bool ret = tryParseDouble((*token), end, &val);
  if (ret) {
    real_t f = static_cast<real_t>(val);
    (*out) = f;
  }
  (*token) = end;
  return ret;
}

static inline void parseReal2(real_t *x, real_t *y, const char **token,
                              const double default_x = 0.0,
                              const double default_y = 0.0) {
  (*x) = parseReal(token, default_x);
  (*y) = parseReal(token, default_y);
}

static inline void parseReal3(real_t *x, real_t *y, real_t *z,
                              const char **token, const double default_x = 0.0,
                              const double default_y = 0.0,
                              const double default_z = 0.0) {
  (*x) = parseReal(token, default_x);
  (*y) = parseReal(token, default_y);
  (*z) = parseReal(token, default_z);
}

#if 0  // not used
static inline void parseV(real_t *x, real_t *y, real_t *z, real_t *w,
                          const char **token, const double default_x = 0.0,
                          const double default_y = 0.0,
                          const double default_z = 0.0,
                          const double default_w = 1.0) {
  (*x) = parseReal(token, default_x);
  (*y) = parseReal(token, default_y);
  (*z) = parseReal(token, default_z);
  (*w) = parseReal(token, default_w);
}
#endif

// Extension: parse vertex with colors(6 items)
// Return 3: xyz, 4: xyzw, 6: xyzrgb
// `r`: red(case 6) or [w](case 4)
static inline int parseVertexWithColor(real_t *x, real_t *y, real_t *z,
                                       real_t *r, real_t *g, real_t *b,
                                       const char **token,
                                       const double default_x = 0.0,
                                       const double default_y = 0.0,
                                       const double default_z = 0.0) {
  // TODO: Check error
  (*x) = parseReal(token, default_x);
  (*y) = parseReal(token, default_y);
  (*z) = parseReal(token, default_z);

  // - 4 components(x, y, z, w) ot 6 components
  bool has_r = parseReal(token, r);

  if (!has_r) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;
  }

  bool has_g = parseReal(token, g);

  if (!has_g) {
    (*g) = (*b) = 1.0;
    return 4;
  }

  bool has_b = parseReal(token, b);

  if (!has_b) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;  // treated as xyz
  }

  return 6;
}

static inline bool parseOnOff(const char **token, bool default_value = true) {
  (*token) += strspn((*token), " \t");
  const char *end = (*token) + strcspn((*token), " \t\r");

  bool ret = default_value;
  if ((0 == strncmp((*token), "on", 2))) {
    ret = true;
  } else if ((0 == strncmp((*token), "off", 3))) {
    ret = false;
  }

  (*token) = end;
  return ret;
}

static inline texture_type_t parseTextureType(
    const char **token, texture_type_t default_value = TEXTURE_TYPE_NONE) {
  (*token) += strspn((*token), " \t");
  const char *end = (*token) + strcspn((*token), " \t\r");
  texture_type_t ty = default_value;

  if ((0 == strncmp((*token), "cube_top", strlen("cube_top")))) {
    ty = TEXTURE_TYPE_CUBE_TOP;
  } else if ((0 == strncmp((*token), "cube_bottom", strlen("cube_bottom")))) {
    ty = TEXTURE_TYPE_CUBE_BOTTOM;
  } else if ((0 == strncmp((*token), "cube_left", strlen("cube_left")))) {
    ty = TEXTURE_TYPE_CUBE_LEFT;
  } else if ((0 == strncmp((*token), "cube_right", strlen("cube_right")))) {
    ty = TEXTURE_TYPE_CUBE_RIGHT;
  } else if ((0 == strncmp((*token), "cube_front", strlen("cube_front")))) {
    ty = TEXTURE_TYPE_CUBE_FRONT;
  } else if ((0 == strncmp((*token), "cube_back", strlen("cube_back")))) {
    ty = TEXTURE_TYPE_CUBE_BACK;
  } else if ((0 == strncmp((*token), "sphere", strlen("sphere")))) {
    ty = TEXTURE_TYPE_SPHERE;
  }

  (*token) = end;
  return ty;
}

static tag_sizes parseTagTriple(const char **token) {
  tag_sizes ts;

  (*token) += strspn((*token), " \t");
  ts.num_ints = atoi((*token));
  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    return ts;
  }

  (*token)++;  // Skip '/'

  (*token) += strspn((*token), " \t");
  ts.num_reals = atoi((*token));
  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    return ts;
  }
  (*token)++;  // Skip '/'

  ts.num_strings = parseInt(token);

  return ts;
}

// Parse triples with index offsets: i, i/j/k, i//k, i/j
static bool parseTriple(const char **token, int vsize, int vnsize, int vtsize,
                        vertex_index_t *ret, const warning_context &context) {
  if (!ret) {
    return false;
  }

  vertex_index_t vi(-1);

  if (!fixIndex(atoi((*token)), vsize, &vi.v_idx, false, context)) {
    return false;
  }

  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    (*ret) = vi;
    return true;
  }
  (*token)++;

  // i//k
  if ((*token)[0] == '/') {
    (*token)++;
    if (!fixIndex(atoi((*token)), vnsize, &vi.vn_idx, true, context)) {
      return false;
    }
    (*token) += strcspn((*token), "/ \t\r");
    (*ret) = vi;
    return true;
  }

  // i/j/k or i/j
  if (!fixIndex(atoi((*token)), vtsize, &vi.vt_idx, true, context)) {
    return false;
  }

  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    (*ret) = vi;
    return true;
  }

  // i/j/k
  (*token)++;  // skip '/'
  if (!fixIndex(atoi((*token)), vnsize, &vi.vn_idx, true, context)) {
    return false;
  }
  (*token) += strcspn((*token), "/ \t\r");

  (*ret) = vi;

  return true;
}

// Parse raw triples: i, i/j/k, i//k, i/j
static vertex_index_t parseRawTriple(const char **token) {
  vertex_index_t vi(static_cast<int>(0));  // 0 is an invalid index in OBJ

  vi.v_idx = atoi((*token));
  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    return vi;
  }
  (*token)++;

  // i//k
  if ((*token)[0] == '/') {
    (*token)++;
    vi.vn_idx = atoi((*token));
    (*token) += strcspn((*token), "/ \t\r");
    return vi;
  }

  // i/j/k or i/j
  vi.vt_idx = atoi((*token));
  (*token) += strcspn((*token), "/ \t\r");
  if ((*token)[0] != '/') {
    return vi;
  }

  // i/j/k
  (*token)++;  // skip '/'
  vi.vn_idx = atoi((*token));
  (*token) += strcspn((*token), "/ \t\r");
  return vi;
}

// --- Stream-based parse functions ---

static inline std::string sr_parseString(StreamReader &sr) {
  sr.skip_space();
  std::string s;
  while (!sr.eof()) {
    char c = sr.peek();
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    s += c;
    sr.advance(1);
  }
  return s;
}

static inline int sr_parseInt(StreamReader &sr) {
  sr.skip_space();
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  while (len < rem) {
    char c = start[len];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    len++;
  }
  int i = 0;
  if (len > 0) {
    char tmp[64];
    size_t copy_len = len < 63 ? len : 63;
    if (copy_len != len) {
      sr.advance(len);
      return 0;
    }
    memcpy(tmp, start, copy_len);
    tmp[copy_len] = '\0';
    errno = 0;
    char *endptr = NULL;
    long val = strtol(tmp, &endptr, 10);
    const bool has_error =
        (errno == ERANGE || endptr == tmp ||
         val > (std::numeric_limits<int>::max)() ||
         val < (std::numeric_limits<int>::min)());
    if (!has_error) {
      i = static_cast<int>(val);
    }
  }
  sr.advance(len);
  return i;
}

static inline real_t sr_parseReal(StreamReader &sr, double default_value = 0.0) {
  sr.skip_space();
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  while (len < rem) {
    char c = start[len];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    len++;
  }
  double val = default_value;
  if (len > 0) {
    tryParseDouble(start, start + len, &val);
  }
  sr.advance(len);
  return static_cast<real_t>(val);
}

static inline bool sr_parseReal(StreamReader &sr, real_t *out) {
  sr.skip_space();
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  while (len < rem) {
    char c = start[len];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    len++;
  }
  if (len == 0) return false;
  double val;
  bool ret = tryParseDouble(start, start + len, &val);
  if (ret) {
    (*out) = static_cast<real_t>(val);
  }
  sr.advance(len);
  return ret;
}

static inline void sr_parseReal2(real_t *x, real_t *y, StreamReader &sr,
                                 const double default_x = 0.0,
                                 const double default_y = 0.0) {
  (*x) = sr_parseReal(sr, default_x);
  (*y) = sr_parseReal(sr, default_y);
}

static inline void sr_parseReal3(real_t *x, real_t *y, real_t *z,
                                 StreamReader &sr,
                                 const double default_x = 0.0,
                                 const double default_y = 0.0,
                                 const double default_z = 0.0) {
  (*x) = sr_parseReal(sr, default_x);
  (*y) = sr_parseReal(sr, default_y);
  (*z) = sr_parseReal(sr, default_z);
}

static inline int sr_parseVertexWithColor(real_t *x, real_t *y, real_t *z,
                                          real_t *r, real_t *g, real_t *b,
                                          StreamReader &sr,
                                          const double default_x = 0.0,
                                          const double default_y = 0.0,
                                          const double default_z = 0.0) {
  (*x) = sr_parseReal(sr, default_x);
  (*y) = sr_parseReal(sr, default_y);
  (*z) = sr_parseReal(sr, default_z);

  bool has_r = sr_parseReal(sr, r);
  if (!has_r) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;
  }

  bool has_g = sr_parseReal(sr, g);
  if (!has_g) {
    (*g) = (*b) = 1.0;
    return 4;
  }

  bool has_b = sr_parseReal(sr, b);
  if (!has_b) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;
  }

  return 6;
}

// --- Error-reporting overloads ---
// These overloads push clang-style diagnostics into `err` when parsing fails
// and return false so callers can early-return on unrecoverable parse errors.
// The original signatures are preserved above for backward compatibility.

static inline bool sr_parseInt(StreamReader &sr, int *out, std::string *err,
                               const std::string &filename) {
  sr.skip_space();
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  while (len < rem) {
    char c = start[len];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    len++;
  }
  if (len == 0) {
    if (err) {
      (*err) += sr.format_error(filename, "expected integer value");
    }
    *out = 0;
    return false;
  }
  char tmp[64];
  size_t copy_len = len < 63 ? len : 63;
  memcpy(tmp, start, copy_len);
  tmp[copy_len] = '\0';
  if (copy_len != len) {
    if (err) {
      (*err) += sr.format_error(filename, "integer value too long");
    }
    *out = 0;
    sr.advance(len);
    return false;
  }
  errno = 0;
  char *endptr = NULL;
  long val = strtol(tmp, &endptr, 10);
  if (errno == ERANGE || val > (std::numeric_limits<int>::max)() ||
      val < (std::numeric_limits<int>::min)()) {
    if (err) {
      (*err) += sr.format_error(filename,
          "integer value out of range, got '" + std::string(tmp) + "'");
    }
    *out = 0;
    sr.advance(len);
    return false;
  }
  if (endptr == tmp || (*endptr != '\0' && *endptr != ' ' && *endptr != '\t')) {
    if (err) {
      (*err) += sr.format_error(filename,
          "expected integer, got '" + std::string(tmp) + "'");
    }
    *out = 0;
    sr.advance(len);
    return false;
  }
  *out = static_cast<int>(val);
  sr.advance(len);
  return true;
}

static inline bool sr_parseReal(StreamReader &sr, real_t *out,
                                 double default_value,
                                 std::string *err,
                                 const std::string &filename) {
  sr.skip_space();
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  while (len < rem) {
    char c = start[len];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0') break;
    len++;
  }
  if (len == 0) {
    // No token to parse — not necessarily an error (e.g. optional component).
    *out = static_cast<real_t>(default_value);
    return true;
  }
  double val;
  if (!tryParseDouble(start, start + len, &val)) {
    if (err) {
      char tmp[64];
      size_t copy_len = len < 63 ? len : 63;
      memcpy(tmp, start, copy_len);
      tmp[copy_len] = '\0';
      (*err) += sr.format_error(filename,
          "expected number, got '" + std::string(tmp) + "'");
    }
    *out = static_cast<real_t>(default_value);
    sr.advance(len);
    return false;
  }
  *out = static_cast<real_t>(val);
  sr.advance(len);
  return true;
}

static inline bool sr_parseReal2(real_t *x, real_t *y, StreamReader &sr,
                                  std::string *err,
                                  const std::string &filename,
                                  const double default_x = 0.0,
                                  const double default_y = 0.0) {
  if (!sr_parseReal(sr, x, default_x, err, filename)) return false;
  if (!sr_parseReal(sr, y, default_y, err, filename)) return false;
  return true;
}

static inline bool sr_parseReal3(real_t *x, real_t *y, real_t *z,
                                  StreamReader &sr,
                                  std::string *err,
                                  const std::string &filename,
                                  const double default_x = 0.0,
                                  const double default_y = 0.0,
                                  const double default_z = 0.0) {
  if (!sr_parseReal(sr, x, default_x, err, filename)) return false;
  if (!sr_parseReal(sr, y, default_y, err, filename)) return false;
  if (!sr_parseReal(sr, z, default_z, err, filename)) return false;
  return true;
}

// Returns number of components parsed (3, 4, or 6) on success, -1 on error.
static inline int sr_parseVertexWithColor(real_t *x, real_t *y, real_t *z,
                                          real_t *r, real_t *g, real_t *b,
                                          StreamReader &sr,
                                          std::string *err,
                                          const std::string &filename,
                                          const double default_x = 0.0,
                                          const double default_y = 0.0,
                                          const double default_z = 0.0) {
  if (!sr_parseReal(sr, x, default_x, err, filename)) return -1;
  if (!sr_parseReal(sr, y, default_y, err, filename)) return -1;
  if (!sr_parseReal(sr, z, default_z, err, filename)) return -1;

  bool has_r = sr_parseReal(sr, r);
  if (!has_r) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;
  }

  bool has_g = sr_parseReal(sr, g);
  if (!has_g) {
    (*g) = (*b) = 1.0;
    return 4;
  }

  bool has_b = sr_parseReal(sr, b);
  if (!has_b) {
    (*r) = (*g) = (*b) = 1.0;
    return 3;
  }

  return 6;
}

static inline int sr_parseIntNoSkip(StreamReader &sr);

// Advance past remaining characters in a tag triple field (stops at '/', whitespace, or line end).
static inline void sr_skipTagField(StreamReader &sr) {
  while (!sr.eof() && !sr.at_line_end() && !IS_SPACE(sr.peek()) &&
         sr.peek() != '/') {
    sr.advance(1);
  }
}

static tag_sizes sr_parseTagTriple(StreamReader &sr) {
  tag_sizes ts;

  sr.skip_space();
  ts.num_ints = sr_parseIntNoSkip(sr);
  sr_skipTagField(sr);
  if (!sr.eof() && sr.peek() == '/') {
    sr.advance(1);
    sr.skip_space();
    ts.num_reals = sr_parseIntNoSkip(sr);
    sr_skipTagField(sr);
    if (!sr.eof() && sr.peek() == '/') {
      sr.advance(1);
      ts.num_strings = sr_parseInt(sr);
    }
  }
  return ts;
}

static inline int sr_parseIntNoSkip(StreamReader &sr) {
  const char *start = sr.current_ptr();
  size_t rem = sr.remaining();
  size_t len = 0;
  if (len < rem && (start[len] == '+' || start[len] == '-')) len++;
  while (len < rem && start[len] >= '0' && start[len] <= '9') len++;
  int i = 0;
  if (len > 0) {
    char tmp[64];
    size_t copy_len = len < 63 ? len : 63;
    if (copy_len != len) {
      sr.advance(len);
      return 0;
    }
    memcpy(tmp, start, copy_len);
    tmp[copy_len] = '\0';
    errno = 0;
    char *endptr = NULL;
    long val = strtol(tmp, &endptr, 10);
    if (errno == 0 && endptr != tmp && *endptr == '\0' &&
        val <= (std::numeric_limits<int>::max)() &&
        val >= (std::numeric_limits<int>::min)()) {
      i = static_cast<int>(val);
    }
  }
  sr.advance(len);
  return i;
}

static inline void sr_skipUntil(StreamReader &sr, const char *delims) {
  while (!sr.eof()) {
    char c = sr.peek();
    for (const char *d = delims; *d; d++) {
      if (c == *d) return;
    }
    sr.advance(1);
  }
}

static bool sr_parseTriple(StreamReader &sr, int vsize, int vnsize, int vtsize,
                           vertex_index_t *ret, const warning_context &context) {
  if (!ret) return false;

  vertex_index_t vi(-1);

  sr.skip_space();
  if (!fixIndex(sr_parseIntNoSkip(sr), vsize, &vi.v_idx, false, context)) {
    return false;
  }

  sr_skipUntil(sr, "/ \t\r\n");
  if (sr.eof() || sr.peek() != '/') {
    (*ret) = vi;
    return true;
  }
  sr.advance(1);

  // i//k
  if (!sr.eof() && sr.peek() == '/') {
    sr.advance(1);
    if (!fixIndex(sr_parseIntNoSkip(sr), vnsize, &vi.vn_idx, true, context)) {
      return false;
    }
    sr_skipUntil(sr, "/ \t\r\n");
    (*ret) = vi;
    return true;
  }

  // i/j/k or i/j
  if (!fixIndex(sr_parseIntNoSkip(sr), vtsize, &vi.vt_idx, true, context)) {
    return false;
  }

  sr_skipUntil(sr, "/ \t\r\n");
  if (sr.eof() || sr.peek() != '/') {
    (*ret) = vi;
    return true;
  }

  // i/j/k
  sr.advance(1);
  if (!fixIndex(sr_parseIntNoSkip(sr), vnsize, &vi.vn_idx, true, context)) {
    return false;
  }
  sr_skipUntil(sr, "/ \t\r\n");

  (*ret) = vi;
  return true;
}

static vertex_index_t sr_parseRawTriple(StreamReader &sr) {
  vertex_index_t vi(static_cast<int>(0));

  sr.skip_space();
  vi.v_idx = sr_parseIntNoSkip(sr);
  sr_skipUntil(sr, "/ \t\r\n");
  if (sr.eof() || sr.peek() != '/') return vi;
  sr.advance(1);

  // i//k
  if (!sr.eof() && sr.peek() == '/') {
    sr.advance(1);
    vi.vn_idx = sr_parseIntNoSkip(sr);
    sr_skipUntil(sr, "/ \t\r\n");
    return vi;
  }

  // i/j/k or i/j
  vi.vt_idx = sr_parseIntNoSkip(sr);
  sr_skipUntil(sr, "/ \t\r\n");
  if (sr.eof() || sr.peek() != '/') return vi;

  sr.advance(1);
  vi.vn_idx = sr_parseIntNoSkip(sr);
  sr_skipUntil(sr, "/ \t\r\n");
  return vi;
}

bool ParseTextureNameAndOption(std::string *texname, texture_option_t *texopt,
                               const char *linebuf) {
  // @todo { write more robust lexer and parser. }
  bool found_texname = false;
  std::string texture_name;

  const char *token = linebuf;  // Assume line ends with NULL

  while (!IS_NEW_LINE((*token))) {
    token += strspn(token, " \t");  // skip space
    if ((0 == strncmp(token, "-blendu", 7)) && IS_SPACE((token[7]))) {
      token += 8;
      texopt->blendu = parseOnOff(&token, /* default */ true);
    } else if ((0 == strncmp(token, "-blendv", 7)) && IS_SPACE((token[7]))) {
      token += 8;
      texopt->blendv = parseOnOff(&token, /* default */ true);
    } else if ((0 == strncmp(token, "-clamp", 6)) && IS_SPACE((token[6]))) {
      token += 7;
      texopt->clamp = parseOnOff(&token, /* default */ true);
    } else if ((0 == strncmp(token, "-boost", 6)) && IS_SPACE((token[6]))) {
      token += 7;
      texopt->sharpness = parseReal(&token, 1.0);
    } else if ((0 == strncmp(token, "-bm", 3)) && IS_SPACE((token[3]))) {
      token += 4;
      texopt->bump_multiplier = parseReal(&token, 1.0);
    } else if ((0 == strncmp(token, "-o", 2)) && IS_SPACE((token[2]))) {
      token += 3;
      parseReal3(&(texopt->origin_offset[0]), &(texopt->origin_offset[1]),
                 &(texopt->origin_offset[2]), &token);
    } else if ((0 == strncmp(token, "-s", 2)) && IS_SPACE((token[2]))) {
      token += 3;
      parseReal3(&(texopt->scale[0]), &(texopt->scale[1]), &(texopt->scale[2]),
                 &token, 1.0, 1.0, 1.0);
    } else if ((0 == strncmp(token, "-t", 2)) && IS_SPACE((token[2]))) {
      token += 3;
      parseReal3(&(texopt->turbulence[0]), &(texopt->turbulence[1]),
                 &(texopt->turbulence[2]), &token);
    } else if ((0 == strncmp(token, "-type", 5)) && IS_SPACE((token[5]))) {
      token += 5;
      texopt->type = parseTextureType((&token), TEXTURE_TYPE_NONE);
    } else if ((0 == strncmp(token, "-texres", 7)) && IS_SPACE((token[7]))) {
      token += 7;
      // TODO(syoyo): Check if arg is int type.
      texopt->texture_resolution = parseInt(&token);
    } else if ((0 == strncmp(token, "-imfchan", 8)) && IS_SPACE((token[8]))) {
      token += 9;
      token += strspn(token, " \t");
      const char *end = token + strcspn(token, " \t\r");
      if ((end - token) == 1) {  // Assume one char for -imfchan
        texopt->imfchan = (*token);
      }
      token = end;
    } else if ((0 == strncmp(token, "-mm", 3)) && IS_SPACE((token[3]))) {
      token += 4;
      parseReal2(&(texopt->brightness), &(texopt->contrast), &token, 0.0, 1.0);
    } else if ((0 == strncmp(token, "-colorspace", 11)) &&
               IS_SPACE((token[11]))) {
      token += 12;
      texopt->colorspace = parseString(&token);
    } else {
// Assume texture filename
#if 0
      size_t len = strcspn(token, " \t\r");  // untile next space
      texture_name = std::string(token, token + len);
      token += len;

      token += strspn(token, " \t");  // skip space
#else
      // Read filename until line end to parse filename containing whitespace
      // TODO(syoyo): Support parsing texture option flag after the filename.
      texture_name = std::string(token);
      token += texture_name.length();
#endif

      found_texname = true;
    }
  }

  if (found_texname) {
    (*texname) = texture_name;
    return true;
  } else {
    return false;
  }
}

static void InitTexOpt(texture_option_t *texopt, const bool is_bump) {
  if (is_bump) {
    texopt->imfchan = 'l';
  } else {
    texopt->imfchan = 'm';
  }
  texopt->bump_multiplier = static_cast<real_t>(1.0);
  texopt->clamp = false;
  texopt->blendu = true;
  texopt->blendv = true;
  texopt->sharpness = static_cast<real_t>(1.0);
  texopt->brightness = static_cast<real_t>(0.0);
  texopt->contrast = static_cast<real_t>(1.0);
  texopt->origin_offset[0] = static_cast<real_t>(0.0);
  texopt->origin_offset[1] = static_cast<real_t>(0.0);
  texopt->origin_offset[2] = static_cast<real_t>(0.0);
  texopt->scale[0] = static_cast<real_t>(1.0);
  texopt->scale[1] = static_cast<real_t>(1.0);
  texopt->scale[2] = static_cast<real_t>(1.0);
  texopt->turbulence[0] = static_cast<real_t>(0.0);
  texopt->turbulence[1] = static_cast<real_t>(0.0);
  texopt->turbulence[2] = static_cast<real_t>(0.0);
  texopt->texture_resolution = -1;
  texopt->type = TEXTURE_TYPE_NONE;
}

static void InitMaterial(material_t *material) {
  InitTexOpt(&material->ambient_texopt, /* is_bump */ false);
  InitTexOpt(&material->diffuse_texopt, /* is_bump */ false);
  InitTexOpt(&material->specular_texopt, /* is_bump */ false);
  InitTexOpt(&material->specular_highlight_texopt, /* is_bump */ false);
  InitTexOpt(&material->bump_texopt, /* is_bump */ true);
  InitTexOpt(&material->displacement_texopt, /* is_bump */ false);
  InitTexOpt(&material->alpha_texopt, /* is_bump */ false);
  InitTexOpt(&material->reflection_texopt, /* is_bump */ false);
  InitTexOpt(&material->roughness_texopt, /* is_bump */ false);
  InitTexOpt(&material->metallic_texopt, /* is_bump */ false);
  InitTexOpt(&material->sheen_texopt, /* is_bump */ false);
  InitTexOpt(&material->emissive_texopt, /* is_bump */ false);
  InitTexOpt(&material->normal_texopt,
             /* is_bump */ false);  // @fixme { is_bump will be true? }
  material->name = "";
  material->ambient_texname = "";
  material->diffuse_texname = "";
  material->specular_texname = "";
  material->specular_highlight_texname = "";
  material->bump_texname = "";
  material->displacement_texname = "";
  material->reflection_texname = "";
  material->alpha_texname = "";
  for (int i = 0; i < 3; i++) {
    material->ambient[i] = static_cast<real_t>(0.0);
    material->diffuse[i] = static_cast<real_t>(0.0);
    material->specular[i] = static_cast<real_t>(0.0);
    material->transmittance[i] = static_cast<real_t>(0.0);
    material->emission[i] = static_cast<real_t>(0.0);
  }
  material->illum = 0;
  material->dissolve = static_cast<real_t>(1.0);
  material->shininess = static_cast<real_t>(1.0);
  material->ior = static_cast<real_t>(1.0);

  material->roughness = static_cast<real_t>(0.0);
  material->metallic = static_cast<real_t>(0.0);
  material->sheen = static_cast<real_t>(0.0);
  material->clearcoat_thickness = static_cast<real_t>(0.0);
  material->clearcoat_roughness = static_cast<real_t>(0.0);
  material->anisotropy_rotation = static_cast<real_t>(0.0);
  material->anisotropy = static_cast<real_t>(0.0);
  material->roughness_texname = "";
  material->metallic_texname = "";
  material->sheen_texname = "";
  material->emissive_texname = "";
  material->normal_texname = "";

  material->unknown_parameter.clear();
}

// code from https://wrf.ecse.rpi.edu//Research/Short_Notes/pnpoly.html
template <typename T>
static int pnpoly(int nvert, T *vertx, T *verty, T testx, T testy) {
  int i, j, c = 0;
  for (i = 0, j = nvert - 1; i < nvert; j = i++) {
    if (((verty[i] > testy) != (verty[j] > testy)) &&
        (testx <
         (vertx[j] - vertx[i]) * (testy - verty[i]) / (verty[j] - verty[i]) +
             vertx[i]))
      c = !c;
  }
  return c;
}

struct TinyObjPoint {
  real_t x, y, z;
  TinyObjPoint() : x(0), y(0), z(0) {}
  TinyObjPoint(real_t x_, real_t y_, real_t z_) : x(x_), y(y_), z(z_) {}
};

inline TinyObjPoint cross(const TinyObjPoint &v1, const TinyObjPoint &v2) {
  return TinyObjPoint(v1.y * v2.z - v1.z * v2.y, v1.z * v2.x - v1.x * v2.z,
                      v1.x * v2.y - v1.y * v2.x);
}

inline real_t dot(const TinyObjPoint &v1, const TinyObjPoint &v2) {
  return (v1.x * v2.x + v1.y * v2.y + v1.z * v2.z);
}

inline real_t GetLength(TinyObjPoint &e) {
  return std::sqrt(e.x * e.x + e.y * e.y + e.z * e.z);
}

inline TinyObjPoint Normalize(TinyObjPoint e) {
  real_t len = GetLength(e);
  if (len <= real_t(0)) return TinyObjPoint(real_t(0), real_t(0), real_t(0));
  real_t inv_length = real_t(1) / len;
  return TinyObjPoint(e.x * inv_length, e.y * inv_length, e.z * inv_length);
}

inline TinyObjPoint WorldToLocal(const TinyObjPoint &a, const TinyObjPoint &u,
                                 const TinyObjPoint &v, const TinyObjPoint &w) {
  return TinyObjPoint(dot(a, u), dot(a, v), dot(a, w));
}

// TODO(syoyo): refactor function.
static bool exportGroupsToShape(shape_t *shape, const PrimGroup &prim_group,
                                const std::vector<tag_t> &tags,
                                const int material_id, const std::string &name,
                                bool triangulate, const std::vector<real_t> &v,
                                std::string *warn) {
  if (prim_group.IsEmpty()) {
    return false;
  }

  shape->name = name;

  // polygon
  if (!prim_group.faceGroup.empty()) {
    // Flatten vertices and indices
    for (size_t i = 0; i < prim_group.faceGroup.size(); i++) {
      const face_t &face = prim_group.faceGroup[i];

      size_t npolys = face.vertex_indices.size();

      if (npolys < 3) {
        // Face must have 3+ vertices.
        if (warn) {
          (*warn) += "Degenerated face found\n.";
        }
        continue;
      }

      if (triangulate && npolys != 3) {
        if (npolys == 4) {
          vertex_index_t i0 = face.vertex_indices[0];
          vertex_index_t i1 = face.vertex_indices[1];
          vertex_index_t i2 = face.vertex_indices[2];
          vertex_index_t i3 = face.vertex_indices[3];

          size_t vi0 = size_t(i0.v_idx);
          size_t vi1 = size_t(i1.v_idx);
          size_t vi2 = size_t(i2.v_idx);
          size_t vi3 = size_t(i3.v_idx);

          if (((3 * vi0 + 2) >= v.size()) || ((3 * vi1 + 2) >= v.size()) ||
              ((3 * vi2 + 2) >= v.size()) || ((3 * vi3 + 2) >= v.size())) {
            // Invalid triangle.
            // FIXME(syoyo): Is it ok to simply skip this invalid triangle?
            if (warn) {
              (*warn) += "Face with invalid vertex index found.\n";
            }
            continue;
          }

          real_t v0x = v[vi0 * 3 + 0];
          real_t v0y = v[vi0 * 3 + 1];
          real_t v0z = v[vi0 * 3 + 2];
          real_t v1x = v[vi1 * 3 + 0];
          real_t v1y = v[vi1 * 3 + 1];
          real_t v1z = v[vi1 * 3 + 2];
          real_t v2x = v[vi2 * 3 + 0];
          real_t v2y = v[vi2 * 3 + 1];
          real_t v2z = v[vi2 * 3 + 2];
          real_t v3x = v[vi3 * 3 + 0];
          real_t v3y = v[vi3 * 3 + 1];
          real_t v3z = v[vi3 * 3 + 2];

          // There are two candidates to split the quad into two triangles.
          //
          // Choose the shortest edge.
          // TODO: Is it better to determine the edge to split by calculating
          // the area of each triangle?
          //
          // +---+
          // |\  |
          // | \ |
          // |  \|
          // +---+
          //
          // +---+
          // |  /|
          // | / |
          // |/  |
          // +---+

          real_t e02x = v2x - v0x;
          real_t e02y = v2y - v0y;
          real_t e02z = v2z - v0z;
          real_t e13x = v3x - v1x;
          real_t e13y = v3y - v1y;
          real_t e13z = v3z - v1z;

          real_t sqr02 = e02x * e02x + e02y * e02y + e02z * e02z;
          real_t sqr13 = e13x * e13x + e13y * e13y + e13z * e13z;

          index_t idx0, idx1, idx2, idx3;

          idx0.vertex_index = i0.v_idx;
          idx0.normal_index = i0.vn_idx;
          idx0.texcoord_index = i0.vt_idx;
          idx1.vertex_index = i1.v_idx;
          idx1.normal_index = i1.vn_idx;
          idx1.texcoord_index = i1.vt_idx;
          idx2.vertex_index = i2.v_idx;
          idx2.normal_index = i2.vn_idx;
          idx2.texcoord_index = i2.vt_idx;
          idx3.vertex_index = i3.v_idx;
          idx3.normal_index = i3.vn_idx;
          idx3.texcoord_index = i3.vt_idx;

          if (sqr02 < sqr13) {
            // [0, 1, 2], [0, 2, 3]
            shape->mesh.indices.push_back(idx0);
            shape->mesh.indices.push_back(idx1);
            shape->mesh.indices.push_back(idx2);

            shape->mesh.indices.push_back(idx0);
            shape->mesh.indices.push_back(idx2);
            shape->mesh.indices.push_back(idx3);
          } else {
            // [0, 1, 3], [1, 2, 3]
            shape->mesh.indices.push_back(idx0);
            shape->mesh.indices.push_back(idx1);
            shape->mesh.indices.push_back(idx3);

            shape->mesh.indices.push_back(idx1);
            shape->mesh.indices.push_back(idx2);
            shape->mesh.indices.push_back(idx3);
          }

          // Two triangle faces
          shape->mesh.num_face_vertices.push_back(3);
          shape->mesh.num_face_vertices.push_back(3);

          shape->mesh.material_ids.push_back(material_id);
          shape->mesh.material_ids.push_back(material_id);

          shape->mesh.smoothing_group_ids.push_back(face.smoothing_group_id);
          shape->mesh.smoothing_group_ids.push_back(face.smoothing_group_id);

        } else {
#ifdef TINYOBJLOADER_USE_MAPBOX_EARCUT
          vertex_index_t i0 = face.vertex_indices[0];
          vertex_index_t i0_2 = i0;

          // TMW change: Find the normal axis of the polygon using Newell's
          // method
          TinyObjPoint n;
          for (size_t k = 0; k < npolys; ++k) {
            i0 = face.vertex_indices[k % npolys];
            size_t vi0 = size_t(i0.v_idx);

            size_t j = (k + 1) % npolys;
            i0_2 = face.vertex_indices[j];
            size_t vi0_2 = size_t(i0_2.v_idx);

            real_t v0x = v[vi0 * 3 + 0];
            real_t v0y = v[vi0 * 3 + 1];
            real_t v0z = v[vi0 * 3 + 2];

            real_t v0x_2 = v[vi0_2 * 3 + 0];
            real_t v0y_2 = v[vi0_2 * 3 + 1];
            real_t v0z_2 = v[vi0_2 * 3 + 2];

            const TinyObjPoint point1(v0x, v0y, v0z);
            const TinyObjPoint point2(v0x_2, v0y_2, v0z_2);

            TinyObjPoint a(point1.x - point2.x, point1.y - point2.y,
                           point1.z - point2.z);
            TinyObjPoint b(point1.x + point2.x, point1.y + point2.y,
                           point1.z + point2.z);

            n.x += (a.y * b.z);
            n.y += (a.z * b.x);
            n.z += (a.x * b.y);
          }
          real_t length_n = GetLength(n);
          // Check if zero length normal
          if (length_n <= 0) {
            continue;
          }
          // Negative is to flip the normal to the correct direction
          real_t inv_length = -real_t(1.0) / length_n;
          n.x *= inv_length;
          n.y *= inv_length;
          n.z *= inv_length;

          TinyObjPoint axis_w, axis_v, axis_u;
          axis_w = n;
          TinyObjPoint a;
          if (std::fabs(axis_w.x) > real_t(0.9999999)) {
            a = TinyObjPoint(0, 1, 0);
          } else {
            a = TinyObjPoint(1, 0, 0);
          }
          axis_v = Normalize(cross(axis_w, a));
          axis_u = cross(axis_w, axis_v);
          using Point = std::array<real_t, 2>;

          // first polyline define the main polygon.
          // following polylines define holes(not used in tinyobj).
          std::vector<std::vector<Point> > polygon;

          std::vector<Point> polyline;

          // TMW change: Find best normal and project v0x and v0y to those
          // coordinates, instead of picking a plane aligned with an axis (which
          // can flip polygons).

          // Fill polygon data(facevarying vertices).
          for (size_t k = 0; k < npolys; k++) {
            i0 = face.vertex_indices[k];
            size_t vi0 = size_t(i0.v_idx);

            assert(((3 * vi0 + 2) < v.size()));

            real_t v0x = v[vi0 * 3 + 0];
            real_t v0y = v[vi0 * 3 + 1];
            real_t v0z = v[vi0 * 3 + 2];

            TinyObjPoint polypoint(v0x, v0y, v0z);
            TinyObjPoint loc = WorldToLocal(polypoint, axis_u, axis_v, axis_w);

            polyline.push_back({loc.x, loc.y});
          }

          polygon.push_back(polyline);
          std::vector<uint32_t> indices = mapbox::earcut<uint32_t>(polygon);
          // => result = 3 * faces, clockwise

          assert(indices.size() % 3 == 0);

          // Reconstruct vertex_index_t
          for (size_t k = 0; k < indices.size() / 3; k++) {
            {
              index_t idx0, idx1, idx2;
              idx0.vertex_index = face.vertex_indices[indices[3 * k + 0]].v_idx;
              idx0.normal_index =
                  face.vertex_indices[indices[3 * k + 0]].vn_idx;
              idx0.texcoord_index =
                  face.vertex_indices[indices[3 * k + 0]].vt_idx;
              idx1.vertex_index = face.vertex_indices[indices[3 * k + 1]].v_idx;
              idx1.normal_index =
                  face.vertex_indices[indices[3 * k + 1]].vn_idx;
              idx1.texcoord_index =
                  face.vertex_indices[indices[3 * k + 1]].vt_idx;
              idx2.vertex_index = face.vertex_indices[indices[3 * k + 2]].v_idx;
              idx2.normal_index =
                  face.vertex_indices[indices[3 * k + 2]].vn_idx;
              idx2.texcoord_index =
                  face.vertex_indices[indices[3 * k + 2]].vt_idx;

              shape->mesh.indices.push_back(idx0);
              shape->mesh.indices.push_back(idx1);
              shape->mesh.indices.push_back(idx2);

              shape->mesh.num_face_vertices.push_back(3);
              shape->mesh.material_ids.push_back(material_id);
              shape->mesh.smoothing_group_ids.push_back(
                  face.smoothing_group_id);
            }
          }

#else  // Built-in ear clipping triangulation
          vertex_index_t i0 = face.vertex_indices[0];
          vertex_index_t i1(-1);
          vertex_index_t i2 = face.vertex_indices[1];

          // find the two axes to work in
          size_t axes[2] = {1, 2};
          for (size_t k = 0; k < npolys; ++k) {
            i0 = face.vertex_indices[(k + 0) % npolys];
            i1 = face.vertex_indices[(k + 1) % npolys];
            i2 = face.vertex_indices[(k + 2) % npolys];
            size_t vi0 = size_t(i0.v_idx);
            size_t vi1 = size_t(i1.v_idx);
            size_t vi2 = size_t(i2.v_idx);

            if (((3 * vi0 + 2) >= v.size()) || ((3 * vi1 + 2) >= v.size()) ||
                ((3 * vi2 + 2) >= v.size())) {
              // Invalid triangle.
              // FIXME(syoyo): Is it ok to simply skip this invalid triangle?
              continue;
            }
            real_t v0x = v[vi0 * 3 + 0];
            real_t v0y = v[vi0 * 3 + 1];
            real_t v0z = v[vi0 * 3 + 2];
            real_t v1x = v[vi1 * 3 + 0];
            real_t v1y = v[vi1 * 3 + 1];
            real_t v1z = v[vi1 * 3 + 2];
            real_t v2x = v[vi2 * 3 + 0];
            real_t v2y = v[vi2 * 3 + 1];
            real_t v2z = v[vi2 * 3 + 2];
            real_t e0x = v1x - v0x;
            real_t e0y = v1y - v0y;
            real_t e0z = v1z - v0z;
            real_t e1x = v2x - v1x;
            real_t e1y = v2y - v1y;
            real_t e1z = v2z - v1z;
            real_t cx = std::fabs(e0y * e1z - e0z * e1y);
            real_t cy = std::fabs(e0z * e1x - e0x * e1z);
            real_t cz = std::fabs(e0x * e1y - e0y * e1x);
            const real_t epsilon = std::numeric_limits<real_t>::epsilon();
            // std::cout << "cx " << cx << ", cy " << cy << ", cz " << cz <<
            // "\n";
            if (cx > epsilon || cy > epsilon || cz > epsilon) {
              // std::cout << "corner\n";
              // found a corner
              if (cx > cy && cx > cz) {
                // std::cout << "pattern0\n";
              } else {
                // std::cout << "axes[0] = 0\n";
                axes[0] = 0;
                if (cz > cx && cz > cy) {
                  // std::cout << "axes[1] = 1\n";
                  axes[1] = 1;
                }
              }
              break;
            }
          }

          face_t remainingFace = face;  // copy
          size_t guess_vert = 0;
          vertex_index_t ind[3];
          real_t vx[3];
          real_t vy[3];

          // How many iterations can we do without decreasing the remaining
          // vertices.
          size_t remainingIterations = face.vertex_indices.size();
          size_t previousRemainingVertices =
              remainingFace.vertex_indices.size();

          while (remainingFace.vertex_indices.size() > 3 &&
                 remainingIterations > 0) {
            // std::cout << "remainingIterations " << remainingIterations <<
            // "\n";

            npolys = remainingFace.vertex_indices.size();
            if (guess_vert >= npolys) {
              guess_vert -= npolys;
            }

            if (previousRemainingVertices != npolys) {
              // The number of remaining vertices decreased. Reset counters.
              previousRemainingVertices = npolys;
              remainingIterations = npolys;
            } else {
              // We didn't consume a vertex on previous iteration, reduce the
              // available iterations.
              remainingIterations--;
            }

            for (size_t k = 0; k < 3; k++) {
              ind[k] = remainingFace.vertex_indices[(guess_vert + k) % npolys];
              size_t vi = size_t(ind[k].v_idx);
              if (((vi * 3 + axes[0]) >= v.size()) ||
                  ((vi * 3 + axes[1]) >= v.size())) {
                // ???
                vx[k] = static_cast<real_t>(0.0);
                vy[k] = static_cast<real_t>(0.0);
              } else {
                vx[k] = v[vi * 3 + axes[0]];
                vy[k] = v[vi * 3 + axes[1]];
              }
            }

            //
            // area is calculated per face
            //
            real_t e0x = vx[1] - vx[0];
            real_t e0y = vy[1] - vy[0];
            real_t e1x = vx[2] - vx[1];
            real_t e1y = vy[2] - vy[1];
            real_t cross = e0x * e1y - e0y * e1x;
            // std::cout << "axes = " << axes[0] << ", " << axes[1] << "\n";
            // std::cout << "e0x, e0y, e1x, e1y " << e0x << ", " << e0y << ", "
            // << e1x << ", " << e1y << "\n";

            real_t area =
                (vx[0] * vy[1] - vy[0] * vx[1]) * static_cast<real_t>(0.5);
            // std::cout << "cross " << cross << ", area " << area << "\n";
            // if an internal angle
            if (cross * area < static_cast<real_t>(0.0)) {
              // std::cout << "internal \n";
              guess_vert += 1;
              // std::cout << "guess vert : " << guess_vert << "\n";
              continue;
            }

            // check all other verts in case they are inside this triangle
            bool overlap = false;
            for (size_t otherVert = 3; otherVert < npolys; ++otherVert) {
              size_t idx = (guess_vert + otherVert) % npolys;

              if (idx >= remainingFace.vertex_indices.size()) {
                // std::cout << "???0\n";
                // ???
                continue;
              }

              size_t ovi = size_t(remainingFace.vertex_indices[idx].v_idx);

              if (((ovi * 3 + axes[0]) >= v.size()) ||
                  ((ovi * 3 + axes[1]) >= v.size())) {
                // std::cout << "???1\n";
                // ???
                continue;
              }
              real_t tx = v[ovi * 3 + axes[0]];
              real_t ty = v[ovi * 3 + axes[1]];
              if (pnpoly(3, vx, vy, tx, ty)) {
                // std::cout << "overlap\n";
                overlap = true;
                break;
              }
            }

            if (overlap) {
              // std::cout << "overlap2\n";
              guess_vert += 1;
              continue;
            }

            // this triangle is an ear
            {
              index_t idx0, idx1, idx2;
              idx0.vertex_index = ind[0].v_idx;
              idx0.normal_index = ind[0].vn_idx;
              idx0.texcoord_index = ind[0].vt_idx;
              idx1.vertex_index = ind[1].v_idx;
              idx1.normal_index = ind[1].vn_idx;
              idx1.texcoord_index = ind[1].vt_idx;
              idx2.vertex_index = ind[2].v_idx;
              idx2.normal_index = ind[2].vn_idx;
              idx2.texcoord_index = ind[2].vt_idx;

              shape->mesh.indices.push_back(idx0);
              shape->mesh.indices.push_back(idx1);
              shape->mesh.indices.push_back(idx2);

              shape->mesh.num_face_vertices.push_back(3);
              shape->mesh.material_ids.push_back(material_id);
              shape->mesh.smoothing_group_ids.push_back(
                  face.smoothing_group_id);
            }

            // remove v1 from the list
            size_t removed_vert_index = (guess_vert + 1) % npolys;
            while (removed_vert_index + 1 < npolys) {
              remainingFace.vertex_indices[removed_vert_index] =
                  remainingFace.vertex_indices[removed_vert_index + 1];
              removed_vert_index += 1;
            }
            remainingFace.vertex_indices.pop_back();
          }

          // std::cout << "remainingFace.vi.size = " <<
          // remainingFace.vertex_indices.size() << "\n";
          if (remainingFace.vertex_indices.size() == 3) {
            i0 = remainingFace.vertex_indices[0];
            i1 = remainingFace.vertex_indices[1];
            i2 = remainingFace.vertex_indices[2];
            {
              index_t idx0, idx1, idx2;
              idx0.vertex_index = i0.v_idx;
              idx0.normal_index = i0.vn_idx;
              idx0.texcoord_index = i0.vt_idx;
              idx1.vertex_index = i1.v_idx;
              idx1.normal_index = i1.vn_idx;
              idx1.texcoord_index = i1.vt_idx;
              idx2.vertex_index = i2.v_idx;
              idx2.normal_index = i2.vn_idx;
              idx2.texcoord_index = i2.vt_idx;

              shape->mesh.indices.push_back(idx0);
              shape->mesh.indices.push_back(idx1);
              shape->mesh.indices.push_back(idx2);

              shape->mesh.num_face_vertices.push_back(3);
              shape->mesh.material_ids.push_back(material_id);
              shape->mesh.smoothing_group_ids.push_back(
                  face.smoothing_group_id);
            }
          }
#endif
        }  // npolys
      } else {
        for (size_t k = 0; k < npolys; k++) {
          index_t idx;
          idx.vertex_index = face.vertex_indices[k].v_idx;
          idx.normal_index = face.vertex_indices[k].vn_idx;
          idx.texcoord_index = face.vertex_indices[k].vt_idx;
          shape->mesh.indices.push_back(idx);
        }

        shape->mesh.num_face_vertices.push_back(
            static_cast<unsigned int>(npolys));
        shape->mesh.material_ids.push_back(material_id);  // per face
        shape->mesh.smoothing_group_ids.push_back(
            face.smoothing_group_id);  // per face
      }
    }

    shape->mesh.tags = tags;
  }

  // line
  if (!prim_group.lineGroup.empty()) {
    // Flatten indices
    for (size_t i = 0; i < prim_group.lineGroup.size(); i++) {
      for (size_t j = 0; j < prim_group.lineGroup[i].vertex_indices.size();
           j++) {
        const vertex_index_t &vi = prim_group.lineGroup[i].vertex_indices[j];

        index_t idx;
        idx.vertex_index = vi.v_idx;
        idx.normal_index = vi.vn_idx;
        idx.texcoord_index = vi.vt_idx;

        shape->lines.indices.push_back(idx);
      }

      shape->lines.num_line_vertices.push_back(
          int(prim_group.lineGroup[i].vertex_indices.size()));
    }
  }

  // points
  if (!prim_group.pointsGroup.empty()) {
    // Flatten & convert indices
    for (size_t i = 0; i < prim_group.pointsGroup.size(); i++) {
      for (size_t j = 0; j < prim_group.pointsGroup[i].vertex_indices.size();
           j++) {
        const vertex_index_t &vi = prim_group.pointsGroup[i].vertex_indices[j];

        index_t idx;
        idx.vertex_index = vi.v_idx;
        idx.normal_index = vi.vn_idx;
        idx.texcoord_index = vi.vt_idx;

        shape->points.indices.push_back(idx);
      }
    }
  }

  return true;
}

// Split a string with specified delimiter character and escape character.
// https://rosettacode.org/wiki/Tokenize_a_string_with_escaping#C.2B.2B
static void SplitString(const std::string &s, char delim, char escape,
                        std::vector<std::string> &elems) {
  std::string token;

  bool escaping = false;
  for (size_t i = 0; i < s.size(); ++i) {
    char ch = s[i];
    if (escaping) {
      escaping = false;
    } else if (ch == escape) {
      if ((i + 1) < s.size()) {
        const char next = s[i + 1];
        if ((next == delim) || (next == escape)) {
          escaping = true;
          continue;
        }
      }
    } else if (ch == delim) {
      if (!token.empty()) {
        elems.push_back(token);
      }
      token.clear();
      continue;
    }
    token += ch;
  }

  elems.push_back(token);
}

static void RemoveEmptyTokens(std::vector<std::string> *tokens) {
  if (!tokens) return;

  const std::vector<std::string> &src = *tokens;
  std::vector<std::string> filtered;
  filtered.reserve(src.size());
  for (size_t i = 0; i < src.size(); i++) {
    if (!src[i].empty()) {
      filtered.push_back(src[i]);
    }
  }
  tokens->swap(filtered);
}

static std::string JoinPath(const std::string &dir,
                            const std::string &filename) {
  if (dir.empty()) {
    return filename;
  } else {
    // check '/'
    char lastChar = *dir.rbegin();
    if (lastChar != '/') {
      return dir + std::string("/") + filename;
    } else {
      return dir + filename;
    }
  }
}

static bool LoadMtlInternal(std::map<std::string, int> *material_map,
                            std::vector<material_t> *materials,
                            StreamReader &sr,
                            std::string *warning, std::string *err,
                            const std::string &filename = "<stream>") {
  if (sr.has_errors()) {
    if (err) {
      (*err) += sr.get_errors();
    }
    return false;
  }

  material_t material;
  InitMaterial(&material);

  // Issue 43. `d` wins against `Tr` since `Tr` is not in the MTL specification.
  bool has_d = false;
  bool has_tr = false;

  // has_kd is used to set a default diffuse value when map_Kd is present
  // and Kd is not.
  bool has_kd = false;

  std::stringstream warn_ss;

  // Handle BOM
  if (sr.remaining() >= 3 &&
      static_cast<unsigned char>(sr.peek()) == 0xEF &&
      static_cast<unsigned char>(sr.peek_at(1)) == 0xBB &&
      static_cast<unsigned char>(sr.peek_at(2)) == 0xBF) {
    sr.advance(3);
  }

  while (!sr.eof()) {
    sr.skip_space();
    if (sr.at_line_end()) { sr.skip_line(); continue; }
    if (sr.peek() == '#') { sr.skip_line(); continue; }

    size_t line_num = sr.line_num();

    // new mtl
    if (sr.match("newmtl", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      // flush previous material.
      if (!material.name.empty()) {
        material_map->insert(std::pair<std::string, int>(
            material.name, static_cast<int>(materials->size())));
        materials->push_back(material);
      }

      InitMaterial(&material);

      has_d = false;
      has_tr = false;
      has_kd = false;

      sr.advance(7);
      {
        std::string namebuf = sr_parseString(sr);
        if (namebuf.empty()) {
          if (warning) {
            (*warning) += "empty material name in `newmtl`\n";
          }
        }
        material.name = namebuf;
      }
      sr.skip_line();
      continue;
    }

    // ambient
    if (sr.peek() == 'K' && sr.peek_at(1) == 'a' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      real_t r, g, b;
      if (!sr_parseReal3(&r, &g, &b, sr, err, filename)) return false;
      material.ambient[0] = r;
      material.ambient[1] = g;
      material.ambient[2] = b;
      sr.skip_line();
      continue;
    }

    // diffuse
    if (sr.peek() == 'K' && sr.peek_at(1) == 'd' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      real_t r, g, b;
      if (!sr_parseReal3(&r, &g, &b, sr, err, filename)) return false;
      material.diffuse[0] = r;
      material.diffuse[1] = g;
      material.diffuse[2] = b;
      has_kd = true;
      sr.skip_line();
      continue;
    }

    // specular
    if (sr.peek() == 'K' && sr.peek_at(1) == 's' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      real_t r, g, b;
      if (!sr_parseReal3(&r, &g, &b, sr, err, filename)) return false;
      material.specular[0] = r;
      material.specular[1] = g;
      material.specular[2] = b;
      sr.skip_line();
      continue;
    }

    // transmittance
    if ((sr.peek() == 'K' && sr.peek_at(1) == 't' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) ||
        (sr.peek() == 'T' && sr.peek_at(1) == 'f' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t'))) {
      sr.advance(2);
      real_t r, g, b;
      if (!sr_parseReal3(&r, &g, &b, sr, err, filename)) return false;
      material.transmittance[0] = r;
      material.transmittance[1] = g;
      material.transmittance[2] = b;
      sr.skip_line();
      continue;
    }

    // ior(index of refraction)
    if (sr.peek() == 'N' && sr.peek_at(1) == 'i' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.ior, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // emission
    if (sr.peek() == 'K' && sr.peek_at(1) == 'e' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      real_t r, g, b;
      if (!sr_parseReal3(&r, &g, &b, sr, err, filename)) return false;
      material.emission[0] = r;
      material.emission[1] = g;
      material.emission[2] = b;
      sr.skip_line();
      continue;
    }

    // shininess
    if (sr.peek() == 'N' && sr.peek_at(1) == 's' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.shininess, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // illum model
    if (sr.match("illum", 5) && (sr.peek_at(5) == ' ' || sr.peek_at(5) == '\t')) {
      sr.advance(6);
      if (!sr_parseInt(sr, &material.illum, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // dissolve
    if (sr.peek() == 'd' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(1);
      if (!sr_parseReal(sr, &material.dissolve, 0.0, err, filename)) return false;

      if (has_tr) {
        warn_ss << "Both `d` and `Tr` parameters defined for \""
                << material.name
                << "\". Use the value of `d` for dissolve (line " << line_num
                << " in .mtl.)\n";
      }
      has_d = true;
      sr.skip_line();
      continue;
    }
    if (sr.peek() == 'T' && sr.peek_at(1) == 'r' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (has_d) {
        warn_ss << "Both `d` and `Tr` parameters defined for \""
                << material.name
                << "\". Use the value of `d` for dissolve (line " << line_num
                << " in .mtl.)\n";
      } else {
        real_t tr_val;
        if (!sr_parseReal(sr, &tr_val, 0.0, err, filename)) return false;
        material.dissolve = static_cast<real_t>(1.0) - tr_val;
      }
      has_tr = true;
      sr.skip_line();
      continue;
    }

    // PBR: roughness
    if (sr.peek() == 'P' && sr.peek_at(1) == 'r' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.roughness, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: metallic
    if (sr.peek() == 'P' && sr.peek_at(1) == 'm' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.metallic, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: sheen
    if (sr.peek() == 'P' && sr.peek_at(1) == 's' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.sheen, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: clearcoat thickness
    if (sr.peek() == 'P' && sr.peek_at(1) == 'c' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(2);
      if (!sr_parseReal(sr, &material.clearcoat_thickness, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: clearcoat roughness
    if (sr.match("Pcr", 3) && (sr.peek_at(3) == ' ' || sr.peek_at(3) == '\t')) {
      sr.advance(4);
      if (!sr_parseReal(sr, &material.clearcoat_roughness, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: anisotropy
    if (sr.match("aniso", 5) && (sr.peek_at(5) == ' ' || sr.peek_at(5) == '\t')) {
      sr.advance(6);
      if (!sr_parseReal(sr, &material.anisotropy, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // PBR: anisotropy rotation
    if (sr.match("anisor", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      if (!sr_parseReal(sr, &material.anisotropy_rotation, 0.0, err, filename)) return false;
      sr.skip_line();
      continue;
    }

    // For texture directives, read rest of line and delegate to
    // ParseTextureNameAndOption (which uses the old const char* parse functions).

    // ambient or ambient occlusion texture
    if (sr.match("map_Ka", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.ambient_texname),
                                &(material.ambient_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // diffuse texture
    if (sr.match("map_Kd", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.diffuse_texname),
                                &(material.diffuse_texopt), line_rest.c_str());
      if (!has_kd) {
        material.diffuse[0] = static_cast<real_t>(0.6);
        material.diffuse[1] = static_cast<real_t>(0.6);
        material.diffuse[2] = static_cast<real_t>(0.6);
      }
      sr.skip_line();
      continue;
    }

    // specular texture
    if (sr.match("map_Ks", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.specular_texname),
                                &(material.specular_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // specular highlight texture
    if (sr.match("map_Ns", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.specular_highlight_texname),
                                &(material.specular_highlight_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // bump texture
    if ((sr.match("map_bump", 8) || sr.match("map_Bump", 8)) &&
        (sr.peek_at(8) == ' ' || sr.peek_at(8) == '\t')) {
      sr.advance(9);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.bump_texname),
                                &(material.bump_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // bump texture (short form)
    if (sr.match("bump", 4) && (sr.peek_at(4) == ' ' || sr.peek_at(4) == '\t')) {
      sr.advance(5);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.bump_texname),
                                &(material.bump_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // alpha texture
    if (sr.match("map_d", 5) && (sr.peek_at(5) == ' ' || sr.peek_at(5) == '\t')) {
      sr.advance(6);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.alpha_texname),
                                &(material.alpha_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // displacement texture
    if ((sr.match("map_disp", 8) || sr.match("map_Disp", 8)) &&
        (sr.peek_at(8) == ' ' || sr.peek_at(8) == '\t')) {
      sr.advance(9);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.displacement_texname),
                                &(material.displacement_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // displacement texture (short form)
    if (sr.match("disp", 4) && (sr.peek_at(4) == ' ' || sr.peek_at(4) == '\t')) {
      sr.advance(5);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.displacement_texname),
                                &(material.displacement_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // reflection map
    if (sr.match("refl", 4) && (sr.peek_at(4) == ' ' || sr.peek_at(4) == '\t')) {
      sr.advance(5);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.reflection_texname),
                                &(material.reflection_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // PBR: roughness texture
    if (sr.match("map_Pr", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.roughness_texname),
                                &(material.roughness_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // PBR: metallic texture
    if (sr.match("map_Pm", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.metallic_texname),
                                &(material.metallic_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // PBR: sheen texture
    if (sr.match("map_Ps", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.sheen_texname),
                                &(material.sheen_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // PBR: emissive texture
    if (sr.match("map_Ke", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(7);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.emissive_texname),
                                &(material.emissive_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // PBR: normal map texture
    if (sr.match("norm", 4) && (sr.peek_at(4) == ' ' || sr.peek_at(4) == '\t')) {
      sr.advance(5);
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      ParseTextureNameAndOption(&(material.normal_texname),
                                &(material.normal_texopt), line_rest.c_str());
      sr.skip_line();
      continue;
    }

    // unknown parameter
    {
      std::string line_rest = trimTrailingWhitespace(sr.read_line());
      const char *_lp = line_rest.c_str();
      const char *_space = strchr(_lp, ' ');
      if (!_space) {
        _space = strchr(_lp, '\t');
      }
      if (_space) {
        std::ptrdiff_t len = _space - _lp;
        std::string key(_lp, static_cast<size_t>(len));
        std::string value = _space + 1;
        material.unknown_parameter.insert(
            std::pair<std::string, std::string>(key, value));
      }
    }
    sr.skip_line();
  }
  // flush last material.
  material_map->insert(std::pair<std::string, int>(
      material.name, static_cast<int>(materials->size())));
  materials->push_back(material);

  if (warning) {
    (*warning) = warn_ss.str();
  }

  return true;
}

void LoadMtl(std::map<std::string, int> *material_map,
             std::vector<material_t> *materials, std::istream *inStream,
             std::string *warning, std::string *err) {
  StreamReader sr(*inStream);
  LoadMtlInternal(material_map, materials, sr, warning, err);
}


bool MaterialFileReader::operator()(const std::string &matId,
                                    std::vector<material_t> *materials,
                                    std::map<std::string, int> *matMap,
                                    std::string *warn, std::string *err) {
  if (!m_mtlBaseDir.empty()) {
#ifdef _WIN32
    char sep = ';';
#else
    char sep = ':';
#endif

    // https://stackoverflow.com/questions/5167625/splitting-a-c-stdstring-using-tokens-e-g
    std::vector<std::string> paths;
    std::istringstream f(m_mtlBaseDir);

    std::string s;
    while (getline(f, s, sep)) {
      paths.push_back(s);
    }

    for (size_t i = 0; i < paths.size(); i++) {
      std::string filepath = JoinPath(paths[i], matId);

#ifdef TINYOBJLOADER_USE_MMAP
      {
        MappedFile mf;
        if (!mf.open(filepath.c_str())) continue;
        if (mf.size > TINYOBJLOADER_STREAM_READER_MAX_BYTES) {
          if (err) {
            std::stringstream ss;
            ss << "input stream too large (" << mf.size
               << " bytes exceeds limit "
               << TINYOBJLOADER_STREAM_READER_MAX_BYTES << " bytes)\n";
            (*err) += ss.str();
          }
          return false;
        }
        StreamReader sr(mf.data, mf.size);
        return LoadMtlInternal(matMap, materials, sr, warn, err, filepath);
      }
#else   // !TINYOBJLOADER_USE_MMAP
#ifdef _WIN32
      std::ifstream matIStream(LongPathW(UTF8ToWchar(filepath)).c_str());
#else
      std::ifstream matIStream(filepath.c_str());
#endif
      if (matIStream) {
        StreamReader mtl_sr(matIStream);
        return LoadMtlInternal(matMap, materials, mtl_sr, warn, err, filepath);
      }
#endif  // TINYOBJLOADER_USE_MMAP
    }

    std::stringstream ss;
    ss << "Material file [ " << matId
       << " ] not found in a path : " << m_mtlBaseDir << "\n";
    if (warn) {
      (*warn) += ss.str();
    }
    return false;

  } else {
    std::string filepath = matId;

#ifdef TINYOBJLOADER_USE_MMAP
    {
      MappedFile mf;
      if (mf.open(filepath.c_str())) {
        if (mf.size > TINYOBJLOADER_STREAM_READER_MAX_BYTES) {
          if (err) {
            std::stringstream ss;
            ss << "input stream too large (" << mf.size
               << " bytes exceeds limit "
               << TINYOBJLOADER_STREAM_READER_MAX_BYTES << " bytes)\n";
            (*err) += ss.str();
          }
          return false;
        }
        StreamReader sr(mf.data, mf.size);
        return LoadMtlInternal(matMap, materials, sr, warn, err, filepath);
      }
    }
#else   // !TINYOBJLOADER_USE_MMAP
#ifdef _WIN32
    std::ifstream matIStream(LongPathW(UTF8ToWchar(filepath)).c_str());
#else
    std::ifstream matIStream(filepath.c_str());
#endif
    if (matIStream) {
      StreamReader mtl_sr(matIStream);
      return LoadMtlInternal(matMap, materials, mtl_sr, warn, err, filepath);
    }
#endif  // TINYOBJLOADER_USE_MMAP

    std::stringstream ss;
    ss << "Material file [ " << filepath
       << " ] not found in a path : " << m_mtlBaseDir << "\n";
    if (warn) {
      (*warn) += ss.str();
    }

    return false;
  }
}

bool MaterialStreamReader::operator()(const std::string &matId,
                                      std::vector<material_t> *materials,
                                      std::map<std::string, int> *matMap,
                                      std::string *warn, std::string *err) {
  (void)matId;
  if (!m_inStream) {
    std::stringstream ss;
    ss << "Material stream in error state. \n";
    if (warn) {
      (*warn) += ss.str();
    }
    return false;
  }

  StreamReader mtl_sr(m_inStream);
  return LoadMtlInternal(matMap, materials, mtl_sr, warn, err, "<stream>");
}

static bool LoadObjInternal(attrib_t *attrib, std::vector<shape_t> *shapes,
                            std::vector<material_t> *materials,
                            std::string *warn, std::string *err,
                            StreamReader &sr,
                            MaterialReader *readMatFn, bool triangulate,
                            bool default_vcols_fallback,
                            const std::string &filename = "<stream>") {
  if (sr.has_errors()) {
    if (err) {
      (*err) += sr.get_errors();
    }
    return false;
  }

  std::vector<real_t> v;
  std::vector<real_t> vertex_weights;
  std::vector<real_t> vn;
  std::vector<real_t> vt;
  std::vector<real_t> vt_w;  // optional [w] component in `vt`
  std::vector<real_t> vc;
  std::vector<skin_weight_t> vw;
  std::vector<tag_t> tags;
  PrimGroup prim_group;
  std::string name;

  // material
  std::set<std::string> material_filenames;
  std::map<std::string, int> material_map;
  int material = -1;

  unsigned int current_smoothing_id = 0;

  int greatest_v_idx = -1;
  int greatest_vn_idx = -1;
  int greatest_vt_idx = -1;

  shape_t shape;

  bool found_all_colors = true;

  // Handle BOM
  if (sr.remaining() >= 3 &&
      static_cast<unsigned char>(sr.peek()) == 0xEF &&
      static_cast<unsigned char>(sr.peek_at(1)) == 0xBB &&
      static_cast<unsigned char>(sr.peek_at(2)) == 0xBF) {
    sr.advance(3);
  }

  warning_context context;
  context.warn = warn;
  context.filename = filename;

  while (!sr.eof()) {
    sr.skip_space();
    if (sr.at_line_end()) { sr.skip_line(); continue; }
    if (sr.peek() == '#') { sr.skip_line(); continue; }

    size_t line_num = sr.line_num();

    // vertex
    if (sr.peek() == 'v' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);
      real_t x, y, z;
      real_t r, g, b;

      int num_components = sr_parseVertexWithColor(&x, &y, &z, &r, &g, &b, sr, err, filename);
      if (num_components < 0) return false;
      found_all_colors &= (num_components == 6);

      v.push_back(x);
      v.push_back(y);
      v.push_back(z);

      vertex_weights.push_back(r);

      if ((num_components == 6) || default_vcols_fallback) {
        vc.push_back(r);
        vc.push_back(g);
        vc.push_back(b);
      }

      sr.skip_line();
      continue;
    }

    // normal
    if (sr.peek() == 'v' && sr.peek_at(1) == 'n' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(3);
      real_t x, y, z;
      if (!sr_parseReal3(&x, &y, &z, sr, err, filename)) return false;
      vn.push_back(x);
      vn.push_back(y);
      vn.push_back(z);
      sr.skip_line();
      continue;
    }

    // texcoord
    if (sr.peek() == 'v' && sr.peek_at(1) == 't' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(3);
      real_t x, y;
      if (!sr_parseReal2(&x, &y, sr, err, filename)) return false;
      vt.push_back(x);
      vt.push_back(y);

      // Parse optional w component
      real_t w = static_cast<real_t>(0.0);
      sr_parseReal(sr, &w);
      vt_w.push_back(w);

      sr.skip_line();
      continue;
    }

    // skin weight. tinyobj extension
    if (sr.peek() == 'v' && sr.peek_at(1) == 'w' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(3);

      int vid;
      if (!sr_parseInt(sr, &vid, err, filename)) return false;

      skin_weight_t sw;
      sw.vertex_id = vid;

      size_t vw_loop_max = sr.remaining() + 1;
      size_t vw_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             vw_loop_iter < vw_loop_max) {
        real_t j, w;
        sr_parseReal2(&j, &w, sr, -1.0);

        if (j < static_cast<real_t>(0)) {
          if (err) {
            (*err) += sr.format_error(filename,
                "failed to parse `vw' line: joint_id is negative");
          }
          return false;
        }

        joint_and_weight_t jw;
        jw.joint_id = int(j);
        jw.weight = w;

        sw.weightValues.push_back(jw);
        sr.skip_space_and_cr();
        vw_loop_iter++;
      }

      vw.push_back(sw);
      sr.skip_line();
      continue;
    }

    context.line_number = line_num;

    // line
    if (sr.peek() == 'l' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);

      __line_t line;

      size_t l_loop_max = sr.remaining() + 1;
      size_t l_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             l_loop_iter < l_loop_max) {
        vertex_index_t vi;
        if (!sr_parseTriple(sr, static_cast<int>(v.size() / 3),
                         static_cast<int>(vn.size() / 3),
                         static_cast<int>(vt.size() / 2), &vi, context)) {
          if (err) {
            (*err) += sr.format_error(filename,
                "failed to parse `l' line (invalid vertex index)");
          }
          return false;
        }

        line.vertex_indices.push_back(vi);
        sr.skip_space_and_cr();
        l_loop_iter++;
      }

      prim_group.lineGroup.push_back(line);
      sr.skip_line();
      continue;
    }

    // points
    if (sr.peek() == 'p' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);

      __points_t pts;

      size_t p_loop_max = sr.remaining() + 1;
      size_t p_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             p_loop_iter < p_loop_max) {
        vertex_index_t vi;
        if (!sr_parseTriple(sr, static_cast<int>(v.size() / 3),
                         static_cast<int>(vn.size() / 3),
                         static_cast<int>(vt.size() / 2), &vi, context)) {
          if (err) {
            (*err) += sr.format_error(filename,
                "failed to parse `p' line (invalid vertex index)");
          }
          return false;
        }

        pts.vertex_indices.push_back(vi);
        sr.skip_space_and_cr();
        p_loop_iter++;
      }

      prim_group.pointsGroup.push_back(pts);
      sr.skip_line();
      continue;
    }

    // face
    if (sr.peek() == 'f' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);
      sr.skip_space();

      face_t face;

      face.smoothing_group_id = current_smoothing_id;
      face.vertex_indices.reserve(3);

      size_t f_loop_max = sr.remaining() + 1;
      size_t f_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             f_loop_iter < f_loop_max) {
        vertex_index_t vi;
        if (!sr_parseTriple(sr, static_cast<int>(v.size() / 3),
                         static_cast<int>(vn.size() / 3),
                         static_cast<int>(vt.size() / 2), &vi, context)) {
          if (err) {
            (*err) += sr.format_error(filename,
                "failed to parse `f' line (invalid vertex index)");
          }
          return false;
        }

        greatest_v_idx = greatest_v_idx > vi.v_idx ? greatest_v_idx : vi.v_idx;
        greatest_vn_idx =
            greatest_vn_idx > vi.vn_idx ? greatest_vn_idx : vi.vn_idx;
        greatest_vt_idx =
            greatest_vt_idx > vi.vt_idx ? greatest_vt_idx : vi.vt_idx;

        face.vertex_indices.push_back(vi);
        sr.skip_space_and_cr();
        f_loop_iter++;
      }

      prim_group.faceGroup.push_back(face);
      sr.skip_line();
      continue;
    }

    // use mtl
    if (sr.match("usemtl", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(6);
      std::string namebuf = sr_parseString(sr);

      int newMaterialId = -1;
      std::map<std::string, int>::const_iterator it =
          material_map.find(namebuf);
      if (it != material_map.end()) {
        newMaterialId = it->second;
      } else {
        if (warn) {
          (*warn) += "material [ '" + namebuf + "' ] not found in .mtl\n";
        }
      }

      if (newMaterialId != material) {
        exportGroupsToShape(&shape, prim_group, tags, material, name,
                            triangulate, v, warn);
        prim_group.faceGroup.clear();
        material = newMaterialId;
      }

      sr.skip_line();
      continue;
    }

    // load mtl
    if (sr.match("mtllib", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      if (readMatFn) {
        sr.advance(7);

        std::string line_rest = trimTrailingWhitespace(sr.read_line());
        std::vector<std::string> filenames;
        SplitString(line_rest, ' ', '\\', filenames);
        RemoveEmptyTokens(&filenames);

        if (filenames.empty()) {
          if (warn) {
            std::stringstream ss;
            ss << "Looks like empty filename for mtllib. Use default "
                  "material (line "
               << line_num << ".)\n";

            (*warn) += ss.str();
          }
        } else {
          bool found = false;
          for (size_t s = 0; s < filenames.size(); s++) {
            if (material_filenames.count(filenames[s]) > 0) {
              found = true;
              continue;
            }

            std::string warn_mtl;
            std::string err_mtl;
            bool ok = (*readMatFn)(filenames[s].c_str(), materials,
                                   &material_map, &warn_mtl, &err_mtl);
            if (warn && (!warn_mtl.empty())) {
              (*warn) += warn_mtl;
            }

            if (err && (!err_mtl.empty())) {
              (*err) += err_mtl;
            }

            if (ok) {
              found = true;
              material_filenames.insert(filenames[s]);
              break;
            }
          }

          if (!found) {
            if (warn) {
              (*warn) +=
                  "Failed to load material file(s). Use default "
                  "material.\n";
            }
          }
        }
      }

      sr.skip_line();
      continue;
    }

    // group name
    if (sr.peek() == 'g' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      // flush previous face group.
      bool ret = exportGroupsToShape(&shape, prim_group, tags, material, name,
                                     triangulate, v, warn);
      (void)ret;

      if (shape.mesh.indices.size() > 0) {
        shapes->push_back(shape);
      }

      shape = shape_t();

      // material = -1;
      prim_group.clear();

      std::vector<std::string> names;

      size_t g_loop_max = sr.remaining() + 1;
      size_t g_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             g_loop_iter < g_loop_max) {
        std::string str = sr_parseString(sr);
        names.push_back(str);
        sr.skip_space_and_cr();
        g_loop_iter++;
      }

      // names[0] must be 'g'

      if (names.size() < 2) {
        // 'g' with empty names
        if (warn) {
          std::stringstream ss;
          ss << "Empty group name. line: " << line_num << "\n";
          (*warn) += ss.str();
          name = "";
        }
      } else {
        std::stringstream ss;
        ss << names[1];

        for (size_t i = 2; i < names.size(); i++) {
          ss << " " << names[i];
        }

        name = ss.str();
      }

      sr.skip_line();
      continue;
    }

    // object name
    if (sr.peek() == 'o' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      // flush previous face group.
      bool ret = exportGroupsToShape(&shape, prim_group, tags, material, name,
                                     triangulate, v, warn);
      (void)ret;

      if (shape.mesh.indices.size() > 0 || shape.lines.indices.size() > 0 ||
          shape.points.indices.size() > 0) {
        shapes->push_back(shape);
      }

      // material = -1;
      prim_group.clear();
      shape = shape_t();

      sr.advance(2);
      std::string rest = sr.read_line();
      name = rest;

      sr.skip_line();
      continue;
    }

    if (sr.peek() == 't' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      const int max_tag_nums = 8192;
      tag_t tag;

      sr.advance(2);

      tag.name = sr_parseString(sr);

      tag_sizes ts = sr_parseTagTriple(sr);

      if (ts.num_ints < 0) {
        ts.num_ints = 0;
      }
      if (ts.num_ints > max_tag_nums) {
        ts.num_ints = max_tag_nums;
      }

      if (ts.num_reals < 0) {
        ts.num_reals = 0;
      }
      if (ts.num_reals > max_tag_nums) {
        ts.num_reals = max_tag_nums;
      }

      if (ts.num_strings < 0) {
        ts.num_strings = 0;
      }
      if (ts.num_strings > max_tag_nums) {
        ts.num_strings = max_tag_nums;
      }

      tag.intValues.resize(static_cast<size_t>(ts.num_ints));

      for (size_t i = 0; i < static_cast<size_t>(ts.num_ints); ++i) {
        tag.intValues[i] = sr_parseInt(sr);
      }

      tag.floatValues.resize(static_cast<size_t>(ts.num_reals));
      for (size_t i = 0; i < static_cast<size_t>(ts.num_reals); ++i) {
        tag.floatValues[i] = sr_parseReal(sr);
      }

      tag.stringValues.resize(static_cast<size_t>(ts.num_strings));
      for (size_t i = 0; i < static_cast<size_t>(ts.num_strings); ++i) {
        tag.stringValues[i] = sr_parseString(sr);
      }

      tags.push_back(tag);

      sr.skip_line();
      continue;
    }

    if (sr.peek() == 's' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      // smoothing group id
      sr.advance(2);
      sr.skip_space();

      if (sr.at_line_end()) {
        sr.skip_line();
        continue;
      }

      if (sr.peek() == '\r') {
        sr.skip_line();
        continue;
      }

      if (sr.remaining() >= 3 && sr.match("off", 3)) {
        current_smoothing_id = 0;
      } else {
        int smGroupId = sr_parseInt(sr);
        if (smGroupId < 0) {
          current_smoothing_id = 0;
        } else {
          current_smoothing_id = static_cast<unsigned int>(smGroupId);
        }
      }

      sr.skip_line();
      continue;
    }

    // Ignore unknown command.
    sr.skip_line();
  }

  // not all vertices have colors, no default colors desired? -> clear colors
  if (!found_all_colors && !default_vcols_fallback) {
    vc.clear();
  }

  if (greatest_v_idx >= static_cast<int>(v.size() / 3)) {
    if (warn) {
      std::stringstream ss;
      ss << "Vertex indices out of bounds (line " << sr.line_num() << ".)\n\n";
      (*warn) += ss.str();
    }
  }
  if (greatest_vn_idx >= static_cast<int>(vn.size() / 3)) {
    if (warn) {
      std::stringstream ss;
      ss << "Vertex normal indices out of bounds (line " << sr.line_num()
         << ".)\n\n";
      (*warn) += ss.str();
    }
  }
  if (greatest_vt_idx >= static_cast<int>(vt.size() / 2)) {
    if (warn) {
      std::stringstream ss;
      ss << "Vertex texcoord indices out of bounds (line " << sr.line_num()
         << ".)\n\n";
      (*warn) += ss.str();
    }
  }

  bool ret = exportGroupsToShape(&shape, prim_group, tags, material, name,
                                 triangulate, v, warn);
  if (ret || shape.mesh.indices.size()) {
    shapes->push_back(shape);
  }
  prim_group.clear();

  attrib->vertices.swap(v);
  attrib->vertex_weights.swap(vertex_weights);
  attrib->normals.swap(vn);
  attrib->texcoords.swap(vt);
  attrib->texcoord_ws.swap(vt_w);
  attrib->colors.swap(vc);
  attrib->skin_weights.swap(vw);

  return true;
}

bool LoadObj(attrib_t *attrib, std::vector<shape_t> *shapes,
             std::vector<material_t> *materials, std::string *warn,
             std::string *err, const char *filename, const char *mtl_basedir,
             bool triangulate, bool default_vcols_fallback) {
  attrib->vertices.clear();
  attrib->vertex_weights.clear();
  attrib->normals.clear();
  attrib->texcoords.clear();
  attrib->texcoord_ws.clear();
  attrib->colors.clear();
  attrib->skin_weights.clear();
  shapes->clear();

  std::string baseDir = mtl_basedir ? mtl_basedir : "";
  if (!baseDir.empty()) {
#ifndef _WIN32
    const char dirsep = '/';
#else
    const char dirsep = '\\';
#endif
    if (baseDir[baseDir.length() - 1] != dirsep) baseDir += dirsep;
  }
  MaterialFileReader matFileReader(baseDir);

#ifdef TINYOBJLOADER_USE_MMAP
  {
    MappedFile mf;
    if (!mf.open(filename)) {
      if (err) {
        std::stringstream ss;
        ss << "Cannot open file [" << filename << "]\n";
        (*err) = ss.str();
      }
      return false;
    }
    if (mf.size > TINYOBJLOADER_STREAM_READER_MAX_BYTES) {
      if (err) {
        std::stringstream ss;
        ss << "input stream too large (" << mf.size
           << " bytes exceeds limit "
           << TINYOBJLOADER_STREAM_READER_MAX_BYTES << " bytes)\n";
        (*err) += ss.str();
      }
      return false;
    }
    StreamReader sr(mf.data, mf.size);
    return LoadObjInternal(attrib, shapes, materials, warn, err, sr,
                           &matFileReader, triangulate, default_vcols_fallback,
                           filename);
  }
#else   // !TINYOBJLOADER_USE_MMAP
#ifdef _WIN32
  std::ifstream ifs(LongPathW(UTF8ToWchar(filename)).c_str());
#else
  std::ifstream ifs(filename);
#endif
  if (!ifs) {
    if (err) {
      std::stringstream ss;
      ss << "Cannot open file [" << filename << "]\n";
      (*err) = ss.str();
    }
    return false;
  }
  {
    StreamReader sr(ifs);
    return LoadObjInternal(attrib, shapes, materials, warn, err, sr,
                           &matFileReader, triangulate, default_vcols_fallback,
                           filename);
  }
#endif  // TINYOBJLOADER_USE_MMAP
}

bool LoadObj(attrib_t *attrib, std::vector<shape_t> *shapes,
             std::vector<material_t> *materials, std::string *warn,
             std::string *err, std::istream *inStream,
             MaterialReader *readMatFn /*= NULL*/, bool triangulate,
             bool default_vcols_fallback) {
  attrib->vertices.clear();
  attrib->vertex_weights.clear();
  attrib->normals.clear();
  attrib->texcoords.clear();
  attrib->texcoord_ws.clear();
  attrib->colors.clear();
  attrib->skin_weights.clear();
  shapes->clear();

  StreamReader sr(*inStream);
  return LoadObjInternal(attrib, shapes, materials, warn, err, sr,
                         readMatFn, triangulate, default_vcols_fallback);
}


static bool LoadObjWithCallbackInternal(StreamReader &sr,
                                        const callback_t &callback,
                                        void *user_data,
                                        MaterialReader *readMatFn,
                                        std::string *warn,
                                        std::string *err) {
  if (sr.has_errors()) {
    if (err) {
      (*err) += sr.get_errors();
    }
    return false;
  }

  // material
  std::set<std::string> material_filenames;
  std::map<std::string, int> material_map;
  int material_id = -1;

  std::vector<index_t> indices;
  std::vector<material_t> materials;
  std::vector<std::string> names;
  names.reserve(2);
  std::vector<const char *> names_out;

  // Handle BOM
  if (sr.remaining() >= 3 &&
      static_cast<unsigned char>(sr.peek()) == 0xEF &&
      static_cast<unsigned char>(sr.peek_at(1)) == 0xBB &&
      static_cast<unsigned char>(sr.peek_at(2)) == 0xBF) {
    sr.advance(3);
  }

  while (!sr.eof()) {
    sr.skip_space();
    if (sr.at_line_end()) { sr.skip_line(); continue; }
    if (sr.peek() == '#') { sr.skip_line(); continue; }

    // vertex
    if (sr.peek() == 'v' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);
      real_t x, y, z;
      real_t r, g, b;

      int num_components = sr_parseVertexWithColor(&x, &y, &z, &r, &g, &b, sr);
      if (callback.vertex_cb) {
        callback.vertex_cb(user_data, x, y, z, r);
      }
      if (callback.vertex_color_cb) {
        bool found_color = (num_components == 6);
        callback.vertex_color_cb(user_data, x, y, z, r, g, b, found_color);
      }
      sr.skip_line();
      continue;
    }

    // normal
    if (sr.peek() == 'v' && sr.peek_at(1) == 'n' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(3);
      real_t x, y, z;
      sr_parseReal3(&x, &y, &z, sr);
      if (callback.normal_cb) {
        callback.normal_cb(user_data, x, y, z);
      }
      sr.skip_line();
      continue;
    }

    // texcoord
    if (sr.peek() == 'v' && sr.peek_at(1) == 't' && (sr.peek_at(2) == ' ' || sr.peek_at(2) == '\t')) {
      sr.advance(3);
      real_t x, y, z;
      sr_parseReal3(&x, &y, &z, sr);
      if (callback.texcoord_cb) {
        callback.texcoord_cb(user_data, x, y, z);
      }
      sr.skip_line();
      continue;
    }

    // face
    if (sr.peek() == 'f' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);
      sr.skip_space();

      indices.clear();
      size_t cf_loop_max = sr.remaining() + 1;
      size_t cf_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             cf_loop_iter < cf_loop_max) {
        vertex_index_t vi = sr_parseRawTriple(sr);

        index_t idx;
        idx.vertex_index = vi.v_idx;
        idx.normal_index = vi.vn_idx;
        idx.texcoord_index = vi.vt_idx;

        indices.push_back(idx);
        sr.skip_space_and_cr();
        cf_loop_iter++;
      }

      if (callback.index_cb && indices.size() > 0) {
        callback.index_cb(user_data, &indices.at(0),
                          static_cast<int>(indices.size()));
      }

      sr.skip_line();
      continue;
    }

    // use mtl
    if (sr.match("usemtl", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      sr.advance(6);
      std::string namebuf = sr_parseString(sr);

      int newMaterialId = -1;
      std::map<std::string, int>::const_iterator it =
          material_map.find(namebuf);
      if (it != material_map.end()) {
        newMaterialId = it->second;
      } else {
        if (warn && (!callback.usemtl_cb)) {
          (*warn) += "material [ " + namebuf + " ] not found in .mtl\n";
        }
      }

      if (newMaterialId != material_id) {
        material_id = newMaterialId;
      }

      if (callback.usemtl_cb) {
        callback.usemtl_cb(user_data, namebuf.c_str(), material_id);
      }

      sr.skip_line();
      continue;
    }

    // load mtl
    if (sr.match("mtllib", 6) && (sr.peek_at(6) == ' ' || sr.peek_at(6) == '\t')) {
      if (readMatFn) {
        sr.advance(7);

        std::string line_rest = trimTrailingWhitespace(sr.read_line());
        std::vector<std::string> filenames;
        SplitString(line_rest, ' ', '\\', filenames);
        RemoveEmptyTokens(&filenames);

        if (filenames.empty()) {
          if (warn) {
            (*warn) +=
                "Looks like empty filename for mtllib. Use default "
                "material. \n";
          }
        } else {
          bool found = false;
          for (size_t s = 0; s < filenames.size(); s++) {
            if (material_filenames.count(filenames[s]) > 0) {
              found = true;
              continue;
            }

            std::string warn_mtl;
            std::string err_mtl;
            bool ok = (*readMatFn)(filenames[s].c_str(), &materials,
                                   &material_map, &warn_mtl, &err_mtl);

            if (warn && (!warn_mtl.empty())) {
              (*warn) += warn_mtl;
            }

            if (err && (!err_mtl.empty())) {
              (*err) += err_mtl;
            }

            if (ok) {
              found = true;
              material_filenames.insert(filenames[s]);
              break;
            }
          }

          if (!found) {
            if (warn) {
              (*warn) +=
                  "Failed to load material file(s). Use default "
                  "material.\n";
            }
          } else {
            if (callback.mtllib_cb && !materials.empty()) {
              callback.mtllib_cb(user_data, &materials.at(0),
                                 static_cast<int>(materials.size()));
            }
          }
        }
      }

      sr.skip_line();
      continue;
    }

    // group name
    if (sr.peek() == 'g' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      names.clear();

      size_t cg_loop_max = sr.remaining() + 1;
      size_t cg_loop_iter = 0;
      while (!sr.at_line_end() && sr.peek() != '#' &&
             cg_loop_iter < cg_loop_max) {
        std::string str = sr_parseString(sr);
        names.push_back(str);
        sr.skip_space_and_cr();
        cg_loop_iter++;
      }

      assert(names.size() > 0);

      if (callback.group_cb) {
        if (names.size() > 1) {
          names_out.resize(names.size() - 1);
          for (size_t j = 0; j < names_out.size(); j++) {
            names_out[j] = names[j + 1].c_str();
          }
          callback.group_cb(user_data, &names_out.at(0),
                            static_cast<int>(names_out.size()));

        } else {
          callback.group_cb(user_data, NULL, 0);
        }
      }

      sr.skip_line();
      continue;
    }

    // object name
    if (sr.peek() == 'o' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      sr.advance(2);
      std::string object_name = sr.read_line();

      if (callback.object_cb) {
        callback.object_cb(user_data, object_name.c_str());
      }

      sr.skip_line();
      continue;
    }

#if 0  // @todo
    if (sr.peek() == 't' && (sr.peek_at(1) == ' ' || sr.peek_at(1) == '\t')) {
      tag_t tag;

      sr.advance(2);
      tag.name = sr_parseString(sr);

      tag_sizes ts = sr_parseTagTriple(sr);

      tag.intValues.resize(static_cast<size_t>(ts.num_ints));

      for (size_t i = 0; i < static_cast<size_t>(ts.num_ints); ++i) {
        tag.intValues[i] = sr_parseInt(sr);
      }

      tag.floatValues.resize(static_cast<size_t>(ts.num_reals));
      for (size_t i = 0; i < static_cast<size_t>(ts.num_reals); ++i) {
        tag.floatValues[i] = sr_parseReal(sr);
      }

      tag.stringValues.resize(static_cast<size_t>(ts.num_strings));
      for (size_t i = 0; i < static_cast<size_t>(ts.num_strings); ++i) {
        tag.stringValues[i] = sr_parseString(sr);
      }

      tags.push_back(tag);
    }
#endif

    // Ignore unknown command.
    sr.skip_line();
  }

  return true;
}

bool LoadObjWithCallback(std::istream &inStream, const callback_t &callback,
                         void *user_data /*= NULL*/,
                         MaterialReader *readMatFn /*= NULL*/,
                         std::string *warn, /* = NULL*/
                         std::string *err /*= NULL*/) {
  StreamReader sr(inStream);
  return LoadObjWithCallbackInternal(sr, callback, user_data, readMatFn,
                                     warn, err);
}

bool ObjReader::ParseFromFile(const std::string &filename,
                              const ObjReaderConfig &config) {
  std::string mtl_search_path;

  if (config.mtl_search_path.empty()) {
    //
    // split at last '/'(for unixish system) or '\\'(for windows) to get
    // the base directory of .obj file
    //
    size_t pos = filename.find_last_of("/\\");
    if (pos != std::string::npos) {
      mtl_search_path = filename.substr(0, pos);
    }
  } else {
    mtl_search_path = config.mtl_search_path;
  }

  valid_ = LoadObj(&attrib_, &shapes_, &materials_, &warning_, &error_,
                   filename.c_str(), mtl_search_path.c_str(),
                   config.triangulate, config.vertex_color);

  return valid_;
}

bool ObjReader::ParseFromString(const std::string &obj_text,
                                const std::string &mtl_text,
                                const ObjReaderConfig &config) {
  std::stringbuf obj_buf(obj_text);
  std::stringbuf mtl_buf(mtl_text);

  std::istream obj_ifs(&obj_buf);
  std::istream mtl_ifs(&mtl_buf);

  MaterialStreamReader mtl_ss(mtl_ifs);

  valid_ = LoadObj(&attrib_, &shapes_, &materials_, &warning_, &error_,
                   &obj_ifs, &mtl_ss, config.triangulate, config.vertex_color);

  return valid_;
}

// ===========================================================================
// Optimized API implementation (C++11+)
// ===========================================================================
#if __cplusplus >= 201103L || (defined(_MSC_VER) && _MSC_VER >= 1900)

// ---- ArenaAllocator implementation ----

void *ArenaAllocator::allocate(size_t bytes, size_t alignment) {
  if (bytes == 0) bytes = 1;

  // Try to allocate from current block
  if (head_) {
    size_t space = head_->capacity - head_->used;
    void *ptr = head_->data + head_->used;
    if (std::align(alignment, bytes, ptr, space)) {
      head_->used = static_cast<size_t>(static_cast<unsigned char *>(ptr) -
                                        head_->data) +
                    bytes;
      return ptr;
    }
  }

  // Need a new block
  Block *b = new_block(bytes + alignment);
  size_t space = b->capacity;
  void *ptr = b->data;
  std::align(alignment, bytes, ptr, space);
  b->used =
      static_cast<size_t>(static_cast<unsigned char *>(ptr) - b->data) + bytes;
  return ptr;
}

void ArenaAllocator::reset() { destroy(); }

ArenaAllocator::Block *ArenaAllocator::new_block(size_t min_bytes) {
  size_t cap = (min_bytes > default_block_size_) ? min_bytes
                                                 : default_block_size_;
  Block *b = new Block;
  b->data = new unsigned char[cap];
  b->capacity = cap;
  b->used = 0;
  b->next = head_;
  head_ = b;
  return b;
}

void ArenaAllocator::destroy() {
  Block *b = head_;
  while (b) {
    Block *next = b->next;
    delete[] b->data;
    delete b;
    b = next;
  }
  head_ = nullptr;
}

// ---- Optimized parser internals ----

namespace opt_internal {

static const int kOptMaxThreads = 32;

struct LineInfo {
  size_t pos;
  size_t len;
};

#define TINYOBJ_OPT_IS_SPACE(x) (((x) == ' ') || ((x) == '\t'))
#define TINYOBJ_OPT_IS_DIGIT(x) \
  (static_cast<unsigned int>((x) - '0') < static_cast<unsigned int>(10))
#define TINYOBJ_OPT_IS_NEW_LINE(x) \
  (((x) == '\r') || ((x) == '\n') || ((x) == '\0'))

static inline void opt_skip_space(const char **token) {
  while ((**token) == ' ' || (**token) == '\t') {
    (*token)++;
  }
}

static inline void opt_skip_space_and_cr(const char **token) {
  while ((**token) == ' ' || (**token) == '\t' || (**token) == '\r') {
    (*token)++;
  }
}

static inline int opt_until_space(const char *token) {
  const char *p = token;
  while (p[0] != '\0' && p[0] != ' ' && p[0] != '\t' && p[0] != '\r' &&
         p[0] != '\n') {
    p++;
  }
  return static_cast<int>(p - token);
}

static inline int opt_my_atoi(const char *c) {
  int value = 0;
  int sign = 1;
  if (*c == '+' || *c == '-') {
    if (*c == '-') sign = -1;
    c++;
  }
  while ((*c >= '0') && (*c <= '9')) {
    value *= 10;
    value += static_cast<int>(*c - '0');
    c++;
  }
  return value * sign;
}

static inline int opt_fixIndex(int idx, int n) {
  if (idx > 0) return idx - 1;
  if (idx == 0) return -1;
  return n + idx;
}

static bool opt_tryParseDouble(const char *s, const char *s_end,
                               double *result) {
  if (s >= s_end) return false;

  double mantissa = 0.0;
  int exponent = 0;
  char sign = '+';
  char exp_sign = '+';
  const char *curr = s;
  int read = 0;
  bool end_not_reached = false;
  bool has_leading_decimal = false;

  if (*curr == '+' || *curr == '-') {
    sign = *curr;
    curr++;
  }

  if (curr == s_end) return false;

  if (*curr == '.') {
    has_leading_decimal = true;
  } else if (!TINYOBJ_OPT_IS_DIGIT(*curr)) {
    return false;
  }

  end_not_reached = (curr != s_end);
  if (!has_leading_decimal) {
    while (end_not_reached && TINYOBJ_OPT_IS_DIGIT(*curr)) {
      mantissa *= 10;
      mantissa += static_cast<int>(*curr - '0');
      curr++;
      read++;
      end_not_reached = (curr != s_end);
    }
    if (read == 0) return false;
  }
  if (!end_not_reached) goto opt_assemble;

  if (*curr == '.') {
    curr++;
    end_not_reached = (curr != s_end);
    double frac_scale = 0.1;
    while (end_not_reached && TINYOBJ_OPT_IS_DIGIT(*curr)) {
      mantissa += static_cast<int>(*curr - '0') * frac_scale;
      frac_scale *= 0.1;
      read++;
      curr++;
      end_not_reached = (curr != s_end);
    }
    if (has_leading_decimal && read == 0) return false;
  } else if (*curr != 'e' && *curr != 'E') {
    goto opt_assemble;
  }

  if (!end_not_reached) goto opt_assemble;

  if (*curr == 'e' || *curr == 'E') {
    curr++;
    end_not_reached = (curr != s_end);
    if (end_not_reached && (*curr == '+' || *curr == '-')) {
      exp_sign = *curr;
      curr++;
    } else if (!TINYOBJ_OPT_IS_DIGIT(*curr)) {
      return false;
    }
    read = 0;
    end_not_reached = (curr != s_end);
    while (end_not_reached && TINYOBJ_OPT_IS_DIGIT(*curr)) {
      exponent *= 10;
      exponent += static_cast<int>(*curr - '0');
      curr++;
      read++;
      end_not_reached = (curr != s_end);
    }
    exponent *= (exp_sign == '+' ? 1 : -1);
    if (read == 0) return false;
  }

opt_assemble:
  *result = (sign == '+' ? 1.0 : -1.0) *
            (exponent ? std::ldexp(mantissa * std::pow(5.0, exponent), exponent)
                      : mantissa);
  return true;
}

static inline real_t opt_parseFloat(const char **token) {
  opt_skip_space(token);
  const char *end = (*token) + opt_until_space(*token);
  double val = 0.0;
  opt_tryParseDouble(*token, end, &val);
  real_t f = static_cast<real_t>(val);
  *token = end;
  return f;
}

static inline void opt_parseFloat3(real_t *x, real_t *y, real_t *z,
                                   const char **token) {
  *x = opt_parseFloat(token);
  *y = opt_parseFloat(token);
  *z = opt_parseFloat(token);
}

static inline void opt_parseFloat2(real_t *x, real_t *y, const char **token) {
  *x = opt_parseFloat(token);
  *y = opt_parseFloat(token);
}

struct opt_index_t {
  int vertex_index, texcoord_index, normal_index;
  opt_index_t() : vertex_index(-1), texcoord_index(-1), normal_index(-1) {}
  opt_index_t(int vi, int ti, int ni)
      : vertex_index(vi), texcoord_index(ti), normal_index(ni) {}
};

static opt_index_t opt_parseRawTriple(const char **token) {
  opt_index_t vi;
  vi.vertex_index = opt_my_atoi(*token);
  while (**token != '\0' && **token != '/' && **token != ' ' &&
         **token != '\t' && **token != '\r' && **token != '\n') {
    (*token)++;
  }
  if (**token != '/') return vi;
  (*token)++;

  if (**token == '/') {
    (*token)++;
    vi.normal_index = opt_my_atoi(*token);
    while (**token != '\0' && **token != '/' && **token != ' ' &&
           **token != '\t' && **token != '\r' && **token != '\n') {
      (*token)++;
    }
    return vi;
  }

  vi.texcoord_index = opt_my_atoi(*token);
  while (**token != '\0' && **token != '/' && **token != ' ' &&
         **token != '\t' && **token != '\r' && **token != '\n') {
    (*token)++;
  }
  if (**token != '/') return vi;
  (*token)++;
  vi.normal_index = opt_my_atoi(*token);
  while (**token != '\0' && **token != '/' && **token != ' ' &&
         **token != '\t' && **token != '\r' && **token != '\n') {
    (*token)++;
  }
  return vi;
}

static inline int opt_length_until_newline(const char *token, size_t n) {
  size_t len = 0;
  for (len = 0; len < n; len++) {
    if (token[len] == '\n') break;
    if (token[len] == '\r' && (len + 1 < n) && token[len + 1] != '\n') break;
  }
  return static_cast<int>(len);
}

enum OptCommandType {
  OPT_CMD_EMPTY,
  OPT_CMD_V,
  OPT_CMD_VN,
  OPT_CMD_VT,
  OPT_CMD_F,
  OPT_CMD_G,
  OPT_CMD_O,
  OPT_CMD_USEMTL,
  OPT_CMD_MTLLIB
};

struct OptCommand {
  real_t vx, vy, vz;
  real_t nx, ny, nz;
  real_t tx, ty;

  std::vector<opt_index_t> f;
  std::vector<int> f_num_verts;

  const char *group_name;
  unsigned int group_name_len;
  const char *object_name;
  unsigned int object_name_len;
  const char *material_name;
  unsigned int material_name_len;
  const char *mtllib_name;
  unsigned int mtllib_name_len;

  OptCommandType type;

  OptCommand()
      : vx(0), vy(0), vz(0),
        nx(0), ny(0), nz(0),
        tx(0), ty(0),
        group_name(nullptr), group_name_len(0),
        object_name(nullptr), object_name_len(0),
        material_name(nullptr), material_name_len(0),
        mtllib_name(nullptr), mtllib_name_len(0),
        type(OPT_CMD_EMPTY) {}
};

struct OptCommandCount {
  size_t num_v, num_vn, num_vt, num_f, num_indices;
  OptCommandCount() : num_v(0), num_vn(0), num_vt(0), num_f(0), num_indices(0) {}
};

static bool opt_parseLine(OptCommand *command, const char *p, size_t p_len,
                          bool triangulate) {
  // Parse directly from the original buffer without copying.
  // The caller guarantees that p[p_len] is '\n' (or a sentinel),
  // so character-scanning helpers that stop on '\n' are safe.
  const char *token = p;
  command->type = OPT_CMD_EMPTY;
  opt_skip_space(&token);

  if (TINYOBJ_OPT_IS_NEW_LINE(token[0]) || token[0] == '#') return false;

  // vertex
  if (token[0] == 'v' && TINYOBJ_OPT_IS_SPACE(token[1])) {
    token += 2;
    real_t x = 0, y = 0, z = 0;
    opt_parseFloat3(&x, &y, &z, &token);
    command->vx = x;
    command->vy = y;
    command->vz = z;
    command->type = OPT_CMD_V;
    return true;
  }

  // normal
  if (token[0] == 'v' && token[1] == 'n' && TINYOBJ_OPT_IS_SPACE(token[2])) {
    token += 3;
    real_t x = 0, y = 0, z = 0;
    opt_parseFloat3(&x, &y, &z, &token);
    command->nx = x;
    command->ny = y;
    command->nz = z;
    command->type = OPT_CMD_VN;
    return true;
  }

  // texcoord
  if (token[0] == 'v' && token[1] == 't' && TINYOBJ_OPT_IS_SPACE(token[2])) {
    token += 3;
    real_t x = 0, y = 0;
    opt_parseFloat2(&x, &y, &token);
    command->tx = x;
    command->ty = y;
    command->type = OPT_CMD_VT;
    return true;
  }

  // face
  if (token[0] == 'f' && TINYOBJ_OPT_IS_SPACE(token[1])) {
    token += 2;
    opt_skip_space(&token);

    // Collect face vertices (use small stack buffer for typical case)
    opt_index_t face_buf[8];
    int face_count = 0;

    while (!TINYOBJ_OPT_IS_NEW_LINE(token[0])) {
      opt_index_t vi = opt_parseRawTriple(&token);
      opt_skip_space_and_cr(&token);
      if (face_count < 8) {
        face_buf[face_count++] = vi;
      } else {
        if (face_count == 8) {
          command->f.reserve(16);
          for (int k = 0; k < 8; k++) command->f.push_back(face_buf[k]);
        }
        command->f.push_back(vi);
        face_count++;
      }
    }

    command->type = OPT_CMD_F;

    if (triangulate) {
      opt_index_t i0 = (face_count <= 8) ? face_buf[0] : command->f[0];
      if (face_count <= 8) {
        for (int k = 2; k < face_count; k++) {
          command->f.push_back(i0);
          command->f.push_back(face_buf[k - 1]);
          command->f.push_back(face_buf[k]);
          command->f_num_verts.push_back(3);
        }
      } else {
        std::vector<opt_index_t> orig;
        orig.swap(command->f);
        command->f.clear();
        for (size_t k = 2; k < orig.size(); k++) {
          command->f.push_back(i0);
          command->f.push_back(orig[k - 1]);
          command->f.push_back(orig[k]);
          command->f_num_verts.push_back(3);
        }
      }
    } else {
      if (face_count <= 8) {
        for (int k = 0; k < face_count; k++)
          command->f.push_back(face_buf[k]);
      }
      command->f_num_verts.push_back(face_count);
    }
    return true;
  }

  // usemtl
  if (std::strncmp(token, "usemtl", 6) == 0 &&
      TINYOBJ_OPT_IS_SPACE(token[6])) {
    token += 7;
    opt_skip_space(&token);
    command->material_name = token;
    command->material_name_len = static_cast<unsigned int>(
        opt_length_until_newline(token,
                                p_len - static_cast<size_t>(token - p)));
    command->type = OPT_CMD_USEMTL;
    return true;
  }

  // mtllib
  if (std::strncmp(token, "mtllib", 6) == 0 &&
      TINYOBJ_OPT_IS_SPACE(token[6])) {
    token += 7;
    opt_skip_space(&token);
    command->mtllib_name = token;
    command->mtllib_name_len = static_cast<unsigned int>(
        opt_length_until_newline(token,
                                p_len - static_cast<size_t>(token - p)));
    command->type = OPT_CMD_MTLLIB;
    return true;
  }

  // group
  if (token[0] == 'g' && TINYOBJ_OPT_IS_SPACE(token[1])) {
    token += 2;
    command->group_name = token;
    command->group_name_len = static_cast<unsigned int>(
        opt_length_until_newline(token,
                                p_len - static_cast<size_t>(token - p)));
    command->type = OPT_CMD_G;
    return true;
  }

  // object
  if (token[0] == 'o' && TINYOBJ_OPT_IS_SPACE(token[1])) {
    token += 2;
    command->object_name = token;
    command->object_name_len = static_cast<unsigned int>(
        opt_length_until_newline(token,
                                p_len - static_cast<size_t>(token - p)));
    command->type = OPT_CMD_O;
    return true;
  }

  return false;
}

static inline bool opt_is_line_ending(const char *p, size_t i, size_t end_i) {
  if (p[i] == '\0') return true;
  if (p[i] == '\n') return true;
  if (p[i] == '\r') {
    if (((i + 1) < end_i) && (p[i + 1] != '\n')) return true;
  }
  return false;
}

// ---- SIMD newline scanning ----

#ifdef TINYOBJLOADER_USE_SIMD

// Portable count-trailing-zeros for SIMD bitmask extraction
static inline unsigned int tinyobj_ctz(unsigned int x) {
#if defined(_MSC_VER)
  unsigned long idx;
  _BitScanForward(&idx, x);
  return static_cast<unsigned int>(idx);
#else
  return static_cast<unsigned int>(__builtin_ctz(x));
#endif
}

#if defined(TINYOBJLOADER_SIMD_AVX2)

/// AVX2-accelerated newline scanning — finds '\n' positions in a buffer.
static void simd_find_newlines(const char *buf, size_t len,
                               std::vector<size_t> &positions) {
  const __m256i nl = _mm256_set1_epi8('\n');
  size_t i = 0;
  for (; i + 32 <= len; i += 32) {
    __m256i chunk =
        _mm256_loadu_si256(reinterpret_cast<const __m256i *>(buf + i));
    __m256i cmp = _mm256_cmpeq_epi8(chunk, nl);
    unsigned int mask = static_cast<unsigned int>(_mm256_movemask_epi8(cmp));
    while (mask) {
      unsigned int bit = tinyobj_ctz(mask);
      positions.push_back(i + bit);
      mask &= mask - 1;
    }
  }
  // Scalar tail
  for (; i < len; i++) {
    if (buf[i] == '\n') positions.push_back(i);
  }
}

#elif defined(TINYOBJLOADER_SIMD_SSE2)

/// SSE2-accelerated newline scanning — finds '\n' positions in a buffer.
static void simd_find_newlines(const char *buf, size_t len,
                               std::vector<size_t> &positions) {
  const __m128i nl = _mm_set1_epi8('\n');
  size_t i = 0;
  for (; i + 16 <= len; i += 16) {
    __m128i chunk =
        _mm_loadu_si128(reinterpret_cast<const __m128i *>(buf + i));
    __m128i cmp = _mm_cmpeq_epi8(chunk, nl);
    int mask = _mm_movemask_epi8(cmp);
    while (mask) {
      int bit = static_cast<int>(tinyobj_ctz(static_cast<unsigned int>(mask)));
      positions.push_back(i + static_cast<size_t>(bit));
      mask &= mask - 1;
    }
  }
  // Scalar tail
  for (; i < len; i++) {
    if (buf[i] == '\n') positions.push_back(i);
  }
}

#elif defined(TINYOBJLOADER_SIMD_NEON)

/// NEON-accelerated newline scanning — finds '\n' positions in a buffer.
static void simd_find_newlines(const char *buf, size_t len,
                               std::vector<size_t> &positions) {
  const uint8x16_t nl = vdupq_n_u8('\n');
  size_t i = 0;
  for (; i + 16 <= len; i += 16) {
    uint8x16_t chunk = vld1q_u8(reinterpret_cast<const uint8_t *>(buf + i));
    uint8x16_t cmp = vceqq_u8(chunk, nl);
    // Extract results byte-by-byte (NEON lacks movemask).
    // We rotate the comparison result left by 1 each iteration,
    // so lane 0 always holds the result for the current byte.
    for (int j = 0; j < 16; j++) {
      if (vgetq_lane_u8(cmp, 0) != 0) {
        positions.push_back(i + static_cast<size_t>(j));
      }
      cmp = vextq_u8(cmp, cmp, 1);  // Rotate
    }
  }
  for (; i < len; i++) {
    if (buf[i] == '\n') positions.push_back(i);
  }
}

#endif  // SIMD variant

/// Build LineInfo array from SIMD-detected newline positions
static void simd_build_line_infos(const char *buf, size_t len,
                                  const std::vector<size_t> &nl_positions,
                                  std::vector<LineInfo> &out) {
  out.reserve(nl_positions.size() + 1);
  size_t prev = 0;
  for (size_t k = 0; k < nl_positions.size(); k++) {
    size_t pos = nl_positions[k];
    size_t line_len = pos - prev;
    // Skip \r before \n
    if (line_len > 0 && buf[prev + line_len - 1] == '\r') line_len--;
    if (line_len > 0) {
      LineInfo info;
      info.pos = prev;
      info.len = line_len;
      out.push_back(info);
    }
    prev = pos + 1;
  }
  // Handle last line without trailing newline
  if (prev < len) {
    size_t line_len = len - prev;
    if (line_len > 0 && buf[prev + line_len - 1] == '\r') line_len--;
    if (line_len > 0) {
      LineInfo info;
      info.pos = prev;
      info.len = line_len;
      out.push_back(info);
    }
  }
}

#endif  // TINYOBJLOADER_USE_SIMD

/// Scalar fallback newline scanning
static void scalar_find_line_infos(const char *buf, size_t start, size_t end,
                                   std::vector<LineInfo> &out) {
  size_t prev = start;
  for (size_t i = start; i < end; i++) {
    if (buf[i] == '\n') {
      size_t line_len = i - prev;
      if (line_len > 0 && buf[prev + line_len - 1] == '\r') line_len--;
      if (line_len > 0) {
        LineInfo info;
        info.pos = prev;
        info.len = line_len;
        out.push_back(info);
      }
      prev = i + 1;
    }
  }
  if (prev < end) {
    size_t line_len = end - prev;
    if (line_len > 0 && buf[prev + line_len - 1] == '\r') line_len--;
    if (line_len > 0) {
      LineInfo info;
      info.pos = prev;
      info.len = line_len;
      out.push_back(info);
    }
  }
}

}  // namespace opt_internal

// ---- LoadObjOpt (buffer version) ----

bool LoadObjOpt(basic_attrib_t<> *attrib,
                std::vector<basic_shape_t<>> *shapes,
                std::vector<material_t> *materials,
                std::string *warn, std::string *err,
                const char *buf, size_t buf_len,
                const OptLoadConfig &config) {
  using namespace opt_internal;

  if (!attrib || !shapes) {
    if (err) *err = "attrib and shapes must not be null.";
    return false;
  }

  attrib->vertices.clear();
  attrib->normals.clear();
  attrib->texcoords.clear();
  attrib->colors.clear();
  attrib->indices.clear();
  attrib->face_num_verts.clear();
  attrib->material_ids.clear();
  shapes->clear();
  if (materials) materials->clear();

  if (buf_len < 1) return true;  // empty buffer is not an error

  // Ensure buffer ends with a newline for safe tokenization (avoids
  // one-byte over-read on the last line when parsing directly from the
  // buffer without per-line copies).
  const char *work_buf = buf;
  size_t work_len = buf_len;
  std::vector<char> buf_with_sentinel;
  if (buf[buf_len - 1] != '\n') {
    buf_with_sentinel.assign(buf, buf + buf_len);
    buf_with_sentinel.push_back('\n');
    work_buf = buf_with_sentinel.data();
    work_len = buf_with_sentinel.size();
  }

  // Determine thread count
  int num_threads = 1;
#ifdef TINYOBJLOADER_USE_MULTITHREADING
  if (config.num_threads < 0) {
    num_threads = static_cast<int>(std::thread::hardware_concurrency());
    if (num_threads < 1) num_threads = 1;
  } else if (config.num_threads > 1) {
    num_threads = config.num_threads;
  }
  if (num_threads > kOptMaxThreads) num_threads = kOptMaxThreads;
#else
  (void)config;
#endif

  // ---- Phase 1: find line boundaries ----
  std::vector<LineInfo> all_line_infos;

#if defined(TINYOBJLOADER_USE_SIMD) && \
    (defined(TINYOBJLOADER_SIMD_SSE2) || defined(TINYOBJLOADER_SIMD_AVX2) || \
     defined(TINYOBJLOADER_SIMD_NEON))
  {
    std::vector<size_t> nl_positions;
    nl_positions.reserve(work_len / 64);
    simd_find_newlines(work_buf, work_len, nl_positions);
    simd_build_line_infos(work_buf, work_len, nl_positions, all_line_infos);
  }
#else
  {
    all_line_infos.reserve(work_len / 64);
    scalar_find_line_infos(work_buf, 0, work_len, all_line_infos);
  }
#endif

  const size_t total_lines = all_line_infos.size();
  if (total_lines == 0) return true;

  // ---- Phase 2: parse lines ----
  //   Single-threaded or multi-threaded depending on compile option.

#ifdef TINYOBJLOADER_USE_MULTITHREADING
  // Multi-threaded path
  std::vector<std::vector<OptCommand>> thread_commands(
      static_cast<size_t>(num_threads));
  std::vector<OptCommandCount> thread_counts(
      static_cast<size_t>(num_threads));
  int mtllib_t = -1, mtllib_i = -1;

  {
    size_t lines_per_thread = total_lines / static_cast<size_t>(num_threads);
    std::vector<std::thread> workers;
    workers.reserve(static_cast<size_t>(num_threads));

    for (int t = 0; t < num_threads; t++) {
      size_t start = static_cast<size_t>(t) * lines_per_thread;
      size_t end = (t == num_threads - 1)
                       ? total_lines
                       : (static_cast<size_t>(t) + 1) * lines_per_thread;

      workers.emplace_back([&, t, start, end]() {
        thread_commands[static_cast<size_t>(t)].reserve(end - start);
        for (size_t i = start; i < end; i++) {
          OptCommand cmd;
          bool ok = opt_parseLine(&cmd, &work_buf[all_line_infos[i].pos],
                                  all_line_infos[i].len, config.triangulate);
          if (ok) {
            if (cmd.type == OPT_CMD_V)
              thread_counts[static_cast<size_t>(t)].num_v++;
            else if (cmd.type == OPT_CMD_VN)
              thread_counts[static_cast<size_t>(t)].num_vn++;
            else if (cmd.type == OPT_CMD_VT)
              thread_counts[static_cast<size_t>(t)].num_vt++;
            else if (cmd.type == OPT_CMD_F) {
              thread_counts[static_cast<size_t>(t)].num_f += cmd.f.size();
              thread_counts[static_cast<size_t>(t)].num_indices +=
                  cmd.f_num_verts.size();
            }
            if (cmd.type == OPT_CMD_MTLLIB) {
              mtllib_t = t;
              mtllib_i =
                  static_cast<int>(thread_commands[static_cast<size_t>(t)].size());
            }
            thread_commands[static_cast<size_t>(t)].emplace_back(
                std::move(cmd));
          }
        }
      });
    }
    for (auto &w : workers) w.join();
  }

#else
  // Single-threaded path
  const int num_threads_actual = 1;
  std::vector<std::vector<OptCommand>> thread_commands(1);
  std::vector<OptCommandCount> thread_counts(1);
  int mtllib_t = -1, mtllib_i = -1;

  {
    thread_commands[0].reserve(total_lines);
    for (size_t i = 0; i < total_lines; i++) {
      OptCommand cmd;
      bool ok = opt_parseLine(&cmd, &work_buf[all_line_infos[i].pos],
                              all_line_infos[i].len, config.triangulate);
      if (ok) {
        if (cmd.type == OPT_CMD_V)
          thread_counts[0].num_v++;
        else if (cmd.type == OPT_CMD_VN)
          thread_counts[0].num_vn++;
        else if (cmd.type == OPT_CMD_VT)
          thread_counts[0].num_vt++;
        else if (cmd.type == OPT_CMD_F) {
          thread_counts[0].num_f += cmd.f.size();
          thread_counts[0].num_indices += cmd.f_num_verts.size();
        }
        if (cmd.type == OPT_CMD_MTLLIB) {
          mtllib_t = 0;
          mtllib_i = static_cast<int>(thread_commands[0].size());
        }
        thread_commands[0].emplace_back(std::move(cmd));
      }
    }
  }
  (void)num_threads_actual;
#endif

  // ---- Phase 3: load materials ----
  std::map<std::string, int> material_map;
  if (mtllib_t >= 0 && mtllib_i >= 0 && materials) {
    const OptCommand &mtl_cmd =
        thread_commands[static_cast<size_t>(mtllib_t)][static_cast<size_t>(
            mtllib_i)];
    if (mtl_cmd.mtllib_name && mtl_cmd.mtllib_name_len > 0) {
      std::string mtl_filename(mtl_cmd.mtllib_name, mtl_cmd.mtllib_name_len);
      while (!mtl_filename.empty() &&
             (mtl_filename.back() == '\r' || mtl_filename.back() == '\n'))
        mtl_filename.pop_back();

      std::ifstream ifs(mtl_filename);
      if (ifs.good()) {
        LoadMtl(&material_map, materials, &ifs, warn, err);
        ifs.close();
      }
    }
  }

  // ---- Phase 4: merge results ----
  size_t num_v = 0, num_vn = 0, num_vt = 0, num_f = 0, num_indices = 0;
  const size_t num_t = thread_commands.size();
  for (size_t t = 0; t < num_t; t++) {
    num_v += thread_counts[t].num_v;
    num_vn += thread_counts[t].num_vn;
    num_vt += thread_counts[t].num_vt;
    num_f += thread_counts[t].num_f;
    num_indices += thread_counts[t].num_indices;
  }

  attrib->vertices.resize(num_v * 3);
  attrib->normals.resize(num_vn * 3);
  attrib->texcoords.resize(num_vt * 2);
  attrib->indices.resize(num_f);
  attrib->face_num_verts.resize(static_cast<size_t>(num_indices));
  attrib->material_ids.resize(static_cast<size_t>(num_indices), -1);

  // Compute per-thread offsets
  std::vector<size_t> v_off(num_t), n_off(num_t), t_off(num_t), f_off(num_t),
      face_off(num_t);
  v_off[0] = n_off[0] = t_off[0] = f_off[0] = face_off[0] = 0;
  for (size_t t = 1; t < num_t; t++) {
    v_off[t] = v_off[t - 1] + thread_counts[t - 1].num_v;
    n_off[t] = n_off[t - 1] + thread_counts[t - 1].num_vn;
    t_off[t] = t_off[t - 1] + thread_counts[t - 1].num_vt;
    f_off[t] = f_off[t - 1] + thread_counts[t - 1].num_f;
    face_off[t] = face_off[t - 1] + thread_counts[t - 1].num_indices;
  }

  // Merge parsed data into final arrays
  auto merge_thread = [&](size_t t) {
    size_t vc = v_off[t], nc = n_off[t], tc = t_off[t];
    size_t fc = f_off[t], fcc = face_off[t];

    for (size_t i = 0; i < thread_commands[t].size(); i++) {
      const OptCommand &cmd = thread_commands[t][i];
      switch (cmd.type) {
        case OPT_CMD_V:
          attrib->vertices[3 * vc + 0] = cmd.vx;
          attrib->vertices[3 * vc + 1] = cmd.vy;
          attrib->vertices[3 * vc + 2] = cmd.vz;
          vc++;
          break;
        case OPT_CMD_VN:
          attrib->normals[3 * nc + 0] = cmd.nx;
          attrib->normals[3 * nc + 1] = cmd.ny;
          attrib->normals[3 * nc + 2] = cmd.nz;
          nc++;
          break;
        case OPT_CMD_VT:
          attrib->texcoords[2 * tc + 0] = cmd.tx;
          attrib->texcoords[2 * tc + 1] = cmd.ty;
          tc++;
          break;
        case OPT_CMD_F:
          for (size_t k = 0; k < cmd.f.size(); k++) {
            const opt_index_t &vi = cmd.f[k];
            index_t idx;
            idx.vertex_index =
                opt_fixIndex(vi.vertex_index, static_cast<int>(vc));
            idx.texcoord_index =
                opt_fixIndex(vi.texcoord_index, static_cast<int>(tc));
            idx.normal_index =
                opt_fixIndex(vi.normal_index, static_cast<int>(nc));
            attrib->indices[fc + k] = idx;
          }
          for (size_t k = 0; k < cmd.f_num_verts.size(); k++) {
            attrib->face_num_verts[fcc + k] = cmd.f_num_verts[k];
          }
          fc += cmd.f.size();
          fcc += cmd.f_num_verts.size();
          break;
        case OPT_CMD_USEMTL:
          if (cmd.material_name && cmd.material_name_len > 0 &&
              fcc < num_indices) {
            std::string mat_name(cmd.material_name, cmd.material_name_len);
            while (!mat_name.empty() &&
                   (mat_name.back() == '\r' || mat_name.back() == '\n'))
              mat_name.pop_back();
            auto it = material_map.find(mat_name);
            int mat_id = (it != material_map.end()) ? it->second : -2;
            // Assign to next face's material slots
            // Look ahead for next face command
            for (size_t ii = i + 1; ii < thread_commands[t].size(); ii++) {
              if (thread_commands[t][ii].type == OPT_CMD_F) {
                for (size_t k = 0;
                     k < thread_commands[t][ii].f_num_verts.size(); k++) {
                  if (fcc + k < num_indices) {
                    attrib->material_ids[fcc + k] = mat_id;
                  }
                }
                break;
              }
            }
          }
          break;
        default:
          break;
      }
    }
  };

#ifdef TINYOBJLOADER_USE_MULTITHREADING
  if (num_threads > 1) {
    std::vector<std::thread> workers;
    workers.reserve(num_t);
    for (size_t t = 0; t < num_t; t++) {
      workers.emplace_back([&, t]() { merge_thread(t); });
    }
    for (auto &w : workers) w.join();
  } else {
    for (size_t t = 0; t < num_t; t++) merge_thread(t);
  }
#else
  for (size_t t = 0; t < num_t; t++) merge_thread(t);
#endif

  // Propagate material IDs forward
  for (size_t i = 1; i < num_indices; i++) {
    if (attrib->material_ids[i] == -1)
      attrib->material_ids[i] = attrib->material_ids[i - 1];
  }

  // ---- Phase 5: construct shapes ----
  {
    size_t face_count = 0;
    basic_shape_t<> shape;
    size_t face_prev_offset = 0;

    for (size_t t = 0; t < num_t; t++) {
      for (size_t i = 0; i < thread_commands[t].size(); i++) {
        if (thread_commands[t][i].type == OPT_CMD_O ||
            thread_commands[t][i].type == OPT_CMD_G) {
          std::string name;
          const OptCommand &cmd = thread_commands[t][i];
          if (cmd.type == OPT_CMD_O && cmd.object_name) {
            name.assign(cmd.object_name, cmd.object_name_len);
          } else if (cmd.group_name) {
            name.assign(cmd.group_name, cmd.group_name_len);
          }
          while (!name.empty() &&
                 (name.back() == '\r' || name.back() == '\n'))
            name.pop_back();

          if (face_count == 0) {
            shape.name = name;
            face_prev_offset = 0;
          } else {
            if (shapes->empty()) {
              // faces before first group/object
              basic_shape_t<> prev_shape;
              prev_shape.mesh.num_face_vertices.assign(
                  attrib->face_num_verts.begin(),
                  attrib->face_num_verts.begin() +
                      static_cast<std::ptrdiff_t>(face_count));
              // Copy corresponding indices
              size_t idx_count = 0;
              for (size_t fi = 0; fi < face_count; fi++)
                idx_count +=
                    static_cast<size_t>(attrib->face_num_verts[fi]);
              prev_shape.mesh.indices.assign(
                  attrib->indices.begin(),
                  attrib->indices.begin() +
                      static_cast<std::ptrdiff_t>(idx_count));
              prev_shape.mesh.material_ids.assign(
                  attrib->material_ids.begin(),
                  attrib->material_ids.begin() +
                      static_cast<std::ptrdiff_t>(face_count));
              shapes->push_back(std::move(prev_shape));
            } else if (face_count > face_prev_offset) {
              // push previous shape
              basic_shape_t<> prev_shape;
              prev_shape.name = shape.name;
              size_t idx_start = 0;
              for (size_t fi = 0; fi < face_prev_offset; fi++)
                idx_start +=
                    static_cast<size_t>(attrib->face_num_verts[fi]);
              size_t idx_end = idx_start;
              for (size_t fi = face_prev_offset; fi < face_count; fi++)
                idx_end +=
                    static_cast<size_t>(attrib->face_num_verts[fi]);
              prev_shape.mesh.num_face_vertices.assign(
                  attrib->face_num_verts.begin() +
                      static_cast<std::ptrdiff_t>(face_prev_offset),
                  attrib->face_num_verts.begin() +
                      static_cast<std::ptrdiff_t>(face_count));
              prev_shape.mesh.indices.assign(
                  attrib->indices.begin() +
                      static_cast<std::ptrdiff_t>(idx_start),
                  attrib->indices.begin() +
                      static_cast<std::ptrdiff_t>(idx_end));
              prev_shape.mesh.material_ids.assign(
                  attrib->material_ids.begin() +
                      static_cast<std::ptrdiff_t>(face_prev_offset),
                  attrib->material_ids.begin() +
                      static_cast<std::ptrdiff_t>(face_count));
              shapes->push_back(std::move(prev_shape));
            }
            shape.name = name;
            face_prev_offset = face_count;
          }
        }
        if (thread_commands[t][i].type == OPT_CMD_F) {
          face_count += thread_commands[t][i].f_num_verts.size();
        }
      }
    }

    // Final shape
    if (face_count > face_prev_offset) {
      basic_shape_t<> final_shape;
      final_shape.name = shape.name;
      size_t idx_start = 0;
      for (size_t fi = 0; fi < face_prev_offset; fi++)
        idx_start += static_cast<size_t>(attrib->face_num_verts[fi]);
      size_t idx_end = idx_start;
      for (size_t fi = face_prev_offset; fi < face_count; fi++)
        idx_end += static_cast<size_t>(attrib->face_num_verts[fi]);
      final_shape.mesh.num_face_vertices.assign(
          attrib->face_num_verts.begin() +
              static_cast<std::ptrdiff_t>(face_prev_offset),
          attrib->face_num_verts.begin() +
              static_cast<std::ptrdiff_t>(face_count));
      final_shape.mesh.indices.assign(
          attrib->indices.begin() + static_cast<std::ptrdiff_t>(idx_start),
          attrib->indices.begin() + static_cast<std::ptrdiff_t>(idx_end));
      final_shape.mesh.material_ids.assign(
          attrib->material_ids.begin() +
              static_cast<std::ptrdiff_t>(face_prev_offset),
          attrib->material_ids.begin() +
              static_cast<std::ptrdiff_t>(face_count));
      shapes->push_back(std::move(final_shape));
    }
  }

  return true;
}

// ---- LoadObjOpt (file version) ----

bool LoadObjOpt(basic_attrib_t<> *attrib,
                std::vector<basic_shape_t<>> *shapes,
                std::vector<material_t> *materials,
                std::string *warn, std::string *err,
                const char *filename,
                const char *mtl_basedir,
                const OptLoadConfig &config) {
  if (!filename) {
    if (err) *err = "filename is null.";
    return false;
  }

  std::string filepath(filename);
  std::ifstream ifs(filepath, std::ios::binary | std::ios::ate);
  if (!ifs.is_open()) {
    if (err) *err = "Cannot open file: " + filepath;
    return false;
  }

  std::streamsize fsize = ifs.tellg();
  ifs.seekg(0, std::ios::beg);

  if (fsize <= 0) {
    return true;  // empty file
  }

  std::vector<char> buf(static_cast<size_t>(fsize));
  if (!ifs.read(buf.data(), fsize)) {
    if (err) *err = "Failed to read file: " + filepath;
    return false;
  }
  ifs.close();

  // Resolve material base directory
  std::string baseDir;
  if (mtl_basedir) {
    baseDir = mtl_basedir;
  } else {
    // Extract directory from filename
    size_t pos = filepath.find_last_of("/\\");
    if (pos != std::string::npos) {
      baseDir = filepath.substr(0, pos + 1);
    }
  }
  if (!baseDir.empty()) {
#ifndef _WIN32
    const char dirsep = '/';
#else
    const char dirsep = '\\';
#endif
    if (baseDir[baseDir.length() - 1] != dirsep) baseDir += dirsep;
  }

  // Parse the buffer; material loading happens inside LoadObjOpt(buffer).
  // We need to set up the mtl base dir for internal material loading.
  // For now, we directly parse the buffer and handle mtl path resolution
  // by pre-scanning for mtllib and adjusting the buffer approach.
  //
  // The buffer-based LoadObjOpt loads mtllib files using the filename as-is.
  // To support mtl_basedir, we use MaterialFileReader for proper path search.
  bool ret = LoadObjOpt(attrib, shapes, materials, warn, err, buf.data(),
                        static_cast<size_t>(fsize), config);

  // If materials weren't loaded by the buffer path (mtllib path may need
  // base dir), try loading via MaterialFileReader as a fallback.
  if (ret && materials && materials->empty()) {
    // Scan buffer for mtllib directive
    std::string mtl_filename;
    const char *p = buf.data();
    const char *end_p = p + fsize;
    while (p < end_p) {
      while (p < end_p && (*p == ' ' || *p == '\t')) p++;
      if (p + 7 < end_p && std::strncmp(p, "mtllib", 6) == 0 &&
          (p[6] == ' ' || p[6] == '\t')) {
        p += 7;
        while (p < end_p && (*p == ' ' || *p == '\t')) p++;
        const char *name_start = p;
        while (p < end_p && *p != '\n' && *p != '\r') p++;
        mtl_filename.assign(name_start, p);
        while (!mtl_filename.empty() &&
               (mtl_filename.back() == ' ' || mtl_filename.back() == '\t'))
          mtl_filename.pop_back();
        break;
      }
      while (p < end_p && *p != '\n') p++;
      if (p < end_p) p++;
    }

    if (!mtl_filename.empty() && !baseDir.empty()) {
      std::map<std::string, int> matMap;
      std::string mtl_path = baseDir + mtl_filename;
      std::ifstream mtl_ifs(mtl_path);
      if (mtl_ifs.good()) {
        LoadMtl(&matMap, materials, &mtl_ifs, warn, err);
      }
    }
  }

  return ret;
}

#endif  // C++11 optimized API

#ifdef __clang__
#pragma clang diagnostic pop
#endif
}  // namespace tinyobj

#endif
