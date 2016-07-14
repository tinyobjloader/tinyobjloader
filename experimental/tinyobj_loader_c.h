/*
The MIT License (MIT)

Copyright (c) 2016 Syoyo Fujita and many contributors.

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
#ifndef TINOBJ_LOADER_C_H_
#define TINOBJ_LOADER_C_H_

#ifdef _WIN64
#define atoll(S) _atoi64(S)
#include <windows.h>
#else
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <unistd.h>
#endif

#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  const char* name;

  float ambient[3];
  float diffuse[3];
  float specular[3];
  float transmittance[3];
  float emission[3];
  float shininess;
  float ior;       /* index of refraction */
  float dissolve;  /* 1 == opaque; 0 == fully transparent */
  /* illumination model (see http://www.fileformat.info/format/material/) */
  int illum;

  const char* ambient_texname;             /* map_Ka */
  const char* diffuse_texname;             /* map_Kd */
  const char* specular_texname;            /* map_Ks */
  const char* specular_highlight_texname;  /* map_Ns */
  const char* bump_texname;                /* map_bump, bump */
  const char* displacement_texname;        /* disp */
  const char* alpha_texname;               /* map_d */
} tinyobj_material_t;

typedef struct {
  const char* name;  /* group name or object name. */
  unsigned int face_offset;
  unsigned int length;
} tinyobj_shape_t;

typedef struct {
  int v_idx, vt_idx, vn_idx;
} tinyobj_vertex_index_t;

typedef struct {
  float* vertices;
  unsigned int num_vertices;
  float* normals;
  unsigned int num_normals;
  float* texcoords;
  unsigned int num_texcoords;
  tinyobj_vertex_index_t *faces;
  unsigned int num_faces;
  int *face_num_verts;
  unsigned int num_face_num_verts; 
  int *material_ids;
} tinyobj_attrib_t;

#define TINYOBJ_FLAG_TRIANGULATE  (1 << 0)
#define TINYOBJ_SUCCESS (0)
#define TINYOBJ_ERROR_EMPTY (-1)
#define TINYOBJ_ERROR_INVALID_PARAMETER (-2)

/* Parse wavefront .obj(.obj string data is expanded to linear char array `buf')
 * flags are combination of TINYOBJ_FLAG_***
 * Retruns TINYOBJ_SUCCESS if things goes well.
 * Retruns TINYOBJ_ERR_*** when there is an error.
 */
extern int tinyobj_parse(tinyobj_attrib_t *attrib, tinyobj_shape_t *shapes, size_t *num_shapes, const char *buf, size_t len, unsigned int flags);


#ifdef TINYOBJ_LOADER_C_IMPLEMENTATION

#define TINYOBJ_MAX_FACES_PER_F_LINE	(32)

#define IS_SPACE(x) (((x) == ' ') || ((x) == '\t'))
#define IS_DIGIT(x) \
  ((unsigned int)((x) - '0') < (unsigned int)(10))
#define IS_NEW_LINE(x) (((x) == '\r') || ((x) == '\n') || ((x) == '\0'))

static void skip_space(const char **token) {
  while ((*token)[0] == ' ' || (*token)[0] == '\t') {
    (*token)++;
  }
}

static void skip_space_and_cr(const char **token) {
  while ((*token)[0] == ' ' || (*token)[0] == '\t' || (*token)[0] == '\r') {
    (*token)++;
  }
}

static int until_space(const char *token) {
  const char *p = token;
  while (p[0] != '\0' && p[0] != ' ' && p[0] != '\t' && p[0] != '\r') {
    p++;
  }

  return (int)(p - token);
}

static int length_until_newline(const char *token, int n) {
  int len = 0;

  /* Assume token[n-1] = '\0' */
  for (len = 0; len < n - 1; len++) {
    if (token[len] == '\n') {
      break;
    }
    if ((token[len] == '\r') && ((len < (n - 2)) && (token[len + 1] != '\n'))) {
      break;
    }
  }

  return len;
}

/* http://stackoverflow.com/questions/5710091/how-does-atoi-function-in-c-work */
static int my_atoi(const char *c) {
  int value = 0;
  int sign = 1;
  if (*c == '+' || *c == '-') {
    if (*c == '-') sign = -1;
    c++;
  }
  while (((*c) >= '0') && ((*c) <= '9')) {  /* isdigit(*c) */
    value *= 10;
    value += (int)(*c - '0');
    c++;
  }
  return value * sign;
}

/* Make index zero-base, and also support relative index. */
static int fixIndex(int idx, int n) {
  if (idx > 0) return idx - 1;
  if (idx == 0) return 0;
  return n + idx;  /* negative value = relative */
}

/* Parse raw triples: i, i/j/k, i//k, i/j */
static tinyobj_vertex_index_t parseRawTriple(const char **token) {
  tinyobj_vertex_index_t vi;
  /* 0x80000000 = -2147483648 = invalid */
  vi.v_idx = (int)(0x80000000);
  vi.vn_idx = (int)(0x80000000);
  vi.vt_idx = (int)(0x80000000);

  vi.v_idx = my_atoi((*token));
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' &&
         (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }
  (*token)++;

  /* i//k */
  if ((*token)[0] == '/') {
    (*token)++;
    vi.vn_idx = my_atoi((*token));
    while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' &&
           (*token)[0] != '\t' && (*token)[0] != '\r') {
      (*token)++;
    }
    return vi;
  }

  /* i/j/k or i/j */
  vi.vt_idx = my_atoi((*token));
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' &&
         (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }

  /* i/j/k */
  (*token)++;  /* skip '/' */
  vi.vn_idx = my_atoi((*token));
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' &&
         (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  return vi;
}

/* assume `s' has enough storage spage to store parsed string. */
static void parseString(char *s, int *n, const char **token) {
  int e = 0;
  skip_space(token);                 
  e = until_space((*token));
  memcpy(s, (*token), e);
  (*n) = e;
  (*token) += e;
}

static int parseInt(const char **token) {
  int i = 0;
  skip_space(token); 
  i = my_atoi((*token));
  (*token) += until_space((*token));
  return i;
}

/*
 * Tries to parse a floating point number located at s.
 *
 * s_end should be a location in the string where reading should absolutely
 * stop. For example at the end of the string, to prevent buffer overflows.
 *
 * Parses the following EBNF grammar:
 *   sign    = "+" | "-" ;
 *   END     = ? anything not in digit ?
 *   digit   = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
 *   integer = [sign] , digit , {digit} ;
 *   decimal = integer , ["." , integer] ;
 *   float   = ( decimal , END ) | ( decimal , ("E" | "e") , integer , END ) ;
 *
 *  Valid strings are for example:
 *   -0  +3.1417e+2  -0.0E-3  1.0324  -1.41   11e2
 *
 * If the parsing is a success, result is set to the parsed value and true
 * is returned.
 *
 * The function is greedy and will parse until any of the following happens:
 *  - a non-conforming character is encountered.
 *  - s_end is reached.
 *
 * The following situations triggers a failure:
 *  - s >= s_end.
 *  - parse failure.
 */
static int tryParseDouble(const char *s, const char *s_end, double *result) {
  double mantissa = 0.0;
  /* This exponent is base 2 rather than 10.
   * However the exponent we parse is supposed to be one of ten,
   * thus we must take care to convert the exponent/and or the
   * mantissa to a * 2^E, where a is the mantissa and E is the
   * exponent.
   * To get the final double we will use ldexp, it requires the
   * exponent to be in base 2.
   */
  int exponent = 0;

  /* NOTE: THESE MUST BE DECLARED HERE SINCE WE ARE NOT ALLOWED
   * TO JUMP OVER DEFINITIONS.
   */
  char sign = '+';
  char exp_sign = '+';
  char const *curr = s;

  /* How many characters were read in a loop. */
  int read = 0;
  /* Tells whether a loop terminated due to reaching s_end. */
  int end_not_reached = 0;

  /*
          BEGIN PARSING.
  */

  if (s >= s_end) {
    return 0; /* fail */
  }

  /* Find out what sign we've got. */
  if (*curr == '+' || *curr == '-') {
    sign = *curr;
    curr++;
  } else if (IS_DIGIT(*curr)) { /* Pass through. */
  } else {
    goto fail;
  }

  /* Read the integer part. */
  end_not_reached = (curr != s_end);
  while (end_not_reached && IS_DIGIT(*curr)) {
    mantissa *= 10;
    mantissa += (int)(*curr - 0x30);
    curr++;
    read++;
    end_not_reached = (curr != s_end);
  }

  /* We must make sure we actually got something. */
  if (read == 0) goto fail;
  /* We allow numbers of form "#", "###" etc. */
  if (!end_not_reached) goto assemble; 

  /* Read the decimal part. */
  if (*curr == '.') {
    curr++;
    read = 1;
    end_not_reached = (curr != s_end);
    while (end_not_reached && IS_DIGIT(*curr)) {
      /* pow(10.0, -read) */
      double frac_value = 1.0;
      int f;
      for (f = 0; f < read; f++) {
        frac_value *= 0.1;
      }
      mantissa += (int)(*curr - 0x30) * frac_value;
      read++;
      curr++;
      end_not_reached = (curr != s_end);
    }
  } else if (*curr == 'e' || *curr == 'E') {
  } else {
    goto assemble;
  }

  if (!end_not_reached) goto assemble;

  /* Read the exponent part. */
  if (*curr == 'e' || *curr == 'E') {
    curr++;
    /* Figure out if a sign is present and if it is. */
    end_not_reached = (curr != s_end);
    if (end_not_reached && (*curr == '+' || *curr == '-')) {
      exp_sign = *curr;
      curr++;
    } else if (IS_DIGIT(*curr)) { /* Pass through. */
    } else {
      /* Empty E is not allowed. */
      goto fail;
    }

    read = 0;
    end_not_reached = (curr != s_end);
    while (end_not_reached && IS_DIGIT(*curr)) {
      exponent *= 10;
      exponent += (int)(*curr - 0x30);
      curr++;
      read++;
      end_not_reached = (curr != s_end);
    }
    exponent *= (exp_sign == '+' ? 1 : -1);
    if (read == 0) goto fail;
  }

assemble :

  {
    /* = pow(5.0, exponent); */
    double a = 5.0;
    int i;
    for (i = 0; i < exponent; i++) {
      a = a * a;
    }
    *result =
        /* (sign == '+' ? 1 : -1) * ldexp(mantissa * pow(5.0, exponent), exponent); */
        (sign == '+' ? 1 : -1) * (mantissa * a) *
        (double)(1 << exponent);  /* 5.0^exponent * 2^exponent */
  }

  return 1;
fail:
  return 0;
}

static float parseFloat(const char **token) {
  const char *end;
  double val = 0.0;
  float f = 0.0f;
  skip_space(token); 
  end =
      (*token) + until_space((*token));
  val = 0.0;
  tryParseDouble((*token), end, &val);
  f = (float)(val);
  (*token) = end;
  return f;
}

static void parseFloat2(float *x, float *y, const char **token) {
  (*x) = parseFloat(token);
  (*y) = parseFloat(token);
}

static void parseFloat3(float *x, float *y, float *z,
                               const char **token) {
  (*x) = parseFloat(token);
  (*y) = parseFloat(token);
  (*z) = parseFloat(token);
}

static void InitMaterial(tinyobj_material_t *material) {
  int i;
  material->name = "";
  material->ambient_texname = "";
  material->diffuse_texname = "";
  material->specular_texname = "";
  material->specular_highlight_texname = "";
  material->bump_texname = "";
  material->displacement_texname = "";
  material->alpha_texname = "";
  for (i = 0; i < 3; i++) {
    material->ambient[i] = 0.f;
    material->diffuse[i] = 0.f;
    material->specular[i] = 0.f;
    material->transmittance[i] = 0.f;
    material->emission[i] = 0.f;
  }
  material->illum = 0;
  material->dissolve = 1.f;
  material->shininess = 1.f;
  material->ior = 1.f;
}

#if 0 /* todo */
static void LoadMtl(std::map<std::string, int> *material_map,
                    std::vector<material_t> *materials,
                    std::istream *inStream) {
  // Create a default material anyway.
  material_t material;
  InitMaterial(&material);

  size_t maxchars = 8192;           // Alloc enough size.
  std::vector<char> buf(maxchars);  // Alloc enough size.
  while (inStream->peek() != -1) {
    inStream->getline(&buf[0], static_cast<std::streamsize>(maxchars));

    std::string linebuf(&buf[0]);

    // Trim newline '\r\n' or '\n'
    if (linebuf.size() > 0) {
      if (linebuf[linebuf.size() - 1] == '\n')
        linebuf.erase(linebuf.size() - 1);
    }
    if (linebuf.size() > 0) {
      if (linebuf[linebuf.size() - 1] == '\r')
        linebuf.erase(linebuf.size() - 1);
    }

    // Skip if empty line.
    if (linebuf.empty()) {
      continue;
    }

    // Skip leading space.
    const char *token = linebuf.c_str();
    token += strspn(token, " \t");

    assert(token);
    if (token[0] == '\0') continue;  // empty line

    if (token[0] == '#') continue;  // comment line

    // new mtl
    if ((0 == strncmp(token, "newmtl", 6)) && IS_SPACE((token[6]))) {
      // flush previous material.
      if (!material.name.empty()) {
        material_map->insert(std::pair<std::string, int>(
            material.name, static_cast<int>(materials->size())));
        materials->push_back(material);
      }

      // initial temporary material
      InitMaterial(&material);

      // set new mtl name
      char namebuf[4096];
      token += 7;
#ifdef _MSC_VER
      sscanf_s(token, "%s", namebuf, (unsigned)_countof(namebuf));
#else
      sscanf(token, "%s", namebuf);
#endif
      material.name = namebuf;
      continue;
    }

    // ambient
    if (token[0] == 'K' && token[1] == 'a' && IS_SPACE((token[2]))) {
      token += 2;
      float r, g, b;
      parseFloat3(&r, &g, &b, &token);
      material.ambient[0] = r;
      material.ambient[1] = g;
      material.ambient[2] = b;
      continue;
    }

    // diffuse
    if (token[0] == 'K' && token[1] == 'd' && IS_SPACE((token[2]))) {
      token += 2;
      float r, g, b;
      parseFloat3(&r, &g, &b, &token);
      material.diffuse[0] = r;
      material.diffuse[1] = g;
      material.diffuse[2] = b;
      continue;
    }

    // specular
    if (token[0] == 'K' && token[1] == 's' && IS_SPACE((token[2]))) {
      token += 2;
      float r, g, b;
      parseFloat3(&r, &g, &b, &token);
      material.specular[0] = r;
      material.specular[1] = g;
      material.specular[2] = b;
      continue;
    }

    // transmittance
    if (token[0] == 'K' && token[1] == 't' && IS_SPACE((token[2]))) {
      token += 2;
      float r, g, b;
      parseFloat3(&r, &g, &b, &token);
      material.transmittance[0] = r;
      material.transmittance[1] = g;
      material.transmittance[2] = b;
      continue;
    }

    // ior(index of refraction)
    if (token[0] == 'N' && token[1] == 'i' && IS_SPACE((token[2]))) {
      token += 2;
      material.ior = parseFloat(&token);
      continue;
    }

    // emission
    if (token[0] == 'K' && token[1] == 'e' && IS_SPACE(token[2])) {
      token += 2;
      float r, g, b;
      parseFloat3(&r, &g, &b, &token);
      material.emission[0] = r;
      material.emission[1] = g;
      material.emission[2] = b;
      continue;
    }

    // shininess
    if (token[0] == 'N' && token[1] == 's' && IS_SPACE(token[2])) {
      token += 2;
      material.shininess = parseFloat(&token);
      continue;
    }

    // illum model
    if (0 == strncmp(token, "illum", 5) && IS_SPACE(token[5])) {
      token += 6;
      material.illum = parseInt(&token);
      continue;
    }

    // dissolve
    if ((token[0] == 'd' && IS_SPACE(token[1]))) {
      token += 1;
      material.dissolve = parseFloat(&token);
      continue;
    }
    if (token[0] == 'T' && token[1] == 'r' && IS_SPACE(token[2])) {
      token += 2;
      // Invert value of Tr(assume Tr is in range [0, 1])
      material.dissolve = 1.0f - parseFloat(&token);
      continue;
    }

    // ambient texture
    if ((0 == strncmp(token, "map_Ka", 6)) && IS_SPACE(token[6])) {
      token += 7;
      material.ambient_texname = token;
      continue;
    }

    // diffuse texture
    if ((0 == strncmp(token, "map_Kd", 6)) && IS_SPACE(token[6])) {
      token += 7;
      material.diffuse_texname = token;
      continue;
    }

    // specular texture
    if ((0 == strncmp(token, "map_Ks", 6)) && IS_SPACE(token[6])) {
      token += 7;
      material.specular_texname = token;
      continue;
    }

    // specular highlight texture
    if ((0 == strncmp(token, "map_Ns", 6)) && IS_SPACE(token[6])) {
      token += 7;
      material.specular_highlight_texname = token;
      continue;
    }

    // bump texture
    if ((0 == strncmp(token, "map_bump", 8)) && IS_SPACE(token[8])) {
      token += 9;
      material.bump_texname = token;
      continue;
    }

    // alpha texture
    if ((0 == strncmp(token, "map_d", 5)) && IS_SPACE(token[5])) {
      token += 6;
      material.alpha_texname = token;
      continue;
    }

    // bump texture
    if ((0 == strncmp(token, "bump", 4)) && IS_SPACE(token[4])) {
      token += 5;
      material.bump_texname = token;
      continue;
    }

    // displacement texture
    if ((0 == strncmp(token, "disp", 4)) && IS_SPACE(token[4])) {
      token += 5;
      material.displacement_texname = token;
      continue;
    }

    // unknown parameter
    const char *_space = strchr(token, ' ');
    if (!_space) {
      _space = strchr(token, '\t');
    }
    if (_space) {
      std::ptrdiff_t len = _space - token;
      std::string key(token, static_cast<size_t>(len));
      std::string value = _space + 1;
      material.unknown_parameter.insert(
          std::pair<std::string, std::string>(key, value));
    }
  }
  // flush last material.
  material_map->insert(std::pair<std::string, int>(
      material.name, static_cast<int>(materials->size())));
  materials->push_back(material);
}
#endif

typedef enum {
  COMMAND_EMPTY,
  COMMAND_V,
  COMMAND_VN,
  COMMAND_VT,
  COMMAND_F,
  COMMAND_G,
  COMMAND_O,
  COMMAND_USEMTL,
  COMMAND_MTLLIB

} CommandType;

typedef struct {
  float vx, vy, vz;
  float nx, ny, nz;
  float tx, ty;

	/* @todo { Use dynamic array } */
	tinyobj_vertex_index_t f[TINYOBJ_MAX_FACES_PER_F_LINE];
	int num_f;

	int f_num_verts[TINYOBJ_MAX_FACES_PER_F_LINE];
	int num_f_num_verts;

  const char *group_name;
  unsigned int group_name_len;
  const char *object_name;
  unsigned int object_name_len;
  const char *material_name;
  unsigned int material_name_len;

  const char *mtllib_name;
  unsigned int mtllib_name_len;

  CommandType type;
} Command;

static int parseLine(Command *command, const char *p, size_t p_len, int triangulate) {
  char linebuf[4096];
	const char *token;
  assert(p_len < 4095);

  memcpy(linebuf, p, p_len);
  linebuf[p_len] = '\0';

  token = linebuf;

  command->type = COMMAND_EMPTY;

  /* Skip leading space. */
  skip_space(&token);

  assert(token);
  if (token[0] == '\0') {  /* empty line */
    return 0;
  }

  if (token[0] == '#') {  /* comment line */
    return 0;
  }

  /* vertex */
  if (token[0] == 'v' && IS_SPACE((token[1]))) {
    float x, y, z;
    token += 2;
    parseFloat3(&x, &y, &z, &token);
    command->vx = x;
    command->vy = y;
    command->vz = z;
    command->type = COMMAND_V;
    return 1;
  }

  /* normal */
  if (token[0] == 'v' && token[1] == 'n' && IS_SPACE((token[2]))) {
    float x, y, z;
    token += 3;
    parseFloat3(&x, &y, &z, &token);
    command->nx = x;
    command->ny = y;
    command->nz = z;
    command->type = COMMAND_VN;
    return 1;
  }

  /* texcoord */
  if (token[0] == 'v' && token[1] == 't' && IS_SPACE((token[2]))) {
    float x, y;
    token += 3;
    parseFloat2(&x, &y, &token);
    command->tx = x;
    command->ty = y;
    command->type = COMMAND_VT;
    return 1;
  }

  /* face */
  if (token[0] == 'f' && IS_SPACE((token[1]))) {
		int num_f = 0;

		tinyobj_vertex_index_t f[TINYOBJ_MAX_FACES_PER_F_LINE];
    token += 2;
    skip_space(&token);


    while (!IS_NEW_LINE(token[0])) {
      tinyobj_vertex_index_t vi = parseRawTriple(&token);
      skip_space_and_cr(&token);

      f[num_f] = vi;
    }

    command->type = COMMAND_F;

    if (triangulate) {
			int k;
			int n = 0;

      tinyobj_vertex_index_t i0 = f[0];
      tinyobj_vertex_index_t i1;
      tinyobj_vertex_index_t i2 = f[1];

			assert(3 * num_f < TINYOBJ_MAX_FACES_PER_F_LINE);

      for (k = 2; k < num_f; k++) {
        i1 = i2;
        i2 = f[k];
        command->f[3*n+0] = i0;
        command->f[3*n+1] = i1;
        command->f[3*n+2] = i2;

        command->f_num_verts[n] = 3;
				n++;
      }
			command->num_f = 3 * n;
			command->num_f_num_verts = n;

    } else {
			int k = 0;
			assert(num_f < TINYOBJ_MAX_FACES_PER_F_LINE);
      for (k = 0; k < num_f; k++) {
        command->f[k] = f[k];
      }

      command->f_num_verts[0] = num_f;
			command->num_f_num_verts = 1;
    }

    return 1;
  }

  /* use mtl */
  if ((0 == strncmp(token, "usemtl", 6)) && IS_SPACE((token[6]))) {
    token += 7;

    skip_space(&token);
    command->material_name = p + (token - linebuf);
    command->material_name_len =
        length_until_newline(token, p_len - (token - linebuf)) + 1;
    command->type = COMMAND_USEMTL;

    return 1;
  }

  /* load mtl */
  if ((0 == strncmp(token, "mtllib", 6)) && IS_SPACE((token[6]))) {
    /* By specification, `mtllib` should be appear only once in .obj */
    token += 7;

    skip_space(&token);
    command->mtllib_name = p + (token - linebuf);
    command->mtllib_name_len =
        length_until_newline(token, p_len - (token - linebuf)) + 1;
    command->type = COMMAND_MTLLIB;

    return 1;
  }

  /* group name */
  if (token[0] == 'g' && IS_SPACE((token[1]))) {
    /* @todo { multiple group name. } */
    token += 2;

    command->group_name = p + (token - linebuf);
    command->group_name_len =
        length_until_newline(token, p_len - (token - linebuf)) + 1;
    command->type = COMMAND_G;

    return 1;
  }

  /* object name */
  if (token[0] == 'o' && IS_SPACE((token[1]))) {
    /* @todo { multiple object name? } */
    token += 2;

    command->object_name = p + (token - linebuf);
    command->object_name_len =
        length_until_newline(token, p_len - (token - linebuf)) + 1;
    command->type = COMMAND_O;

    return 1;
  }

  return 0;
}

typedef struct {
  size_t pos;
  size_t len;
} LineInfo;

static int is_line_ending(const char *p, size_t i, size_t end_i) {
  if (p[i] == '\0') return 1;
  if (p[i] == '\n') return 1;  /* this includes \r\n */
  if (p[i] == '\r') {
    if (((i + 1) < end_i) && (p[i + 1] != '\n')) {  /* detect only \r case */
      return 1;
    }
  }
  return 0;
}

int tinyobj_parse(tinyobj_attrib_t *attrib, tinyobj_shape_t *shapes, size_t *num_shapes, const char *buf, size_t len, unsigned int flags)
{
	LineInfo* line_infos = NULL;
  Command*  commands = NULL;
	size_t    num_lines = 0;

  size_t    num_v = 0;
  size_t    num_vn = 0;
  size_t    num_vt = 0;
  size_t    num_f = 0;
  size_t    num_faces = 0;

  if (len < 1) return 0;

  /* 1. Find '\n' and create line data. */
  {
		size_t i;
		size_t end_idx = len - 1;
		size_t prev_pos = 0;
		size_t line_no = 0;
		
		/* Count # of lines. */
		for (i = 0; i < end_idx; i++) { /* Assume last char is '\0' */
      if (is_line_ending(buf, i, end_idx)) {
				num_lines++;
			}
		}
		printf("num lines %d\n", (int)num_lines);

    if (num_lines == 0) return TINYOBJ_ERROR_EMPTY;

		line_infos = (LineInfo*)malloc(sizeof(LineInfo) * num_lines);

		/* Fill line infoss. */
		for (i = 0; i < end_idx; i++) {
      if (is_line_ending(buf, i, end_idx)) {
				line_infos[line_no].pos = prev_pos;
				line_infos[line_no].len = i - prev_pos;
				prev_pos = i + 1;
				line_no++;
			}
		}
  }

  commands = (Command*)malloc(sizeof(Command) * num_lines);

  /* 2. parse each line */
  {
    size_t i = 0;
    for (i = 0; i < num_lines; i++) {
      int ret = parseLine(&commands[i], &buf[line_infos[i].pos],
                           line_infos[i].len, flags & TINYOBJ_FLAG_TRIANGULATE);
      if (ret) {
        if (commands[i].type == COMMAND_V) {
          num_v++;
        } else if (commands[i].type == COMMAND_VN) {
          num_vn++;
        } else if (commands[i].type == COMMAND_VT) {
          num_vt++;
        } else if (commands[i].type == COMMAND_F) {
          num_f += commands[i].num_f;
          num_faces++;
        }

        if (commands[i].type == COMMAND_MTLLIB) {
          /* @todo
          mtllib_t_index = t;
          mtllib_i_index = commands->size();
          */
        }

      }
    }
  }

  /* line_infos are not used anymore. Release memory. */
	if (line_infos) {
		free(line_infos);
	}

#if 0

  std::map<std::string, int> material_map;
  std::vector<material_t> materials;

  // Load material(if exits)
  if (mtllib_i_index >= 0 && mtllib_t_index >= 0 &&
      commands[mtllib_t_index][mtllib_i_index].mtllib_name &&
      commands[mtllib_t_index][mtllib_i_index].mtllib_name_len > 0) {
    std::string material_filename =
        std::string(commands[mtllib_t_index][mtllib_i_index].mtllib_name,
                    commands[mtllib_t_index][mtllib_i_index].mtllib_name_len);
    // std::cout << "mtllib :" << material_filename << std::endl;

    auto t1 = std::chrono::high_resolution_clock::now();

    std::ifstream ifs(material_filename);
    if (ifs.good()) {
      LoadMtl(&material_map, &materials, &ifs);

      // std::cout << "maetrials = " << materials.size() << std::endl;

      ifs.close();
    }

    auto t2 = std::chrono::high_resolution_clock::now();

    ms_load_mtl = t2 - t1;
  }
#endif

  /* Construct attributes */

  {
    size_t v_count = 0;
    size_t n_count = 0;
    size_t t_count = 0;
    size_t f_count = 0;
    size_t face_count = 0;
    int material_id = -1;  /* -1 = default unknown material. */
    size_t i = 0;

    attrib->vertices = (float*)malloc(sizeof(float) * num_v * 3);
    attrib->normals = (float*)malloc(sizeof(float) * num_vn * 3);
    attrib->texcoords = (float*)malloc(sizeof(float) * num_vt * 2);
    attrib->faces = (tinyobj_vertex_index_t*)malloc(sizeof(tinyobj_vertex_index_t) * num_f);
    attrib->face_num_verts = (int*)malloc(sizeof(int) * num_faces);
    attrib->material_ids = (int*)malloc(sizeof(int) * num_faces);

        for (i = 0; i < num_lines; i++) {
          if (commands[i].type == COMMAND_EMPTY) {
            continue;
          } else if (commands[i].type == COMMAND_USEMTL) {
            /* @todo
            if (commands[t][i].material_name &&
                commands[t][i].material_name_len > 0) {
              std::string material_name(commands[t][i].material_name,
                                        commands[t][i].material_name_len);

              if (material_map.find(material_name) != material_map.end()) {
                material_id = material_map[material_name];
              } else {
                // Assign invalid material ID
                material_id = -1;
              }
            }
            */
          } else if (commands[i].type == COMMAND_V) {
            attrib->vertices[3 * v_count + 0] = commands[i].vx;
            attrib->vertices[3 * v_count + 1] = commands[i].vy;
            attrib->vertices[3 * v_count + 2] = commands[i].vz;
            v_count++;
          } else if (commands[i].type == COMMAND_VN) {
            attrib->normals[3 * n_count + 0] = commands[i].nx;
            attrib->normals[3 * n_count + 1] = commands[i].ny;
            attrib->normals[3 * n_count + 2] = commands[i].nz;
            n_count++;
          } else if (commands[i].type == COMMAND_VT) {
            attrib->texcoords[2 * t_count + 0] = commands[i].tx;
            attrib->texcoords[2 * t_count + 1] = commands[i].ty;
            t_count++;
          } else if (commands[i].type == COMMAND_F) {
            size_t k =0;
            for (k = 0; k < commands[i].num_f; k++) {
              tinyobj_vertex_index_t vi = commands[i].f[k];
              int v_idx = fixIndex(vi.v_idx, v_count);
              int vn_idx = fixIndex(vi.vn_idx, n_count);
              int vt_idx = fixIndex(vi.vt_idx, t_count);
              attrib->faces[f_count + k].v_idx = v_idx;
              attrib->faces[f_count + k].vn_idx = vn_idx;
              attrib->faces[f_count + k].vt_idx = vt_idx;
            }
            attrib->material_ids[face_count] = material_id;
            attrib->face_num_verts[face_count] = commands[i].num_f;

            f_count += commands[i].num_f;
            face_count++;
          }
        }
  }

  /* 5. Construct shape information. */
  {
    int face_count = 0;
    int face_prev_offset = 0;
    size_t i = 0;
      for (i = 0; i < num_lines; i++) {
        if (commands[i].type == COMMAND_O ||
            commands[i].type == COMMAND_G) {
#if 0 /* @todo */
          if (commands[i].type == COMMAND_O) {
            name = std::string(commands[t][i].object_name,
                               commands[t][i].object_name_len);
          } else {
            name = std::string(commands[t][i].group_name,
                               commands[t][i].group_name_len);
          }

          if (face_count == 0) {
            // 'o' or 'g' appears before any 'f'
            shape.name = name;
            shape.face_offset = face_count;
            face_prev_offset = face_count;
          } else {
            if (shapes->size() == 0) {
              // 'o' or 'g' after some 'v' lines.
              // create a shape with null name
              shape.length = face_count - face_prev_offset;
              face_prev_offset = face_count;

              shapes->push_back(shape);

            } else {
              if ((face_count - face_prev_offset) > 0) {
                // push previous shape
                shape.length = face_count - face_prev_offset;
                shapes->push_back(shape);
                face_prev_offset = face_count;
              }
            }

            // redefine shape.
            shape.name = name;
            shape.face_offset = face_count;
            shape.length = 0;
          }
#endif
        }
        if (commands[i].type == COMMAND_F) {
          face_count++;
        }
      }

    if ((face_count - face_prev_offset) > 0) {
#if 0 /* todo */ 
      shape.length = face_count - shape.face_offset;
      if (shape.length > 0) {
        shapes->push_back(shape);
      }
#endif
    } else {
      /* Guess no 'v' line occurrence after 'o' or 'g', so discards current shape information. */
    }

  }

  if (commands) {
    free(commands);
  }

  return TINYOBJ_SUCCESS;
}
#endif  /* TINYOBJ_LOADER_C_IMPLEMENTATION */

#endif  /* TINOBJ_LOADER_C_H_ */
