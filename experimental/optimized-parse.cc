#ifdef _WIN64
#define atoll(S) _atoi64(S)
#include <windows.h>
#else
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#endif

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <cassert>
#include <vector>
#include <iostream>

#include <chrono> // C++11
#include <thread> // C++11
#include <atomic> // C++11

// ----------------------------------------------------------------------------
// Small vector class useful for multi-threaded environment.
//
// stack_container.h
//
// Copyright (c) 2006-2008 The Chromium Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// This allocator can be used with STL containers to provide a stack buffer
// from which to allocate memory and overflows onto the heap. This stack buffer
// would be allocated on the stack and allows us to avoid heap operations in
// some situations.
//
// STL likes to make copies of allocators, so the allocator itself can't hold
// the data. Instead, we make the creator responsible for creating a
// StackAllocator::Source which contains the data. Copying the allocator
// merely copies the pointer to this shared source, so all allocators created
// based on our allocator will share the same stack buffer.
//
// This stack buffer implementation is very simple. The first allocation that
// fits in the stack buffer will use the stack buffer. Any subsequent
// allocations will not use the stack buffer, even if there is unused room.
// This makes it appropriate for array-like containers, but the caller should
// be sure to reserve() in the container up to the stack buffer size. Otherwise
// the container will allocate a small array which will "use up" the stack
// buffer.
template <typename T, size_t stack_capacity>
class StackAllocator : public std::allocator<T> {
 public:
  typedef typename std::allocator<T>::pointer pointer;
  typedef typename std::allocator<T>::size_type size_type;

  // Backing store for the allocator. The container owner is responsible for
  // maintaining this for as long as any containers using this allocator are
  // live.
  struct Source {
    Source() : used_stack_buffer_(false) {}

    // Casts the buffer in its right type.
    T *stack_buffer() { return reinterpret_cast<T *>(stack_buffer_); }
    const T *stack_buffer() const {
      return reinterpret_cast<const T *>(stack_buffer_);
    }

    //
    // IMPORTANT: Take care to ensure that stack_buffer_ is aligned
    // since it is used to mimic an array of T.
    // Be careful while declaring any unaligned types (like bool)
    // before stack_buffer_.
    //

    // The buffer itself. It is not of type T because we don't want the
    // constructors and destructors to be automatically called. Define a POD
    // buffer of the right size instead.
    char stack_buffer_[sizeof(T[stack_capacity])];

    // Set when the stack buffer is used for an allocation. We do not track
    // how much of the buffer is used, only that somebody is using it.
    bool used_stack_buffer_;
  };

  // Used by containers when they want to refer to an allocator of type U.
  template <typename U>
  struct rebind {
    typedef StackAllocator<U, stack_capacity> other;
  };

  // For the straight up copy c-tor, we can share storage.
  StackAllocator(const StackAllocator<T, stack_capacity> &rhs)
      : source_(rhs.source_) {}

  // ISO C++ requires the following constructor to be defined,
  // and std::vector in VC++2008SP1 Release fails with an error
  // in the class _Container_base_aux_alloc_real (from <xutility>)
  // if the constructor does not exist.
  // For this constructor, we cannot share storage; there's
  // no guarantee that the Source buffer of Ts is large enough
  // for Us.
  // TODO(Google): If we were fancy pants, perhaps we could share storage
  // iff sizeof(T) == sizeof(U).
  template <typename U, size_t other_capacity>
  StackAllocator(const StackAllocator<U, other_capacity> &other)
      : source_(NULL) {
    (void)other;
  }

  explicit StackAllocator(Source *source) : source_(source) {}

  // Actually do the allocation. Use the stack buffer if nobody has used it yet
  // and the size requested fits. Otherwise, fall through to the standard
  // allocator.
  pointer allocate(size_type n, void *hint = 0) {
    if (source_ != NULL && !source_->used_stack_buffer_ &&
        n <= stack_capacity) {
      source_->used_stack_buffer_ = true;
      return source_->stack_buffer();
    } else {
      return std::allocator<T>::allocate(n, hint);
    }
  }

  // Free: when trying to free the stack buffer, just mark it as free. For
  // non-stack-buffer pointers, just fall though to the standard allocator.
  void deallocate(pointer p, size_type n) {
    if (source_ != NULL && p == source_->stack_buffer())
      source_->used_stack_buffer_ = false;
    else
      std::allocator<T>::deallocate(p, n);
  }

 private:
  Source *source_;
};

// A wrapper around STL containers that maintains a stack-sized buffer that the
// initial capacity of the vector is based on. Growing the container beyond the
// stack capacity will transparently overflow onto the heap. The container must
// support reserve().
//
// WATCH OUT: the ContainerType MUST use the proper StackAllocator for this
// type. This object is really intended to be used only internally. You'll want
// to use the wrappers below for different types.
template <typename TContainerType, int stack_capacity>
class StackContainer {
 public:
  typedef TContainerType ContainerType;
  typedef typename ContainerType::value_type ContainedType;
  typedef StackAllocator<ContainedType, stack_capacity> Allocator;

  // Allocator must be constructed before the container!
  StackContainer() : allocator_(&stack_data_), container_(allocator_) {
    // Make the container use the stack allocation by reserving our buffer size
    // before doing anything else.
    container_.reserve(stack_capacity);
  }

  // Getters for the actual container.
  //
  // Danger: any copies of this made using the copy constructor must have
  // shorter lifetimes than the source. The copy will share the same allocator
  // and therefore the same stack buffer as the original. Use std::copy to
  // copy into a "real" container for longer-lived objects.
  ContainerType &container() { return container_; }
  const ContainerType &container() const { return container_; }

  // Support operator-> to get to the container. This allows nicer syntax like:
  //   StackContainer<...> foo;
  //   std::sort(foo->begin(), foo->end());
  ContainerType *operator->() { return &container_; }
  const ContainerType *operator->() const { return &container_; }

#ifdef UNIT_TEST
  // Retrieves the stack source so that that unit tests can verify that the
  // buffer is being used properly.
  const typename Allocator::Source &stack_data() const { return stack_data_; }
#endif

 protected:
  typename Allocator::Source stack_data_;
  unsigned char pad_[7];
  Allocator allocator_;
  ContainerType container_;

  // DISALLOW_EVIL_CONSTRUCTORS(StackContainer);
  StackContainer(const StackContainer &);
  void operator=(const StackContainer &);
};

// StackVector
//
// Example:
//   StackVector<int, 16> foo;
//   foo->push_back(22);  // we have overloaded operator->
//   foo[0] = 10;         // as well as operator[]
template <typename T, size_t stack_capacity>
class StackVector
    : public StackContainer<std::vector<T, StackAllocator<T, stack_capacity> >,
                            stack_capacity> {
 public:
  StackVector()
      : StackContainer<std::vector<T, StackAllocator<T, stack_capacity> >,
                       stack_capacity>() {}

  // We need to put this in STL containers sometimes, which requires a copy
  // constructor. We can't call the regular copy constructor because that will
  // take the stack buffer from the original. Here, we create an empty object
  // and make a stack buffer of its own.
  StackVector(const StackVector<T, stack_capacity> &other)
      : StackContainer<std::vector<T, StackAllocator<T, stack_capacity> >,
                       stack_capacity>() {
    this->container().assign(other->begin(), other->end());
  }

  StackVector<T, stack_capacity> &operator=(
      const StackVector<T, stack_capacity> &other) {
    this->container().assign(other->begin(), other->end());
    return *this;
  }

  // Vectors are commonly indexed, which isn't very convenient even with
  // operator-> (using "->at()" does exception stuff we don't want).
  T &operator[](size_t i) { return this->container().operator[](i); }
  const T &operator[](size_t i) const {
    return this->container().operator[](i);
  }
};

// ----------------------------------------------------------------------------

typedef StackVector<char, 256> ShortString;

#define IS_SPACE(x) (((x) == ' ') || ((x) == '\t'))
#define IS_DIGIT(x) \
  (static_cast<unsigned int>((x) - '0') < static_cast<unsigned int>(10))
#define IS_NEW_LINE(x) (((x) == '\r') || ((x) == '\n') || ((x) == '\0'))

static inline void skip_space(const char **token)
{
  while ((*token)[0] == ' ' || (*token)[0] == '\t') {
    (*token)++;
  }
}

static inline void skip_space_and_cr(const char **token)
{
  while ((*token)[0] == ' ' || (*token)[0] == '\t' || (*token)[0] == '\r') {
    (*token)++;
  }
}

static inline int until_space(const char *token)
{
  const char *p = token;
  while (p[0] != '\0' && p[0] != ' ' && p[0] != '\t' && p[0] != '\r') {
    p++;
  }

  return p - token;
}

// http://stackoverflow.com/questions/5710091/how-does-atoi-function-in-c-work
static inline int my_atoi( const char *c ) {
    int value = 0;
    int sign = 1;
    if( *c == '+' || *c == '-' ) {
       if( *c == '-' ) sign = -1;
       c++;
    }
    while ( ((*c) >= '0') && ((*c) <= '9') ) { // isdigit(*c)
        value *= 10;
        value += (int) (*c-'0');
        c++;
    }
    return value * sign;
}

struct vertex_index {
  int v_idx, vt_idx, vn_idx;
  vertex_index() : v_idx(-1), vt_idx(-1), vn_idx(-1) {}
  explicit vertex_index(int idx) : v_idx(idx), vt_idx(idx), vn_idx(idx) {}
  vertex_index(int vidx, int vtidx, int vnidx)
      : v_idx(vidx), vt_idx(vtidx), vn_idx(vnidx) {}
};

// Make index zero-base, and also support relative index.
static inline int fixIndex(int idx, int n) {
  if (idx > 0) return idx - 1;
  if (idx == 0) return 0;
  return n + idx;  // negative value = relative
}

#if 0
// Parse triples with index offsets: i, i/j/k, i//k, i/j
static vertex_index parseTriple(const char **token, int vsize, int vnsize,
                                int vtsize) {
  vertex_index vi(-1);

  vi.v_idx = fixIndex(my_atoi((*token)), vsize);

  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }
  (*token)++;

  // i//k
  if ((*token)[0] == '/') {
    (*token)++;
    vi.vn_idx = fixIndex(my_atoi((*token)), vnsize);
    //(*token) += strcspn((*token), "/ \t\r");
    while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
      (*token)++;
    }
    return vi;
  }

  // i/j/k or i/j
  vi.vt_idx = fixIndex(my_atoi((*token)), vtsize);
  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }

  // i/j/k
  (*token)++;  // skip '/'
  vi.vn_idx = fixIndex(my_atoi((*token)), vnsize);
  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  return vi;
}
#endif

// Parse raw triples: i, i/j/k, i//k, i/j
static vertex_index parseRawTriple(const char **token) {
  vertex_index vi(
      static_cast<int>(0x80000000));  // 0x80000000 = -2147483648 = invalid

  vi.v_idx = my_atoi((*token));
  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }
  (*token)++;

  // i//k
  if ((*token)[0] == '/') {
    (*token)++;
    vi.vn_idx = my_atoi((*token));
    //(*token) += strcspn((*token), "/ \t\r");
    while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
      (*token)++;
    }
    return vi;
  }

  // i/j/k or i/j
  vi.vt_idx = my_atoi((*token));
  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  if ((*token)[0] != '/') {
    return vi;
  }

  // i/j/k
  (*token)++;  // skip '/'
  vi.vn_idx = my_atoi((*token));
  //(*token) += strcspn((*token), "/ \t\r");
  while ((*token)[0] != '\0' && (*token)[0] != '/' && (*token)[0] != ' ' && (*token)[0] != '\t' && (*token)[0] != '\r') {
    (*token)++;
  }
  return vi;
}

static inline bool parseString(ShortString *s, const char **token) {
  skip_space(token); //(*token) += strspn((*token), " \t");
  size_t e = until_space((*token)); //strcspn((*token), " \t\r");
  (*s)->insert((*s)->end(), (*token), (*token) + e);
  (*token) += e;
  return true;
}

static inline int parseInt(const char **token) {
  skip_space(token); //(*token) += strspn((*token), " \t");
  int i = my_atoi((*token));
  (*token) += until_space((*token)); //strcspn((*token), " \t\r");
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

  /*
          BEGIN PARSING.
  */

  // Find out what sign we've got.
  if (*curr == '+' || *curr == '-') {
    sign = *curr;
    curr++;
  } else if (IS_DIGIT(*curr)) { /* Pass through. */
  } else {
    goto fail;
  }

  // Read the integer part.
  end_not_reached = (curr != s_end);
  while (end_not_reached && IS_DIGIT(*curr)) {
    mantissa *= 10;
    mantissa += static_cast<int>(*curr - 0x30);
    curr++;
    read++;
    end_not_reached = (curr != s_end);
  }

  // We must make sure we actually got something.
  if (read == 0) goto fail;
  // We allow numbers of form "#", "###" etc.
  if (!end_not_reached) goto assemble;

  // Read the decimal part.
  if (*curr == '.') {
    curr++;
    read = 1;
    end_not_reached = (curr != s_end);
    while (end_not_reached && IS_DIGIT(*curr)) {
      // NOTE: Don't use powf here, it will absolutely murder precision.

      // pow(10.0, -read)
      double frac_value = 10.0;
      for (int f = 0; f < read; f++) {
        frac_value *= 0.1;
      }
      mantissa += static_cast<int>(*curr - 0x30) * frac_value;
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
  *result =
      (sign == '+' ? 1 : -1) * ldexp(mantissa * pow(5.0, exponent), exponent);
  return true;
fail:
  return false;
}

static inline float parseFloat(const char **token) {
  skip_space(token); //(*token) += strspn((*token), " \t");
#ifdef TINY_OBJ_LOADER_OLD_FLOAT_PARSER
  float f = static_cast<float>(atof(*token));
  (*token) += strcspn((*token), " \t\r");
#else
  const char *end = (*token) + until_space((*token)); //strcspn((*token), " \t\r");
  double val = 0.0;
  tryParseDouble((*token), end, &val);
  float f = static_cast<float>(val);
  (*token) = end;
#endif
  return f;
}

static inline void parseFloat2(float *x, float *y, const char **token) {
  (*x) = parseFloat(token);
  (*y) = parseFloat(token);
}

static inline void parseFloat3(float *x, float *y, float *z,
                               const char **token) {
  (*x) = parseFloat(token);
  (*y) = parseFloat(token);
  (*z) = parseFloat(token);
}

typedef enum
{
  COMMAND_EMPTY,
  COMMAND_V,
  COMMAND_VN,
  COMMAND_VT,
  COMMAND_F,
  COMMAND_G,
  COMMAND_O,
  COMMAND_USEMTL,

} CommandType;

typedef struct
{
  float vx, vy, vz;
  float nx, ny, nz;
  float tx, ty;

  // for f
  std::vector<vertex_index> f;

  const char* group_name;
  const char* object_name;
  const char* material_name;

  CommandType type;
} Command;

struct CommandCount
{
  size_t num_v;
  size_t num_vn;
  size_t num_vt;
  size_t num_f;
  CommandCount() {
    num_v = 0;
    num_vn = 0;
    num_vt = 0;
    num_f = 0;
  }
};

static bool parseLine(Command *command, const char *p, size_t p_len)
{
    char linebuf[4096];
    assert(p_len < 4095);
    //StackVector<char, 256> linebuf;
    //linebuf->resize(p_len + 1);
    memcpy(&linebuf, p, p_len);
    linebuf[p_len] = '\0';

    const char *token = linebuf;

    command->type = COMMAND_EMPTY;

    // Skip leading space.
    //token += strspn(token, " \t");
    skip_space(&token); //(*token) += strspn((*token), " \t");

    assert(token);
    if (token[0] == '\0') { // empty line
      return false;
    }

    if (token[0] == '#') { // comment line
      return false;
    }

    // vertex
    if (token[0] == 'v' && IS_SPACE((token[1]))) {
      token += 2;
      float x, y, z;
      parseFloat3(&x, &y, &z, &token);
      command->vx = x;
      command->vy = y;
      command->vz = z;
      command->type = COMMAND_V;
      return true;
    } 

    // normal
    if (token[0] == 'v' && token[1] == 'n' && IS_SPACE((token[2]))) {
      token += 3;
      float x, y, z;
      parseFloat3(&x, &y, &z, &token);
      command->nx = x;
      command->ny = y;
      command->nz = z;
      command->type = COMMAND_VN;
      return true;
    }

    // texcoord
    if (token[0] == 'v' && token[1] == 't' && IS_SPACE((token[2]))) {
      token += 3;
      float x, y;
      parseFloat2(&x, &y, &token);
      command->tx = x;
      command->ty = y;
      command->type = COMMAND_VT;
      return true;
    }

    // face
    if (token[0] == 'f' && IS_SPACE((token[1]))) {
      token += 2;
      //token += strspn(token, " \t");
      skip_space(&token);

      while (!IS_NEW_LINE(token[0])) {
        vertex_index vi = parseRawTriple(&token);
        //printf("v = %d, %d, %d\n", vi.v_idx, vi.vn_idx, vi.vt_idx);
        //if (callback.index_cb) {
        //  callback.index_cb(user_data, vi.v_idx, vi.vn_idx, vi.vt_idx);
        //}
        //size_t n = strspn(token, " \t\r");
        //token += n;
        skip_space_and_cr(&token);

        command->f.push_back(vi);
      }

      command->type = COMMAND_F;

      return true;
    }

    // use mtl
    if ((0 == strncmp(token, "usemtl", 6)) && IS_SPACE((token[6]))) {
      char namebuf[8192];
      token += 7;
#ifdef _MSC_VER
      sscanf_s(token, "%s", namebuf, (unsigned)_countof(namebuf));
#else
      sscanf(token, "%s", namebuf);
#endif

      //int newMaterialId = -1;
      //if (material_map.find(namebuf) != material_map.end()) {
      //  newMaterialId = material_map[namebuf];
      //} else {
      //  // { error!! material not found }
      //}

      //if (newMaterialId != materialId) {
      //  materialId = newMaterialId;
      //}
      
      //command->material_name = .insert(command->material_name->end(), namebuf, namebuf + strlen(namebuf));
      //command->material_name->push_back('\0');
      command->type = COMMAND_USEMTL;
      
      return true;
    }

#if 0
    // load mtl
    if ((0 == strncmp(token, "mtllib", 6)) && IS_SPACE((token[6]))) {
      char namebuf[TINYOBJ_SSCANF_BUFFER_SIZE];
      token += 7;
#ifdef _MSC_VER
      sscanf_s(token, "%s", namebuf, (unsigned)_countof(namebuf));
#else
      sscanf(token, "%s", namebuf);
#endif

      std::string err_mtl;
      std::vector<material_t> materials;
      bool ok = (*readMatFn)(namebuf, &materials, &material_map, &err_mtl);
      if (err) {
        (*err) += err_mtl;
      }

      if (!ok) {
        return false;
      }

      if (callback.mtllib_cb) {
        callback.mtllib_cb(user_data, &materials.at(0),
                           static_cast<int>(materials.size()));
      }

      continue;
    }
#endif

    // group name
    if (token[0] == 'g' && IS_SPACE((token[1]))) {
      std::vector<ShortString> names;
      
      int num_names = 0;

      while (!IS_NEW_LINE(token[0])) {
        bool ret = parseString(&(names[num_names]), &token);
        assert(ret);
        token += strspn(token, " \t\r");  // skip tag
        num_names++;
      }

      assert(num_names > 0);

      //int name_idx = 0;
      // names[0] must be 'g', so skip the 0th element.
      if (num_names > 1) {
        //name_idx = 1;
      }

      //command->group_name->assign(names[name_idx]);
      command->type = COMMAND_G;

      //if (callback.group_cb) {
      //  if (names.size() > 1) {
      //    // create const char* array.
      //    std::vector<const char *> tmp(names.size() - 1);
      //    for (size_t j = 0; j < tmp.size(); j++) {
      //      tmp[j] = names[j + 1].c_str();
      //    }
      //    callback.group_cb(user_data, &tmp.at(0),
      //                      static_cast<int>(tmp.size()));

      //  } else {
      //    callback.group_cb(user_data, NULL, 0);
      //  }

      //}
      return true;
    }

    // object name
    if (token[0] == 'o' && IS_SPACE((token[1]))) {
      // @todo { multiple object name? }
      char namebuf[8192];
      token += 2;
#ifdef _MSC_VER
      sscanf_s(token, "%s", namebuf, (unsigned)_countof(namebuf));
#else
      sscanf(token, "%s", namebuf);
#endif

      //if (callback.object_cb) {
      //  callback.object_cb(user_data, name.c_str());
      //}
      
      //command->object_name->insert(command->object_name->end(), namebuf, namebuf + strlen(namebuf));
      //command->object_name->push_back('\0');
      command->type = COMMAND_O;

      return true;
    }


    return false;
}

typedef struct
{
  size_t pos;
  size_t len;
} LineInfo;

// Idea come from https://github.com/antonmks/nvParse
// 1. mmap file
// 2. find newline(\n, \r\n, \r) and list of line data.
// 3. Do parallel parsing for each line.
// 4. Reconstruct final mesh data structure.

#define kMaxThreads (32)

static inline bool is_line_ending(const char* p, size_t i, size_t end_i)
{
  if (p[i] == '\0') return true;
  if (p[i] == '\n') return true; // this includes \r\n 
  if (p[i] == '\r') {
    if (((i+1) < end_i) && (p[i+1] != '\n')) { // detect only \r case
      return true;
    }
  }
  return false;
}

void parse(std::vector<float> &vertices, std::vector<float> &normals, std::vector<float> &texcoords, std::vector<vertex_index> &faces, const char* buf, size_t len, int req_num_threads)
{

  std::vector<char> newline_marker(len, 0);

  auto num_threads = (req_num_threads < 0) ? std::thread::hardware_concurrency() : req_num_threads;
  num_threads = std::max(1, std::min(static_cast<int>(num_threads), kMaxThreads));
  std::cout << "# of threads = " << num_threads << std::endl;

  auto t1 = std::chrono::high_resolution_clock::now();

  std::atomic<size_t> newline_counter(0);

  std::vector<LineInfo> line_infos[kMaxThreads];
  for (size_t t = 0; t < static_cast<size_t>(num_threads); t++) {
    // Pre allocate enough memory. len / 1024 / num_threads is just a heuristic value.
    line_infos[t].reserve(len / 1024 / num_threads);
  }

  // 1. Find '\n' and create line data.
  {
    std::vector<std::thread> workers;

    auto start_time = std::chrono::high_resolution_clock::now();
    auto chunk_size = len / num_threads;

    for (size_t t = 0; t < static_cast<size_t>(num_threads); t++) {
      workers.push_back(std::thread([&, t]() {
        auto start_idx = (t + 0) * chunk_size;
        auto end_idx   = std::min((t + 1) * chunk_size, len - 1);
        if (t == static_cast<size_t>((num_threads - 1))) {
          end_idx = len - 1;
        }

        size_t prev_pos = start_idx;
        for (size_t i = start_idx; i < end_idx; i++) {
          if (is_line_ending(buf, i, end_idx)) {
            if ((t > 0) && (prev_pos == start_idx) && (!is_line_ending(buf, start_idx-1, end_idx))) { 
              // first linebreak found in (chunk > 0), and a line before this linebreak belongs to previous chunk, so skip it.
              prev_pos = i + 1;
              continue;
            } else {
              LineInfo info;
              info.pos = prev_pos;
              info.len = i - prev_pos;

              if (info.len > 0) {
                line_infos[t].push_back(info);
              }

              prev_pos = i+1;
            }
          }
        }

        // Find extra line which spand across chunk boundary.
        if ((t < num_threads) && (buf[end_idx-1] != '\n')) {
          auto extra_span_idx = std::min(end_idx-1+chunk_size, len - 1);
          for (size_t i = end_idx; i < extra_span_idx; i++) {
            if (is_line_ending(buf, i, extra_span_idx)) {
              LineInfo info;
              info.pos = prev_pos;
              info.len = i - prev_pos;

              if (info.len > 0) {
                line_infos[t].push_back(info);
              }

              break;
            }
          }
        }
      }));
    }

    for (auto &t : workers) {
      t.join();
    }

    auto end_time = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double, std::milli> ms = end_time - start_time;
    std::cout << "line detection:" << ms.count() << " ms\n";
  }

  auto line_sum = 0;
  for (size_t t = 0; t < num_threads; t++) {
    std::cout << t << ": # of lines = " << line_infos[t].size() << std::endl;
    line_sum += line_infos[t].size();
  }
  std::cout << "# of lines = " << line_sum << std::endl;

  std::vector<Command> commands[kMaxThreads];

  for (size_t t = 0; t < num_threads; t++) {
    commands[t].reserve(line_infos[t].size());
  }  

  auto t2 = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double, std::milli> ms1 = t2 - t1;

  std::cout << ms1.count() << " ms\n";

  CommandCount command_count[kMaxThreads];

  // 2. parse each line in parallel.
  {
    std::vector<std::thread> workers;
    auto t_start = std::chrono::high_resolution_clock::now();

    for (size_t t = 0; t < num_threads; t++) {
      workers.push_back(std::thread([&, t]() {

        for (size_t i = 0; i < line_infos[t].size(); i++) {
          Command command;
          bool ret = parseLine(&command, &buf[line_infos[t][i].pos], line_infos[t][i].len);
          if (ret) {
            if (command.type == COMMAND_V) {
              command_count[t].num_v++;
            } else if (command.type == COMMAND_VN) {
              command_count[t].num_vn++;
            } else if (command.type == COMMAND_VT) {
              command_count[t].num_vt++;
            } else if (command.type == COMMAND_F) {
              command_count[t].num_f++;
            } 
            commands[t].emplace_back(std::move(command));
          }
        }

      }));
    }

    for (auto &t : workers) {
      t.join();
    }

    auto t_end = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double, std::milli> ms = t_end - t_start;
    std::cout << "parse:" << ms.count() << " ms\n";
  }

  auto command_sum = 0;
  for (size_t t = 0; t < num_threads; t++) {
    //std::cout << t << ": # of commands = " << commands[t].size() << std::endl;
    command_sum += commands[t].size();
  }
  //std::cout << "# of commands = " << command_sum << std::endl;

  size_t num_v = 0;
  size_t num_vn = 0;
  size_t num_vt = 0;
  size_t num_f = 0;
  for (size_t t = 0; t < num_threads; t++) {
      num_v += command_count[t].num_v;
      num_vn += command_count[t].num_vn;
      num_vt += command_count[t].num_vt;
      num_f += command_count[t].num_f;
  }
  std::cout << "# v " << num_v << std::endl;
  std::cout << "# vn " << num_vn << std::endl;
  std::cout << "# vt " << num_vt << std::endl;
  std::cout << "# f " << num_f << std::endl;

  vertices.reserve(num_v * 3);
  normals.reserve(num_vn * 3);
  texcoords.reserve(num_vt * 2);
  faces.reserve(num_f);

  // merge
  {
    auto t_start = std::chrono::high_resolution_clock::now();

    for (size_t t = 0; t < num_threads; t++) {
      for (size_t i = 0; i < commands[t].size(); i++) {
        if (commands[t][i].type == COMMAND_EMPTY) {
          continue;
        } else if (commands[t][i].type == COMMAND_V) {
          vertices.emplace_back(commands[t][i].vx);
          vertices.emplace_back(commands[t][i].vy);
          vertices.emplace_back(commands[t][i].vz);
        } else if (commands[t][i].type == COMMAND_VN) {
          normals.emplace_back(commands[t][i].nx);
          normals.emplace_back(commands[t][i].ny);
          normals.emplace_back(commands[t][i].nz);
        } else if (commands[t][i].type == COMMAND_VT) {
          texcoords.emplace_back(commands[t][i].tx);
          texcoords.emplace_back(commands[t][i].ty);
        } else if (commands[t][i].type == COMMAND_F) {
          int v_size = vertices.size() / 3;
          int vn_size = normals.size() / 3;
          int vt_size = texcoords.size() / 2;
          for (size_t k = 0; k < commands[t][i].f.size(); k++) {
            int v_idx = fixIndex(commands[t][i].f[k].v_idx, v_size);
            int vn_idx = fixIndex(commands[t][i].f[k].vn_idx, vn_size);
            int vt_idx = fixIndex(commands[t][i].f[k].vt_idx, vt_size);
            faces.emplace_back(std::move(vertex_index(v_idx, vn_idx, vt_idx)));
          }
        }
      }
    }

    auto t_end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double, std::milli> ms = t_end - t_start;
    std::cout << "merge:" << ms.count() << " ms\n";
  }

  std::cout << "# of vertices = " << vertices.size() << std::endl;
  std::cout << "# of normals = " << normals.size() << std::endl;
  std::cout << "# of texcoords = " << texcoords.size() << std::endl;
  std::cout << "# of faces = " << faces.size() << std::endl;

  auto t4 = std::chrono::high_resolution_clock::now();
 
  std::chrono::duration<double, std::milli> ms_total = t4 - t1;
  std::cout << "total: " << ms_total.count() << " ms\n";

}

#ifdef CONSOLE_TEST
int
main(int argc, char **argv)
{

  if (argc < 2) {
    printf("Needs .obj\n");
    return EXIT_FAILURE;
  }

  int req_num_threads = -1;
  if (argc > 2) {
    req_num_threads = atoi(argv[2]);
  }

#ifdef _WIN64
  HANDLE file = CreateFileA(argv[1], GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL | FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    assert(file != INVALID_HANDLE_VALUE);

    HANDLE fileMapping = CreateFileMapping(file, NULL, PAGE_READONLY, 0, 0, NULL);
    assert(fileMapping != INVALID_HANDLE_VALUE);
 
    LPVOID fileMapView = MapViewOfFile(fileMapping, FILE_MAP_READ, 0, 0, 0);
    auto fileMapViewChar = (const char*)fileMapView;
    assert(fileMapView != NULL);
#else

  FILE* f = fopen(argv[1], "r" );
  fseek(f, 0, SEEK_END);
  long fileSize = ftell(f);
  fclose(f);

  struct stat sb;
  char *p;
  int fd;

  fd = open (argv[1], O_RDONLY);
  if (fd == -1) {
    perror ("open");
    return 1;
  }

  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return 1;
  }

  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a file\n", "lineitem.tbl");
    return 1;
  }

  p = (char*)mmap (0, fileSize, PROT_READ, MAP_SHARED, fd, 0);

  if (p == MAP_FAILED) {
    perror ("mmap");
    return 1;
  }

  if (close (fd) == -1) {
    perror ("close");
    return 1;
  }

  printf("fsize: %lu\n", fileSize);
#endif

  parse(p, fileSize, req_num_threads);
  
  return EXIT_SUCCESS;
}
#endif