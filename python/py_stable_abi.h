/*
 * Python Stable ABI (abi3) Manual Definitions
 *
 * This header manually defines Python C API structures and functions
 * for the stable ABI (abi3) targeting Python 3.11+.
 *
 * This allows building the extension without requiring Python headers
 * or a Python distribution at build time.
 *
 * Reference: https://docs.python.org/3/c-api/stable.html
 */

#ifndef PY_STABLE_ABI_H_
#define PY_STABLE_ABI_H_

#include <stddef.h>
#include <stdint.h>

// Need ssize_t
#ifdef _WIN32
  #include <BaseTsd.h>
  typedef SSIZE_T ssize_t;
#else
  #include <sys/types.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

// Python version targeting
#define Py_LIMITED_API 0x030A0000  // Python 3.10+

// Opaque types - actual layout is hidden in stable ABI
typedef struct _object {
    // Opaque, only access via API functions
    // Note: In stable ABI, we cannot access members directly
    size_t _opaque[16];  // Large enough buffer
} PyObject;

typedef struct _typeobject PyTypeObject;
typedef struct PyMethodDef PyMethodDef;
typedef struct PyModuleDef PyModuleDef;
typedef struct PyModuleDef_Slot PyModuleDef_Slot;
typedef struct PyMemberDef PyMemberDef;
typedef struct PyGetSetDef PyGetSetDef;
typedef ssize_t Py_ssize_t;
typedef int (*visitproc)(PyObject *, void *);
typedef int (*traverseproc)(PyObject *, visitproc, void *);
typedef int (*inquiry)(PyObject *);
typedef void (*freefunc)(void *);
typedef void (*destructor)(PyObject *);
typedef PyObject *(*unaryfunc)(PyObject *);
typedef PyObject *(*binaryfunc)(PyObject *, PyObject *);
typedef PyObject *(*ternaryfunc)(PyObject *, PyObject *, PyObject *);
typedef PyObject *(*PyCFunction)(PyObject *, PyObject *);
typedef PyObject *(*getter)(PyObject *, void *);
typedef int (*setter)(PyObject *, PyObject *, void *);
typedef PyObject *(*newfunc)(PyTypeObject *, PyObject *, PyObject *);
typedef int (*initproc)(PyObject *, PyObject *, PyObject *);

// Method flags
#define METH_VARARGS  0x0001
#define METH_KEYWORDS 0x0002
#define METH_NOARGS   0x0004
#define METH_O        0x0008
#define METH_CLASS    0x0010
#define METH_STATIC   0x0020

// Type flags
#define Py_TPFLAGS_DEFAULT (1UL << 0)
#define Py_TPFLAGS_BASETYPE (1UL << 10)
#define Py_TPFLAGS_HEAPTYPE (1UL << 9)

// Return values
#define Py_RETURN_NONE return Py_IncRef(Py_None), Py_None
#define Py_RETURN_TRUE return Py_IncRef(Py_True), Py_True
#define Py_RETURN_FALSE return Py_IncRef(Py_False), Py_False

// Member types
#define T_BYTE      0
#define T_SHORT     1
#define T_INT       2
#define T_LONG      3
#define T_FLOAT     4
#define T_DOUBLE    5
#define T_STRING    6
#define T_OBJECT    7
#define T_OBJECT_EX 16
#define T_LONGLONG  17
#define T_ULONGLONG 18
#define T_PYSSIZET  19
#define T_BOOL      14

// Member flags
#define READONLY 1

// Module def base
#define PyModuleDef_HEAD_INIT {1, NULL}

// Structures
struct PyMethodDef {
    const char  *ml_name;
    PyCFunction  ml_meth;
    int          ml_flags;
    const char  *ml_doc;
};

struct PyMemberDef {
    const char *name;
    int type;
    Py_ssize_t offset;
    int flags;
    const char *doc;
};

struct PyGetSetDef {
    const char *name;
    getter get;
    setter set;
    const char *doc;
    void *closure;
};

struct PyModuleDef_Slot {
    int slot;
    void *value;
};

struct PyModuleDef {
    int m_base;
    void *m_init;
    const char* m_name;
    const char* m_doc;
    Py_ssize_t m_size;
    PyMethodDef *m_methods;
    PyModuleDef_Slot* m_slots;
    traverseproc m_traverse;
    inquiry m_clear;
    freefunc m_free;
};

// Type structure (opaque in stable ABI, only use via PyType_* functions)
typedef struct {
    PyObject ob_base;
    Py_ssize_t ob_size;
} PyVarObject;

// Type spec structures (stable ABI way to define types)
typedef struct {
    const char* name;
    int basicsize;
    int itemsize;
    unsigned int flags;
    PyMethodDef *methods;
    PyMemberDef *members;
    PyGetSetDef *getset;
} PyType_Slot_Spec;

typedef struct {
    const char* name;
    int basicsize;
    int itemsize;
    unsigned int flags;
    void *slots;
} PyType_Spec;

// Type slots
#define Py_tp_dealloc 1
#define Py_tp_repr 6
#define Py_tp_hash 15
#define Py_tp_call 19
#define Py_tp_str 20
#define Py_tp_getattro 21
#define Py_tp_setattro 22
#define Py_tp_doc 23
#define Py_tp_traverse 24
#define Py_tp_clear 25
#define Py_tp_iter 31
#define Py_tp_iternext 32
#define Py_tp_methods 33
#define Py_tp_members 34
#define Py_tp_getset 35
#define Py_tp_init 60
#define Py_tp_alloc 61
#define Py_tp_new 62
#define Py_tp_free 63

typedef struct {
    int slot;
    void *pfunc;
} PyType_Slot;

// Function declarations
extern PyObject *Py_None;
extern PyObject *Py_True;
extern PyObject *Py_False;

// Reference counting
extern void Py_IncRef(PyObject *);
extern void Py_DecRef(PyObject *);

// Object protocol
extern PyObject* PyObject_Str(PyObject *);
extern PyObject* PyObject_GetAttrString(PyObject *, const char *);
extern int PyObject_SetAttrString(PyObject *, const char *, PyObject *);
extern PyObject* PyObject_Call(PyObject *, PyObject *, PyObject *);
extern PyObject* PyObject_CallObject(PyObject *, PyObject *);

// Type objects
extern PyObject* PyType_FromSpec(PyType_Spec *);
extern int PyType_Ready(PyTypeObject *);

// Module creation
extern PyObject* PyModule_Create2(PyModuleDef *, int);
extern int PyModule_AddObject(PyObject *, const char *, PyObject *);
extern int PyModule_AddStringConstant(PyObject *, const char *, const char *);
extern int PyModule_AddIntConstant(PyObject *, const char *, long);

// Tuple
extern PyObject* PyTuple_New(Py_ssize_t);
extern int PyTuple_SetItem(PyObject *, Py_ssize_t, PyObject *);
extern PyObject* PyTuple_GetItem(PyObject *, Py_ssize_t);
extern Py_ssize_t PyTuple_Size(PyObject *);

// List
extern PyObject* PyList_New(Py_ssize_t);
extern int PyList_SetItem(PyObject *, Py_ssize_t, PyObject *);
extern int PyList_Append(PyObject *, PyObject *);
extern PyObject* PyList_GetItem(PyObject *, Py_ssize_t);
extern Py_ssize_t PyList_Size(PyObject *);

// Dict
extern PyObject* PyDict_New(void);
extern int PyDict_SetItemString(PyObject *, const char *, PyObject *);
extern PyObject* PyDict_GetItemString(PyObject *, const char *);

// String (Unicode)
extern PyObject* PyUnicode_FromString(const char *);
extern PyObject* PyUnicode_FromStringAndSize(const char *, Py_ssize_t);
extern const char* PyUnicode_AsUTF8(PyObject *);
extern const char* PyUnicode_AsUTF8AndSize(PyObject *, Py_ssize_t *);

// Bytes
extern PyObject* PyBytes_FromStringAndSize(const char *, Py_ssize_t);
extern char* PyBytes_AsString(PyObject *);
extern Py_ssize_t PyBytes_Size(PyObject *);

// Long (int)
extern PyObject* PyLong_FromLong(long);
extern PyObject* PyLong_FromLongLong(long long);
extern PyObject* PyLong_FromUnsignedLong(unsigned long);
extern PyObject* PyLong_FromSize_t(size_t);
extern PyObject* PyLong_FromSsize_t(Py_ssize_t);
extern long PyLong_AsLong(PyObject *);
extern long long PyLong_AsLongLong(PyObject *);
extern unsigned long PyLong_AsUnsignedLong(PyObject *);
extern size_t PyLong_AsSize_t(PyObject *);

// Float
extern PyObject* PyFloat_FromDouble(double);
extern double PyFloat_AsDouble(PyObject *);

// Bool
extern PyObject* PyBool_FromLong(long);
extern int PyObject_IsTrue(PyObject *);

// Error handling
extern PyObject* PyErr_Occurred(void);
extern void PyErr_SetString(PyObject *, const char *);
extern void PyErr_Format(PyObject *, const char *, ...);
extern void PyErr_Clear(void);
extern PyObject *PyExc_RuntimeError;
extern PyObject *PyExc_TypeError;
extern PyObject *PyExc_ValueError;
extern PyObject *PyExc_MemoryError;
extern PyObject *PyExc_IOError;

// Memory
extern void* PyMem_Malloc(size_t);
extern void* PyMem_Realloc(void *, size_t);
extern void PyMem_Free(void *);

// Argument parsing
extern int PyArg_ParseTuple(PyObject *, const char *, ...);
extern int PyArg_ParseTupleAndKeywords(PyObject *, PyObject *, const char *, char **, ...);
extern PyObject* Py_BuildValue(const char *, ...);

// Type checking
extern int PyObject_TypeCheck(PyObject *, PyTypeObject *);
extern int PyLong_Check(PyObject *);
extern int PyFloat_Check(PyObject *);
extern int PyUnicode_Check(PyObject *);
extern int PyBytes_Check(PyObject *);
extern int PyList_Check(PyObject *);
extern int PyTuple_Check(PyObject *);
extern int PyDict_Check(PyObject *);

// Capsules (for storing C pointers)
extern PyObject* PyCapsule_New(void *, const char *, void (*)(PyObject *));
extern void* PyCapsule_GetPointer(PyObject *, const char *);
extern int PyCapsule_SetPointer(PyObject *, void *);

// GIL
extern void PyEval_InitThreads(void);
extern int PyEval_ThreadsInitialized(void);

// Buffer protocol (for numpy-like arrays)
typedef struct {
    void *buf;
    PyObject *obj;
    Py_ssize_t len;
    Py_ssize_t itemsize;
    int readonly;
    int ndim;
    char *format;
    Py_ssize_t *shape;
    Py_ssize_t *strides;
    Py_ssize_t *suboffsets;
    void *internal;
} Py_buffer;

#define PyBUF_SIMPLE 0
#define PyBUF_WRITABLE 0x0001
#define PyBUF_FORMAT 0x0004
#define PyBUF_ND 0x0008
#define PyBUF_STRIDES (0x0010 | PyBUF_ND)
#define PyBUF_C_CONTIGUOUS (0x0020 | PyBUF_STRIDES)
#define PyBUF_F_CONTIGUOUS (0x0040 | PyBUF_STRIDES)
#define PyBUF_ANY_CONTIGUOUS (0x0080 | PyBUF_STRIDES)
#define PyBUF_INDIRECT (0x0100 | PyBUF_STRIDES)

extern int PyObject_GetBuffer(PyObject *, Py_buffer *, int);
extern void PyBuffer_Release(Py_buffer *);

// Memory view
extern PyObject* PyMemoryView_FromBuffer(Py_buffer *);
extern PyObject* PyMemoryView_FromMemory(char *, Py_ssize_t, int);

#define PyMemoryView_READ  0x100
#define PyMemoryView_WRITE 0x200

#ifdef __cplusplus
}
#endif

#endif // PY_STABLE_ABI_H_
