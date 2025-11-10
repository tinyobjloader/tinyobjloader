/*
 * TinyObjLoader v3 Python Bindings
 *
 * Uses Python Stable ABI (abi3) for Python 3.10+
 *
 * To build without Python headers, define NO_PYTHON_H
 * Otherwise uses standard Python.h with limited API
 */

#define Py_LIMITED_API 0x030A0000

#ifdef NO_PYTHON_H
  #include "py_stable_abi.h"
#else
  #include <Python.h>
#endif

#include "../tinyobj_v3.hh"
#include <string>
#include <vector>
#include <memory>

using namespace tinyobj;
using namespace tinyobj::v3;

// ============================================================================
// Type definitions for Python objects wrapping C++ types
// ============================================================================

typedef struct {
    PyObject_HEAD
    ObjParser *parser;
} PyObjParser;

typedef struct {
    PyObject_HEAD
    ParseResult *result;
    bool owns_data;  // Whether this object owns the ParseResult
} PyParseResult;

typedef struct {
    PyObject_HEAD
    attrib_t *attrib;
    bool owns_data;
} PyAttrib;

typedef struct {
    PyObject_HEAD
    ParserConfig config;
} PyParserConfig;

// Forward declarations
static PyTypeObject *PyObjParserType = NULL;
static PyTypeObject *PyParseResultType = NULL;
static PyTypeObject *PyAttribType = NULL;
static PyTypeObject *PyParserConfigType = NULL;

// ============================================================================
// PyParserConfig - Wraps tinyobj::v3::ParserConfig
// ============================================================================

static PyObject* PyParserConfig_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    PyParserConfig *self = (PyParserConfig *)type->tp_alloc(type, 0);
    if (self != NULL) {
        new (&self->config) ParserConfig();
    }
    return (PyObject *)self;
}

static void PyParserConfig_dealloc(PyObject *self) {
    PyParserConfig *config = (PyParserConfig *)self;
    config->config.~ParserConfig();
    Py_TYPE(self)->tp_free(self);
}

static PyObject* PyParserConfig_get_triangulate(PyObject *self, void *closure) {
    PyParserConfig *config = (PyParserConfig *)self;
    return PyBool_FromLong(config->config.triangulate);
}

static int PyParserConfig_set_triangulate(PyObject *self, PyObject *value, void *closure) {
    PyParserConfig *config = (PyParserConfig *)self;
    if (!PyLong_Check(value) && value != Py_True && value != Py_False) {
        PyErr_SetString(PyExc_TypeError, "triangulate must be a boolean");
        return -1;
    }
    config->config.triangulate = PyObject_IsTrue(value);
    return 0;
}

static PyGetSetDef PyParserConfig_getset[] = {
    {(char*)"triangulate", PyParserConfig_get_triangulate, PyParserConfig_set_triangulate,
     (char*)"Enable automatic triangulation of polygons", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

// ============================================================================
// PyAttrib - Wraps tinyobj::attrib_t
// ============================================================================

static void PyAttrib_dealloc(PyObject *self) {
    PyAttrib *attrib = (PyAttrib *)self;
    if (attrib->owns_data && attrib->attrib) {
        delete attrib->attrib;
    }
    Py_TYPE(self)->tp_free(self);
}

static PyObject* PyAttrib_get_vertices(PyObject *self, void *closure) {
    PyAttrib *attrib = (PyAttrib *)self;
    if (!attrib->attrib) {
        Py_RETURN_NONE;
    }

    const std::vector<real_t> &verts = attrib->attrib->vertices;
    PyObject *list = PyList_New(verts.size());
    if (!list) return NULL;

    for (size_t i = 0; i < verts.size(); i++) {
        PyObject *val = PyFloat_FromDouble(verts[i]);
        if (!val) {
            Py_DecRef(list);
            return NULL;
        }
        PyList_SetItem(list, i, val);
    }
    return list;
}

static PyObject* PyAttrib_get_normals(PyObject *self, void *closure) {
    PyAttrib *attrib = (PyAttrib *)self;
    if (!attrib->attrib) {
        Py_RETURN_NONE;
    }

    const std::vector<real_t> &normals = attrib->attrib->normals;
    PyObject *list = PyList_New(normals.size());
    if (!list) return NULL;

    for (size_t i = 0; i < normals.size(); i++) {
        PyObject *val = PyFloat_FromDouble(normals[i]);
        if (!val) {
            Py_DecRef(list);
            return NULL;
        }
        PyList_SetItem(list, i, val);
    }
    return list;
}

static PyObject* PyAttrib_get_texcoords(PyObject *self, void *closure) {
    PyAttrib *attrib = (PyAttrib *)self;
    if (!attrib->attrib) {
        Py_RETURN_NONE;
    }

    const std::vector<real_t> &texcoords = attrib->attrib->texcoords;
    PyObject *list = PyList_New(texcoords.size());
    if (!list) return NULL;

    for (size_t i = 0; i < texcoords.size(); i++) {
        PyObject *val = PyFloat_FromDouble(texcoords[i]);
        if (!val) {
            Py_DecRef(list);
            return NULL;
        }
        PyList_SetItem(list, i, val);
    }
    return list;
}

static PyObject* PyAttrib_get_colors(PyObject *self, void *closure) {
    PyAttrib *attrib = (PyAttrib *)self;
    if (!attrib->attrib) {
        Py_RETURN_NONE;
    }

    const std::vector<real_t> &colors = attrib->attrib->colors;
    PyObject *list = PyList_New(colors.size());
    if (!list) return NULL;

    for (size_t i = 0; i < colors.size(); i++) {
        PyObject *val = PyFloat_FromDouble(colors[i]);
        if (!val) {
            Py_DecRef(list);
            return NULL;
        }
        PyList_SetItem(list, i, val);
    }
    return list;
}

static PyGetSetDef PyAttrib_getset[] = {
    {(char*)"vertices", PyAttrib_get_vertices, NULL,
     (char*)"Vertex positions (flat list of x,y,z triplets)", NULL},
    {(char*)"normals", PyAttrib_get_normals, NULL,
     (char*)"Vertex normals (flat list of x,y,z triplets)", NULL},
    {(char*)"texcoords", PyAttrib_get_texcoords, NULL,
     (char*)"Texture coordinates (flat list of u,v pairs)", NULL},
    {(char*)"colors", PyAttrib_get_colors, NULL,
     (char*)"Vertex colors (flat list of r,g,b triplets)", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

// ============================================================================
// PyParseResult - Wraps tinyobj::v3::ParseResult
// ============================================================================

static void PyParseResult_dealloc(PyObject *self) {
    PyParseResult *result = (PyParseResult *)self;
    if (result->owns_data && result->result) {
        delete result->result;
    }
    Py_TYPE(self)->tp_free(self);
}

static PyObject* PyParseResult_success(PyObject *self, PyObject *args) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        PyErr_SetString(PyExc_RuntimeError, "Invalid ParseResult object");
        return NULL;
    }
    return PyBool_FromLong(result->result->success());
}

static PyObject* PyParseResult_get_attributes(PyObject *self, void *closure) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        Py_RETURN_NONE;
    }

    PyAttrib *attrib_obj = (PyAttrib *)PyAttribType->tp_alloc(PyAttribType, 0);
    if (!attrib_obj) return NULL;

    attrib_obj->attrib = &result->result->attributes();
    attrib_obj->owns_data = false;  // ParseResult owns this

    return (PyObject *)attrib_obj;
}

static PyObject* PyParseResult_get_shapes(PyObject *self, void *closure) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        Py_RETURN_NONE;
    }

    const std::vector<shape_t> &shapes = result->result->shapes();
    PyObject *list = PyList_New(shapes.size());
    if (!list) return NULL;

    for (size_t i = 0; i < shapes.size(); i++) {
        // Create a dict for each shape
        PyObject *shape_dict = PyDict_New();
        if (!shape_dict) {
            Py_DecRef(list);
            return NULL;
        }

        // Add name
        PyObject *name = PyUnicode_FromString(shapes[i].name.c_str());
        PyDict_SetItemString(shape_dict, "name", name);
        Py_DecRef(name);

        // Add mesh info
        const mesh_t &mesh = shapes[i].mesh;
        PyObject *mesh_dict = PyDict_New();

        // num_face_vertices
        PyObject *nfv_list = PyList_New(mesh.num_face_vertices.size());
        for (size_t j = 0; j < mesh.num_face_vertices.size(); j++) {
            PyList_SetItem(nfv_list, j, PyLong_FromLong(mesh.num_face_vertices[j]));
        }
        PyDict_SetItemString(mesh_dict, "num_face_vertices", nfv_list);
        Py_DecRef(nfv_list);

        // indices (as list of tuples)
        PyObject *indices_list = PyList_New(mesh.indices.size());
        for (size_t j = 0; j < mesh.indices.size(); j++) {
            PyObject *idx_tuple = PyTuple_New(3);
            PyTuple_SetItem(idx_tuple, 0, PyLong_FromLong(mesh.indices[j].vertex_index));
            PyTuple_SetItem(idx_tuple, 1, PyLong_FromLong(mesh.indices[j].normal_index));
            PyTuple_SetItem(idx_tuple, 2, PyLong_FromLong(mesh.indices[j].texcoord_index));
            PyList_SetItem(indices_list, j, idx_tuple);
        }
        PyDict_SetItemString(mesh_dict, "indices", indices_list);
        Py_DecRef(indices_list);

        // material_ids
        PyObject *matid_list = PyList_New(mesh.material_ids.size());
        for (size_t j = 0; j < mesh.material_ids.size(); j++) {
            PyList_SetItem(matid_list, j, PyLong_FromLong(mesh.material_ids[j]));
        }
        PyDict_SetItemString(mesh_dict, "material_ids", matid_list);
        Py_DecRef(matid_list);

        PyDict_SetItemString(shape_dict, "mesh", mesh_dict);
        Py_DecRef(mesh_dict);

        PyList_SetItem(list, i, shape_dict);
    }

    return list;
}

static PyObject* PyParseResult_get_materials(PyObject *self, void *closure) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        Py_RETURN_NONE;
    }

    const std::vector<material_t> &materials = result->result->materials();
    PyObject *list = PyList_New(materials.size());
    if (!list) return NULL;

    for (size_t i = 0; i < materials.size(); i++) {
        const material_t &mat = materials[i];
        PyObject *mat_dict = PyDict_New();
        if (!mat_dict) {
            Py_DecRef(list);
            return NULL;
        }

        // Add material properties
        PyObject *name = PyUnicode_FromString(mat.name.c_str());
        PyDict_SetItemString(mat_dict, "name", name);
        Py_DecRef(name);

        // Add float properties
        PyDict_SetItemString(mat_dict, "shininess", PyFloat_FromDouble(mat.shininess));
        PyDict_SetItemString(mat_dict, "ior", PyFloat_FromDouble(mat.ior));
        PyDict_SetItemString(mat_dict, "dissolve", PyFloat_FromDouble(mat.dissolve));
        PyDict_SetItemString(mat_dict, "illum", PyLong_FromLong(mat.illum));

        // PBR properties
        PyDict_SetItemString(mat_dict, "roughness", PyFloat_FromDouble(mat.roughness));
        PyDict_SetItemString(mat_dict, "metallic", PyFloat_FromDouble(mat.metallic));
        PyDict_SetItemString(mat_dict, "sheen", PyFloat_FromDouble(mat.sheen));

        // Texture names
        if (!mat.ambient_texname.empty()) {
            PyObject *tex = PyUnicode_FromString(mat.ambient_texname.c_str());
            PyDict_SetItemString(mat_dict, "ambient_texname", tex);
            Py_DecRef(tex);
        }
        if (!mat.diffuse_texname.empty()) {
            PyObject *tex = PyUnicode_FromString(mat.diffuse_texname.c_str());
            PyDict_SetItemString(mat_dict, "diffuse_texname", tex);
            Py_DecRef(tex);
        }

        PyList_SetItem(list, i, mat_dict);
    }

    return list;
}

static PyObject* PyParseResult_get_errors(PyObject *self, void *closure) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        Py_RETURN_NONE;
    }

    const ErrorStack &errors = result->result->errors();
    std::string error_str = errors.formatErrors();

    return PyUnicode_FromString(error_str.c_str());
}

static PyObject* PyParseResult_get_stats(PyObject *self, void *closure) {
    PyParseResult *result = (PyParseResult *)self;
    if (!result->result) {
        Py_RETURN_NONE;
    }

    const ParseResult::Stats &stats = result->result->stats();
    PyObject *stats_dict = PyDict_New();
    if (!stats_dict) return NULL;

    PyDict_SetItemString(stats_dict, "vertices_parsed", PyLong_FromSize_t(stats.vertices_parsed));
    PyDict_SetItemString(stats_dict, "normals_parsed", PyLong_FromSize_t(stats.normals_parsed));
    PyDict_SetItemString(stats_dict, "texcoords_parsed", PyLong_FromSize_t(stats.texcoords_parsed));
    PyDict_SetItemString(stats_dict, "faces_parsed", PyLong_FromSize_t(stats.faces_parsed));
    PyDict_SetItemString(stats_dict, "triangles_generated", PyLong_FromSize_t(stats.triangles_generated));
    PyDict_SetItemString(stats_dict, "materials_loaded", PyLong_FromSize_t(stats.materials_loaded));
    PyDict_SetItemString(stats_dict, "bytes_processed", PyLong_FromSize_t(stats.bytes_processed));
    PyDict_SetItemString(stats_dict, "parse_time_seconds", PyFloat_FromDouble(stats.parse_time_seconds));

    return stats_dict;
}

static PyMethodDef PyParseResult_methods[] = {
    {"success", PyParseResult_success, METH_NOARGS,
     "Check if parsing was successful (no fatal errors)"},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyParseResult_getset[] = {
    {(char*)"attributes", PyParseResult_get_attributes, NULL,
     (char*)"Vertex attributes (positions, normals, texcoords, colors)", NULL},
    {(char*)"shapes", PyParseResult_get_shapes, NULL,
     (char*)"List of shapes in the model", NULL},
    {(char*)"materials", PyParseResult_get_materials, NULL,
     (char*)"List of materials", NULL},
    {(char*)"errors", PyParseResult_get_errors, NULL,
     (char*)"Error and warning messages", NULL},
    {(char*)"stats", PyParseResult_get_stats, NULL,
     (char*)"Parsing statistics", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

// ============================================================================
// PyObjParser - Wraps tinyobj::v3::ObjParser
// ============================================================================

static PyObject* PyObjParser_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    PyObjParser *self = (PyObjParser *)type->tp_alloc(type, 0);
    if (self != NULL) {
        PyObject *config_obj = NULL;
        static char *kwlist[] = {(char*)"config", NULL};

        if (!PyArg_ParseTupleAndKeywords(args, kwds, "|O", kwlist, &config_obj)) {
            Py_DecRef((PyObject*)self);
            return NULL;
        }

        if (config_obj && PyObject_TypeCheck(config_obj, PyParserConfigType)) {
            PyParserConfig *config = (PyParserConfig *)config_obj;
            self->parser = new ObjParser(config->config);
        } else {
            self->parser = new ObjParser();
        }
    }
    return (PyObject *)self;
}

static void PyObjParser_dealloc(PyObject *self) {
    PyObjParser *parser = (PyObjParser *)self;
    if (parser->parser) {
        delete parser->parser;
    }
    Py_TYPE(self)->tp_free(self);
}

static PyObject* PyObjParser_parse_from_string(PyObject *self, PyObject *args) {
    PyObjParser *parser = (PyObjParser *)self;
    if (!parser->parser) {
        PyErr_SetString(PyExc_RuntimeError, "Invalid ObjParser object");
        return NULL;
    }

    const char *content;
    Py_ssize_t content_len;
    if (!PyArg_ParseTuple(args, "s#", &content, &content_len)) {
        return NULL;
    }

    ParseResult *result = new ParseResult();
    *result = parser->parser->parseFromString(std::string(content, content_len));

    PyParseResult *py_result = (PyParseResult *)PyParseResultType->tp_alloc(PyParseResultType, 0);
    if (!py_result) {
        delete result;
        return NULL;
    }

    py_result->result = result;
    py_result->owns_data = true;

    return (PyObject *)py_result;
}

static PyObject* PyObjParser_parse_from_memory(PyObject *self, PyObject *args) {
    PyObjParser *parser = (PyObjParser *)self;
    if (!parser->parser) {
        PyErr_SetString(PyExc_RuntimeError, "Invalid ObjParser object");
        return NULL;
    }

    const char *data;
    Py_ssize_t size;
    if (!PyArg_ParseTuple(args, "s#", &data, &size)) {
        return NULL;
    }

    ParseResult *result = new ParseResult();
    *result = parser->parser->parseFromMemory(data, size);

    PyParseResult *py_result = (PyParseResult *)PyParseResultType->tp_alloc(PyParseResultType, 0);
    if (!py_result) {
        delete result;
        return NULL;
    }

    py_result->result = result;
    py_result->owns_data = true;

    return (PyObject *)py_result;
}

static PyMethodDef PyObjParser_methods[] = {
    {"parse_from_string", PyObjParser_parse_from_string, METH_VARARGS,
     "Parse OBJ data from a string"},
    {"parse_from_memory", PyObjParser_parse_from_memory, METH_VARARGS,
     "Parse OBJ data from a memory buffer"},
    {NULL, NULL, 0, NULL}
};

// ============================================================================
// Module initialization
// ============================================================================

static PyMethodDef module_methods[] = {
    {NULL, NULL, 0, NULL}
};

static PyModuleDef tinyobjloader_v3_module = {
    PyModuleDef_HEAD_INIT,
    NULL,  // m_init
    "tinyobjloader_v3",
    "TinyObjLoader v3 - Modern C++14 Wavefront OBJ parser with stable Python ABI",
    -1,
    module_methods,
    NULL,  // m_slots
    NULL,  // m_traverse
    NULL,  // m_clear
    NULL   // m_free
};

extern "C" {

PyMODINIT_FUNC PyInit_tinyobjloader_v3(void) {
    PyObject *module = PyModule_Create2(&tinyobjloader_v3_module, Py_LIMITED_API);
    if (!module) return NULL;

    // Define ParserConfig type
    PyType_Slot parserconfig_slots[] = {
        {Py_tp_new, (void*)PyParserConfig_new},
        {Py_tp_dealloc, (void*)PyParserConfig_dealloc},
        {Py_tp_getset, (void*)PyParserConfig_getset},
        {Py_tp_doc, (void*)"Parser configuration options"},
        {0, NULL}
    };

    PyType_Spec parserconfig_spec = {
        "tinyobjloader_v3.ParserConfig",
        sizeof(PyParserConfig),
        0,
        Py_TPFLAGS_DEFAULT,
        parserconfig_slots
    };

    PyParserConfigType = (PyTypeObject*)PyType_FromSpec(&parserconfig_spec);
    if (!PyParserConfigType) return NULL;
    PyModule_AddObject(module, "ParserConfig", (PyObject*)PyParserConfigType);

    // Define Attrib type
    PyType_Slot attrib_slots[] = {
        {Py_tp_dealloc, (void*)PyAttrib_dealloc},
        {Py_tp_getset, (void*)PyAttrib_getset},
        {Py_tp_doc, (void*)"Vertex attributes container"},
        {0, NULL}
    };

    PyType_Spec attrib_spec = {
        "tinyobjloader_v3.Attrib",
        sizeof(PyAttrib),
        0,
        Py_TPFLAGS_DEFAULT,
        attrib_slots
    };

    PyAttribType = (PyTypeObject*)PyType_FromSpec(&attrib_spec);
    if (!PyAttribType) return NULL;
    PyModule_AddObject(module, "Attrib", (PyObject*)PyAttribType);

    // Define ParseResult type
    PyType_Slot parseresult_slots[] = {
        {Py_tp_dealloc, (void*)PyParseResult_dealloc},
        {Py_tp_methods, (void*)PyParseResult_methods},
        {Py_tp_getset, (void*)PyParseResult_getset},
        {Py_tp_doc, (void*)"Parse result containing attributes, shapes, materials, and errors"},
        {0, NULL}
    };

    PyType_Spec parseresult_spec = {
        "tinyobjloader_v3.ParseResult",
        sizeof(PyParseResult),
        0,
        Py_TPFLAGS_DEFAULT,
        parseresult_slots
    };

    PyParseResultType = (PyTypeObject*)PyType_FromSpec(&parseresult_spec);
    if (!PyParseResultType) return NULL;
    PyModule_AddObject(module, "ParseResult", (PyObject*)PyParseResultType);

    // Define ObjParser type
    PyType_Slot objparser_slots[] = {
        {Py_tp_new, (void*)PyObjParser_new},
        {Py_tp_dealloc, (void*)PyObjParser_dealloc},
        {Py_tp_methods, (void*)PyObjParser_methods},
        {Py_tp_doc, (void*)"Wavefront OBJ parser (v3 API)"},
        {0, NULL}
    };

    PyType_Spec objparser_spec = {
        "tinyobjloader_v3.ObjParser",
        sizeof(PyObjParser),
        0,
        Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,
        objparser_slots
    };

    PyObjParserType = (PyTypeObject*)PyType_FromSpec(&objparser_spec);
    if (!PyObjParserType) return NULL;
    PyModule_AddObject(module, "ObjParser", (PyObject*)PyObjParserType);

    // Add version info
    PyModule_AddStringConstant(module, "__version__", "3.0.0");

    return module;
}

} // extern "C"
