// python2/3 module for tinyobjloader
//
// usage:
// import tinyobjloader as tol
// model = tol.LoadObj(name)
// print(model["shapes"])
// print(model["materials"]
// note:
//   `shape.mesh.index_t` is represented as flattened array: (vertex_index, normal_index, texcoord_index) * num_faces

#include <Python.h>
#include <vector>
#include "../tiny_obj_loader.h"

typedef std::vector<double> vectd;
typedef std::vector<int> vecti;

PyObject* pyTupleFromfloat3(float array[3]) {
  int i;
  PyObject* tuple = PyTuple_New(3);

  for (i = 0; i <= 2; i++) {
    PyTuple_SetItem(tuple, i, PyFloat_FromDouble(array[i]));
  }

  return tuple;
}

extern "C" {

static PyObject* pyLoadObj(PyObject* self, PyObject* args) {
  PyObject *rtndict, *pyshapes, *pymaterials, *pymaterial_indices, *attribobj, *current, *meshobj;

  char const* current_name;
  char const* filename;
  vectd vect;
  std::vector<tinyobj::index_t> indices;
  std::vector<unsigned char> face_verts;

  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;

  if (!PyArg_ParseTuple(args, "s", &filename)) return NULL;

  std::string err;
  tinyobj::LoadObj(&attrib, &shapes, &materials, &err, filename);

  pyshapes = PyDict_New();
  pymaterials = PyDict_New();
  pymaterial_indices = PyList_New(0);
  rtndict = PyDict_New();

  attribobj = PyDict_New();

  for (int i = 0; i <= 2; i++) {
    current = PyList_New(0);

    switch (i) {
      case 0:
        current_name = "vertices";
        vect = vectd(attrib.vertices.begin(), attrib.vertices.end());
        break;
      case 1:
        current_name = "normals";
        vect = vectd(attrib.normals.begin(), attrib.normals.end());
        break;
      case 2:
        current_name = "texcoords";
        vect = vectd(attrib.texcoords.begin(), attrib.texcoords.end());
        break;
    }

    for (vectd::iterator it = vect.begin(); it != vect.end(); it++) {
      PyList_Insert(current, it - vect.begin(), PyFloat_FromDouble(*it));
    }

    PyDict_SetItemString(attribobj, current_name, current);
  }

  for (std::vector<tinyobj::shape_t>::iterator shape = shapes.begin();
       shape != shapes.end(); shape++) {
    meshobj = PyDict_New();
    tinyobj::mesh_t cm = (*shape).mesh;

    {
      current = PyList_New(0);

      for (size_t i = 0; i < cm.indices.size(); i++) {
        // Flatten index array: v_idx, vn_idx, vt_idx, v_idx, vn_idx, vt_idx,
        // ...
        PyList_Insert(current, 3 * i + 0,
                      PyLong_FromLong(cm.indices[i].vertex_index));
        PyList_Insert(current, 3 * i + 1,
                      PyLong_FromLong(cm.indices[i].normal_index));
        PyList_Insert(current, 3 * i + 2,
                      PyLong_FromLong(cm.indices[i].texcoord_index));
      }

      PyDict_SetItemString(meshobj, "indices", current);
    }

    {
      current = PyList_New(0);

      for (size_t i = 0; i < cm.num_face_vertices.size(); i++) {
        // Widen data type to long.
        PyList_Insert(current, i, PyLong_FromLong(cm.num_face_vertices[i]));
      }

      PyDict_SetItemString(meshobj, "num_face_vertices", current);
    }

    {
      current = PyList_New(0);

      for (size_t i = 0; i < cm.material_ids.size(); i++) {
        PyList_Insert(current, i, PyLong_FromLong(cm.material_ids[i]));
      }

      PyDict_SetItemString(meshobj, "material_ids", current);
    }

    PyDict_SetItemString(pyshapes, (*shape).name.c_str(), meshobj);
  }

  for (std::vector<tinyobj::material_t>::iterator mat = materials.begin();
       mat != materials.end(); mat++) {
    PyObject* matobj = PyDict_New();
    PyObject* unknown_parameter = PyDict_New();

    for (std::map<std::string, std::string>::iterator p =
             mat->unknown_parameter.begin();
         p != mat->unknown_parameter.end(); ++p) {
      PyDict_SetItemString(unknown_parameter, p->first.c_str(),
                           PyUnicode_FromString(p->second.c_str()));
    }

    PyDict_SetItemString(matobj, "shininess",
                         PyFloat_FromDouble(mat->shininess));
    PyDict_SetItemString(matobj, "ior", PyFloat_FromDouble(mat->ior));
    PyDict_SetItemString(matobj, "dissolve",
                         PyFloat_FromDouble(mat->dissolve));
    PyDict_SetItemString(matobj, "illum", PyLong_FromLong(mat->illum));
    PyDict_SetItemString(matobj, "ambient_texname",
                         PyUnicode_FromString(mat->ambient_texname.c_str()));
    PyDict_SetItemString(matobj, "diffuse_texname",
                         PyUnicode_FromString(mat->diffuse_texname.c_str()));
    PyDict_SetItemString(matobj, "specular_texname",
                         PyUnicode_FromString(mat->specular_texname.c_str()));
    PyDict_SetItemString(
        matobj, "specular_highlight_texname",
        PyUnicode_FromString(mat->specular_highlight_texname.c_str()));
    PyDict_SetItemString(matobj, "bump_texname",
                         PyUnicode_FromString(mat->bump_texname.c_str()));
    PyDict_SetItemString(
        matobj, "displacement_texname",
        PyUnicode_FromString(mat->displacement_texname.c_str()));
    PyDict_SetItemString(matobj, "alpha_texname",
                         PyUnicode_FromString(mat->alpha_texname.c_str()));
    PyDict_SetItemString(matobj, "ambient", pyTupleFromfloat3(mat->ambient));
    PyDict_SetItemString(matobj, "diffuse", pyTupleFromfloat3(mat->diffuse));
    PyDict_SetItemString(matobj, "specular",
                         pyTupleFromfloat3(mat->specular));
    PyDict_SetItemString(matobj, "transmittance",
                         pyTupleFromfloat3(mat->transmittance));
    PyDict_SetItemString(matobj, "emission",
                         pyTupleFromfloat3(mat->emission));
    PyDict_SetItemString(matobj, "unknown_parameter", unknown_parameter);

    PyDict_SetItemString(pymaterials, mat->name.c_str(), matobj);
    PyList_Append(pymaterial_indices, PyUnicode_FromString(mat->name.c_str()));
  }

  PyDict_SetItemString(rtndict, "shapes", pyshapes);
  PyDict_SetItemString(rtndict, "materials", pymaterials);
  PyDict_SetItemString(rtndict, "material_indices", pymaterial_indices);
  PyDict_SetItemString(rtndict, "attribs", attribobj);

  return rtndict;
}

static PyMethodDef mMethods[] = {

    {"LoadObj", pyLoadObj, METH_VARARGS}, {NULL, NULL, 0, NULL}

};

#if PY_MAJOR_VERSION >= 3

static struct PyModuleDef moduledef = {PyModuleDef_HEAD_INIT, "tinyobjloader",
                                       NULL, -1, mMethods};

PyMODINIT_FUNC PyInit_tinyobjloader(void) {
  return PyModule_Create(&moduledef);
}

#else

PyMODINIT_FUNC inittinyobjloader(void) {
  Py_InitModule3("tinyobjloader", mMethods, NULL);
}

#endif  // PY_MAJOR_VERSION >= 3

}
