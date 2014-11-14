//python3 module for tinyobjloader
//
//usage:
// import tinyobjloader as tol
// model = tol.LoadObj(name)
// print(model["shapes"])
// print(model["materials"]
#include <Python.h>
#include <vector>
#include "tiny_obj_loader.h"

typedef std::vector<double> vectd;

PyObject*
pyTupleFromfloat3 (float array[3])
{
    int i;
    PyObject* tuple = PyTuple_New(3);

    for(i=0; i<=2 ; i++){
        PyTuple_SetItem(tuple, i, PyFloat_FromDouble(array[i]));
    }

    return tuple;
}

extern "C"
{

static PyObject*
pyLoadObj(PyObject* self, PyObject* args)
{
    PyObject *rtntpl, *pyshapes, *pymaterials;
    char const* filename;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;

    if(!PyArg_ParseTuple(args, "s", &filename))
        return NULL;

    tinyobj::LoadObj(shapes, materials, filename);

    pyshapes = PyDict_New();
    pymaterials = PyDict_New();
    rtntpl = PyDict_New();

    for (std::vector<tinyobj::shape_t>::iterator shape = shapes.begin() ;
         shape != shapes.end(); shape++)
    {
         PyObject *meshobj;
         PyObject *positions, *normals, *texcoords, *indices, *material_ids;

         meshobj = PyTuple_New(5);
         positions = PyList_New(0);
         normals = PyList_New(0);
         texcoords = PyList_New(0);
         indices = PyList_New(0);
         material_ids = PyList_New(0);

         tinyobj::mesh_t cm  = (*shape).mesh;
         for (int i = 0; i <= 4 ; i++ )
         {
            PyObject *current;
            vectd vect;

            switch  (i)
            {
                case 0: current = positions;
                        vect = vectd(cm.positions.begin(), cm.positions.end());
                case 1: current = normals;
                        vect = vectd(cm.normals.begin(), cm.normals.end());
                case 2: current = texcoords;
                        vect = vectd(cm.texcoords.begin(), cm.texcoords.end());
                case 3: current = indices;
                        vect = vectd(cm.indices.begin(), cm.indices.end());
                case 4: current = material_ids;
                        vect = vectd(cm.material_ids.begin(), cm.material_ids.end());
            }

            for (std::vector<double>::iterator it = vect.begin() ;
                it != vect.end(); it++)
            {
                PyList_Insert(current, it - vect.begin(), PyFloat_FromDouble(*it));
            }

            PyTuple_SetItem(meshobj, i, current);
         }

         PyDict_SetItemString(pyshapes, (*shape).name.c_str(), meshobj);
    }

    for (std::vector<tinyobj::material_t>::iterator mat = materials.begin() ;
         mat != materials.end(); mat++)
    {
        PyObject *matobj = PyDict_New();

        PyDict_SetItemString(matobj, "shininess",  PyFloat_FromDouble((*mat).shininess));
        PyDict_SetItemString(matobj, "ior",  PyFloat_FromDouble((*mat).ior));
        PyDict_SetItemString(matobj, "dissolve",  PyFloat_FromDouble((*mat).dissolve));
        PyDict_SetItemString(matobj, "illum",  PyLong_FromLong((*mat).illum));
        PyDict_SetItemString(matobj, "ambient_texname", PyUnicode_FromString((*mat).ambient_texname.c_str()));
        PyDict_SetItemString(matobj, "diffuse_texname", PyUnicode_FromString((*mat).diffuse_texname.c_str()));
        PyDict_SetItemString(matobj, "specular_texname", PyUnicode_FromString((*mat).specular_texname.c_str()));
        PyDict_SetItemString(matobj, "normal_texname", PyUnicode_FromString((*mat).normal_texname.c_str()));
        PyDict_SetItemString(matobj, "ambient", pyTupleFromfloat3((*mat).ambient));
        PyDict_SetItemString(matobj, "diffuse", pyTupleFromfloat3((*mat).diffuse));
        PyDict_SetItemString(matobj, "specular", pyTupleFromfloat3((*mat).specular));
        PyDict_SetItemString(matobj, "transmittance", pyTupleFromfloat3((*mat).transmittance));
        PyDict_SetItemString(matobj, "emission", pyTupleFromfloat3((*mat).emission));

        PyDict_SetItemString(pymaterials, (*mat).name.c_str(), matobj);
    }

    PyDict_SetItemString(rtntpl, "shapes", pyshapes);
    PyDict_SetItemString(rtntpl, "materials", pymaterials);

    return rtntpl;
}


static PyMethodDef mMethods[] = {

{"LoadObj", pyLoadObj, METH_VARARGS},
{NULL, NULL, 0, NULL}

};


static struct PyModuleDef moduledef = {
    PyModuleDef_HEAD_INIT,
    "tinyobjloader",
    NULL,
    -1,
    mMethods
};


PyMODINIT_FUNC
PyInit_tinyobjloader(void)
{
    return PyModule_Create(&moduledef);
}

}
