#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "tiny_obj_loader.h"


namespace py = pybind11;

using namespace tinyobj;

// Simple wrapper for LoadObj.
// TODO(syoyo): Make it more pythonic.
bool load_obj(attrib_t *attrib, std::vector<shape_t> *shapes,
              std::vector<material_t> *materials,
              std::string *warn, std::string *err,
              const std::string &filename,
              const std::string &mtl_basedir = "./",
              bool triangulate = true,
              bool default_vcols_fallback = true)
{
  return LoadObj(attrib, shapes, materials, warn, err, filename.c_str(), mtl_basedir.c_str(), triangulate, default_vcols_fallback);
}

// Simple wrapper for LoadMtl.
// TODO(syoyo): Make it more pythonic.
void load_mtl(std::map<std::string, int> *material_map,
             std::vector<material_t> *materials, std::istream *inStream,
             std::string *warning, std::string *err) {
  LoadMtl(material_map, materials, inStream, warning, err);
}


PYBIND11_MODULE(tinyobjloader, tobj_module)
{
  tobj_module.doc() = "Python bindings for TinyObjLoader.";

  // register struct
  // py::init<>() for default constructor
  py::class_<attrib_t>(tobj_module, "Attrib")
    .def(py::init<>());
  py::class_<shape_t>(tobj_module, "Shape")
    .def(py::init<>());
  py::class_<material_t>(tobj_module, "Material")
    .def(py::init<>());

  tobj_module.def("load_obj", &load_obj, "Load wavefront .obj file.");
  tobj_module.def("load_mtl", &load_mtl, "Load wavefront material file.");
}

