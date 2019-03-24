#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "tiny_obj_loader.h"


namespace py = pybind11;

using namespace tinyobj;

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
  py::class_<ObjLoader>(tobj_module, "ObjLoader")
    .def(py::init<>())
    .def("Load", &ObjLoader::Load)
    .def("Valid", &ObjLoader::Valid)
    .def("GetAttrib", &ObjLoader::GetAttrib)
    .def("GetShapes", &ObjLoader::GetShapes)
    .def("GetMaterials", &ObjLoader::GetMaterials)
    .def("Warning", &ObjLoader::Warning)
    .def("Error", &ObjLoader::Error);

  py::class_<attrib_t>(tobj_module, "attrib_t")
    .def(py::init<>())
    .def_property_readonly("vertices", &attrib_t::GetVertices);

  py::class_<shape_t>(tobj_module, "shape_t")
    .def(py::init<>());

  py::class_<material_t>(tobj_module, "material_t")
    .def(py::init<>());

  py::class_<ObjLoaderConfig>(tobj_module, "ObjLoaderConfig")
    .def(py::init<>());

}

