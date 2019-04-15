#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "tiny_obj_loader.h"


namespace py = pybind11;

using namespace tinyobj;

PYBIND11_MODULE(tinyobj, tobj_module)
{
  tobj_module.doc() = "Python bindings for TinyObjLoader.";

  // register struct
  py::class_<ObjReaderConfig>(tobj_module, "ObjReaderConfig")
    .def(py::init<>())
    .def_readwrite("triangulate", &ObjReaderConfig::triangulate);

  // py::init<>() for default constructor
  py::class_<ObjReader>(tobj_module, "ObjReader")
    .def(py::init<>())
    .def("ParseFromFile", &ObjReader::ParseFromFile, py::arg("filename"), py::arg("option") = ObjReaderConfig())
    .def("ParseFromString", &ObjReader::ParseFromString, py::arg("obj_text"), py::arg("mtl_text"), py::arg("option") = ObjReaderConfig())
    .def("Valid", &ObjReader::Valid)
    .def("GetAttrib", &ObjReader::GetAttrib)
    .def("GetShapes", &ObjReader::GetShapes)
    .def("GetMaterials", &ObjReader::GetMaterials)
    .def("Warning", &ObjReader::Warning)
    .def("Error", &ObjReader::Error);

  py::class_<attrib_t>(tobj_module, "attrib_t")
    .def(py::init<>())
    .def_property_readonly("vertices", &attrib_t::GetVertices);

  py::class_<shape_t>(tobj_module, "shape_t")
    .def(py::init<>())
    .def_readwrite("name", &shape_t::name)
    .def_readwrite("mesh", &shape_t::mesh)
    .def_readwrite("lines", &shape_t::lines)
    .def_readwrite("points", &shape_t::points);

  py::class_<index_t>(tobj_module, "index_t")
    .def(py::init<>())
    .def_readwrite("vertex_index", &index_t::vertex_index)
    .def_readwrite("normal_index", &index_t::normal_index)
    .def_readwrite("texcoord_index", &index_t::texcoord_index)
    ;

  // TODO(syoyo): write more bindings
  py::class_<material_t>(tobj_module, "material_t")
    .def(py::init<>());

  py::class_<mesh_t>(tobj_module, "mesh_t")
    .def(py::init<>())
    .def_readonly("indices", &mesh_t::indices);

  py::class_<lines_t>(tobj_module, "lines_t")
    .def(py::init<>());

  py::class_<points_t>(tobj_module, "points_t")
    .def(py::init<>());

}

