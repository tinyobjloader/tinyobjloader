#ifdef __EMSCRIPTEN__
#include <emscripten/bind.h>
#else
#error "Need to compile with emcc"
#endif

#define TINYOBJLOADER_USE_DOUBLE
#define TINYOBJLOADER_USE_MAPBOX_EARCUT
#define TINYOBJLOADER_IMPLEMENTATION
#include "tiny_obj_loader.h"


#ifdef __EMSCRIPTEN__
EMSCRIPTEN_BINDINGS(tinyobj)
{
  emscripten::class_<tinyobj::ObjReaderConfig>("ObjReaderConfig")
    .constructor<>()
    .property("triangulation_method", &tinyobj::ObjReaderConfig::triangulation_method)
    .property("vertex_color", &tinyobj::ObjReaderConfig::vertex_color)
    .property("mtl_search_path", &tinyobj::ObjReaderConfig::mtl_search_path)
      ;

  emscripten::class_<tinyobj::attrib_t>("attrib_t")
      .constructor<>()
      .function("GetVertices", &tinyobj::attrib_t::GetVertices)
      ;

  emscripten::class_<tinyobj::ObjReader>("ObjReader")
      .constructor<>()
      //.function("ParseFromFile", &tinyobj::ObjReader::ParseFromFile) // TODO
      .function("ParseFromString", &tinyobj::ObjReader::ParseFromString)
      .function("Valid", &tinyobj::ObjReader::Valid)
      .function("GetAttrib", &tinyobj::ObjReader::GetAttrib)
      .function("GetShapes", &tinyobj::ObjReader::GetShapes)
      ;

  emscripten::register_vector<int>("vector<int>");
  emscripten::register_vector<double>("vector<double>");
}
#endif
