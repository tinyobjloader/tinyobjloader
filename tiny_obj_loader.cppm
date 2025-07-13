module;

#define TINYOBJLOADER_IMPLEMENTATION // optional
#include <tiny_obj_loader.h>

export module tinyobj;


export namespace tinyobj {
    using tinyobj::real_t;
    using tinyobj::texture_type_t;
    using tinyobj::texture_option_t;
    using tinyobj::material_t;

#ifdef TINY_OBJ_LOADER_PYTHON_BINDING
    using tinyobj::GetDiffuse;
    using tinyobj::GetSpecular;
    using tinyobj::GetTransmittance;
    using tinyobj::GetEmission;
    using tinyobj::GetAmbient;
    using tinyobj::SetDiffuse;
    using tinyobj::SetAmbient;
    using tinyobj::SetSpecular;
    using tinyobj::SetTransmittance;
    using tinyobj::GetCustomParameter;
#endif // TINY_OBJ_LOADER_PYTHON_BINDING

    using tinyobj::tag_t;
    using tinyobj::joint_and_weight_t;
    using tinyobj::skin_weight_t;
    using tinyobj::index_t;
    using tinyobj::mesh_t;
    using tinyobj::lines_t;
    using tinyobj::points_t;
    using tinyobj::shape_t;
    using tinyobj::attrib_t;
    using tinyobj::callback_t;
    using tinyobj::MaterialReader;
    using tinyobj::MaterialFileReader;
    using tinyobj::MaterialStreamReader;
    using tinyobj::ObjReaderConfig;
    using tinyobj::ObjReader;
    using tinyobj::LoadObj;
    using tinyobj::LoadObjWithCallback;
    using tinyobj::LoadMtl;
    using tinyobj::ParseTextureNameAndOption;


    using tinyobj::vertex_index_t;
    using tinyobj::face_t;
    using tinyobj::__line_t;
    using tinyobj::__points_t;
    using tinyobj::tag_sizes;
    using tinyobj::obj_shape;
    using tinyobj::PrimGroup;

    using tinyobj::warning_context;

    using tinyobj::TinyObjPoint;
    using tinyobj::cross;
    using tinyobj::dot;
    using tinyobj::GetLength;
    using tinyobj::Normalize;
    using tinyobj::WorldToLocal;
}
