//
//  NuoMaterial.hpp
//  ModelViewer
//
//  Created by middleware on 8/28/16.
//  Copyright © 2016 middleware. All rights reserved.
//

#ifndef NuoMaterial_hpp
#define NuoMaterial_hpp

#include <string>
#include "tiny_obj_loader.h"


class NuoMaterial
{
private:
    int id;
    
    std::string ambient_texname;             // map_Ka
    std::string diffuse_texname;             // map_Kd
    std::string specular_texname;            // map_Ks
    std::string specular_highlight_texname;  // map_Ns
    std::string bump_texname;                // map_bump, bump
    std::string displacement_texname;        // disp
    std::string alpha_texname;               // map_d
    
    // PBR extension
    // http://exocortex.com/blog/extending_wavefront_mtl_to_support_pbr
    float roughness;                // [0, 1] default 0
    float metallic;                 // [0, 1] default 0
    float sheen;                    // [0, 1] default 0
    float clearcoat_thickness;      // [0, 1] default 0
    float clearcoat_roughness;      // [0, 1] default 0
    float anisotropy;               // aniso. [0, 1] default 0
    float anisotropy_rotation;      // anisor. [0, 1] default 0
    std::string roughness_texname;  // map_Pr
    std::string metallic_texname;   // map_Pm
    std::string sheen_texname;      // map_Ps
    std::string emissive_texname;   // map_Ke
    std::string normal_texname;     // norm. For normal mapping.
    
public:
    NuoMaterial();
    NuoMaterial(const tinyobj::material_t& material);
    
    bool operator < (const NuoMaterial& other) const;
};


#endif /* NuoMaterial_hpp */
