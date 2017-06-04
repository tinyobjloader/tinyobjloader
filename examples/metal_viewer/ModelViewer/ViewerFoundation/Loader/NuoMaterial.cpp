//
//  NuoMaterial.cpp
//  ModelViewer
//
//  Created by middleware on 8/28/16.
//  Copyright © 2016 middleware. All rights reserved.
//

#include "NuoMaterial.h"



NuoMaterial::NuoMaterial() : id(-1)
{
}



NuoMaterial::NuoMaterial(const tinyobj::material_t& material) :
    id(0),

    ambient_texname(material.ambient_texname),
    diffuse_texname(material.diffuse_texname),
    specular_texname(material.specular_texname),
    specular_highlight_texname(material.specular_highlight_texname),
    bump_texname(material.bump_texname),
    displacement_texname(material.displacement_texname),
    alpha_texname(material.alpha_texname),

    // PBR extension
    roughness_texname(material.roughness_texname),
    metallic_texname(material.metallic_texname),
    sheen_texname(material.sheen_texname),
    emissive_texname(material.emissive_texname),
    normal_texname(material.normal_texname)
{
}



bool NuoMaterial::operator < (const NuoMaterial& other) const
{
    if (id < other.id)
        return true;
    
    if (id > other.id)
        return false;
    
    return
        (ambient_texname < other.ambient_texname             &&
         diffuse_texname < other.diffuse_texname             &&
         specular_texname < other.specular_texname           &&
         specular_highlight_texname < other.specular_texname &&
         bump_texname < other.bump_texname                   &&
         displacement_texname < other.displacement_texname   &&
         alpha_texname < other.alpha_texname                 &&
    
         // PBR extension
         roughness_texname < other.roughness_texname         &&
         metallic_texname < other.metallic_texname           &&
         sheen_texname < other.sheen_texname                 &&
         emissive_texname < other.emissive_texname           &&
         normal_texname < other.normal_texname);
}
