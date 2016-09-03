//
//  NuoModelLoader.m
//  ModelViewer
//
//  Created by middleware on 8/26/16.
//  Copyright © 2016 middleware. All rights reserved.
//

#import "NuoModelLoader.h"

#include "NuoModelBase.h"
#include "NuoMaterial.h"
#include "NuoMesh.h"

#include "tiny_obj_loader.h"



typedef std::vector<tinyobj::shape_t> ShapeVector;
typedef std::shared_ptr<ShapeVector> PShapeVector;




static void DoSplitShapes(const PShapeVector result, const tinyobj::shape_t shape)
{
    tinyobj::mesh_t mesh = shape.mesh;
    
    assert(mesh.num_face_vertices.size() == mesh.material_ids.size());
    
    
    size_t faceAccount = mesh.num_face_vertices.size();
    size_t i = 0;
    for (i = 0; i < faceAccount - 1; ++i)
    {
        unsigned char numPerFace1 = mesh.num_face_vertices[i];
        unsigned char numPerFace2 = mesh.num_face_vertices[i+1];
        
        int material1 = mesh.material_ids[i];
        int material2 = mesh.material_ids[i+1];
        
        if (numPerFace1 != numPerFace2 || material1 != material2)
        {
            tinyobj::shape_t splitShape;
            tinyobj::shape_t remainShape;
            splitShape.name = shape.name;
            remainShape.name = shape.name;
            
            std::vector<tinyobj::index_t>& addedIndices = splitShape.mesh.indices;
            std::vector<tinyobj::index_t>& remainIndices = remainShape.mesh.indices;
            addedIndices.insert(addedIndices.begin(),
                                mesh.indices.begin(),
                                mesh.indices.begin() + i * numPerFace1);
            remainIndices.insert(remainIndices.begin(),
                                 mesh.indices.begin() + i * numPerFace1,
                                 mesh.indices.end());
            
            std::vector<unsigned char>& addedNumberPerFace = splitShape.mesh.num_face_vertices;
            std::vector<unsigned char>& remainNumberPerFace = remainShape.mesh.num_face_vertices;
            addedNumberPerFace.insert(addedNumberPerFace.begin(),
                                      mesh.num_face_vertices.begin(),
                                      mesh.num_face_vertices.begin() + i);
            remainNumberPerFace.insert(remainNumberPerFace.begin(),
                                       mesh.num_face_vertices.begin() + i,
                                       mesh.num_face_vertices.end());
            
            std::vector<int>& addedMaterial = splitShape.mesh.material_ids;
            std::vector<int>& remainMaterial = remainShape.mesh.material_ids;
            addedMaterial.insert(addedMaterial.begin(),
                                 mesh.material_ids.begin(),
                                 mesh.material_ids.begin() + i);
            remainMaterial.insert(remainMaterial.begin(),
                                  mesh.material_ids.begin() + i,
                                  mesh.material_ids.end());
            
            result->push_back(splitShape);
            DoSplitShapes(result, remainShape);
            break;
        }
    }
    
    if (i == faceAccount - 1)
        result->push_back(shape);
}



static tinyobj::shape_t DoMergeShapes(std::vector<tinyobj::shape_t> shapes)
{
    tinyobj::shape_t result;
    result.name = shapes[0].name;
    
    for (const auto& shape : shapes)
    {
        result.mesh.indices.insert(result.mesh.indices.end(),
                                   shape.mesh.indices.begin(),
                                   shape.mesh.indices.end());
        result.mesh.material_ids.insert(result.mesh.material_ids.end(),
                                        shape.mesh.material_ids.begin(),
                                        shape.mesh.material_ids.end());
        result.mesh.num_face_vertices.insert(result.mesh.num_face_vertices.end(),
                                             shape.mesh.num_face_vertices.begin(),
                                             shape.mesh.num_face_vertices.end());
    }
    
    return result;
}




static void DoMergeShapesInVector(const PShapeVector result, std::vector<tinyobj::material_t>& materials)
{
    typedef std::map<NuoMaterial, std::vector<tinyobj::shape_t>> ShapeMap;
    ShapeMap shapesMap;
    
    NuoMaterial nonMaterial;
    
    for (size_t i = 0; i < result->size(); ++i)
    {
        const auto& shape = (*result)[i];
        int shapeMaterial = shape.mesh.material_ids[0];
        
        if (shapeMaterial < 0)
        {
            shapesMap[nonMaterial].push_back(shape);
        }
        else
        {
            tinyobj::material_t material = materials[(size_t)shapeMaterial];
            NuoMaterial materialIndex(material);
            shapesMap[materialIndex].push_back(shape);
        }
    }
    
    result->clear();
    
    for (auto itr = shapesMap.begin(); itr != shapesMap.end(); ++itr)
    {
        std::vector<tinyobj::shape_t>& shapes = itr->second;
        result->push_back(DoMergeShapes(shapes));
    }
}




static PShapeVector GetShapeVector(ShapeVector& shapes, std::vector<tinyobj::material_t> &materials)
{
    PShapeVector result = std::make_shared<ShapeVector>();
    for (const auto& shape : shapes)
        DoSplitShapes(result, shape);
    
    DoMergeShapesInVector(result, materials);
    
    return result;
}




@implementation NuoModelLoader



-(NSArray<NuoMesh*>*)loadModelObjects:(NSString*)objPath
                             withType:(NSString*)type
                           withDevice:(id<MTLDevice>)device
{
    typedef std::shared_ptr<NuoModelBase> PNuoModelBase;
    
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string err;
    
    tinyobj::LoadObj(&attrib, &shapes, &materials, &err, objPath.UTF8String);
    
    PShapeVector shapeVector = GetShapeVector(shapes, materials);
    
    std::vector<PNuoModelBase> models;
    std::vector<uint32> indices;
    
    for (const auto& shape : (*shapeVector))
    {
        PNuoModelBase modelBase = CreateModel(type.UTF8String);
        
        for (size_t i = 0; i < shape.mesh.indices.size(); ++i)
        {
            tinyobj::index_t index = shape.mesh.indices[i];
            
            modelBase->AddPosition(index.vertex_index, attrib.vertices);
            if (attrib.normals.size())
                modelBase->AddNormal(index.normal_index, attrib.normals);
        }
        
        modelBase->GenerateIndices();
        if (!attrib.normals.size())
            modelBase->GenerateNormals();
        
        models.push_back(modelBase);
    }
    
    float xMin = 1e9f, xMax = -1e9f;
    float yMin = 1e9f, yMax = -1e9f;
    float zMin = 1e9f, zMax = -1e9f;
    
    NSMutableArray<NuoMesh*>* result = [[NSMutableArray<NuoMesh*> alloc] init];
    
    for (auto& model : models)
    {
        NuoBox boundingBox = model->GetBoundingBox();
        
        float xRadius = boundingBox._spanX / 2.0f;
        float yRadius = boundingBox._spanY / 2.0f;
        float zRadius = boundingBox._spanZ / 2.0f;
        
        xMin = std::min(xMin, boundingBox._centerX - xRadius);
        xMax = std::max(xMax, boundingBox._centerX + xRadius);
        yMin = std::min(yMin, boundingBox._centerY - yRadius);
        yMax = std::max(yMax, boundingBox._centerY + yRadius);
        zMin = std::min(zMin, boundingBox._centerZ - zRadius);
        zMax = std::max(zMax, boundingBox._centerZ + zRadius);
        
        NuoMesh* mesh = [[NuoMesh alloc] initWithDevice:device
                                     withVerticesBuffer:model->Ptr()
                                             withLength:model->Length()
                                            withIndices:model->IndicesPtr()
                                             withLength:model->IndicesLength()];
        
        NuoMeshBox* meshBounding = [[NuoMeshBox alloc] init];
        meshBounding.spanX = boundingBox._spanX;
        meshBounding.spanY = boundingBox._spanY;
        meshBounding.spanZ = boundingBox._spanZ;
        meshBounding.centerX = boundingBox._centerX;
        meshBounding.centerY = boundingBox._centerY;
        meshBounding.centerZ = boundingBox._centerZ;
        
        mesh.boundingBox = meshBounding;
        [result addObject:mesh];
    }
    
    return result;
}

@end
