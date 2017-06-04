//
//  NuoModelBase.hpp
//  ModelViewer
//
//  Created by middleware on 8/28/16.
//  Copyright © 2016 middleware. All rights reserved.
//

#ifndef NuoModelBase_hpp
#define NuoModelBase_hpp

#include <vector>
#include <string>

#include <simd/simd.h>



const extern std::string kNuoModelType_Simple;



class NuoModelBase;


class NuoBox
{
public:
    float _centerX;
    float _centerY;
    float _centerZ;
    
    float _spanX;
    float _spanY;
    float _spanZ;
};



std::shared_ptr<NuoModelBase> CreateModel(std::string type);



class NuoModelBase : public std::enable_shared_from_this<NuoModelBase>
{
protected:
    std::vector<uint32_t> _indices;
    
public:
    virtual void AddPosition(size_t sourceIndex, const std::vector<float>& positionsBuffer) = 0;
    virtual void AddNormal(size_t sourceIndex, const std::vector<float>& normalBuffer) = 0;
    virtual void GenerateIndices() = 0;
    virtual void GenerateNormals() = 0;
    
    virtual size_t GetVerticesNumber() = 0;
    virtual vector_float4 GetPosition(size_t index) = 0;
    virtual NuoBox GetBoundingBox();
    
    virtual void* Ptr() = 0;
    virtual size_t Length() = 0;
    virtual void* IndicesPtr();
    virtual size_t IndicesLength();
};



class NuoModelSimple : public NuoModelBase
{
protected:
    struct Item
    {
        vector_float4 _position;
        vector_float4 _normal;
        
        bool operator == (const Item& i2);
        
        Item();
    };
    
    std::vector<Item> _buffer;
    
public:
    NuoModelSimple();
    
    virtual void AddPosition(size_t sourceIndex, const std::vector<float>& positionsBuffer) override;
    virtual void AddNormal(size_t sourceIndex, const std::vector<float>& normalBuffer) override;
    virtual void GenerateIndices() override;
    virtual void GenerateNormals() override;
    
    virtual size_t GetVerticesNumber() override;
    virtual vector_float4 GetPosition(size_t index) override;
    
    virtual void* Ptr() override;
    virtual size_t Length() override;
};



#endif /* NuoModelBase_hpp */
