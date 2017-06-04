#import <simd/simd.h>
#import <Metal/Metal.h>



typedef struct
{
    matrix_float4x4 modelViewProjectionMatrix;
    matrix_float4x4 modelViewMatrix;
    matrix_float3x3 normalMatrix;
}
ModelUniforms;
