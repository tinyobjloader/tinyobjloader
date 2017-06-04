

#import "NuoMathUtilities.h"


#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>

static matrix_float4x4& to_matrix(glm::mat4x4& gmat)
{
    matrix_float4x4* result = (matrix_float4x4*)(&gmat);
    return *result;
}

matrix_float4x4 matrix_float4x4_translation(vector_float3 t)
{
    glm::vec3 gt(t.x, t.y, t.z);
    glm::mat4x4 gmat = glm::translate(glm::mat4x4(1.0), gt);
    
    return to_matrix(gmat);
}

matrix_float4x4 matrix_float4x4_uniform_scale(float scale)
{
    glm::mat4x4 gmat = glm::scale(glm::mat4x4(1.0), glm::vec3(scale));
    return to_matrix(gmat);
}

matrix_float4x4 matrix_float4x4_rotation(vector_float3 axis, float angle)
{
    glm::vec3 gaxis(axis.x, axis.y, axis.z);
    glm::mat4x4 gmat = glm::rotate(glm::mat4x4(1.0), -angle, gaxis);
    
    return to_matrix(gmat);
}

matrix_float4x4 matrix_float4x4_perspective(float aspect, float fovy, float near, float far)
{
    glm::mat4x4 gmat = glm::perspective(fovy, aspect, near, far);
    return to_matrix(gmat);
}

matrix_float3x3 matrix_float4x4_extract_linear(matrix_float4x4 m)
{
    vector_float3 X = m.columns[0].xyz;
    vector_float3 Y = m.columns[1].xyz;
    vector_float3 Z = m.columns[2].xyz;
    matrix_float3x3 l = { X, Y, Z };
    return l;
}