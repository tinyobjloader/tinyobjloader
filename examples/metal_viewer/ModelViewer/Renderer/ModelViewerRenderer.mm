#import "ModelViewerRenderer.h"
#import "ModelUniforms.h"

#import <Metal/Metal.h>
#import <QuartzCore/QuartzCore.h>
#import <simd/simd.h>

#include "NuoMesh.h"
#include "NuoMathUtilities.h"
#include "NuoModelBase.h"
#include "NuoModelLoader.h"

static const NSInteger InFlightBufferCount = 3;

@interface ModelRenderer ()

@property (strong) id<MTLDevice> device;
@property (strong) NSArray<NuoMesh*>* mesh;
@property (strong) NSArray<id<MTLBuffer>>* uniformBuffers;
@property (strong) id<MTLCommandQueue> commandQueue;
@property (strong) id<MTLRenderPipelineState> renderPipelineState;
@property (strong) id<MTLDepthStencilState> depthStencilState;
@property (strong) dispatch_semaphore_t displaySemaphore;
@property (assign) NSInteger bufferIndex;

@end

@implementation ModelRenderer

- (instancetype)init
{
    if ((self = [super init]))
    {
        _device = MTLCreateSystemDefaultDevice();
        _displaySemaphore = dispatch_semaphore_create(InFlightBufferCount);
        _commandQueue = [self.device newCommandQueue];
        [self makeResources];
    }

    return self;
}

- (void)loadMesh:(NSString*)path
{
    NuoModelLoader* loader = [NuoModelLoader new];
    _mesh = [loader loadModelObjects:path
                            withType:[NSString stringWithUTF8String:kNuoModelType_Simple.c_str()]
                          withDevice:_device];
}

- (void)makeResources
{
    id<MTLBuffer> buffers[InFlightBufferCount];
    for (size_t i = 0; i < InFlightBufferCount; ++i)
    {
        id<MTLBuffer> uniformBuffer = [self.device newBufferWithLength:sizeof(ModelUniforms)
                                                               options:MTLResourceOptionCPUCacheModeDefault];
        buffers[i] = uniformBuffer;
        
        NSString* label = [NSString stringWithFormat:@"Uniforms %lu", i];
        [uniformBuffer setLabel:label];
    }
    _uniformBuffers = [[NSArray alloc] initWithObjects:buffers[0], buffers[1], buffers[2], nil];
}

- (void)updateUniformsForView:(NuoMetalView *)viewBase
{
    ModelView* view = (ModelView*)viewBase;
    
    float scaleFactor = 1;
    const vector_float3 xAxis = { 1, 0, 0 };
    const vector_float3 yAxis = { 0, 1, 0 };
    const matrix_float4x4 xRot = matrix_float4x4_rotation(xAxis, self.rotationX);
    const matrix_float4x4 yRot = matrix_float4x4_rotation(yAxis, self.rotationY);
    const matrix_float4x4 scale = matrix_float4x4_uniform_scale(scaleFactor);
    const matrix_float4x4 rotationMatrix = matrix_multiply(matrix_multiply(xRot, yRot), scale);

    NuoMeshBox* bounding = _mesh[0].boundingBox;
    for (size_t i = 1; i < _mesh.count; ++i)
        bounding = [bounding unionWith:_mesh[i].boundingBox];
    
    const vector_float3 translationToCenter =
    {
        - bounding.centerX,
        - bounding.centerY,
        - bounding.centerZ
    };
    const matrix_float4x4 modelCenteringMatrix = matrix_float4x4_translation(translationToCenter);
    const matrix_float4x4 modelMatrix = matrix_multiply(rotationMatrix, modelCenteringMatrix);
    
    float modelSpanZ = bounding.spanZ;
    float modelNearest = - modelSpanZ / 2.0;
    
    const vector_float3 cameraTranslation =
    {
        0, 0,
        (modelNearest - modelSpanZ) + _zoom * modelSpanZ / 20.0f
    };

    const matrix_float4x4 viewMatrix = matrix_float4x4_translation(cameraTranslation);

    const CGSize drawableSize = view.drawableSize;
    const float aspect = drawableSize.width / drawableSize.height;
    const float fov = (2 * M_PI) / 8;
    const float near = 0.1;
    const float far = -(modelNearest - modelSpanZ) + modelSpanZ * 2.0f - _zoom * modelSpanZ / 20.0f;
    const matrix_float4x4 projectionMatrix = matrix_float4x4_perspective(aspect, fov, near, far);

    ModelUniforms uniforms;
    uniforms.modelViewMatrix = matrix_multiply(viewMatrix, modelMatrix);
    uniforms.modelViewProjectionMatrix = matrix_multiply(projectionMatrix, uniforms.modelViewMatrix);
    uniforms.normalMatrix = matrix_float4x4_extract_linear(uniforms.modelViewMatrix);

    memcpy([self.uniformBuffers[self.bufferIndex] contents], &uniforms, sizeof(uniforms));
}

- (void)drawInView:(NuoMetalView *)view
{
    dispatch_semaphore_wait(self.displaySemaphore, DISPATCH_TIME_FOREVER);

    view.clearColor = MTLClearColorMake(0.95, 0.95, 0.95, 1);

    [self updateUniformsForView:view];

    id<MTLCommandBuffer> commandBuffer = [self.commandQueue commandBuffer];

    MTLRenderPassDescriptor *passDescriptor = [view currentRenderPassDescriptor];
    id<MTLRenderCommandEncoder> renderPass = [commandBuffer renderCommandEncoderWithDescriptor:passDescriptor];
    
    [renderPass setVertexBuffer:self.uniformBuffers[self.bufferIndex] offset:0 atIndex:1];

    for (NuoMesh* mesh : _mesh)
        [mesh drawMesh:renderPass];

    [renderPass endEncoding];

    [commandBuffer presentDrawable:view.currentDrawable];
    [commandBuffer addCompletedHandler:^(id<MTLCommandBuffer> commandBuffer) {
        self.bufferIndex = (self.bufferIndex + 1) % InFlightBufferCount;
        dispatch_semaphore_signal(self.displaySemaphore);
    }];
    
    [commandBuffer commit];
}

@end
