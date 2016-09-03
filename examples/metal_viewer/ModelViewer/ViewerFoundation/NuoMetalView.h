#import <Cocoa/Cocoa.h>
#import <Metal/Metal.h>
#import <Quartz/Quartz.h>

@protocol NuoMetalViewDelegate;



@interface NuoMetalView : NSView

/**
 *  The delegate of this view, responsible for maintain the model/scene state,
 *  and the rendering
 */
@property (nonatomic, weak) id<NuoMetalViewDelegate> delegate;

@property (nonatomic) NSInteger preferredFramesPerSecond;

@property (nonatomic) MTLPixelFormat colorPixelFormat;
@property (nonatomic, assign) MTLClearColor clearColor;

@property (nonatomic, readonly) id<CAMetalDrawable> currentDrawable;
@property (nonatomic, readonly) MTLRenderPassDescriptor *currentRenderPassDescriptor;

@property (nonatomic, readonly) CGSize drawableSize;


- (void)commonInit;


/**
 *  Notify the view to render the model/scene (i.e. in turn notifying the delegate)
 */
- (void)render;

@end



@protocol NuoMetalViewDelegate <NSObject>

- (void)drawInView:(NuoMetalView *)view;

@end
