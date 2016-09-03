#import "ModelView.h"



@interface ModelRenderer : NSObject <NuoMetalViewDelegate>


@property (nonatomic, assign) float rotationX;
@property (nonatomic, assign) float rotationY;
@property (nonatomic, assign) float zoom;


- (void)loadMesh:(NSString*)path;

@end
