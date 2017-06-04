//
//  NuoModelLoader.h
//  ModelViewer
//
//  Created by middleware on 8/26/16.
//  Copyright © 2016 middleware. All rights reserved.
//

#import <Foundation/Foundation.h>


@class NuoMesh;


@interface NuoModelLoader : NSObject

-(NSArray<NuoMesh*>*) loadModelObjects:(NSString*)objPath
                              withType:(NSString*)type
                            withDevice:(id<MTLDevice>)device;

@end
