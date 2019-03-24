import sys
import tinyobjloader

filename = "../models/cornell_box.obj";

config = tinyobjloader.ObjLoaderConfig()

loader = tinyobjloader.ObjLoader()

ret = loader.Load(filename, config)

if ret == False:
    print("Failed to load : ", filename)
    sys.exit(-1)

attrib = loader.GetAttrib()
print("attrib.vertices = ", len(attrib.vertices))
for v in attrib.vertices:
    print(v)
