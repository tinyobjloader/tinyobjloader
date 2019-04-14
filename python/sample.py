import sys
import tinyobj

filename = "../models/cornell_box.obj";

config = tinyobj.ObjReaderConfig()

reader = tinyobj.ObjReader()

ret = reader.ParseFromFile(filename, config)

if ret == False:
    print("Failed to load : ", filename)
    sys.exit(-1)

attrib = reader.GetAttrib()
print("attrib.vertices = ", len(attrib.vertices))
for v in attrib.vertices:
    print(v)

# TODO(syoyo): print mesh
for shape in reader.GetShapes():
    print(shape.name)
    print(len(shape.mesh.indices))
