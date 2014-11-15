import tinyobjloader as tol

model = tol.LoadObj("cube.obj")

print(model["shapes"], model["materials"])
