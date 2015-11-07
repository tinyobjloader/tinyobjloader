import tinyobjloader as tol
import json

model = tol.LoadObj("cornell_box_multimaterial.obj")

#print(model["shapes"], model["materials"])
print( json.dumps(model, indent=4) )

#see cornell_box_output.json
