/**
 * Parses OBJ/MTL off the main thread so large models do not freeze the UI.
 * The wasm module is instantiated lazily inside the worker; results are plain
 * objects with transferable typed arrays.
 */
import { initTinyObj } from '../js/index.js';

let tinyobj = null;

self.onmessage = async (event) => {
  const { id, obj, mtl, mtlName } = event.data;
  try {
    if (!tinyobj) tinyobj = await initTinyObj();
    self.postMessage({ id, type: 'progress', stage: 'parsing' });
    const model = tinyobj.parse(obj, mtl ? { mtl, mtlName } : {});
    const result = {
      id,
      type: 'done',
      heapBytes: tinyobj.module.HEAPU8.byteLength,
      model: {
        shapes: model.shapes.map((shape) => ({
          name: shape.name,
          vertices: shape.vertices,
          cornerVertices: shape.cornerVertices,
          cornerSkin: shape.cornerSkin,
          triangleCount: shape.triangleCount,
          groups: shape.groups,
          tagLines: shape.tagLines,
        })),
        materials: model.materials,
        skinWeights: model.skinWeights,
        skelLines: model.skelLines,
        message: model.message,
      },
    };
    const transfer = [];
    for (const shape of result.model.shapes) {
      transfer.push(shape.vertices.buffer);
      transfer.push(shape.cornerVertices.buffer);
      if (shape.cornerSkin) transfer.push(shape.cornerSkin.buffer);
    }
    self.postMessage(result, transfer);
  } catch (error) {
    self.postMessage({
      id,
      type: 'error',
      message: error?.message || String(error),
      result: error?.result,
    });
  }
};
